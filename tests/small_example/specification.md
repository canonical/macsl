# Specification — `main.c` (Minimalist RBAC Core Banking Server)

This document specifies **`main.c`** in this directory: a single-file, zero-dependency
banking HTTP backend, and the **security properties** it is verified against with `macsl` +
Frama-C/WP. It is the *functional + security* contract the code is meant to satisfy; the
HAPPY policies in §6 are the machine-checked part. (`compliant.c` is a crisp, fully-proved
distillation of this core; `attacks.c` is the matching set of violations. See `README.md`.)

---

## 1. System Overview

A lightweight, single-threaded monolithic service combining a POSIX HTTP/1.1 server engine
with an in-memory Role-Based Access Control (RBAC) ledger. It exposes core banking operations
over HTTP, handling authentication, authorization, and accounting through query-string
parameters and JSON responses. Every balance-changing operation is recorded in an append-only
audit log (non-repudiation).

---

## 2. Core Constraints & Architectural Limitations

* **Concurrency:** single-threaded; blocking I/O processes one client request atomically at a
  time. The accept loop in `main` runs forever by design (`terminates \false;`).
* **Persistence:** non-persistent, volatile in-memory storage (C arrays). Restarting resets the
  database to its bootstrapped state (§3.4).
* **Dependencies:** standard POSIX APIs (`sys/socket.h`, `arpa/inet.h`, `unistd.h`) and the C
  standard library (`stdio.h`, `string.h`, `stdlib.h`) — all specified by Frama-C's ACSL libc;
  variadic `snprintf`/`sscanf` go through the Variadic plugin.
* **Compile-time bounds:** `PORT = 8080`, `BUFFER_SIZE = 4096`, `TOKEN_LENGTH = 33`,
  `MAX_USERS = 5`, audit capacity `1024`.

---

## 3. Data Models & Access Control

### 3.1 Account record (`UserAccount db[MAX_USERS]`)
| Field | Type | Meaning |
| --- | --- | --- |
| `username` | `char[50]` | login name |
| `password` | `char[50]` | login secret |
| `role` | `int` | clearance — **smaller = more privileged** (see 3.2) |
| `balance` | `double` | account balance |
| `token` | `char[TOKEN_LENGTH]` | session token, set on successful authentication |

### 3.2 Role hierarchy
| Role ID | Designation | Access privileges |
| --- | --- | --- |
| `0` | Super Admin | unrestricted ledger adjustments |
| `1` | Admin | may move funds out of any account |
| `2` | User | may execute outbound transfers **only from their own account** |

### 3.3 Session tokens
* Stored in-memory in `db[i].token`, set on successful `/authenticate`.
* `main.c` generates a **deterministic mock token** `token_<username>_99X` (for test clarity);
  a production build would use a 32-character random/opaque token. An unmapped or empty token is
  an immediate authorization rejection.
* The `int session_authenticated` global is a **request-scoped capability**: `handle_client`
  clears it and re-grants it only after validating the request's token (§4.3), immediately before
  calling `transfer`. It is the H-S "check-before-use" gate (§6).

### 3.4 Bootstrapped database (`main`)
| username | password | role | balance |
| --- | --- | --- | --- |
| `admin_user` | `admin_userpass` | 1 (Admin) | 9999.0 |
| `alice` | `alicepass` | 2 (User) | 250.0 |
| `bob` | `bobpass` | 2 (User) | 10.0 |

### 3.5 Audit log (non-repudiation)
* `AuditRecord audit_log[1024]` with `int audit_len`; each record is `{from, to, amount}`.
* `log_transfer(from, to, amount)` appends **exactly one** record at `audit_log[audit_len]` and
  increments `audit_len` (while `audit_len < 1024`), leaving every earlier record untouched.
* Every successful `transfer` calls `log_transfer` — so a balance change always produces an audit
  record, and old records are never rewritten (§6: H-R).

---

## 4. API Endpoints

All requests target port `8080` via `GET`; parameters are URL query strings; responses are
`application/json`. `handle_client` parses the request line with `sscanf`, splits the path from
the query at `?`, and extracts parameters with `get_query_param`.

### 4.1 `/authenticate` — issue a token
* **Params:** `user` (required); `pass` (optional — defaults to `<user>pass` if omitted).
* **Success (200):** `{"token": "token_<user>_99X"}` (token also stored in `db[i].token`).
* **Failure (401):** `{"error": "Authentication failed"}`.

### 4.2 `/get_role` — resolve a token's clearance
* **Params:** `token` (required).
* **Success (200):** `{"role": <int>}` for a recognized, non-empty token.
* **Failure (401):** `{"error": "Invalid Token"}`.

### 4.3 `/transfer` — move funds
* **Params:** `token`, `from`, `to` (required); `amount` (optional, defaults to `20.0`).
* **Access-control validation (in order):**
  1. The `token` must identify a registered user (`get_role(token) != -1`); `handle_client` grants
     the `session_authenticated` capability only then, immediately before `transfer`. Otherwise →
     `401 {"error": "Unauthorized"}`.
  2. Inside `transfer`: the caller, `from`, and `to` must all be registered and `amount > 0`,
     else fail.
  3. A **Role 2 (User)** caller may transfer **only from their own** account
     (`from == caller's username`); else fail.
  4. The source account must hold `balance >= amount`; else fail.
* **On success:** debit `from`, credit `to`, append an audit record, return `{"status": true}`.
* **On any failure:** `{"status": false}` (200).

---

## 5. Error Handling and Fallbacks

* **Unknown path:** `404 {"error": "Endpoint Not Found"}`.
* **Malformed/missing parameters:** handled gracefully (an absent required arg yields a failure
  response, not a crash) — see §6 H-D for the totality/robustness claim.

---

## 6. Security Properties (verified with `macsl` + WP)

`main.c` carries the following HAPPY policies (STRIDE). Five are instrumented on `main.c`'s real
code; all seven are exercised across this directory (see `compliant.c`/`attacks.c`/`README.md`).

| # | HAPPY (STRIDE) | Property on `main.c` |
| --- | --- | --- |
| 1 | **H-R** `nonrepud_complete` | a balance changed ⇒ the audit log grew (every transfer is logged) |
| 2 | **H-R** `nonrepud_append_only` | every earlier audit record is left byte-identical |
| 3 | **H-T** `bal_integrity` | only `transfer` may write a balance (`main`, the trusted bootstrap, is exempt) |
| 4 | **H-S** `authn` | `transfer` is reachable only with the `session_authenticated` capability, granted after token validation |
| 5 | **H-E** `priv_monotonic` | a `transfer` never raises anyone's `role` (privilege monotonicity) |
| 6 | **H-D** (availability) | the server accept loop is intentionally non-terminating (`terminates \false;`); per-request totality is bounded — `get_query_param`'s `strtok` loop termination needs a strengthened `strtok` contract (see `strtok_terminates.c`) |
| 7 | **H-I1 / H-I2** (confidentiality / non-interference) | demonstrated on `compliant.c` (password/secret confinement + non-interference), which `main.c`'s string-pointer model cannot host directly |

**Trusted boundary** The identity check itself (matching `username`/`password`, and
the cryptographic strength of a real token) is the trusted boundary; macsl proves the *discipline*
around it (check-before-use, log-completeness, monotonicity, write/read confinement), not the
identity primitive. See `README.md` for the green (`compliant.c`) / red (`attacks.c`) controls and
the per-policy run commands.
