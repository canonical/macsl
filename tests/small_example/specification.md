# Software Requirements and API Specification: Minimalist RBAC Core Banking Server

This document outlines the system architecture, data models, functional requirements, and API specifications for the minimalist, zero-dependency embedded web application implemented in pure C.

---

## 1. System Overview

The application is a lightweight, single-threaded monolithic service that combines a POSIX-compliant HTTP/1.1 web server engine with an in-memory role-based access control (RBAC) ledger. The purpose of this system is to expose core banking operations over standard HTTP protocols, handling authentication, authorization checking, and accounting operations through JSON payloads.

---

## 2. Core Constraints & Architectural Limitations

* **Concurrency:** Single-threaded execution. Blocking I/O loops process one HTTP client request atomically at a time.
* **Persistence:** Non-persistent, volatile in-memory storage (C array structural representation). Restarting the application resets the database to its bootstrapped state.
* **Dependencies:** Strict reliance on standard POSIX APIs (`sys/socket.h`, `arpa/inet.h`, `unistd.h`) and standard C library headers (`stdio.h`, `string.h`, `stdlib.h`).

---

## 3. Data Models & Access Control Policies

### 3.1 Role Hierarchy

The system enforces a tiered authorization matrix mapping integer values to security clearances:

| Role ID | Designation | Access Privileges |
| --- | --- | --- |
| `0` | Super Admin | Complete structural rights, configuration modifications, unrestricted financial ledger adjustments. |
| `1` | Admin | Administrative oversight, capacity to move funds out of any target account. |
| `2` | User | Restricted sandbox access. Can view own status and execute outbound transactions *only* from their verified account. |

### 3.2 Session Tokens

* Formatted as safe alphanumeric strings (32 hexadecimal characters + Null Terminator).
* Generated upon successful authentication.
* Stored strictly in-memory alongside user records. Passing an unmapped or null token constitutes an immediate authorization rejection.

---

## 4. API Endpoints Specification

All incoming HTTP requests must target port `8080` using the `GET` method. Parameters are supplied using standard URL query strings. Responses are returned with an `application/json` Content-Type header.

### 4.1 Authenticate User

Generates a valid tracking token against recognized username and password matches.

* **Endpoint:** `/authenticate`
* **Query Parameters:**
* `user` (string, required): The target username.
* `pass` (string, optional): The target password (system defaults to `<username>pass` if omitted).



#### Sample Request

```http
GET /authenticate?user=alice&pass=alicepass HTTP/1.1
Host: localhost:8080

```

#### Expected Responses

* **Success (200 OK):**
```json
{"token": "token_alice_99X"}

```


* **Failure (401 Unauthorized):**
```json
{"error": "Authentication failed"}

```



---

### 4.2 Fetch Identity Role

Inspects the system context to identify the authorization level granted to an active session token.

* **Endpoint:** `/get_role`
* **Query Parameters:**
* `token` (string, required): A session token obtained via `/authenticate`.



#### Sample Request

```http
GET /get_role?token=token_alice_99X HTTP/1.1
Host: localhost:8080

```

#### Expected Responses

* **Success (200 OK):**
```json
{"role": 2}

```


* **Failure (401 Unauthorized):**
```json
{"error": "Invalid Token"}

```



---

### 4.3 Transfer Funds

Executes a balance transfer transaction between two ledger accounts.

* **Endpoint:** `/transfer`
* **Query Parameters:**
* `token` (string, required): Token belonging to the entity calling the command.
* `from` (string, required): The source account username to be debited.
* `to` (string, required): The destination account username to be credited.
* `amount` (float, optional): Total numeric cash value to move.



#### Access Control Validation Logic

Before executing a financial operation, the core application checks permissions sequentially:

1. Is the provided `token` active and valid?
2. If the user tied to that token has **Role 2 (User)**, does the `from` parameter exactly match their username? If no, fail immediately.
3. If the user has **Role 1 (Admin)** or **Role 0 (Super Admin)**, bypass the identity lookup and permit cross-account debiting.
4. Does the source (`from`) account hold a balance greater than or equal to the requested `amount`? If no, fail.

#### Sample Request

```http
GET /transfer?token=token_alice_99X&from=alice&to=bob&amount=50.00 HTTP/1.1
Host: localhost:8080

```

#### Expected Responses

* **Success (200 OK - Transaction Completed):**
```json
{"status": true}

```


* **Failure (200 OK - Denied due to Insufficient Funds, Incorrect Role, or Missing User):**
```json
{"status": false}

```



---

## 5. Error Handling and Fallbacks

* **Invalid Endpoints:** Any resource request outside the explicit paths listed above (`/authenticate`, `/get_role`, `/transfer`) must return an HTTP status code `404 Not Found` paired with a descriptive response payload:
```json
{"error": "Endpoint Not Found"}

```


* **Malformed Inputs:** Missing critical query arguments inside structural parameters triggers failure behavior gracefully (e.g., rejecting an anonymous transfer with a `{"status": false}` payload).
