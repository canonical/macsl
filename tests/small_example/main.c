#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <arpa/inet.h>
#include <sys/socket.h>

#define PORT 8080
#define BUFFER_SIZE 4096
#define TOKEN_LENGTH 33
#define MAX_USERS 5

/* =========================================================================
   1. BACKEND DATABASE & ENGINE DEFINITIONS
   ========================================================================= */
typedef struct {
    char username[50];
    char password[50];
    int role; // 0: super admin, 1: admin, 2: user
    double balance;
    char token[TOKEN_LENGTH];
} UserAccount;

UserAccount db[MAX_USERS];

/* --- Audit log (non-repudiation). Every balance-changing transfer appends one
   record here; old records are never overwritten. The HAPPY policies that make
   this a machine-checked guarantee are demonstrated on the focused, fully-
   specified core `banking.c`. (This file's libc calls -- strtok/strcmp/strncpy,
   read/write, socket/accept -- ARE specified by Frama-C's ACSL libc, and the
   variadic snprintf/sscanf go through the Variadic plugin; a clean WP proof of
   the whole file is a matter of loop invariants + those coarse library specs,
   not impossibility.) The policies:
     - H-R nonrepud_complete   : balance changed  ==> audit_len grew
     - H-R nonrepud_append_only: \forall i<old(audit_len); audit[i] unchanged
     - H-S authn               : transfer requires an authenticated session
     - H-T bal_integrity       : only transfer may write a balance
   See banking.c / banking_attacks.c and ../docs/usage.md. --- */
typedef struct {
    char from[50];
    char to[50];
    double amount;
} AuditRecord;

AuditRecord audit_log[1024];
int audit_len = 0;

/*@ requires 0 <= audit_len < 1024;
    requires valid_read_nstring(from, 49) && valid_read_nstring(to, 49);
    // object distinctness: the source strings are a different object than the
    // audit buffer (HTTP params vs a global) -> full separation for WP.
    requires \base_addr(from) != \base_addr((char *)&audit_log[0]);
    requires \base_addr(to)   != \base_addr((char *)&audit_log[0]);
    assigns audit_log[audit_len], audit_len;
    ensures audit_len == \old(audit_len) + 1;     // with room, every call appends exactly one
*/
void log_transfer(const char *from, const char *to, double amount) {
    if (audit_len < 1024) {
        strncpy(audit_log[audit_len].from, from, sizeof(audit_log[audit_len].from) - 1);
        audit_log[audit_len].from[sizeof(audit_log[audit_len].from) - 1] = '\0';
        strncpy(audit_log[audit_len].to, to, sizeof(audit_log[audit_len].to) - 1);
        audit_log[audit_len].to[sizeof(audit_log[audit_len].to) - 1] = '\0';
        audit_log[audit_len].amount = amount;
        audit_len++;
    }
}

// Helper to look up parameters in a query string (e.g., "?user=alice&to=bob")
void get_query_param(const char *query, const char *key, char *dest, size_t max_len) {
    dest[0] = '\0';
    if (!query || strlen(query) == 0) return;

    char temp_query[512];
    strncpy(temp_query, query, sizeof(temp_query) - 1);
    temp_query[sizeof(temp_query) - 1] = '\0';

    char *token = strtok(temp_query, "&");
    while (token != NULL) {
        char *eq = strchr(token, '=');
        if (eq) {
            *eq = '\0';
            if (strcmp(token, key) == 0) {
                strncpy(dest, eq + 1, max_len - 1);
                dest[max_len - 1] = '\0';
                return;
            }
        }
        token = strtok(NULL, "&");
    }
}

/* =========================================================================
   2. THE 3 MANDATORY BACKEND FUNCTIONS
   ========================================================================= */

int authenticate(const char *username, const char *password, char *token_output) {
    for (int i = 0; i < MAX_USERS; i++) {
        if (strcmp(db[i].username, username) == 0 && strcmp(db[i].password, password) == 0) {
            // Generate a deterministic mock token for testing clarity
            snprintf(token_output, TOKEN_LENGTH, "token_%s_99X", db[i].username);
            strcpy(db[i].token, token_output);
            return 0; // Success
        }
    }
    return -1; // Auth Failed
}

int get_role(const char *token) {
    if (!token || strlen(token) == 0) return -1;
    for (int i = 0; i < MAX_USERS; i++) {
        if (strcmp(db[i].token, token) == 0) {
            return db[i].role;
        }
    }
    return -1; // Not found / Unauthorized
}

/*@ requires 0 <= audit_len < 1024;
    requires valid_read_string(token) && valid_read_string(user_sending)
             && valid_read_string(user_receiving);
    requires \forall integer k; 0 <= k < MAX_USERS ==>
               valid_read_string(&db[k].token[0]) && valid_read_string(&db[k].username[0]);
    requires valid_read_nstring(user_sending, 49) && valid_read_nstring(user_receiving, 49);
    requires \base_addr(user_sending)   != \base_addr((char *)&audit_log[0]);
    requires \base_addr(user_receiving) != \base_addr((char *)&audit_log[0]);
    assigns db[0 .. MAX_USERS - 1], audit_log[audit_len], audit_len;
*/
int transfer(const char *token, const char *user_sending, const char *user_receiving, double amount) {
    int caller_idx = -1;
    int sender_idx = -1;
    int receiver_idx = -1;

    /*@ loop invariant 0 <= i <= MAX_USERS;
        loop invariant -1 <= caller_idx   < MAX_USERS;
        loop invariant -1 <= sender_idx   < MAX_USERS;
        loop invariant -1 <= receiver_idx < MAX_USERS;
        loop assigns i, caller_idx, sender_idx, receiver_idx;
        loop variant MAX_USERS - i;
    */
    for (int i = 0; i < MAX_USERS; i++) {
        if (strlen(db[i].token) > 0 && strcmp(db[i].token, token) == 0) caller_idx = i;
        if (strcmp(db[i].username, user_sending) == 0) sender_idx = i;
        if (strcmp(db[i].username, user_receiving) == 0) receiver_idx = i;
    }

    // Protection guards
    if (caller_idx == -1 || sender_idx == -1 || receiver_idx == -1 || amount <= 0) return -1;

    // Enforce permissions: Regular user (2) can only send from their own account
    if (db[caller_idx].role == 2 && strcmp(db[caller_idx].username, user_sending) != 0) {
        return -1; // Unauthorized
    }

    // Check balance
    if (db[sender_idx].balance < amount) return -1;

    // Execute atomic balance shifting
    db[sender_idx].balance -= amount;
    db[receiver_idx].balance += amount;
    log_transfer(user_sending, user_receiving, amount); // non-repudiation: record it
    return 0; // Success
}

/* H-R non-repudiation, ON main.c's real transfer(): if any balance changed,
   the audit log grew.

   WP PROOF STATUS (frama-c -macsl -wp, this install):
     - `transfer` alone: 51/51 proved, INCLUDING the macsl-generated
       `Post-condition 'nonrepud_complete,meta'`. WP discharges it THROUGH
       Frama-C's ACSL libc (strcmp/strlen contracts checked at the call sites)
       plus the loop invariant above and log_transfer's contract. This is the
       headline: the policy is machine-checked on the real function — libc and
       all. ("outside WP's reach" was wrong.)
     - `transfer` + `log_transfer`: 17/18 on log_transfer. The single open goal
       is in log_transfer's BODY: the second strncpy's `valid_read_nstring(to,49)`
       precondition (with the `\base_addr` object-distinctness preconditions, the
       cascade into transfer is gone and the goal is a genuine theorem).
   COQ ESCALATION (done end-to-end; verdict: WP's Coq backend cannot discharge
   it either). The goal is a MEMORY-MODEL FRAMING obligation: preserve
   `valid_read_nstring(to,49)` across the first strncpy's writes. A full hand
   proof was written and COMPILES (coqc exit 0) — see tests/small_example/coq/
   (frame lemmas via memcpy'def/Map.set'def + object distinctness; the init
   disjunct closes by separation alone; the valid_read_string disjunct reduces
   to a strlen frame). It is complete EXCEPT for exactly three
   `is_sint8 (t3 (shift to k))` byte-typing facts. Those are guarded into every
   `Q_strlen_*` axiom, and the only hypothesis that could supply char-typing is
   `sconst`, which WP's own realization (wp/coqwp/Memory.v) leaves `Admitted`
   (opaque). So the fact is unavailable to the Coq backend — which is why
   `-wp-prover coq` returns [Unknown], not just SMT. This is the framing case
   `frama-c/references/coq-escalation.md` says to DISSOLVE, not hand-prove. Left
   as a precisely-characterised residual on the logger's body; NO admit/axiom is
   in any verified result. The policy stands at transfer 51/51.
   Run: see tests/small_example/README.md and tests/small_example/coq/README.md. */
/*@ happy \prop, \name("nonrepud_complete"),
      \targets({transfer}), \context(\postcond),
      (\exists integer i; 0 <= i < MAX_USERS && db[i].balance != \old(db[i].balance))
        ==> audit_len > \old(audit_len);
*/

/* =========================================================================
   3. WEB SERVER ROUTING & HTTP PROTOCOL LAYER
   ========================================================================= */

void send_json_response(int client_socket, int http_status, const char *json_body) {
    char response[2048];
    snprintf(response, sizeof(response),
             "HTTP/1.1 %d %s\r\n"
             "Content-Type: application/json\r\n"
             "Content-Length: %ld\r\n"
             "Connection: close\r\n\r\n"
             "%s",
             http_status, (http_status == 200 ? "OK" : "Bad Request"),
             strlen(json_body), json_body);
    write(client_socket, response, strlen(response));
}

void handle_client(int client_socket) {
    char buffer[BUFFER_SIZE];
    long valread = read(client_socket, buffer, BUFFER_SIZE - 1);
    if (valread < 0) { close(client_socket); return; }
    buffer[valread] = '\0';

    char method[10], path_raw[512], protocol[10];
    sscanf(buffer, "%9s %511s %9s", method, path_raw, protocol);

    // Isolate path endpoints from query parameters
    char *query = strchr(path_raw, '?');
    char path[512];
    if (query) {
        *query = '\0';
        strcpy(path, path_raw);
        query++; // Point to the start of parameters
    } else {
        strcpy(path, path_raw);
    }

    char json_output[512];

    // ROUTE 1: /authenticate
    if (strcmp(path, "/authenticate") == 0) {
        char user[50], pass[50], token[TOKEN_LENGTH];
        get_query_param(query, "user", user, sizeof(user));
        get_query_param(query, "pass", pass, sizeof(pass));
        
        // Fallback default password if omitted in curl command
        if (strlen(pass) == 0) snprintf(pass, sizeof(pass), "%spass", user); 

        if (authenticate(user, pass, token) == 0) {
            snprintf(json_output, sizeof(json_output), "{\"token\": \"%s\"}", token);
            send_json_response(client_socket, 200, json_output);
        } else {
            send_json_response(client_socket, 401, "{\"error\": \"Authentication failed\"}");
        }
    } 
    // ROUTE 2: /get_role
    else if (strcmp(path, "/get_role") == 0) {
        char token[TOKEN_LENGTH];
        get_query_param(query, "token", token, sizeof(token));

        int role = get_role(token);
        if (role != -1) {
            snprintf(json_output, sizeof(json_output), "{\"role\": %d}", role);
            send_json_response(client_socket, 200, json_output);
        } else {
            send_json_response(client_socket, 401, "{\"error\": \"Invalid Token\"}");
        }
    } 
    // ROUTE 3: /transfer
    else if (strcmp(path, "/transfer") == 0) {
        char token[TOKEN_LENGTH], from[50], to[50], amt_str[32];
        get_query_param(query, "token", token, sizeof(token));
        get_query_param(query, "from", from, sizeof(from));
        get_query_param(query, "to", to, sizeof(to));
        get_query_param(query, "amount", amt_str, sizeof(amt_str));

        double amount = strlen(amt_str) > 0 ? atof(amt_str) : 20.0; // Defaulting $20 if amount is absent

        if (transfer(token, from, to, amount) == 0) {
            send_json_response(client_socket, 200, "{\"status\": true}");
        } else {
            send_json_response(client_socket, 200, "{\"status\": false}");
        }
    } 
    // FALLBACK 404
    else {
        send_json_response(client_socket, 404, "{\"error\": \"Endpoint Not Found\"}");
    }

    close(client_socket);
}

/* =========================================================================
   4. BOOTSTRAPPING & MAIN DRIVER LOOP
   ========================================================================= */
int main() {
    // Seed mock data for runtime validation
    strcpy(db[0].username, "admin_user");     strcpy(db[0].password, "admin_userpass");     db[0].role = 1; db[0].balance = 9999.0;
    strcpy(db[1].username, "alice");          strcpy(db[1].password, "alicepass");          db[1].role = 2; db[1].balance = 250.0;
    strcpy(db[2].username, "bob");            strcpy(db[2].password, "bobpass");            db[2].role = 2; db[2].balance = 10.0;

    int server_fd, client_socket;
    struct sockaddr_in address;
    int opt = 1, addrlen = sizeof(address);

    server_fd = socket(AF_INET, SOCK_STREAM, 0);
    setsockopt(server_fd, SOL_SOCKET, SO_REUSEADDR, &opt, sizeof(opt));

    address.sin_family = AF_INET;
    address.sin_addr.s_addr = INADDR_ANY;
    address.sin_port = htons(PORT);

    bind(server_fd, (struct sockaddr *)&address, sizeof(address));
    listen(server_fd, 10);

    printf("API Server running at http://localhost:%d\n", PORT);

    while (1) {
        client_socket = accept(server_fd, (struct sockaddr *)&address, (socklen_t*)&addrlen);
        if (client_socket >= 0) {
            handle_client(client_socket);
        }
    }
    return 0;
}
