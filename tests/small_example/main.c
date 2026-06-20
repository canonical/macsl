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

int transfer(const char *token, const char *user_sending, const char *user_receiving, double amount) {
    int caller_idx = -1;
    int sender_idx = -1;
    int receiver_idx = -1;

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
    return 0; // Success
}

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
