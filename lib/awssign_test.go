package vegeta

import (
	"context"
	"io"
	"net/http"
	"net/http/httptest"
	"os"
	"strings"
	"testing"
)

func TestNewAWSSigner(t *testing.T) {
	t.Parallel()

	tests := []struct {
		name        string
		region      string
		service     string
		creds       AWSCredentials
		expectError bool
	}{
		{
			name:    "valid credentials",
			region:  "us-east-1",
			service: "execute-api",
			creds: AWSCredentials{
				AccessKeyID:     "TestKeyId",
				SecretAccessKey: "TestSecretKey",
			},
			expectError: false,
		},
		{
			name:        "missing region",
			region:      "",
			service:     "execute-api",
			creds:       AWSCredentials{AccessKeyID: "key", SecretAccessKey: "secret"},
			expectError: true,
		},
		{
			name:        "missing service",
			region:      "us-east-1",
			service:     "",
			creds:       AWSCredentials{AccessKeyID: "key", SecretAccessKey: "secret"},
			expectError: true,
		},
		{
			name:        "missing access key",
			region:      "us-east-1",
			service:     "execute-api",
			creds:       AWSCredentials{SecretAccessKey: "secret"},
			expectError: true,
		},
		{
			name:        "missing secret key",
			region:      "us-east-1",
			service:     "execute-api",
			creds:       AWSCredentials{AccessKeyID: "key"},
			expectError: true,
		},
	}

	for _, tt := range tests {
		tt := tt
		t.Run(tt.name, func(t *testing.T) {
			t.Parallel()
			signer, err := NewAWSSigner(tt.region, tt.service, tt.creds)
			if tt.expectError {
				if err == nil {
					t.Errorf("expected error, got nil")
				}
			} else {
				if err != nil {
					t.Errorf("unexpected error: %v", err)
				}
				if signer == nil {
					t.Errorf("expected signer, got nil")
				}
			}
		})
	}
}

func TestLoadCredentialsFromEnv(t *testing.T) {
	// Save original env vars
	origAccessKey := os.Getenv("AWS_ACCESS_KEY_ID")
	origSecretKey := os.Getenv("AWS_SECRET_ACCESS_KEY")
	origSessionToken := os.Getenv("AWS_SESSION_TOKEN")
	defer func() {
		os.Setenv("AWS_ACCESS_KEY_ID", origAccessKey)
		os.Setenv("AWS_SECRET_ACCESS_KEY", origSecretKey)
		os.Setenv("AWS_SESSION_TOKEN", origSessionToken)
	}()

	// Set test env vars
	os.Setenv("AWS_ACCESS_KEY_ID", "TestKeyId")
	os.Setenv("AWS_SECRET_ACCESS_KEY", "TestSecretKey")
	os.Setenv("AWS_SESSION_TOKEN", "TestSessionToken")

	creds, err := LoadCredentials("", "", "", "")
	if err != nil {
		t.Fatalf("unexpected error loading credentials from env: %v", err)
	}

	if creds.AccessKeyID != "TestKeyId" {
		t.Errorf("expected AccessKeyID=TestKeyId, got %s", creds.AccessKeyID)
	}
	if creds.SecretAccessKey != "TestSecretKey" {
		t.Errorf("expected SecretAccessKey=TestSecretKey, got %s", creds.SecretAccessKey)
	}
	if creds.SessionToken != "TestSessionToken" {
		t.Errorf("expected SessionToken=TestSessionToken, got %s", creds.SessionToken)
	}
}

func TestLoadCredentialsExplicit(t *testing.T) {
	// Explicit credentials should take precedence over env
	creds, err := LoadCredentials("EXPLICIT_KEY", "EXPLICIT_SECRET", "EXPLICIT_TOKEN", "")
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}

	if creds.AccessKeyID != "EXPLICIT_KEY" {
		t.Errorf("expected AccessKeyID=EXPLICIT_KEY, got %s", creds.AccessKeyID)
	}
	if creds.SecretAccessKey != "EXPLICIT_SECRET" {
		t.Errorf("expected SecretAccessKey=EXPLICIT_SECRET, got %s", creds.SecretAccessKey)
	}
	if creds.SessionToken != "EXPLICIT_TOKEN" {
		t.Errorf("expected SessionToken=EXPLICIT_TOKEN, got %s", creds.SessionToken)
	}
}

func TestAWSSigningTransport(t *testing.T) {
	// Create a test server that checks for AWS signature headers
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		// Verify AWS signature headers are present
		if r.Header.Get("Authorization") == "" {
			t.Error("missing Authorization header")
		}
		if r.Header.Get("X-Amz-Date") == "" {
			t.Error("missing X-Amz-Date header")
		}
		if !strings.HasPrefix(r.Header.Get("Authorization"), "AWS4-HMAC-SHA256") {
			t.Errorf("invalid Authorization header format: %s", r.Header.Get("Authorization"))
		}

		w.WriteHeader(http.StatusOK)
		w.Write([]byte("OK"))
	}))
	defer server.Close()

	// Create AWS signer
	signer, err := NewAWSSigner("us-east-1", "execute-api", AWSCredentials{
		AccessKeyID:     "TestKeyId",
		SecretAccessKey: "TestSecretKey",
	})
	if err != nil {
		t.Fatalf("failed to create signer: %v", err)
	}

	// Create transport with signing
	transport := &awsSigningTransport{
		wrapped: http.DefaultTransport,
		signer:  signer,
	}

	// Create HTTP client with signing transport
	client := &http.Client{
		Transport: transport,
	}

	// Make request
	req, err := http.NewRequestWithContext(context.Background(), "GET", server.URL+"/test", nil)
	if err != nil {
		t.Fatalf("failed to create request: %v", err)
	}

	resp, err := client.Do(req)
	if err != nil {
		t.Fatalf("failed to make request: %v", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		t.Errorf("expected status 200, got %d", resp.StatusCode)
	}

	body, err := io.ReadAll(resp.Body)
	if err != nil {
		t.Fatalf("failed to read response body: %v", err)
	}

	if string(body) != "OK" {
		t.Errorf("expected body 'OK', got %s", string(body))
	}
}

func TestAWSSigningWithBody(t *testing.T) {
	// Create a test server
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		// Verify AWS signature headers are present
		if r.Header.Get("Authorization") == "" {
			t.Error("missing Authorization header")
		}
		if r.Header.Get("X-Amz-Date") == "" {
			t.Error("missing X-Amz-Date header")
		}

		// Read and verify body
		body, err := io.ReadAll(r.Body)
		if err != nil {
			t.Errorf("failed to read body: %v", err)
		}
		if string(body) != "test body content" {
			t.Errorf("expected body 'test body content', got %s", string(body))
		}

		w.WriteHeader(http.StatusOK)
	}))
	defer server.Close()

	// Create AWS signer
	signer, err := NewAWSSigner("us-east-1", "execute-api", AWSCredentials{
		AccessKeyID:     "TestKeyId",
		SecretAccessKey: "TestSecretKey",
	})
	if err != nil {
		t.Fatalf("failed to create signer: %v", err)
	}

	// Create transport with signing
	transport := &awsSigningTransport{
		wrapped: http.DefaultTransport,
		signer:  signer,
	}

	client := &http.Client{Transport: transport}

	// Make POST request with body
	req, err := http.NewRequestWithContext(
		context.Background(),
		"POST",
		server.URL+"/test",
		strings.NewReader("test body content"),
	)
	if err != nil {
		t.Fatalf("failed to create request: %v", err)
	}

	resp, err := client.Do(req)
	if err != nil {
		t.Fatalf("failed to make request: %v", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		t.Errorf("expected status 200, got %d", resp.StatusCode)
	}
}
