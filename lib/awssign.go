package vegeta

import (
	"bytes"
	"context"
	"crypto/sha256"
	"fmt"
	"io"
	"net/http"
	"time"

	"github.com/aws/aws-sdk-go-v2/config"
	"github.com/aws/smithy-go/aws-http-auth/credentials"
	sigv4 "github.com/aws/smithy-go/aws-http-auth/sigv4"
)

// AWSCredentials holds AWS access credentials
type AWSCredentials struct {
	AccessKeyID     string
	SecretAccessKey string
	SessionToken    string
}

// AWSSigner signs HTTP requests with AWS Signature Version 4
type AWSSigner struct {
	region      string
	service     string
	credentials AWSCredentials
	signer      *sigv4.Signer
}

// NewAWSSigner creates a new AWS request signer
func NewAWSSigner(region, service string, creds AWSCredentials) (*AWSSigner, error) {
	if region == "" {
		return nil, fmt.Errorf("AWS region is required")
	}
	if service == "" {
		return nil, fmt.Errorf("AWS service name is required")
	}
	if creds.AccessKeyID == "" || creds.SecretAccessKey == "" {
		return nil, fmt.Errorf("AWS credentials (access key and secret key) are required")
	}

	signer := sigv4.New()

	return &AWSSigner{
		region:      region,
		service:     service,
		credentials: creds,
		signer:      signer,
	}, nil
}

// LoadCredentials loads AWS credentials from various sources in priority order:
// 1. Explicit parameters (accessKey, secretKey, sessionToken)
// 2. AWS Profile (profile parameter or AWS_PROFILE env var)
// 3. Environment variables (AWS_ACCESS_KEY_ID, AWS_SECRET_ACCESS_KEY, AWS_SESSION_TOKEN)
// 4. Shared credentials file (~/.aws/credentials, default profile)
func LoadCredentials(accessKey, secretKey, sessionToken, profile string) (AWSCredentials, error) {
	// Priority 1: Explicit credentials from CLI flags
	if accessKey != "" && secretKey != "" {
		return AWSCredentials{
			AccessKeyID:     accessKey,
			SecretAccessKey: secretKey,
			SessionToken:    sessionToken,
		}, nil
	}

	// Priority 2 & 3: Try AWS SDK config (handles env vars, profiles, and credentials file)
	ctx := context.Background()
	var opts []func(*config.LoadOptions) error

	// Use specified profile if provided, otherwise SDK uses AWS_PROFILE env or "default"
	if profile != "" {
		opts = append(opts, config.WithSharedConfigProfile(profile))
	}

	cfg, err := config.LoadDefaultConfig(ctx, opts...)
	if err != nil {
		return AWSCredentials{}, fmt.Errorf("failed to load AWS config: %w", err)
	}

	creds, err := cfg.Credentials.Retrieve(ctx)
	if err != nil {
		return AWSCredentials{}, fmt.Errorf("failed to retrieve AWS credentials: %w", err)
	}

	return AWSCredentials{
		AccessKeyID:     creds.AccessKeyID,
		SecretAccessKey: creds.SecretAccessKey,
		SessionToken:    creds.SessionToken,
	}, nil
}

// awsSigningTransport is an http.RoundTripper that signs requests with AWS SigV4
type awsSigningTransport struct {
	wrapped http.RoundTripper
	signer  *AWSSigner
}

// RoundTrip implements the http.RoundTripper interface
func (t *awsSigningTransport) RoundTrip(req *http.Request) (*http.Response, error) {
	// Sign the request
	if err := t.signer.signRequest(req); err != nil {
		return nil, fmt.Errorf("failed to sign AWS request: %w", err)
	}

	// Forward to underlying transport
	return t.wrapped.RoundTrip(req)
}

// signRequest signs a single HTTP request with AWS Signature Version 4
func (s *AWSSigner) signRequest(req *http.Request) error {
	// Read and hash the request body
	var bodyHash []byte
	var err error

	if req.Body != nil {
		// Read the body
		bodyBytes, err := io.ReadAll(req.Body)
		if err != nil {
			return fmt.Errorf("failed to read request body: %w", err)
		}

		// Close the original body
		req.Body.Close()

		// Hash the body
		hash := sha256.Sum256(bodyBytes)
		bodyHash = hash[:]

		// Restore the body for the actual request
		req.Body = io.NopCloser(bytes.NewReader(bodyBytes))
		req.ContentLength = int64(len(bodyBytes))
	} else {
		// Empty body hash
		hash := sha256.Sum256([]byte{})
		bodyHash = hash[:]
	}

	// Prepare signing input
	signingTime := time.Now()

	creds := credentials.Credentials{
		AccessKeyID:     s.credentials.AccessKeyID,
		SecretAccessKey: s.credentials.SecretAccessKey,
		SessionToken:    s.credentials.SessionToken,
	}

	// Sign the request
	err = s.signer.SignRequest(&sigv4.SignRequestInput{
		Request:     req,
		PayloadHash: bodyHash,
		Credentials: creds,
		Service:     s.service,
		Region:      s.region,
		Time:        signingTime,
	})
	if err != nil {
		return fmt.Errorf("SigV4 signing failed: %w", err)
	}

	return nil
}

// Ensure awsSigningTransport implements http.RoundTripper
var _ http.RoundTripper = (*awsSigningTransport)(nil)
