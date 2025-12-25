# Music Topos Framework - Deployment Guide

Complete guide to deploying the Music Topos Framework in different environments.

---

## Table of Contents

1. [Local Development](#local-development)
2. [Docker Deployment](#docker-deployment)
3. [Cloud Deployment](#cloud-deployment)
4. [Production Configuration](#production-configuration)
5. [Monitoring and Maintenance](#monitoring-and-maintenance)

---

## Local Development

### Prerequisites

- Ruby 3.0 or higher
- Git
- No external dependencies needed (uses only Ruby standard library for core)

### Installation

```bash
# Clone repository
git clone https://github.com/[username]/music-topos.git
cd music-topos

# No bundle needed! Framework runs with pure Ruby
```

### Running Locally

#### Option 1: Direct Ruby Execution

```bash
# Run the REST API server
ruby api/music_topos_server.rb

# Server starts on http://localhost:4567
```

#### Option 2: IRB Interactive Console

```bash
# Start interactive Ruby console
irb

# Load and test the framework
require_relative 'lib/music_topos_framework'
require_relative 'lib/chord'

framework = MusicToposFramework.new
chords = [
  Chord.from_notes(['C', 'E', 'G']),
  Chord.from_notes(['G', 'B', 'D']),
  Chord.from_notes(['C', 'E', 'G'])
]

analysis = framework.analyze_progression(chords, key: 'C')
```

#### Option 3: Run Tests

```bash
# Run all category tests
ruby test_category_4.rb
ruby test_category_5.rb
# ... etc ...

# Run integration tests
ruby test_integration_framework.rb

# Expected: 27/27 tests passing
```

### API Access

Once server is running:

```bash
# Health check
curl http://localhost:4567/health

# Status
curl http://localhost:4567/status

# Analyze progression
curl -X POST http://localhost:4567/analyze/progression \
  -H "Content-Type: application/json" \
  -d '{
    "progressions": [
      ["C", "E", "G"],
      ["G", "B", "D"],
      ["C", "E", "G"]
    ],
    "key": "C"
  }'
```

### Web Dashboard

Once server is running:

```
http://localhost:4567/public/index.html
```

Features:
- Interactive chord progression entry
- Pre-built example progressions
- 8-category analysis visualization
- Coherence validation
- Real-time API testing

---

## Docker Deployment

### Prerequisites

- Docker 20.10+
- Docker Compose 2.0+

### Quick Start with Docker Compose

```bash
# Build and start the service
docker-compose up -d

# Check status
docker-compose ps

# View logs
docker-compose logs -f music-topos-api

# Stop service
docker-compose down
```

Service will be available at `http://localhost:4567`

### Manual Docker Build

```bash
# Build image
docker build -t music-topos:latest .

# Run container
docker run -p 4567:4567 music-topos:latest

# With custom port
docker run -p 8000:4567 music-topos:latest
```

### Docker Image Details

- **Base Image**: `ruby:3.2-slim`
- **Exposed Port**: 4567
- **Health Check**: HTTP GET to `/health` every 30 seconds
- **Default CMD**: `ruby api/music_topos_server.rb`

### Docker Compose Configuration

The `docker-compose.yml` provides:

```yaml
services:
  music-topos-api:
    build: .
    ports:
      - "4567:4567"
    healthcheck:
      test: ["CMD", "ruby", "-e", "require 'net/http'; Net::HTTP.get(...)"]
      interval: 30s
      timeout: 3s
      retries: 3
    restart: unless-stopped
    networks:
      - music-topos-network
```

### Building for Distribution

```bash
# Build specific version
docker build -t music-topos:1.0.0 .
docker tag music-topos:1.0.0 music-topos:latest

# Push to registry
docker push your-registry/music-topos:1.0.0
```

---

## Cloud Deployment

### Heroku Deployment

#### Prerequisites
- Heroku CLI installed
- Heroku account
- Git configured

#### Steps

```bash
# Create Heroku app
heroku create music-topos

# Set environment variables
heroku config:set RACK_ENV=production

# Deploy
git push heroku main

# View logs
heroku logs --tail

# Scale dynos if needed
heroku ps:scale web=1
```

Create a `Procfile` in root:

```
web: ruby api/music_topos_server.rb
```

Create `Gemfile`:

```ruby
source 'https://rubygems.org'

gem 'sinatra'
```

Then:

```bash
bundle install
git add Gemfile Gemfile.lock
git commit -m "Add Gemfile"
git push heroku main
```

### AWS Lambda / API Gateway

1. Create Lambda function with Ruby 3.2 runtime
2. Upload Docker image:

```bash
# Build and push to ECR
aws ecr get-login-password --region us-east-1 | docker login --username AWS --password-stdin [ACCOUNT].dkr.ecr.us-east-1.amazonaws.com
docker build -t music-topos .
docker tag music-topos:latest [ACCOUNT].dkr.ecr.us-east-1.amazonaws.com/music-topos:latest
docker push [ACCOUNT].dkr.ecr.us-east-1.amazonaws.com/music-topos:latest
```

3. Configure Lambda to use the ECR image
4. Set up API Gateway to proxy requests

### DigitalOcean App Platform

1. Connect GitHub repository
2. Create app.yaml:

```yaml
name: music-topos
services:
  - name: api
    github:
      repo: [username]/music-topos
      branch: main
    build_command: bundle install
    run_command: ruby api/music_topos_server.rb
    http_port: 4567
    health_check:
      http:
        path: /health
```

3. Deploy via DigitalOcean dashboard

### Google Cloud Run

```bash
# Build and push to GCR
gcloud builds submit --tag gcr.io/[PROJECT]/music-topos
gcloud run deploy music-topos \
  --image gcr.io/[PROJECT]/music-topos \
  --platform managed \
  --port 4567
```

---

## Production Configuration

### Environment Variables

```bash
# Port configuration
export PORT=4567

# Rack environment
export RACK_ENV=production

# Optional: API key (future enhancement)
export API_KEY=your-secret-key

# Optional: CORS origins
export CORS_ORIGINS=https://yourdomain.com
```

### HTTPS / SSL

For production, use a reverse proxy (nginx, Caddy, or cloud provider's load balancer):

```nginx
upstream music_topos {
    server localhost:4567;
}

server {
    listen 443 ssl http2;
    server_name api.music-topos.com;

    ssl_certificate /etc/ssl/certs/certificate.crt;
    ssl_certificate_key /etc/ssl/private/key.key;

    location / {
        proxy_pass http://music_topos;
        proxy_set_header Host $host;
        proxy_set_header X-Real-IP $remote_addr;
        proxy_set_header X-Forwarded-For $proxy_add_x_forwarded_for;
        proxy_set_header X-Forwarded-Proto $scheme;
    }
}
```

### Rate Limiting

Add to nginx config:

```nginx
limit_req_zone $binary_remote_addr zone=api_limit:10m rate=10r/s;
limit_req zone=api_limit burst=20;
```

### Logging

Configure application logging:

```ruby
# In api/music_topos_server.rb
configure :production do
  enable :logging
  use Rack::CommonLogger, File.open("api.log", 'a')
end
```

---

## Monitoring and Maintenance

### Health Monitoring

```bash
# Check service health
curl -i http://localhost:4567/health

# Expected response:
# HTTP/1.1 200 OK
# {"status":"ok","service":"Music Topos Framework API",...}
```

### Logs

```bash
# Docker logs
docker-compose logs -f music-topos-api

# Heroku logs
heroku logs --tail

# Docker container logs
docker logs [container-id]
```

### Performance Monitoring

Monitor these metrics:

- Request latency (should be < 100ms)
- Error rate (should be < 1%)
- CPU usage
- Memory usage (should be < 200MB)

### Backup Strategy

Core files to backup:

```bash
# Source code (already in git)
git push origin main

# Any custom configurations or data files
# (current framework stores no persistent data)
```

### Security Best Practices

1. **API Authentication** (future enhancement)
   - Implement API key requirement
   - Use JWT tokens for sessions

2. **Rate Limiting**
   - Implement per-IP rate limiting
   - Use reverse proxy like nginx

3. **HTTPS Only**
   - Enforce HTTPS in production
   - Use valid SSL certificates

4. **Input Validation**
   - Already implemented in REST API
   - Validates note names and keys

5. **CORS Configuration**
   - Currently allows all origins
   - Configure for specific domains in production

### Updating the Framework

```bash
# Development
git pull origin main
# Restart: ruby api/music_topos_server.rb

# Docker
git pull origin main
docker-compose down
docker-compose build --no-cache
docker-compose up -d

# Heroku
git push heroku main
```

### Troubleshooting

#### Server won't start

```bash
# Check port availability
lsof -i :4567

# Check Ruby version
ruby --version  # Should be 3.0+

# Check dependencies
bundle check
```

#### High memory usage

- Current framework uses ~50-100MB
- Check for memory leaks with profiling tools
- Restart service if needed

#### Slow responses

- Normal analysis time: 1-10ms
- Check system resources
- Verify network connectivity

#### Test failures

```bash
# Verify installation
ruby test_integration_framework.rb

# Should see: ✓ ALL 6 INTEGRATION TESTS PASSED!
```

---

## Performance Benchmarks

### Expected Performance

| Operation | Time |
|-----------|------|
| Single chord analysis | < 1ms |
| Progression analysis (4 chords) | 2-5ms |
| Coherence validation | < 1ms |
| Framework initialization | < 100ms |
| All 27 tests | < 5 seconds |

### System Requirements

| Metric | Requirement |
|--------|-------------|
| RAM | 256MB minimum, 512MB recommended |
| Disk | 100MB for code and dependencies |
| CPU | 1 core minimum, 2+ cores recommended |
| Network | Bandwidth for JSON responses (<10KB per request) |

---

## Support and Documentation

- **API Docs**: [API.md](API.md)
- **Academic Paper**: [MUSIC_TOPOS_PAPER.md](MUSIC_TOPOS_PAPER.md)
- **Quick Start**: [README.md](README.md)
- **Implementation Report**: [PHASE_10_COMPLETION_REPORT.md](PHASE_10_COMPLETION_REPORT.md)

---

## Getting Help

- Check [README.md](README.md) for quick start
- See [API.md](API.md) for endpoint documentation
- Review test files for usage examples
- Open issue on GitHub for bugs

---

**Last Updated**: December 2025
**Framework Version**: 1.0.0
**Status**: Production Ready
