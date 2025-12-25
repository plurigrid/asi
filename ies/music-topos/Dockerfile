# Music Topos Framework Docker Container
# Containerized REST API server for music theory analysis

FROM ruby:3.2-slim

# Set working directory
WORKDIR /app

# Install system dependencies
RUN apt-get update && apt-get install -y \
    graphviz \
    fonts-dejavu-core \
    && rm -rf /var/lib/apt/lists/*

# Copy Gemfile and install dependencies
COPY Gemfile* ./
RUN gem install sinatra bundler

# Copy application code
COPY lib/ ./lib/
COPY api/ ./api/

# Expose port
EXPOSE 4567

# Health check
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
    CMD ruby -e "require 'net/http'; Net::HTTP.get(URI('http://localhost:4567/health'))" || exit 1

# Start the server
CMD ["ruby", "api/music_topos_server.rb"]
