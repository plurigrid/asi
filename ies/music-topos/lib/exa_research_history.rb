#!/usr/bin/env ruby
# -*- coding: utf-8 -*-

"""
Exa Research History Enumeration Tool
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Retrieves complete history of all deep research tasks ever run using Exa API.

Discovered that Exa provides:
  • GET /research/v1 - List all research tasks (paginated)
  • GET /research/v1/{researchId} - Get specific task details
  • events=true parameter - Include detailed event logs

This tool enumerates the complete research history.
"""

require 'net/http'
require 'json'
require 'time'

class ExaResearchHistory
  # ========================================================================
  # Initialization
  # ========================================================================

  BASE_URL = 'https://api.exa.ai/research/v1'

  def initialize(api_key: ENV['EXA_API_KEY'])
    @api_key = api_key
    raise 'EXA_API_KEY not set' unless @api_key
    @all_tasks = []
    @cursor = nil
  end

  # ========================================================================
  # Main Enumeration Methods
  # ========================================================================

  def fetch_all_research_tasks(include_events: false)
    """
    Fetch ALL research tasks from Exa API.

    Args:
      include_events: If true, fetch detailed event logs for each task

    Returns:
      {
        total_count: 42,
        tasks: [...],
        summary: {...}
      }
    """
    puts "╔════════════════════════════════════════════════════════════╗"
    puts "║  EXA RESEARCH HISTORY ENUMERATION                          ║"
    puts "╚════════════════════════════════════════════════════════════╝"
    puts ""

    fetch_paginated_tasks

    if include_events
      fetch_detailed_events
    end

    generate_report
  end

  # ========================================================================
  # Pagination - Fetch all pages
  # ========================================================================

  def fetch_paginated_tasks
    """Fetch all pages of research tasks using cursor pagination"""
    page_count = 0
    total_fetched = 0

    loop do
      page_count += 1
      puts "Fetching page #{page_count}..."

      response = fetch_page(@cursor, limit: 50)

      if response['data'].empty?
        puts "No more tasks found."
        break
      end

      tasks = response['data']
      @all_tasks.concat(tasks)
      total_fetched += tasks.length

      puts "  ✓ Retrieved #{tasks.length} tasks (total: #{total_fetched})"

      # Print first few tasks on this page
      tasks[0..2].each do |task|
        print_task_summary(task)
      end

      # Check if more pages exist
      unless response['hasMore']
        puts ""
        puts "✓ Reached end of research history."
        break
      end

      # Set cursor for next page
      @cursor = response['nextCursor']
    end

    puts ""
    puts "Total tasks retrieved: #{@all_tasks.length}"
    puts ""
  end

  # ========================================================================
  # Single Page Fetch
  # ========================================================================

  def fetch_page(cursor = nil, limit: 50)
    """Fetch single page of research tasks"""
    uri = URI(BASE_URL)
    uri.query = "limit=#{limit}"
    uri.query += "&cursor=#{cursor}" if cursor

    http = Net::HTTP.new(uri.host, uri.port)
    http.use_ssl = true

    request = Net::HTTP::Get.new(uri)
    request['x-api-key'] = @api_key
    request['Content-Type'] = 'application/json'

    response = http.request(request)

    if response.code != '200'
      puts "ERROR: HTTP #{response.code}"
      puts response.body
      return { 'data' => [], 'hasMore' => false }
    end

    JSON.parse(response.body)
  rescue => e
    puts "ERROR fetching page: #{e.message}"
    { 'data' => [], 'hasMore' => false }
  end

  # ========================================================================
  # Detailed Event Fetching
  # ========================================================================

  def fetch_detailed_events
    """Fetch detailed event logs for each task"""
    puts "Fetching detailed event logs for #{@all_tasks.length} tasks..."
    puts ""

    @all_tasks.each_with_index do |task, idx|
      research_id = task['researchId']
      print "\r[#{idx + 1}/#{@all_tasks.length}] Fetching events for #{research_id[0..12]}..."

      uri = URI("#{BASE_URL}/#{research_id}")
      uri.query = 'events=true'

      http = Net::HTTP.new(uri.host, uri.port)
      http.use_ssl = true

      request = Net::HTTP::Get.new(uri)
      request['x-api-key'] = @api_key

      response = http.request(request)

      if response.code == '200'
        detailed = JSON.parse(response.body)
        task['events'] = detailed['events'] if detailed['events']
      end
    end

    puts "\n✓ Event logs retrieved\n"
  end

  # ========================================================================
  # Report Generation
  # ========================================================================

  def generate_report
    """Generate comprehensive report of all research tasks"""
    report = {
      timestamp: Time.now.iso8601,
      total_count: @all_tasks.length,
      tasks: @all_tasks,
      summary: analyze_tasks,
      status_breakdown: breakdown_by_status,
      model_breakdown: breakdown_by_model,
      timeline: generate_timeline
    }

    print_summary_report(report)
    save_json_report(report)

    report
  end

  # ========================================================================
  # Analysis
  # ========================================================================

  def analyze_tasks
    """Analyze all research tasks"""
    {
      total_count: @all_tasks.length,
      status_counts: @all_tasks.group_by { |t| t['status'] }.transform_values(&:length),
      models_used: @all_tasks.map { |t| t['model'] }.uniq,
      date_range: {
        earliest: @all_tasks.map { |t| t['createdAt'] || t['startedAt'] }.compact.min,
        latest: @all_tasks.map { |t| t['createdAt'] || t['startedAt'] }.compact.max
      }
    }
  end

  def breakdown_by_status
    """Break down tasks by status"""
    @all_tasks.group_by { |t| t['status'] }.transform_values { |tasks|
      {
        count: tasks.length,
        percentage: (tasks.length.to_f / @all_tasks.length * 100).round(1)
      }
    }
  end

  def breakdown_by_model
    """Break down tasks by model"""
    @all_tasks.group_by { |t| t['model'] }.transform_values { |tasks|
      {
        count: tasks.length,
        percentage: (tasks.length.to_f / @all_tasks.length * 100).round(1)
      }
    }
  end

  def generate_timeline
    """Generate timeline of research tasks"""
    @all_tasks.group_by { |t|
      date = t['createdAt'] || t['startedAt']
      date ? date.split('T')[0] : 'unknown'
    }.sort.to_h
  end

  # ========================================================================
  # Printing / Formatting
  # ========================================================================

  def print_task_summary(task)
    """Print single task summary"""
    research_id = task['researchId']
    status = task['status']
    model = task['model']
    instructions = (task['instructions'] || '(no instructions)')[0..60]

    status_emoji = case status
                   when 'completed' then '✓'
                   when 'running' then '⚙'
                   when 'pending' then '⏳'
                   when 'failed' then '✗'
                   when 'canceled' then '◯'
                   else '?'
                   end

    puts "    #{status_emoji} [#{model}] #{research_id[0..12]}... - #{instructions}"
  end

  def print_summary_report(report)
    """Print formatted summary report"""
    puts "╔════════════════════════════════════════════════════════════╗"
    puts "║              RESEARCH HISTORY ANALYSIS REPORT              ║"
    puts "╚════════════════════════════════════════════════════════════╝"
    puts ""

    summary = report[:summary]
    puts "OVERALL STATISTICS:"
    puts "─" * 60
    puts "  Total Research Tasks: #{summary[:total_count]}"
    puts "  Models Used: #{summary[:models_used].join(', ')}"
    puts "  Date Range: #{summary[:date_range][:earliest]} to #{summary[:date_range][:latest]}"
    puts ""

    puts "STATUS BREAKDOWN:"
    puts "─" * 60
    breakdown = report[:status_breakdown]
    breakdown.each do |status, data|
      bar_width = (data[:percentage] / 2).to_i
      bar = "█" * bar_width
      puts "  #{status.capitalize.ljust(12)}: #{bar.ljust(50)} #{data[:count]} (#{data[:percentage]}%)"
    end
    puts ""

    puts "MODEL BREAKDOWN:"
    puts "─" * 60
    report[:model_breakdown].each do |model, data|
      bar_width = (data[:percentage] / 2).to_i
      bar = "█" * bar_width
      puts "  #{model.ljust(20)}: #{bar.ljust(30)} #{data[:count]} (#{data[:percentage]}%)"
    end
    puts ""

    puts "TIMELINE (by date):"
    puts "─" * 60
    report[:timeline].each do |date, _|
      count = @all_tasks.select { |t| (t['createdAt'] || t['startedAt'] || '').start_with?(date) }.length
      puts "  #{date}: #{count} tasks"
    end
    puts ""
  end

  # ========================================================================
  # Export
  # ========================================================================

  def save_json_report(report)
    """Save report to JSON file"""
    filename = "exa_research_history_#{Time.now.strftime('%Y%m%d_%H%M%S')}.json"
    File.write(filename, JSON.pretty_generate(report))
    puts "Report saved to: #{filename}"
  end

  # ========================================================================
  # Filtering & Searching
  # ========================================================================

  def find_tasks_by_status(status)
    """Find all tasks with specific status"""
    @all_tasks.select { |t| t['status'] == status }
  end

  def find_tasks_by_model(model)
    """Find all tasks using specific model"""
    @all_tasks.select { |t| t['model'] == model }
  end

  def search_tasks_by_instruction(keyword)
    """Search tasks by instruction text"""
    @all_tasks.select { |t|
      (t['instructions'] || '').downcase.include?(keyword.downcase)
    }
  end

  def get_task_by_id(research_id)
    """Get specific task by ID"""
    @all_tasks.find { |t| t['researchId'] == research_id }
  end

  # ========================================================================
  # Export Formats
  # ========================================================================

  def export_csv
    """Export all tasks to CSV"""
    require 'csv'

    filename = "exa_research_history_#{Time.now.strftime('%Y%m%d_%H%M%S')}.csv"

    CSV.open(filename, 'w') do |csv|
      csv << ['researchId', 'status', 'model', 'instructions', 'createdAt']

      @all_tasks.each do |task|
        csv << [
          task['researchId'],
          task['status'],
          task['model'],
          task['instructions'],
          task['createdAt'] || task['startedAt']
        ]
      end
    end

    puts "CSV exported to: #{filename}"
    filename
  end

  def export_markdown
    """Export summary to Markdown"""
    filename = "exa_research_history_#{Time.now.strftime('%Y%m%d_%H%M%S')}.md"

    File.open(filename, 'w') do |f|
      f.puts "# Exa Research History Report"
      f.puts ""
      f.puts "Generated: #{Time.now.iso8601}"
      f.puts ""

      f.puts "## Summary"
      f.puts ""
      f.puts "- **Total Tasks**: #{@all_tasks.length}"
      f.puts "- **Statuses**: #{breakdown_by_status.map { |s, d| "#{s}: #{d[:count]}" }.join(', ')}"
      f.puts "- **Models**: #{breakdown_by_model.map { |m, d| "#{m}: #{d[:count]}" }.join(', ')}"
      f.puts ""

      f.puts "## All Tasks"
      f.puts ""

      @all_tasks.each do |task|
        f.puts "### #{task['researchId']}"
        f.puts ""
        f.puts "- **Status**: #{task['status']}"
        f.puts "- **Model**: #{task['model']}"
        f.puts "- **Instructions**: #{task['instructions']}"
        f.puts "- **Created**: #{task['createdAt'] || task['startedAt']}"
        f.puts ""
      end
    end

    puts "Markdown exported to: #{filename}"
    filename
  end
end

# ============================================================================
# CLI Interface
# ============================================================================

if __FILE__ == $PROGRAM_NAME
  api_key = ENV['EXA_API_KEY']

  if api_key.nil?
    puts "ERROR: EXA_API_KEY environment variable not set"
    exit 1
  end

  enumerator = ExaResearchHistory.new(api_key: api_key)

  # Fetch all research tasks
  report = enumerator.fetch_all_research_tasks(include_events: false)

  # Export in multiple formats
  puts ""
  puts "Exporting in multiple formats..."
  puts ""
  enumerator.export_csv
  enumerator.export_markdown

  # Example filtering
  puts ""
  puts "Example Filtering:"
  puts "─" * 60

  completed = enumerator.find_tasks_by_status('completed')
  puts "Completed tasks: #{completed.length}"

  exa_research = enumerator.find_tasks_by_model('exa-research')
  puts "exa-research model tasks: #{exa_research.length}"

  # Display first 5 completed tasks
  puts ""
  puts "First 5 Completed Tasks:"
  completed[0..4].each do |task|
    puts "  • #{task['researchId']} - #{task['instructions'][0..50]}"
  end
end
