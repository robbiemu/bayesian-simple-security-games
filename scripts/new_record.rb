#!/usr/bin/env ruby
require "fileutils"
require "securerandom"
require "time"
require "yaml"

kind, question = ARGV
kinds = %w[question attempt result review decision]
abort "usage: ruby scripts/new_record.rb {#{kinds.join('|')}} NODE" unless ARGV.length == 2 && kinds.include?(kind) && question.match?(/\A[A-Za-z0-9-]+\z/)
Dir.chdir(File.expand_path("..", __dir__))
id = SecureRandom.uuid
record = { "schema" => 1, "id" => id, "kind" => kind, "title" => "",
           (kind == "question" ? "parent" : "question") => question,
           "at" => Time.now.utc.iso8601, "by" => [{ "id" => "", "roles" => [] }],
           "ai_use" => "unknown", "tools" => [] }
case kind
when "question" then record["criterion"] = ""
when "attempt" then record["phase"] = "started"
when "result" then record["outcome"] = "partial"
when "review" then record.merge!("target" => "", "verdict" => "supports")
when "decision" then record.merge!("action" => "reopen", "basis" => [])
end
FileUtils.mkdir_p("records")
path = "records/#{id}.md"
File.open(path, File::WRONLY | File::CREAT | File::EXCL) do |file|
  file.write(record.to_yaml + "---\n\n")
end
puts "#{path}\nFill in the title, contributor, disclosure and Markdown body, then run ruby scripts/build_map.rb."
