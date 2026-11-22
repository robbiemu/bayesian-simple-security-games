#!/usr/bin/env ruby
# Build the public board from the catalog and contributor records.
require "date"
require "digest"
require "fileutils"
require "json"
require "pathname"
require "time"
require "uri"
require "yaml"

Dir.chdir(File.expand_path("..", __dir__))
CHECK = ARGV == ["--check"]
abort "usage: ruby scripts/build_map.rb [--check]" unless CHECK || ARGV.empty?
ROOT_URL = "https://github.com/robbiemu/bayesian-simple-security-games"
STATES = { "open" => "🟦 Open", "partial" => "🟨 Partial result",
           "scoped" => "🟩 Result for the stated scope", "background" => "Background" }.freeze
MARK = "<!-- Generated from catalog/ and records/ by scripts/build_map.rb -->"
UUID = /\A[0-9a-f]{8}-[0-9a-f]{4}-4[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}\z/
KINDS = %w[question attempt result review decision].freeze

def ensure_value(ok, message)
  raise ArgumentError, message unless ok
end

def text_field(hash, field, label)
  value = hash[field]
  ensure_value(value.is_a?(String) && !value.strip.empty?, "#{label}: missing #{field}")
  value
end

def evidence(path)
  ensure_value(path.is_a?(String) && !path.empty?, "Missing evidence path")
  if path.start_with?("https://")
    uri = URI.parse(path)
    ensure_value(uri.host && !uri.userinfo, "Invalid public evidence URL: #{path}")
    return
  end
  file = path.split("#", 2).first
  ensure_value(!file.empty? && !Pathname.new(file).absolute? && !file.split("/").include?("..") && File.file?(file), "Missing evidence: #{path}")
  anchor = path.split("#", 2)[1]
  if anchor && file.end_with?(".md")
    headings = File.read(file).scan(/^\#{1,6} (.+)$/).flatten
    slugs = headings.map { |h| h.strip.downcase.gsub(/[^\p{L}\p{N}_ -]/, "").tr(" ", "-") }
    ensure_value(slugs.include?(anchor), "Missing evidence section: #{path}")
  end
end

def local_link(path, prefix)
  path.start_with?("https://") ? path : prefix + path
end

def safe_label(value)
  value.to_s.gsub(/[\n\r]+/, " ").gsub(/([\[\]\\|])/) { |c| "\\#{c}" }
end

def node_link(node, prefix = "")
  "[#{node['id']} · #{safe_label(node['title'])}](#{prefix}#{node['id']}.md)"
end

def read_records
  Dir["records/*.md"].sort.map do |file|
    match = /\A---\r?\n(.*?)\r?\n---\r?\n(.+)\z/m.match(File.read(file))
    ensure_value(match && !match[2].strip.empty?, "#{file}: add YAML front matter and a research note")
    r = YAML.safe_load(match[1])
    ensure_value(r.is_a?(Hash), "#{file}: expected a mapping")
    id = File.basename(file, ".md")
    ensure_value(id.match?(UUID) && r["id"] == id && r["schema"] == 1, "#{file}: filename, UUIDv4 or schema mismatch")
    %w[title at kind].each { |k| text_field(r, k, file) }
    ensure_value(Time.iso8601(r["at"]).utc_offset.zero?, "#{file}: use UTC")
    ensure_value(KINDS.include?(r["kind"]), "#{file}: unknown kind")
    ensure_value(r["by"].is_a?(Array) && !r["by"].empty?, "#{file}: name the contributors")
    r["by"].each { |p| text_field(p, "id", file) }
    ensure_value(%w[used none unknown undisclosed].include?(r["ai_use"]) && r["tools"].is_a?(Array), "#{file}: incomplete disclosure")
    models = []
    r["tools"].each do |tool|
      %w[kind name contribution].each { |k| text_field(tool, k, file) }
      ensure_value(%w[model software].include?(tool["kind"]), "#{file}: invalid tool kind")
      next unless tool["kind"] == "model"
      models << tool
      %w[provider client check].each { |k| text_field(tool, k, file) }
      ensure_value(tool.key?("version") && Array(tool["roles"]).any?, "#{file}: specify the model role and version (null is allowed)")
    end
    ensure_value(!models.empty? == (r["ai_use"] == "used"), "#{file}: model list and declaration differ")
    evidence(r["source"]) if r["source"]
    Array(r["artifacts"]).each do |artifact|
      path = text_field(artifact, "path", file)
      evidence(path)
      ensure_value(!path.start_with?("https://") && !path.include?("#") && Digest::SHA256.file(path).hexdigest == artifact["sha256"], "#{file}: artifact digest mismatch")
    end
    r
  end
end

catalog = JSON.parse(File.read("catalog/investigation.json"))
directions = JSON.parse(File.read("catalog/directions.json"))
records = read_records
record_ids = records.to_h { |r| [r["id"], r] }
replacements = {}
records.each do |r|
  older = r["supersedes"]
  next unless older
  previous = record_ids[older]
  ensure_value(previous && previous["kind"] == r["kind"] && previous["question"] == r["question"] &&
               previous["parent"] == r["parent"], "#{r['id']}: correction must identify a record of the same kind and scope")
  ensure_value(!replacements.key?(older), "#{older}: reconcile competing corrections before adopting them")
  replacements[older] = r
end
def current_record(record, replacements)
  seen = {}
  while (successor = replacements[record["id"]])
    ensure_value(!seen[record["id"]], "Cycle in corrections")
    seen[record["id"]] = true
    record = successor
  end
  record
end
replacements.each_value { |r| current_record(r, replacements) }
question_roots = {}
questions = records.select { |r| r["kind"] == "question" && !r["supersedes"] }.map do |original|
  id = original["id"]
  revision = original
  loop do
    question_roots[revision["id"]] = id
    break unless replacements[revision["id"]]
    revision = replacements[revision["id"]]
  end
  { "id" => id, "parent" => original.fetch("parent"), "title" => revision["title"], "state" => "open",
    "summary" => text_field(revision, "criterion", id), "source" => "records/#{revision['id']}.md" }
end
nodes = {}
(catalog.fetch("nodes") + questions).each do |n|
  id = n.fetch("id")
  ensure_value(id.match?(/\A[A-Za-z0-9][A-Za-z0-9-]*\z/) && !nodes.key?(id), "Invalid or duplicate node #{id}")
  %w[title summary].each { |k| text_field(n, k, id) }
  ensure_value(STATES.key?(n["state"]), "#{id}: invalid state")
  evidence(n["source"])
  nodes[id] = n
end
ensure_value(nodes.key?("R") && nodes["R"]["parent"].nil?, "Missing root R")
nodes.each_key do |id|
  path = []
  p = id
  until p == "R"
    ensure_value(nodes.key?(p) && !path.include?(p), "#{id}: missing parent or cycle")
    path << p
    p = nodes[p]["parent"]
  end
end
links = catalog.fetch("links")
links.each do |edge|
  ensure_value(nodes.key?(edge["origin"]) && nodes.key?(edge["target"]) && edge["origin"] != edge["target"], "Broken research relation: #{edge.inspect}")
  %w[reason relation].each { |k| text_field(edge, k, "relation") }
  evidence(edge["source"])
end
ensure_value(directions.map { |d| d.fetch("id") }.uniq.length == directions.length, "Duplicate direction")
directions.each do |d|
  ensure_value(d.fetch("nodes").all? { |id| nodes.key?(id) }, "#{d['id']}: unknown node")
end

records.each do |r|
  id = r["id"]
  target = r["target"]
  q = r["kind"] == "question" ? question_roots.fetch(id) : r["question"]
  ensure_value(nodes.key?(q), "#{id}: unknown question")
  (Array(r["depends_on"]) + Array(r["related_to"]) + Array(r["supersedes"])).each do |ref|
    ensure_value(ref != id && (nodes.key?(ref) || record_ids.key?(ref)), "#{id}: unresolved reference #{ref}")
  end
  case r["kind"]
  when "attempt"
    ensure_value(%w[started paused finished].include?(r["phase"]), "#{id}: invalid phase")
    if target
      original = record_ids.fetch(target)
      ensure_value(original["kind"] == "attempt" && original["question"] == q, "#{id}: invalid attempt target")
    end
  when "result"
    ensure_value(%w[proof counterexample computation partial dead_end].include?(r["outcome"]), "#{id}: invalid result outcome")
  when "review"
    ensure_value(%w[supports reproduced challenged].include?(r["verdict"]), "#{id}: invalid verdict")
    result = record_ids[target]
    imported = target == q && r["revision"].to_s.match?(/\A[0-9a-f]{40}\z/)
    ensure_value(imported || (result && result["kind"] == "result" && result["question"] == q), "#{id}: identify the exact result or imported note revision")
  when "decision"
    ensure_value(%w[resolve reopen].include?(r["action"]) && Array(r["basis"]).any?, "#{id}: decision needs an action and evidence")
    Array(r["basis"]).each { |ref| ensure_value(record_ids.key?(ref) || nodes.key?(ref), "#{id}: unknown decision evidence") }
  end
end

# Editorial decisions are selected by maintainers in the reviewed catalog.
catalog.fetch("decisions", {}).each do |q, id|
  r = record_ids.fetch(id)
  ensure_value(nodes.key?(q) && r["kind"] == "decision" && r["question"] == q, "#{q}: invalid adopted decision")
  if r["action"] == "resolve"
    reviews = r["basis"].map { |ref| record_ids[ref] }.compact.select { |entry| entry["kind"] == "review" }
    supported = reviews.any? do |v|
      result = record_ids[v["target"]]
      reviewed = v["question"] == q && %w[supports reproduced].include?(v["verdict"]) && r["basis"].include?(v["target"])
      separate = !result || (result["by"].map { |p| p["id"] } & v["by"].map { |p| p["id"] }).empty?
      reviewed && separate
    end
    ensure_value(supported, "#{q}: cite the result and a supporting review by a different contributor")
  end
  nodes[q]["state"] = r["action"] == "resolve" ? "scoped" : "open"
end

pages = {}
children = nodes.values.group_by { |n| n["parent"] }
nodes.each do |id, n|
  body = [MARK, "# #{id} · #{n['title']}", "**#{STATES[n['state']]}**", n["summary"]]
  body << "**Open task** — #{n['next']}" if n["next"]
  body << "[Read the evidence](#{local_link(n['source'], '../')}) · [Investigation index](README.md)"
  body << "Parent question · #{node_link(nodes.fetch(n['parent']))}" if n["parent"]
  child_rows = Array(children[id]).map { |c| "- #{node_link(c)} · #{STATES[c['state']]}" }
  body += ["## Subquestions", child_rows.join("\n")] unless child_rows.empty?
  linked = links.select { |e| [e["origin"], e["target"]].include?(id) }.map do |e|
    first = e["origin"] == id ? id : node_link(nodes.fetch(e["origin"]))
    last = e["target"] == id ? id : node_link(nodes.fetch(e["target"]))
    "- #{first} **#{e['relation']}** #{last}. #{e['reason']} [Evidence](#{local_link(e['source'], '../')})"
  end
  body += ["## Relevant work", linked.join("\n")] unless linked.empty?
  credits = directions.select { |d| d["nodes"].include?(id) }.map do |d|
    "- #{d['person']} · [#{d['title']}](../DIRECTIONS.md#direction-#{d['id']}) · #{d['role']}"
  end
  body += ["## Where the direction came from", credits.join("\n")] unless credits.empty?
  attached = records.select { |r| question_roots[r["id"]] == id || r["question"] == id }.sort_by { |r| [r["at"], r["id"]] }
  other = records.select do |r|
    !attached.include?(r) && (Array(r["depends_on"]) + Array(r["related_to"])).any? do |ref|
      ref == id || attached.any? { |mine| mine["id"] == ref }
    end
  end
  unless other.empty?
    body += ["## Contributions elsewhere that cite this work", other.map { |r| "- [#{safe_label(r['title'])}](../records/#{r['id']}.md)" }.join("\n")]
  end
  decisions = catalog.fetch("decisions", {})
  adopted = record_ids[decisions[id]]
  unresolved = attached.select { |r| r["verdict"] == "challenged" && !replacements.key?(r["id"]) && !r["withdrawn"] && !(adopted && adopted["basis"].include?(r["id"])) }
  body << "**Disputed** · A recorded challenge is awaiting resolution." unless unresolved.empty?
  if adopted && adopted["basis"].any? { |ref| replacements.key?(ref) || (record_ids[ref] && record_ids[ref]["withdrawn"]) }
    body << "**Fresh review needed** · Evidence cited by the adopted decision has been revised or withdrawn."
  end
  unless attached.empty?
    body << "## Contribution log"
    body << attached.map { |r|
      people = r["by"].map { |p| safe_label(p["id"]) }.join(", ")
      tools = r["tools"].map { |t| safe_label(t["name"]) }
      outcome = r["verdict"] || r["outcome"] || r["phase"] || r["action"]
      label = [r["kind"], outcome, ("superseded" if replacements.key?(r["id"])), ("withdrawn" if r["withdrawn"])].compact.join(" · ")
      "- [#{safe_label(r['title'])}](../records/#{r['id']}.md) · #{label} · #{people}" +
        (tools.empty? ? "" : " · #{tools.join(', ')}")
    }.join("\n")
  end
  query = URI.encode_www_form("template" => "research.yml", "title" => "[#{id}] ")
  search = URI.encode_www_form("q" => "is:issue in:title \"[#{id}]\"")
  body << "[Join an existing discussion](#{ROOT_URL}/issues?#{search}) · [Contribute to this question](#{ROOT_URL}/issues/new?#{query}) · [Contributor guide](../CONTRIBUTING.md)"
  pages["investigation/#{id}.md"] = body.join("\n\n") + "\n"
end

outline = lambda do |id, depth|
  n = nodes.fetch(id)
  line = "#{'  ' * depth}- #{node_link(n)} · #{STATES[n['state']]}"
  ([line] + Array(children[id]).flat_map { |child| outline.call(child["id"], depth+1) })
end
open_rows = nodes.values.select { |n| n["state"] == "open" && n["id"] != "R" }.map { |n| "- #{node_link(n)} — #{n['next'] || n['summary']}" }
index = [MARK, "# Investigation index", "Choose an open question to see its evidence, the reason for each connection, work already tried, and how to contribute.",
         "## Open questions", open_rows.join("\n"), "## Full tree", outline.call("R", 0).join("\n"),
         "[Diagram of the tree](DIAGRAM.md) · [Mathematical proof map](../PROOF-MAP.md) · [Direction and credit catalog](../DIRECTIONS.md)"]
pages["investigation/README.md"] = index.join("\n\n") + "\n"

diagram = nodes.map.with_index { |(id, _), i| [id, "n#{i}"] }.to_h
chart = ["flowchart TD"]
nodes.each do |id, n|
  chart << "  #{diagram[id]}[\"#{id}\"]:::#{n['state']}"
  chart << "  #{diagram[n['parent']]} --> #{diagram[id]}" if n["parent"]
end
chart += ["  classDef open fill:#deebff,color:#142f4e,stroke:#4275ad", "  classDef partial fill:#fff0cf,color:#502e07,stroke:#a86c18",
          "  classDef scoped fill:#dcf5e7,color:#143e2a,stroke:#38805c", "  classDef background fill:#eee,color:#222,stroke:#777"]
fence = 96.chr * 3
pages["investigation/DIAGRAM.md"] = [MARK, "# Investigation tree", "Blue shows open questions, amber shows partial bounds, and green shows results for the stated scope. [Browse the linked questions](README.md)",
  "#{fence}mermaid\n#{chart.join("\n")}\n#{fence}"].join("\n\n") + "\n"

credit = [MARK, "# Research directions and credit",
  "The source problem is Vincent Conitzer’s. Robert Thomas Collins selected and directed the investigation. The dates below identify the discussion that set each direction (UTC when a time is given). Entries distinguish a personally proposed idea from a research brief supplied or selected for investigation. A direction can motivate a result without conferring authorship of the derivation.",
  "Collins confirmed at publication that he suggested most of the later directions, some after looking up similar problems. The catalog credits his suggestions to apply or test those approaches here. The historical methods, such as Hungarian alternating trees and generalized flow, have their own sources. The main investigation and manuscript discussions supply the dates and role descriptions.",
  "The mathematical work was developed in Codex-assisted research sessions. For the fixed-flow sketch, the recorded disclosure identifies GPT-6.2 Sol for literature review and exact examples and GPT-6.2 Astra for development and checking of the reduction and drafting. Per-lemma model versions and independent human verification are unspecified unless a linked record says otherwise. Researchers cited in the notes retain credit for their original results. [Prior-work audit](notes/L3-prior-partials.md) · [Publication record](PUBLICATION.md)"]
directions.each do |d|
  credit << "<a name=\"direction-#{d['id']}\"></a>\n\n## #{d['title']}"
  credit << "#{d['person']} · #{d['role']} · #{d['date']}"
  credit << d["account"]
  credit << d["nodes"].map { |id| "[#{id}](investigation/#{id}.md)" }.join(" · ")
end
pages["DIRECTIONS.md"] = credit.join("\n\n") + "\n"

changed = pages.select { |file, content| !File.file?(file) || File.binread(file) != content.b }
unexpected = Dir["investigation/*.md"] - pages.keys
ensure_value(unexpected.empty?, "Unexpected generated pages: #{unexpected.join(', ')}")
if CHECK
  abort "Regenerate with ruby scripts/build_map.rb: #{changed.keys.join(', ')}" unless changed.empty?
else
  changed.each { |file, contents| FileUtils.mkdir_p(File.dirname(file)); File.write(file, contents) }
end
puts "#{nodes.length} questions and branches, #{links.length} research links, #{directions.length} directions, #{records.length} contribution records."
