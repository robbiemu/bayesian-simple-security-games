# How to join the investigation

Start with an [open question](investigation/README.md). Each node gives the mathematical scope, a source note, earlier directions, and reasons to follow a related result. Several people can pursue one question at the same time. A short failed attempt, a precise objection, and an independently reproduced computation are all contributions.

## Contribute from a browser

1. Open a node and choose **Contribute to this question**. Use the form for a new subquestion, an attempt, a result, or a review. To join a conversation already in progress, reply on its issue. [Research contribution form](https://github.com/robbiemu/bayesian-simple-security-games/issues/new?template=research.yml) · [Open discussions in Issues](https://github.com/robbiemu/bayesian-simple-security-games/issues)
2. Name the node and the people responsible for the idea, work and checks. Link the exact record or Git revision you examined. A pseudonym is welcome. Explain the relation to another attempt in a sentence, especially when a counterexample affects only a special case.
3. Describe your tools. For each model, give provider, displayed name, client, version if known, role, the specific step it supplied, and how its output was checked. If a model originated the question or suggested the key lemma, say so. Use `none`, `unknown`, or `undisclosed` where appropriate. For software, include the version and reproducible inputs or commands.
4. A maintainer can turn the submission into a versioned record through a pull request, link the issue in `source`, name the recorder in `submitted_by`, and reply with the merged record link. The indexed archive is rebuilt from committed records. Share material and excerpts you are entitled and willing to publish.

## Contribute with Git

Original writing is contributed under CC BY 4.0 and original code under MIT. Identify third-party sources and their own terms. [Repository licenses](LICENSE.md)

From the repository root, Ruby and its standard library are sufficient. This example starts a result about the supplied-capacity problem.

```sh
ruby scripts/new_record.rb result A4h5
```

Edit the new file under `records/`. Give it a title and add your proof, failure mode, or reproduction instructions below the YAML header. For a new question, use `question` in the same command and give a criterion that would settle it. The printed UUID becomes its stable node ID. Then run the checks and open a pull request with the files that changed.

```sh
ruby scripts/build_map.rb
ruby scripts/build_map.rb --check
```

### Research records

| Kind | Fields that locate the work |
| --- | --- |
| `question` | `parent` is a node ID and `criterion` states the success condition. |
| `attempt` | `question` and a `phase` of `started`, `paused`, or `finished`. Use `target` to identify an earlier attempt you are updating. |
| `result` | `question` and an `outcome` of `proof`, `counterexample`, `computation`, `partial`, or `dead_end`. Explain the scope and supply evidence. |
| `review` | `question`, the result ID in `target`, and a `verdict` of `supports`, `reproduced`, or `challenged`. For a historical note, use its node ID as the target and give its full Git commit in `revision`. |
| `decision` | `question`, `action` (`resolve` or `reopen`), and the IDs in `basis`. A maintainer adopts a decision by mapping the question to its record in `catalog/investigation.json` under `decisions`. Resolution needs a review by someone outside the answer’s author group who checked the stated criterion. |

`by` names the contributors and their roles. `at` is a quoted UTC timestamp. A later record can cite `depends_on`, link other records through `related_to`, or correct a prior record with `supersedes`. Give a reason for each relation in the body. To withdraw a contribution, append a correction with `withdrawn: true`. Reviews keep their original targets. Cite papers and existing notes in the body. Each attached file in `artifacts` has a repository-relative `path` and a `sha256` digest. The maintainer confirms attribution and checks the cited evidence before merging.

Use one tools entry per model or program. For a model record the provider, displayed name, client, version (or `null`), roles, contribution and check. In joint work add `used_by` with the relevant contributor IDs. A software entry uses `kind: software`, `name`, `version` and `contribution`. [Example disclosure for an exact replay](records/b550a724-e9aa-4fb3-9668-c0ca5c9e8142.md)

## Maintain the tree and focused views

The historical nodes and explained cross-references are in [the catalog](catalog/investigation.json). Each link has an origin, a target, a relation, a one-sentence reason and a source path. The renderer shows it on both node pages. Question records add new nodes automatically. Historical human direction and source credit live in [the direction catalog](catalog/directions.json). Generated pages include a Markdown tree, a Mermaid diagram, a page for each node and a chronological credit catalog. [Direction catalog for readers](DIRECTIONS.md)

For an experimental check, record the command, input, relevant seed and expected result. For the existing exact witnesses, run `python3 experiments/b3_fixed_load_search.py --replay active` or replace `active` with `used`. The [Lean workspace](lean/README.md) describes the statements it checks.
