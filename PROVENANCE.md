## Field reference

### `[source]`

| Field | Required | Meaning |
|---|---|---|
| `title` | yes | paper title (top-level `title` dropped as redundant) |
| `author` | yes | paper author(s) |
| `location` | yes | generic link — DOI URL, `arxiv.org/abs/...`, publisher page, anything resolvable |
| `hash` | yes | `sha256:<hex>` of the exact source artifact used (use `curl -L "{location link}" \| sha256sum `) 
| `year` | optional | publication year |
| `type` | optional | `paper`, `book`, `preprint`, `thesis`, `note`, … |

### `[formalization]`

| Field | Required | Meaning |
|---|---|---|
| `formalizers` | yes | who did/owns the formalization (distinct from `author`), typically github handle |
| `scope` | yes | free text on what was **omitted**: remarks, examples, sections, side lemmas, … |
| `source-hooks` | yes | a list of source <-> target reference methods used, e.g. labels, line number, etc.
