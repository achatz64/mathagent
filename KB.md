# Knowledge base

## Scope

For each supported language, the knowledge base consists of the available
dependencies, declarations, documentation, and project-specific metadata. Lean
is the first supported language (`ma1`).

The initial Lean knowledge base is not a cold start: Mathlib is available from
the beginning. Mathlib declarations, types, docstrings, modules, imports, and
source locations are part of the imported Lean environment and can therefore be
extracted and indexed automatically.

We do not attempt to reconstruct the scholarly provenance of Mathlib
declarations. Provenance metadata applies to formalizations produced from the
papers and books processed by this project.

Parallel statements and proofs are expected. Each source-specific
formalization remains an independent record; the knowledge base does not
deduplicate them or select a canonical proof.

## Requirements

Author-maintained Lean source is authoritative. Generated documentation,
search indexes, and databases are disposable build artifacts.

The knowledge base must be reproducible from the authoritative data and pinned
versions of its dependencies.

The index build must be incremental. Adding or changing project code must not
require reprocessing all of Mathlib. Unchanged extracted records and embeddings
should be reused, and additions, changes, and deletions must be reflected in the
next index version. A complete rebuild must remain possible for reproducibility.

The system must support references from project formalizations to their
sources. The form and granularity of such references are not fixed. Depending
on the source, useful information might include a bibliographic identifier, a
URL, a document version, a named result, or another locator. None of these is
required universally.

Copyrighted source text is not assumed to be part of the knowledge base.

## Current design direction

We will investigate representing project-specific bibliography and source
references as structured native Lean data, for example by custom commands,
declarations, attributes, or persistent environment extensions. The precise
representation remains an open design question.

Mathlib's inline `@[stacks TAG]` cross-references are a relevant existing
example, although they are Mathlib metadata rather than project provenance.
See [Mathlib Stacks Project tags](lean-search.md) for the mechanism and its
current MCP retrieval limits.

## Architecture

```text
Lean environment
  +-- Mathlib declarations
  +-- project-generated declarations
  +-- project source-reference metadata
            |
            v
extended documentation/declaration extraction
            |
            v
unified machine-readable declaration records
            |
            v
unified lexical, structural, and semantic index
            |
            v
KB MCP tools
            |
            v
Lean LSP verification
```

The generated record for a project declaration may include:

- qualified declaration name;
- formal type and docstring;
- module, imports, and Lean source location;
- zero or more source references in an extensible format;
- the formalization occurrence;
- fields required by lexical and semantic retrieval.

Mathlib records use the same schema where applicable, but their
project-specific source-reference fields remain empty.

## Search

The MCP search surface covers Mathlib and all subsequently generated Lean code.
It should support:

- semantic discovery from informal mathematical language;
- exact declaration and metadata lookup;
- lexical search for names and terminology;
- structural/type search using Lean-aware tools;
- filtering by source and other generated metadata.

Existing Mathlib search infrastructure should be reused. LeanExplore and
LeanSearch provide semantic discovery, while Loogle and Lean's search commands
provide structural and type-based search. Public services do not automatically
contain newly generated project code, so the project needs to run an indexing
pipeline under its own control. We will first try the existing LeanExplore
pipeline on Mathlib together with local project code, and extend it only where
required behavior is missing.

For the usable system, the implementation should reuse a pinned Mathlib base
index and incrementally add project changes. Whether this is represented
internally as one physical index or as several indexes behind one query
interface is an implementation choice. It must behave as one search corpus to
MCP clients.

Incremental change detection should use stable declaration identifiers and
content hashes of the fields that affect extraction and embeddings. Publishing
an updated index should be atomic: clients see either the previous complete
version or the next complete version. This is not required for the initial
proof of concept, which may perform a full rebuild.

Search results are candidates. `lean-lsp-mcp` confirms that a declaration is
available in the locally pinned Lean/Mathlib environment and returns its exact
type, imports, documentation, and goal information.

## Initial proof of concept

The first implementation should avoid decisions that are not needed to test
the core workflow:

1. pin the Lean toolchain and Mathlib revision;
2. extract declarations from Mathlib and a local Lean module;
3. inspect and reuse the LeanExplore indexing pipeline where practical;
4. extend the pipeline only as needed to include the local declaration;
5. build a unified logical search corpus;
6. expose it through a minimal KB MCP tool;
7. verify retrieved declarations through `lean-lsp-mcp`.

The proof-of-concept acceptance test is:

```text
Mathlib + one local Lean module
    -> search corpus
    -> semantic queries covering the four combinations of a result being
       present or absent in Mathlib and in the local module
    -> correct Mathlib and local results
    -> Lean LSP confirmation of the results
```

The proof of concept may rebuild everything and may use temporary storage. Its
purpose is to validate extraction, retrieval, and Lean verification.

## Iteration after the proof of concept

After the core workflow works:

1. extend extraction with one experimental project source-reference field;
2. verify that the field survives extraction, is indexed, and can be used as a
   query filter;
3. determine how the chosen pipeline handles additions, changes, and
   deletions;
4. avoid rebuilding and re-embedding unchanged Mathlib declarations;
5. add stable declaration identifiers and content-based change detection;
6. publish complete index versions atomically;
7. record the Git commit, Lean version, Mathlib revision, and embedding model
   for reproducibility.

No semantic database has been selected. The proof of concept can use whatever
storage the existing indexing pipeline already provides. A different storage
or query engine should be considered only after measuring the working
prototype.

The incremental-update acceptance test is:

```text
existing Mathlib + project index
    -> change one local declaration
    -> update only the affected project records and embeddings
    -> leave the Mathlib base index unchanged
    -> publish a complete new index version
```

## Deferred design choices

These choices do not block the proof of concept:

- the native Lean representation for project source references;
- useful source locators for different source formats;
- the incremental index layout;
- the long-term semantic storage and query engine.
