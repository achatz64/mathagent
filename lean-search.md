# Mathlib Stacks Project tags

Mathlib supports inline links to the Stacks Project with the declaration
attribute:

```lean
@[stacks TAG]
```

`TAG` is a four-character Stacks Project tag. This metadata is attached to the
Lean declaration and is therefore available from its source.

Mathlib provides `#stacks_tags` to enumerate all tagged declarations and
`#stacks_tags!` to include their statements. These global commands should be
treated as batch tools: in the current MCP setup, enumerating all tags did not
return promptly.

Current MCP workflow:

1. use LeanExplore to discover a declaration by name or mathematical meaning;
2. retrieve its source with LeanExplore; and
3. inspect the source for `@[stacks ...]`.

The normal LeanExplore result schema does not expose Stacks tags as a dedicated
search/filter field. Tags are consequently usable for provenance inspection
after discovery, but not currently for reliable tag-based retrieval.
