# Frontend, checked core, and runtime boundary

A richer frontend may elaborate into the checked VegasCore source language.
VegasCore does not duplicate frontend parsing, diagnostics, or deployment
configuration. Integration requires a canonical checked artifact and a proof
or independently audited validation of the elaboration boundary.

```text
rich source
  -> checked sequential core
  -> typed event graph
  -> native public-message application
```

The checked artifact must identify its language version, declarations, initial
environment, and retained executable expressions. A source hash records
identity but does not prove that two implementations assign the same meaning.

Frontend features outside the checked core must be rejected or elaborated
explicitly. Runtime capabilities such as private delivery, deadlines, entropy,
authentication, and settlement are not silently inferred from source syntax.

The maintained high-level prototype, `Vegas.Language`, provides typed syntax,
nullable guard sugar, and lowering to `SurfaceCore`. Its optional `Legal`
predicate requires a satisfying value for every commitment guard in every
visible environment. The failure-aware `SourceProgram` has no such requirement:
it retains guards for deferred resolution and admits explicit failures.
`SurfaceCore` supplies no execution semantics, so typed lowering does not
establish a strategic or operational correspondence. A verified elaborator
must account for these choices, including publication-result handling, before
the prototype can serve as a frontend to the checked compiler.
