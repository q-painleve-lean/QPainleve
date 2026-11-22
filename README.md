# QPainleve

A Lean 4 library toward the q-Painlevé equations and their cluster-algebraic symmetries,
built on [Tau Ceti](https://github.com/TauCetiProject/TauCeti) and Mathlib.

Targets live in [QPainleveRoadmap](https://github.com/q-painleve-lean/QPainleveRoadmap).
Current area: signed cluster modular groups of anticanonical cycles.

## Building

```sh
lake exe cache get
lake build
```

## Merging

Workers submit finished PRs. Review runs only four rubrics (`[review]` in
[tauceti.toml](tauceti.toml)): `correctness`, `reuse`, `scope` and `placement`. Once all four
are green on the current head and CI passes, [auto-merge.yml](.github/workflows/auto-merge.yml)
enqueues the PR and the merge queue builds the combined commit before it lands. Changes outside
`QPainleve/` (workflows, scripts, Lake configuration) always need a human merge.
