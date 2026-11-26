# Comparator challenges

Each challenge is a single file `Challenge/<Name>.lean` with a configuration
`comparator/<Name>.json` for [`lake comparator`](https://github.com/leanprover/comparator), which
is part of Lake since Lean v4.35.0.

A challenge file is the trusted specification: it imports only Tau Ceti and Mathlib, defines
everything its statement uses, and states the challenge theorem with `sorry`. The `Challenge` and
`Solution` libraries are outside the audited `QPainleve` library and the default targets, so the
library's no-`sorry` rule and axiom audit do not apply to them.

To submit a solution, copy the challenge file to `Solution/<Name>.lean` and replace the `sorry` by
a proof. The proof may import anything, including `QPainleve`. Run comparator from a clean
checkout (no `.lake` directory) with `bubblewrap` installed:

```sh
lake comparator --config comparator/<Name>.json
```

Comparator checks that every theorem in `theorem_names` has the same statement in the solution as
in the challenge, uses only the permitted axioms, and is accepted by the kernel.

## Challenges

* `SignedClusterModularGroup`: for every toric presentation whose surface satisfies the
  target-pair conditions, the signed cluster modular group of its seed is isomorphic to the group
  of signed boundary isometries of its Picard lattice.
  The [solution](../Solution/SignedClusterModularGroup.lean) uses the cyclic-ray comparison in
  `QPainleve.SignedClusterModularGroup.Realization.Presentation.CyclicRays`.
