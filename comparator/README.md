# Comparator challenges

Each challenge has an entry file `Challenge/<Name>.lean` and a configuration
`comparator/<Name>.json` for [`lake comparator`](https://github.com/leanprover/comparator), which
is part of Lake since Lean v4.35.0.

The `Challenge` library contains the trusted specification. It uses Tau Ceti and Mathlib and
states each challenge theorem with `sorry`. The challenge and solution import the same definitions
when the statement uses local definitions. The `Challenge` and `Solution` libraries are outside
the audited `QPainleve` library and the default targets.

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
