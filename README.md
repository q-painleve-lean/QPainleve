# QPainleve

A Lean 4 library on q-Painlevé equations, built on
[Tau Ceti](https://github.com/TauCetiProject/TauCeti) and Mathlib.

Targets live in [QPainleveRoadmap](https://github.com/q-painleve-lean/QPainleveRoadmap).

## Main theorems

- **Toric models.** Every numbered anticanonical cycle on a smooth projective rational complex
  surface has a toric presentation:
  [`TauCeti.Toric.Fan.hasToricPresentation_of_ruled_reduction`](QPainleve/Geometry/Toric/Fan/Presentation/Induction.lean).
- **Torelli theorem.** For anticanonical pairs without internal (−2)-curves, a Picard isometry
  that matches the boundary components, intertwines the signed boundary periods and sends an
  ample class to an ample class is induced by an isomorphism of pairs:
  [`AlgebraicGeometry.Scheme.IdealSheafData.exists_pair_iso_of_root_free_signed_boundary_period`](QPainleve/AlgebraicGeometry/Curves/Node/Period/Torelli.lean)
  (and [`AlgebraicGeometry.Scheme.IdealSheafData.exists_pair_iso_of_root_free_signed_boundary_period_of_nef`](QPainleve/AlgebraicGeometry/Curves/Node/Period/Torelli.lean)
  for a nef boundary of square zero).
- **Cluster modular groups.** For a primitive, nef, square-zero anticanonical cycle of length n
  on a smooth projective rational complex surface, there is a toric seed on `Fin (12 - n)`
  whose signed and unsigned cluster modular groups (opposite groups) are isomorphic to the
  signed boundary isometries and the boundary rotations of the Picard lattice:
  [`QPainleve.SignedClusterModularGroup.exists_picardGroupEquivs_of_anticanonical_cycle`](QPainleve/SignedClusterModularGroup/Realization/Presentation/Anticanonical.lean).

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
