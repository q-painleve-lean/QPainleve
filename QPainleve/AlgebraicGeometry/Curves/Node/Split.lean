/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Locus
public import TauCeti.RingTheory.Node.Branches

import TauCeti.AlgebraicGeometry.Curves.Node.Branches
import TauCeti.AlgebraicGeometry.Curves.SingularLocus.Smooth

/-!
# Nodes of a split node chart

The relative singular locus of the split chart `xy = 0` is its origin section.
This identifies the nodes of the chart in the pointwise sense.
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry

namespace TauCeti.NodeAlgebra

/-- The relative nodes of the split chart are exactly the points on the origin section. -/
theorem isNodeAt_iff_mem_range_origin {R : Type*} [CommRing R]
    (x : Spec (.of (NodeAlgebra R 0))) :
    let f := Spec.map (CommRingCat.ofHom (algebraMap R (NodeAlgebra R 0)))
    f.IsNodeAt x ↔ x ∈ Set.range (Spec.map (CommRingCat.ofHom (origin R).toRingHom)) := by
  intro f
  let X := Spec (.of (NodeAlgebra R 0))
  let : X.Over (Spec (.of R)) := ⟨f⟩
  have hnodal := atWorstNodalOfRelativeDimensionOne (0 : R)
  have : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of R)) := hnodal.syntomic
  have hnode := f.isNodeAt_iff_notMem_smoothLocus hnodal x
  have hsing := X.mem_support_singularLocus_iff_notMem_smoothLocus (R := R) x
  refine hnode.trans (hsing.symm.trans ?_)
  rw [← SetLike.mem_coe, ← Scheme.IdealSheafData.range_subschemeι]
  have hrange :
      Set.range ((X.singularLocus R).subschemeι ∘ (splitSingularLocusIso R).inv) =
        Set.range (X.singularLocus R).subschemeι :=
    (splitSingularLocusIso R).inv.surjective.range_comp _
  rw [← hrange, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
    splitSingularLocusIso_inv_subschemeι]

end TauCeti.NodeAlgebra
