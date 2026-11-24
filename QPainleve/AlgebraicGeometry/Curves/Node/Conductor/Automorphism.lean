/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Isomorphism
public import TauCeti.AlgebraicGeometry.Curves.Node.Normalization

import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import TauCeti.AlgebraicGeometry.Curves.Node.FiniteEtale
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyReduced

/-!
# Automorphisms of nodal branch schemes

An automorphism of a separated nodal curve over an algebraically closed field
induces the identity on the branch scheme exactly when it fixes each branch point.
-/

public section

open AlgebraicGeometry TauCeti.AlgebraicGeometry

universe u

namespace CategoryTheory.Iso

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
  [C.Over (Spec (.of k))] [IsSeparated (C ↘ Spec (.of k))]
  (e : C ≅ C) [e.hom.IsOver (Spec (.of k))]

/-- An automorphism of a separated nodal curve over the ground field acts trivially
on the branch scheme if and only if it fixes every branch point. -/
theorem branchSchemeIso_eq_refl_iff
    (hn : AtWorstNodalOfRelativeDimensionOne (C ↘ Spec (.of k))) :
    letI := hn.syntomic
    e.branchSchemeIso (R := k) = Iso.refl (C.branchScheme k) ↔
      ∀ q : C.branchScheme k, (e.branchSchemeIso (R := k)).hom q = q := by
  have := hn.syntomic
  let B := C.branchScheme k
  let g := (e.branchSchemeIso (R := k)).hom
  let s := C.branchSchemeToSingularLocus k ≫ (C.singularLocus k).subschemeι ≫ (C ↘ Spec (.of k))
  have : Etale ((C.singularLocus k).subschemeι ≫ (C ↘ Spec (.of k))) :=
    C.etale_singularLocus_subschemeι_comp hn
  have : IsFinite (C.branchSchemeToSingularLocus k) := C.isFinite_branchSchemeToSingularLocus hn
  have : Etale (C.branchSchemeToSingularLocus k) := C.etale_branchSchemeToSingularLocus hn
  have : Etale s := inferInstanceAs (Etale (_ ≫ _))
  have : IsSeparated s := inferInstanceAs (IsSeparated (_ ≫ _))
  have : IsReduced B := s.isReduced_of_smooth
  have hs : g ≫ s = s := by
    simp only [s, g, branchSchemeIso_hom_branchSchemeToSingularLocus_assoc,
      singularLocusIso_hom_subschemeι_assoc, comp_over]
  have : LocallyOfFiniteType (g ≫ s) := hs.symm ▸ inferInstanceAs (LocallyOfFiniteType s)
  refine ⟨fun h q ↦ by simp [h], fun h ↦ Iso.ext ?_⟩
  refine ext_of_apply_eq (f := g) (g := 𝟙 B) s Set.univ isOpen_univ.isLocallyClosed dense_univ
    (fun q _ _ ↦ ?_) (hs.trans (Category.id_comp s).symm)
  exact (h q).trans (rfl : (𝟙 B) q = q).symm

end CategoryTheory.Iso
