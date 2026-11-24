/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.RingTheory.LocalRing.Cotangent
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
import QPainleve.AlgebraicGeometry.RationalPoint
import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme

/-!
# First infinitesimal neighbourhoods of smooth points

At a closed point of a smooth scheme of relative dimension `n` over an algebraically
closed field, the local ring modulo the squared maximal ideal has dimension `n + 1`
over the base field. This counts the linear conditions for a section of a line
bundle to vanish to order two.
-/

public section

open CategoryTheory TauCeti.AlgebraicGeometry IsLocalRing

namespace AlgebraicGeometry.Scheme

universe u

/-- The square-zero truncation of the local ring at a closed point of a smooth
`n`-dimensional scheme has one residue coordinate and `n` cotangent coordinates. -/
theorem finrank_stalk_quotient_maximalIdeal_sq_of_isClosed {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    {n : ℕ} [SmoothOfRelativeDimension n (X ↘ Spec (.of k))]
    {x : X} (hx : IsClosed {x}) :
    Module.finrank k (X.presheaf.stalk x ⧸ maximalIdeal (X.presheaf.stalk x) ^ 2) = n + 1 := by
  let f := X ↘ Spec (CommRingCat.of k)
  let R := X.presheaf.stalk x
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : IsRegular X := IsRegular.of_smooth f
  have : IsRegularLocalRing R := IsRegular.isRegularLocalRing_stalk x
  have hr : Module.finrank k (ResidueField R) = 1 :=
    (f.finrank_residueField_stalk x (by
      ext c
      simp only [algebraMap_stalk_eq_baseRingToStalk, baseRingToStalk_apply, RingHom.comp_apply,
        Scheme.Modules.baseRingToGlobalSections_apply, f, CommRingCat.hom_comp])).trans
      (f.residueDegree_eq_one_of_isClosed hx)
  have : Module.Finite k (ResidueField R) := Module.finite_of_finrank_pos (hr.symm ▸ Nat.one_pos)
  have : Module.Finite k (R ⧸ maximalIdeal R ^ 2) := finite_quotient_maximalIdeal_sq k R
  have hs := spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_residue_surjective k R
    (IsNoetherian.noetherian _) (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hr).surjective
  have hd : (maximalIdeal R).spanFinrank = n := by
    have h := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq f n).mp inferInstance).2 x hx
    exact_mod_cast (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).trans h
  rw [finrank_quotient_maximalIdeal_sq, hr, ← hs, hd]

end AlgebraicGeometry.Scheme
