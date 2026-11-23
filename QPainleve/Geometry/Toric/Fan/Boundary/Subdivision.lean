/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import QPainleve.Geometry.Toric.Fan.Boundary.Center

import QPainleve.AlgebraicGeometry.Morphisms.Pullback.IsoLocus
import TauCeti.RingTheory.LocalRing.Basic

/-!
# The boundary under a fan subdivision

The inverse image of the dense torus under a subdivision is the dense torus.
Consequently the reduced inverse image of the toric boundary is the toric
boundary of the subdividing fan. Every old ray survives and its affine chart is unchanged.
In particular, each binomial center on the old boundary pulls back to the center with
the same primitive orbit character and parameter.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData

namespace TauCeti.Toric.Fan.IsSubdivision

universe u

section Boundary

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i} (h : Φ.IsSubdivision Ψ)
  (hΦ : Nonempty Φ.cones) (hΨ : Nonempty Ψ.cones)

/-- The reduced inverse image of the toric boundary is the boundary of the subdivision. -/
theorem radical_comap_boundaryIdeal :
    ((Ψ.boundaryIdeal hΨ).comap h.toFanHom.algebraicMap).radical = Φ.boundaryIdeal hΦ := by
  rw [← vanishingIdeal_support, Φ.boundaryIdeal_def]
  congr 1
  apply SetLike.coe_injective
  rw [support_comap, Closeds.coe_preimage, Ψ.support_boundaryIdeal,
    Set.preimage_compl, h.preimage_range_denseTorusι hΦ hΨ]
  rfl

/-- The subdivision morphism restricted to the reduced toric boundaries. -/
noncomputable def boundaryMap :
    (Φ.boundaryIdeal hΦ).subscheme ⟶ (Ψ.boundaryIdeal hΨ).subscheme :=
  subschemeMap _ _ h.toFanHom.algebraicMap (le_map_iff_comap_le.mpr
    ((le_radical _).trans_eq (h.radical_comap_boundaryIdeal hΦ hΨ)))

/-- The boundary map commutes with the ambient toric morphism. -/
@[reassoc (attr := simp)]
theorem boundaryMap_comp_subschemeι :
    (h.boundaryMap hΦ hΨ) ≫ (Ψ.boundaryIdeal hΨ).subschemeι =
      (Φ.boundaryIdeal hΦ).subschemeι ≫ h.toFanHom.algebraicMap :=
  subschemeMap_subschemeι _ _ _ _

end Boundary

section Centers

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i} (h : Φ.IsSubdivision Ψ)

variable (ρ : Ψ.Ray) {m : N →+ ℤ} (hdim : Module.finrank ℤ N = 2)
  (hm : m ρ.primitiveGenerator = 0) (hp : Function.Surjective m) (c : ℂˣ)

local notation "s" => ρ.binomialCenter hdim hm hp c
local notation "s'" =>
  Ray.binomialCenter (liftRay h ρ) hdim (m := m)
    (Eq.trans (congrArg m (primitiveGenerator_liftRay h ρ)) hm) hp c

private theorem binomialCenterEval_liftRay :
    (h.liftRay ρ).binomialCenterEval hdim ((congrArg m (h.primitiveGenerator_liftRay ρ)).trans hm)
      hp c = ρ.binomialCenterEval hdim hm hp c := by
  let a := (h.liftRay ρ).binomialCenterEval hdim
    ((congrArg m (h.primitiveGenerator_liftRay ρ)).trans hm) hp c
  let b := ρ.binomialCenterEval hdim hm hp c
  have hker : RingHom.ker a = RingHom.ker b := by
    dsimp only [a, b]
    rw [Ray.ker_binomialCenterEval, Ray.ker_binomialCenterEval]
    have hr : (h.liftRay ρ).toToricRay Φ (h.liftRay ρ).toCone le_rfl =
        ρ.toToricRay Ψ ρ.toCone le_rfl := by
      apply ToricRay.eq_of_toPointedCone_le (Ψ.isToricCone ρ.toCone.property).salient
      rw [Ray.toPointedCone_toToricRay, Ray.toPointedCone_toToricRay, liftRay_toCone]
    have hχ : (h.liftRay ρ).chartCharacter
        ((congrArg m (h.primitiveGenerator_liftRay ρ)).trans hm) = ρ.chartCharacter hm :=
      Subtype.ext (by simp only [Ray.coe_chartCharacter])
    rw [hr, hχ]
    rfl
  let r := Algebra.ofId ℂ (_root_.IsLocalRing.ResidueField ℂ)
  have he : r.comp a = r.comp b := by
    apply TauCeti.IsLocalRing.algHom_residueField_eq_of_ker_eq
    exact (RingHom.ker_comp_of_injective a.toRingHom r.toRingHom.injective).trans
      (hker.trans (RingHom.ker_comp_of_injective b.toRingHom r.toRingHom.injective).symm)
  exact AlgHom.ext fun x ↦ r.toRingHom.injective (congrArg (fun e ↦ e x) he)

/-- The subdivision morphism agrees on old ray centers with the identification of their charts. -/
@[reassoc (attr := simp)]
theorem binomialCenter_comp_algebraicMap :
    s' ≫ h.toFanHom.algebraicMap = s := by
  have hchart : Φ.affineToricChartι (h.liftRay ρ).toCone ≫ h.toFanHom.algebraicMap =
      Ψ.affineToricChartι ρ.toCone :=
    h.affineToricChartι_comp_algebraicMap (h.ray_mem ρ) ρ.toCone.property
  rw [Ray.binomialCenter_def, Category.assoc, hchart, Ray.binomialCenter_def,
    h.binomialCenterEval_liftRay ρ hdim hm hp c]
  rfl

/-- Each binomial center on the old boundary belongs to the isomorphism locus. -/
theorem range_binomialCenter_subset_isoLocus :
    Set.range s ⊆ h.toFanHom.algebraicMap.isoLocus := by
  rw [Ray.binomialCenter_def, Scheme.Hom.comp_base, TopCat.coe_comp]
  exact (Set.range_comp_subset_range _ _).trans
    (h.range_affineToricChartι_subset_isoLocus (h.ray_mem ρ) ρ.toCone.property)

/-- The binomial section in the subdividing fan is the scheme-theoretic inverse image of
the original section. -/
theorem isPullback_binomialCenter :
    IsPullback s' (𝟙 _) h.toFanHom.algebraicMap s :=
  h.toFanHom.algebraicMap.isPullback_of_isIso_of_range_subset_isoLocus _ _ _
    (by simpa only [Category.id_comp] using h.binomialCenter_comp_algebraicMap ρ hdim hm hp c)
    (h.range_binomialCenter_subset_isoLocus ρ hdim hm hp c)

/-- The comparison also identifies the centers as sections on the reduced boundaries. -/
@[reassoc (attr := simp)]
theorem binomialCenterOnBoundary_comp_boundaryMap :
    Ray.binomialCenterOnBoundary (h.liftRay ρ) hdim (m := m)
        ((congrArg m (h.primitiveGenerator_liftRay ρ)).trans hm) hp c ≫
      h.boundaryMap ⟨(h.liftRay ρ).toCone⟩ ⟨ρ.toCone⟩ =
        ρ.binomialCenterOnBoundary hdim hm hp c := by
  apply (cancel_mono (Ψ.boundaryIdeal ⟨ρ.toCone⟩).subschemeι).mp
  rw [Category.assoc, boundaryMap_comp_subschemeι, ← Category.assoc,
    Ray.binomialCenterOnBoundary_comp_subschemeι, Ray.binomialCenterOnBoundary_comp_subschemeι]
  exact h.binomialCenter_comp_algebraicMap ρ hdim hm hp c

end Centers

end TauCeti.Toric.Fan.IsSubdivision
