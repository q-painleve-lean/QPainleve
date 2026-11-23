/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.Pullback
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import TauCeti.AlgebraicGeometry.Blowup.BaseChange

/-!
# Affine base change of scheme blowups

The Rees blowup of the extended ideal on a flat affine base change is the inverse image
of that base in the scheme blowup. In particular this compares the two constructions on
an affine chart already presented as the spectrum of a coordinate ring. The matching maps
come from Tau Ceti's universal properties of the scheme blowup and the affine Rees blowup.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits
open TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}} {R : Type u} [CommRing R] (I : X.IdealSheafData)
  (j : Spec (.of R) ⟶ X) [Flat j] (J : Ideal R)

/-- If a flat morphism from a spectrum pulls the center back to the ideal `J`, the Rees
blowup of `J` is the Cartesian base change of the scheme blowup along that morphism. -/
theorem exists_isPullback_toSpecCoeff_reesAlgebra
    (hJ : I.comap j = ofIdealTop (J.map (Scheme.ΓSpecIso (.of R)).inv.hom)) :
    ∃ a : Proj (reesAlgebra.grade J) ⟶ I.blowup,
      IsPullback a (Proj.toSpecCoeff (reesAlgebra.grade J)) I.blowupToBase j := by
  set π := Proj.toSpecCoeff (reesAlgebra.grade J) with hπ_def
  let B := pullback I.blowupToBase j
  have hπ : (I.comap (π ≫ j)).IsEffectiveCartier := by
    rw [comap_comp, hJ, hπ_def, toSpecCoeff_reesAlgebra]
    exact isEffectiveCartier_comap_toSpecZero_reesAlgebra J
  let a := I.blowupLift (π ≫ j) hπ
  have ha : a ≫ I.blowupToBase = π ≫ j := I.blowupLift_blowupToBase _ _
  have hB : ((ofIdealTop (J.map (Scheme.ΓSpecIso (.of R)).inv.hom)).comap
      (pullback.snd I.blowupToBase j)).IsEffectiveCartier := by
    rw [← hJ, ← comap_comp, ← pullback.condition, comap_comp]
    exact I.isEffectiveCartier_comap_blowupToBase.comap _
  let b := projReesAlgebraLift J (pullback.snd I.blowupToBase j)
    (by simpa only [← toSpecCoeff_reesAlgebra J] using hB)
  have hb : b ≫ π = pullback.snd I.blowupToBase j := by
    rw [hπ_def, toSpecCoeff_reesAlgebra]
    exact projReesAlgebraLift_toSpecZero (I := J) _ _
  have hπ' : ((ofIdealTop (J.map (Scheme.ΓSpecIso (.of R)).inv.hom)).comap π).IsEffectiveCartier :=
    by rwa [comap_comp, hJ] at hπ
  let e : Proj (reesAlgebra.grade J) ≅ B :=
    { hom := pullback.lift a π ha
      inv := b
      hom_inv_id := by
        apply projReesAlgebra_hom_ext (I := J)
        · rw [← toSpecCoeff_reesAlgebra J]
          simp only [← hπ_def, Category.assoc, hb, pullback.lift_snd, Category.id_comp]
        · rw [← toSpecCoeff_reesAlgebra J, ← hπ_def, Category.assoc, hb, pullback.lift_snd]
          exact hπ'
      inv_hom_id := by
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst, Category.id_comp]
          apply I.blowup_hom_ext
          · rw [Category.assoc, ha, ← Category.assoc, hb, ← pullback.condition]
          · rw [Category.assoc, ha, ← Category.assoc, hb, ← pullback.condition, comap_comp]
            exact I.isEffectiveCartier_comap_blowupToBase.comap _
        · simp only [Category.assoc, pullback.lift_snd, hb, Category.id_comp] }
  exact ⟨a, IsPullback.of_iso_pullback ⟨ha⟩ e
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)⟩

end AlgebraicGeometry.Scheme.IdealSheafData
