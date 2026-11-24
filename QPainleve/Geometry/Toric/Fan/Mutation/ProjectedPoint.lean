/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Mutation.Blowup

/-!
# Projected points of a toric elementary transformation

Off the pivot fiber, equality of projected points on either side of the elementary
transformation is equivalent to equality on the other side. This lets a point-blowup
resolution retain the first occurrence of a projected center on that open set.
-/

public section

open AlgebraicGeometry CategoryTheory Module PointedCone

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {Φ : Fan i} (ρ : Φ.Ray) (b : Basis (Fin 2) ℤ N)
  (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones) (c : ℂˣ)

local notation "v" => Ray.primitiveGenerator ρ
local notation "hv" => Ray.primitiveGenerator_ne_zero ρ
local notation "hp" => Ray.hull_primitiveGenerator_mem ρ
local notation "Ψ" => Φ.mutationFan b hv hp hOpp
local notation "I" => Ray.mutationSourceCenterIdeal b ρ c
local notation "J" => Ray.mutationTargetCenterIdeal b ρ hOpp c
local notation "G" => Ray.mutationBlowupIso b ρ hOpp c
local notation "U" => Φ.mutationComplement b (Φ.detCharacter_nonneg_or_nonpos b hv hp hOpp) (c : ℂ)
local notation "W" => mutationComplement (Ψ) b
  (Φ.mutationDetCharacter_nonneg_or_nonpos b hv hp hOpp) (c : ℂ)
local notation "E" => Φ.mutationComplementIso b (c : ℂ) hv hp hOpp
local notation "m" => LinearMap.toAddMonoidHom (b.detDualEquiv v)
local notation "f" => Φ.characterRuling m (Φ.detCharacter_nonneg_or_nonpos b hv hp hOpp)
local notation "g" => characterRuling (Ψ) m (Φ.mutationDetCharacter_nonneg_or_nonpos b hv hp hOpp)

/-- If the reference point projects off the pivot fiber, another point projects to the
same point on the source exactly when it projects to the same point on the target. -/
theorem Ray.mutationBlowupIso_projected_eq_iff {p q : (I).blowup}
    (hq : (I).blowupToBase q ∈ U) :
    (J).blowupToBase ((G).hom p) = (J).blowupToBase ((G).hom q) ↔
      (I).blowupToBase p = (I).blowupToBase q := by
  let y : (U).toScheme := ⟨(I).blowupToBase q, hq⟩
  have hqy := ρ.mutationBlowupIso_apply_over_complement b hOpp c q y rfl
  have hr (z : (I).blowup) : g ((J).blowupToBase ((G).hom z)) = f ((I).blowupToBase z) :=
    congrArg (fun a ↦ a z) (ρ.mutationBlowupIso_hom_comp_ruling b hOpp c)
  constructor
  · intro he
    have hf := (hr p).symm.trans ((congrArg (fun z ↦ g z) he).trans (hr q))
    have hmem : (I).blowupToBase p ∈ U := by
      rw [mutationComplement_eq, Scheme.Hom.mem_preimage] at hq ⊢
      exact hf ▸ hq
    let x : (U).toScheme := ⟨(I).blowupToBase p, hmem⟩
    have hpx := ρ.mutationBlowupIso_apply_over_complement b hOpp c p x rfl
    have e : (W).ι ((E).hom x) = (W).ι ((E).hom y) := hpx.symm.trans (he.trans hqy)
    exact congrArg Subtype.val ((E).hom.injective ((W).ι.injective e))
  · intro he
    exact (ρ.mutationBlowupIso_apply_over_complement b hOpp c p y he).trans hqy.symm

end TauCeti.Toric.Fan
