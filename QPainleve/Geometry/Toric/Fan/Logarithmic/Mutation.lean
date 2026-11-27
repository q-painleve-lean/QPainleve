/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Morphism
public import QPainleve.Geometry.Toric.Fan.Mutation.Subdivision

import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic

/-!
# Specified elementary transformations of logarithmic models

When a logarithmic morphism resolves an elementary transformation, its ordered
internal blowup model over a subdivision resolves the refined transformation.
The first occurrence of the pivot in the ordered centers is determined, and the
two projections from the internal model recover the specified morphisms.
This compares an elementary transformation in the factorization of
[Lutz, Theorem 8.4][HKL] with the ordered blowup model of its source morphism.

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=68
-/

public section

open AlgebraicGeometry CategoryTheory PointedCone QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {K : Type} [Field K] [IsAlgClosed K]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Module.Basis (Fin 2) ℤ N)
  (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (ρ : Φ.Ray)
  (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones) (c : Kˣ)

local notation "S" => Spec (CommRingCat.of K)
local notation "X[" Δ "]" => Fan.finiteFanScheme K Δ
local notation "π[" H "]" => FanHom.finiteFanSchemeHom K (IsSubdivision.toFanHom H)
local notation "rankTwo" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "D" => Φ.toricBoundaryIdeal K hc.nonempty_cones
local notation "M[" Δ "," r "," h "]" =>
  Fan.mutationFan Δ b (Ray.primitiveGenerator_ne_zero r) (Ray.hull_primitiveGenerator_mem r) h
local notation "μ[" Δ "," r "," h "]" =>
  Scheme.PartialMap.toRationalMap (Fan.mutationPartialMap K Δ b (c : K)
    (Ray.primitiveGenerator_ne_zero r) (Ray.hull_primitiveGenerator_mem r) h)

variable {Z : Scheme} [Z.Over (Spec (.of K))] [IsIntegral Z] [Z.IsProjectiveOver K]
  [SmoothOfRelativeDimension 2 (Z ↘ Spec (.of K))]
  {f : Z ⟶ Φ.finiteFanScheme K}
  [f.IsOver (Spec (.of K))] [IsDominant f]
  {P : Z.IdealSheafData}

/-- Suppose the specified logarithmic morphism `f` resolves a toric elementary
transformation and `r` represents its composite. In the normalized ordered internal
model of `f`, the pivot occurs on the lift of its original ray with the original
binomial parameter. The refined mutation is resolved on that same model and its
projection to the coarse target recovers `r` on the entire model. -/
theorem exists_toric_internal_mutation_factorization_of_pullbackTopFormDivisor
    (hf : Scheme.BirationalOver f (𝟙 X[Φ])) (hP : P.IsEffectiveCartier)
    (r : Z ⟶ X[M[Φ,ρ,hOpp]])
    (hr : letI : Nonempty Φ.cones := hc.nonempty_cones
      f.toRationalMap.comp μ[Φ,ρ,hOpp] = r.toRationalMap) :
    letI : Nonempty Φ.cones := hc.nonempty_cones
    letI : SmoothOfRelativeDimension 2 (X[Φ] ↘ Spec (.of K)) :=
      (Φ.finiteFanScheme_over K).symm ▸
        (rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec K hΦ)
    let hD := Φ.isEffectiveCartier_boundaryIdeal K hΦ hc rankTwo
    ∀ (ω : hD.toInvertibleSheaf ≅ canonicalBundle K X[Φ] 2)
      (hTotal : ((D).comap f).IsEffectiveCartier)
      (hRam : letI := SmoothOfRelativeDimension.smooth 2 (Z ↘ Spec (.of K))
        (ramificationIdealSheaf K f).IsEffectiveCartier),
      pullbackTopFormDivisor K f 2 hD ω hTotal hRam = -hP.toCartierDivisor →
    ∃ (Ω : Fan i) (hΩ : Ω.IsRegular) (H : Ω.IsSubdivision Φ),
      let σ := H.liftRay ρ
      let hOpp' := H.hull_neg_primitiveGenerator_liftRay_mem ρ hOpp
      let Hμ := H.mutation b (H.primitiveGenerator_liftRay ρ)
        ρ.primitiveGenerator_ne_zero σ.primitiveGenerator_ne_zero
        ρ.hull_primitiveGenerator_mem hOpp σ.hull_primitiveGenerator_mem hOpp'
      letI : Nonempty Ω.cones := H.nonempty_cones_of_nonempty hc.nonempty_cones
      ∃ (n : ℕ) (a : Fin n → Ω.Ray) (u : Fin n → Kˣ),
        let A := Ω.internalBlowupTower K b a u
        letI : IsIntegral A.1 := isIntegral_internalBlowupTower K b a u hΩ
        letI : IsModification A.2.toTower.toBase :=
          isModification_internalBlowupTower_toBase K b a u hΩ
        ∃ (e : A.1 ≅ Z) (q : A.1 ⟶ X[M[Ω,σ,hOpp']]),
          e.hom ≫ f = A.2.toTower.toBase ≫ π[H] ∧
          e.hom ≫ r = q ≫ π[Hμ] ∧
          P.comap e.hom = A.2.boundaryι.ker ∧
          A.2.toTower.toBase.toRationalMap.comp μ[Ω,σ,hOpp'] = q.toRationalMap ∧
          ∃ k : Fin n, a k = σ ∧ u k = c ∧ ∀ j < k, (a j, u j) ≠ (σ, c) := by
  intro hD ω hTotal hRam hdiv
  let : Nonempty Φ.cones := hc.nonempty_cones
  let : SmoothOfRelativeDimension 2 (X[Φ] ↘ Spec (.of K)) :=
    (Φ.finiteFanScheme_over K).symm ▸
        (rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec K hΦ)
  obtain ⟨Ω, hΩ, H, n, a, u, e, he, hboundary⟩ :=
    exists_toric_internal_factorization_of_pullbackTopFormDivisor K b hΦ hc hf hP ω hTotal hRam hdiv
  let σ := H.liftRay ρ
  let hOpp' := H.hull_neg_primitiveGenerator_liftRay_mem ρ hOpp
  let : Nonempty Ω.cones := H.nonempty_cones_of_nonempty hc.nonempty_cones
  let A := Ω.internalBlowupTower K b a u
  let p := A.2.toTower.toBase
  let := isIntegral_internalBlowupTower K b a u hΩ
  let := isModification_internalBlowupTower_toBase K b a u hΩ
  have hres : (p ≫ π[H]).toRationalMap.comp μ[Φ,ρ,hOpp] = (e.hom ≫ r).toRationalMap := by
    simp only [p, A, ← he, ← Scheme.RationalMap.comp_toRationalMap,
      ← Scheme.Hom.toRationalMap_compHom, Scheme.RationalMap.comp_assoc, hr]
  obtain ⟨q, ⟨hq, hproj⟩, -⟩ := H.existsUnique_mutation_resolution K b ρ hOpp c
    (isClosedPointTower_internalBlowupTower K b a u) hΦ hΩ (e.hom ≫ r) hres
  exact ⟨Ω, hΩ, H, n, a, u, e, q, he, hproj.symm, hboundary, hq,
    σ.exists_first_internalBlowupTower_center_of_resolves K b hOpp' c a u q hq⟩

end TauCeti.Toric.Fan
