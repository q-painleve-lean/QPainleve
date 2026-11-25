/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Ruling.Hirzebruch.Prime
public import QPainleve.Geometry.Toric.Fan.Ruling.Quadric

import QPainleve.Geometry.Toric.Fan.Boundary.Intersection
import QPainleve.Geometry.Toric.Fan.Boundary.Node
import QPainleve.Geometry.Toric.Fan.Picard.Ruling
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective
import TauCeti.AlgebraicGeometry.IdealSheaf.Product

/-!
# Coordinate boundary of a Hirzebruch ruling

The two transverse rays give the scheme-theoretic fibers over the two coordinate
points of the projective line. The two remaining rays give sections of the ruling.
Their ideals, together with the two fiber ideals, give the reduced toric boundary
as a product of ideal sheaves. On the quadric, the two sections are the
coordinate fibers of the exchanged ruling.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.CartierDivisor
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]

local notation "p[" k "]" => projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) k 0

section Hirzebruch

variable
  (b : Basis (Fin 2) ℤ N) (e : ℤ) (hΦ : Φ.IsRegular) (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])

local notation "X" => Φ.algebraicRealization
local notation "S" => Spec (CommRingCat.of ℂ)
local notation "m" => LinearMap.toAddMonoidHom (b.coord 1)
local notation "signCondition" => nonneg_or_nonpos_hirzebruch_ruling_character b e r hr
local notation "q" => Φ.characterRuling m signCondition
local notation "I[" j "]" => Φ.rayBoundaryIdeal hΦ (r j)

/-- The scheme-theoretic fibers at the two coordinate points of a Hirzebruch
ruling are the reduced ray divisors indexed by 1 and 3, respectively. -/
theorem rayBoundaryIdeal_hirzebruch_eq_coordinateFiber (k : Fin 2) :
    I[(![1, 3] : Fin 2 → Fin 4) k] = p[k].ker.comap q := by
  classical
  let j := (![1, 3] : Fin 2 → Fin 4) k
  have hP := (projectiveLine.polynomialPoint_over ℂ (RingHom.id ℂ) k (0 : ℂ)).trans
    (Spec.map_id (CommRingCat.of ℂ))
  let hF := Φ.isEffectiveCartier_characterRuling_fiber m signCondition
    (hirzebruch_ruling_character_ne_zero b) p[k] hP
  let hR := Φ.isEffectiveCartier_rayBoundaryIdeal hΦ (r j)
  have := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  apply (hR.toCartierDivisor_eq_iff hF).mp
  apply toWeilDivisor_injective
  rw [Φ.toWeilDivisor_characterRuling_coordinateFiber m signCondition
    (hirzebruch_ruling_character_ne_zero b) k hΦ,
    hirzebruch_ruling_coordinateFiber_coefficients b e r hr k]
  -- A prime ray ideal is the reduced closure of its generic point.
  have hRW : hR.toCartierDivisor.toWeilDivisor = WeilDivisor.ofPoint
      (Φ.rayBoundaryPoint hΦ (r j)) := by
    simpa only [hR, rayBoundaryIdeal_def] using
      toWeilDivisor_toCartierDivisor_vanishingIdeal_closure_singleton
        (Φ.rayBoundaryPoint hΦ (r j))
  rw [hRW]
  apply WeilDivisor.ext
  intro x
  by_cases hx : x ∈ Set.range (Φ.rayBoundaryPoint hΦ)
  · obtain ⟨ρ, rfl⟩ := hx
    rw [Φ.coeff_rayDivisorToWeilDivisor]
    by_cases hρ : ρ = r j
    · subst ρ
      simp [j]
    · change _ = (Pi.single (r j) 1 : Φ.Ray → ℤ) ρ
      rw [WeilDivisor.coeff_ofPoint_of_ne (fun h ↦ hρ (Φ.rayBoundaryPoint_injective hΦ h)),
        Pi.single_eq_of_ne hρ]
  · rw [Φ.coeff_rayDivisorToWeilDivisor_of_notMem_range hΦ _ hx,
      WeilDivisor.coeff_ofPoint_of_ne (fun h ↦ hx ⟨r j, h.symm⟩)]

/-- A point lies on an invariant fiber exactly when its ruling value is the
corresponding coordinate point of the projective line. -/
theorem mem_support_rayBoundaryIdeal_hirzebruch_coordinateFiber_iff (k : Fin 2) (x : X) :
    x ∈ (I[(![1, 3] : Fin 2 → Fin 4) k]).support ↔ q x = p[k] (IsLocalRing.closedPoint ℂ : S) := by
  have hP := (projectiveLine.polynomialPoint_over ℂ (RingHom.id ℂ) k (0 : ℂ)).trans
    (Spec.map_id (CommRingCat.of ℂ))
  let : IsClosedImmersion p[k] := (p[k]).isClosedImmersion_of_comp_eq_id hP
  have hRange : Set.range ⇑p[k] = {p[k] (IsLocalRing.closedPoint ℂ : S)} :=
    Set.range_eq_singleton (fun y ↦ congrArg (⇑p[k]) (Subsingleton.elim y _))
  rw [rayBoundaryIdeal_hirzebruch_eq_coordinateFiber b e hΦ r hr k,
    ← SetLike.mem_coe, support_comap, TopologicalSpace.Closeds.coe_preimage, Set.mem_preimage,
    Scheme.Hom.support_ker, (p[k]).isClosedEmbedding.isClosed_range.closure_eq, hRange,
    Set.mem_singleton_iff]

private theorem isIso_hirzebruch_ruling_invariant_section (hc : Φ.IsComplete) (k : Fin 2) :
    IsIso (I[(![0, 2] : Fin 2 → Fin 4) k].subschemeι ≫ q) := by
  classical
  let : (X).IsProjectiveOver ℂ :=
    Φ.isProjectiveOver_algebraicRealization_of_isComplete hΦ hc b
  have hdim : finrank ℤ N = 2 := (finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  let : SmoothOfRelativeDimension 2 (X ↘ S) := by
    rw [algebraicRealization_over]
    exact hdim ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  rw [rayBoundaryIdeal_def]
  apply isIso_hirzebruch_ruling_prime_of_degree_one b e hΦ hc r hr
  fin_cases k
  · exact (hirzebruch_section_coordinates b e hΦ r hr).2
  · exact (hirzebruch_opposite_section_coordinates b e hΦ r hr).2

/-- The toric boundary of a complete regular Hirzebruch fan consists of two
disjoint invariant sections and the two coordinate fibers, with equality of ideal sheaves. -/
theorem exists_hirzebruch_toric_boundary_sections_and_fibers (hc : Φ.IsComplete) :
    ∃ s : Fin 2 → (projectiveLine ℂ ⟶ X),
      (∀ k, s k ≫ q = 𝟙 _) ∧
      (∀ k, (s k).ker = I[(![0, 2] : Fin 2 → Fin 4) k]) ∧
      Disjoint (s 0).ker.support (s 1).ker.support ∧
      Φ.boundaryIdeal inferInstance =
        (s 0).ker * (s 1).ker * (p[0].ker.comap q) * (p[1].ker.comap q) := by
  classical
  let ι (k : Fin 2) := (I[(![0, 2] : Fin 2 → Fin 4) k]).subschemeι
  let : ∀ k, IsIso (ι k ≫ q) := isIso_hirzebruch_ruling_invariant_section b e hΦ r hr hc
  let s (k : Fin 2) := inv (ι k ≫ q) ≫ ι k
  have hs (k : Fin 2) : (s k).ker = I[(![0, 2] : Fin 2 → Fin 4) k] :=
    (Scheme.Hom.ker_comp_of_isIso _ _).trans (ker_subschemeι _)
  refine ⟨s, fun k ↦ by simp [s], hs, ?_, ?_⟩
  · rw [hs 0, hs 1, ← sup_eq_top_iff_disjoint_support]
    change I[0] ⊔ I[2] = ⊤
    apply Φ.sup_rayBoundaryIdeal_eq_top hΦ
    rintro ⟨σ, h₀, h₂⟩
    have hpos : i (b 0) ∈ σ.val := by simpa [congrFun hr 0] using h₀ (r 0).primitiveGenerator_mem
    have hneg : -i (b 0) ∈ σ.val := by simpa [congrFun hr 2] using h₂ (r 2).primitiveGenerator_mem
    exact (Φ.isToricCone σ.property).salient _ hpos
      (fun hz ↦ b.ne_zero 0 (Φ.lattice.injective (hz.trans (map_zero i).symm))) hneg
  · let := Fintype.ofFinite Φ.Ray
    have hdim : finrank ℤ N = 2 := (finrank_eq_card_basis b).trans (Fintype.card_fin 2)
    rw [Φ.boundaryIdeal_eq_prod_rayBoundaryIdeal hΦ (Φ.isEffectiveCartier_boundaryIdeal hΦ hc hdim),
      ← r.prod_comp, Fin.prod_univ_four, hs 0, hs 1,
      ← rayBoundaryIdeal_hirzebruch_eq_coordinateFiber b e hΦ r hr 0,
      ← rayBoundaryIdeal_hirzebruch_eq_coordinateFiber b e hΦ r hr 1]
    change I[0] * I[1] * I[2] * I[3] = I[0] * I[2] * I[1] * I[3]
    ac_rfl

end Hirzebruch

variable (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])

local notation "b'" => b.reindex (Equiv.swap 0 1)
local notation "r'" => Equiv.trans (Equiv.trans (Equiv.swap (0 : Fin 4) 1) (Equiv.swap 2 3)) r
local notation "hr'" => quadric_swapped_generators b r hr
local notation "q₀" =>
  Fan.characterRuling Φ (LinearMap.toAddMonoidHom (Basis.coord b 0))
    (nonneg_or_nonpos_quadric_transverse_character b r hr)
local notation "q₁" =>
  Fan.characterRuling Φ (LinearMap.toAddMonoidHom (Basis.coord b 1))
    (nonneg_or_nonpos_hirzebruch_ruling_character b 0 r hr)

include hΦ hc hr in
/-- The toric boundary ideal on the quadric is the product of the two coordinate
fiber ideals in each of its two rulings. -/
theorem boundaryIdeal_eq_four_coordinate_fibers :
    Φ.boundaryIdeal inferInstance =
      (p[0].ker.comap q₀) * (p[1].ker.comap q₀) *
        (p[0].ker.comap q₁) * (p[1].ker.comap q₁) := by
  let := Fintype.ofFinite Φ.Ray
  have hdim : finrank ℤ N = 2 := (finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  have h₀ := rayBoundaryIdeal_hirzebruch_eq_coordinateFiber (b') 0 hΦ (r') (hr') 0
  have h₂ := rayBoundaryIdeal_hirzebruch_eq_coordinateFiber (b') 0 hΦ (r') (hr') 1
  rw [characterRuling_quadric_swap b r hr] at h₀ h₂
  have hr₀ : r' (![1, 3] (0 : Fin 2)) = r 0 := congrArg r (by decide)
  have hr₂ : r' (![1, 3] (1 : Fin 2)) = r 2 := congrArg r (by decide)
  rw [hr₀] at h₀
  rw [hr₂] at h₂
  rw [Φ.boundaryIdeal_eq_prod_rayBoundaryIdeal hΦ (Φ.isEffectiveCartier_boundaryIdeal hΦ hc hdim),
    ← r.prod_comp, Fin.prod_univ_four, ← h₀, ← h₂,
    ← rayBoundaryIdeal_hirzebruch_eq_coordinateFiber b 0 hΦ r hr 0,
    ← rayBoundaryIdeal_hirzebruch_eq_coordinateFiber b 0 hΦ r hr 1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ac_rfl

end TauCeti.Toric.Fan
