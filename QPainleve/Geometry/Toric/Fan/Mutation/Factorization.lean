/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Mutation.Indeterminacy
public import QPainleve.Geometry.Toric.Fan.Mutation.OrderedBlowup

import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic
import QPainleve.Geometry.Toric.Fan.Separated

/-!
# Extracting the pivot of a specified toric mutation

If an ordered internal blowup tower resolves a toric elementary transformation,
the first occurrence of the pivot can be performed first, keeping every other
center in its original relative order. The projection through this pivot blowup
recovers the given morphism to the mutated toric surface. The ordered remaining
centers give a tower over the mutated pivot blowup, with the same boundary
comparison even over the pivot fiber.

The geometry is the elementary transformation of Gross, Hacking and Keel,
[*Birational geometry of cluster algebras*, §3.1](https://arxiv.org/html/1309.2573v2#S3.SS1).
The extraction combines `Ray.exists_internalBlowupTower_center_of_resolves` with
`exists_iso_internalBlowupTower_reindex`.
-/

public section

open AlgebraicGeometry CategoryTheory
open QPainleve.BlowupTower TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [hΦ : Nonempty Φ.cones]
  (b : Module.Basis (Fin 2) ℤ N) (ρ : Φ.Ray) (c : ℂˣ)

local notation "v" => Ray.primitiveGenerator ρ
local notation "hv" => Ray.primitiveGenerator_ne_zero ρ
local notation "hp" => Ray.hull_primitiveGenerator_mem ρ
local notation "J₀" => Ray.mutationSourceCenterIdeal b ρ c
local notation "ι₀" => Ray.mutationSourceBoundaryι b ρ c

variable {n : ℕ} (s : Fin (n + 1) → Φ.Ray) (d : Fin (n + 1) → ℂˣ)

local notation "M" => internalBlowupTower b s d
local notation "F" => QPainleve.BlowupTower.toBase (WithBoundary.toTower (Sigma.snd M))
local notation "tail(" k ")" => alongBoundary (ι₀)
  (fun a ↦ Ray.internalCenter b (s (Fin.succAbove k a)) (d (Fin.succAbove k a)))

variable (hOpp : PointedCone.hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones)

local notation "Ψ" => Φ.mutationFan b hv hp hOpp
local notation "J₁" => Ray.mutationTargetCenterIdeal b ρ hOpp c
local notation "E" => Ray.mutationBlowupIso b ρ hOpp c
local notation "q" =>
  Scheme.PartialMap.toRationalMap (Fan.mutationPartialMap Φ b (c : ℂ) hv hp hOpp)

include hOpp in
private theorem comp_mutationBlowupIso_eq_of_resolves
    {W : Scheme} [IsIntegral W] (p : W ⟶ (J₀).blowup)
    [IsDominant (p ≫ (J₀).blowupToBase)] (r : W ⟶ (Ψ).algebraicRealization)
    (hr : (p ≫ (J₀).blowupToBase).toRationalMap.comp q = r.toRationalMap) :
    p ≫ (E).hom ≫ (J₁).blowupToBase = r := by
  let : Nonempty (Ψ).cones := ⟨Φ.mutationFanConeEquiv b hv hp hOpp ρ.toCone⟩
  let : Scheme.IsSeparated (Ψ).algebraicRealization := (Ψ).isSeparated_algebraicRealization
  apply Scheme.Hom.toRationalMap_injective
  exact (ρ.mutationPartialMap_resolved_of_comp_eq b hOpp c p _ rfl).symm.trans hr

include hOpp in
/-- A specified morphism resolving a toric elementary transformation factors through the
first occurrence of the pivot. The remaining centers retain their original order, including
any repeated centers on the pivot fiber. The source projection, the fixed boundary embedding,
and the given morphism to the mutated fan all agree with those of the factored model. -/
theorem Ray.exists_ordered_pivot_factorization_of_resolves
    [IsIntegral M.1] [IsDominant F] (r : M.1 ⟶ (Ψ).algebraicRealization)
    (hr : (F).toRationalMap.comp q = r.toRationalMap) :
    ∃ k : Fin (n + 1), s k = ρ ∧ d k = c ∧
      (∀ a < k, (s a, d a) ≠ (ρ, c)) ∧
      ∃ e : M.1 ≅ (tail(k)).1,
        e.hom ≫ (tail(k)).2.toTower.toBase ≫ (J₀).blowupToBase = F ∧
        M.2.boundaryι ≫ e.hom = (tail(k)).2.boundaryι ∧
        e.hom ≫ (tail(k)).2.toTower.toBase ≫ (E).hom ≫ (J₁).blowupToBase = r := by
  classical
  let S := Finset.univ.filter fun j ↦ (s j, d j) = (ρ, c)
  obtain ⟨l, hl, hl'⟩ := ρ.exists_internalBlowupTower_center_of_resolves b hOpp c s d r hr
  have hS : S.Nonempty := ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Prod.ext hl hl'⟩⟩
  let k := S.min' hS
  have hk : (s k, d k) = (ρ, c) := (Finset.mem_filter.mp (S.min'_mem hS)).2
  have hk₀ : s k = ρ := congrArg Prod.fst hk
  have hk₁ : d k = c := congrArg Prod.snd hk
  have hfirst (a : Fin (n + 1)) (ha : a < k) : (s a, d a) ≠ (ρ, c) := by
    intro h
    exact (not_le_of_gt ha) (S.min'_le a (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
  have hI : ((s k).internalCenter b (d k)).val.map (Φ.boundaryIdeal hΦ).subschemeι = J₀ := by
    rw [hk₀, hk₁, Ray.mutationSourceCenterIdeal_eq, Ray.map_internalCenter_subschemeι]
  obtain ⟨e, he, hb, -⟩ := exists_iso_internalBlowupTower_split_at b s d k
    (fun a ha h ↦ hfirst a ha (h.trans hk)) hI (ρ.mutationSourceBoundaryι_blowupToBase b c)
  refine ⟨k, hk₀, hk₁, hfirst, e, he, hb, ?_⟩
  let p := e.hom ≫ (tail(k)).2.toTower.toBase
  have hproj : p ≫ (J₀).blowupToBase = F := (Category.assoc _ _ _).trans he
  have : IsDominant (p ≫ (J₀).blowupToBase) := hproj ▸ inferInstanceAs (IsDominant F)
  simpa only [p, Category.assoc] using comp_mutationBlowupIso_eq_of_resolves b ρ c hOpp p r
    (by simpa only [hproj] using hr)

local notation "ray(" a ")" => Φ.mutationFanRayEquiv b hv hp hOpp (s a)
local notation "param(" a ")" =>
  d a * c ^ max (Module.Basis.det b ![Ray.primitiveGenerator (s a), v]) 0
local notation "hΨ" => Nonempty.intro (Φ.mutationFanConeEquiv b hv hp hOpp (Subtype.mk _ hp))
local notation "targetTail(" k ")" => alongBoundary (ρ.mutationTargetBoundaryι b hOpp c)
  (fun a ↦ Ray.internalCenter (h₀ := hΨ) b (ray(Fin.succAbove k a)) (param(Fin.succAbove k a)))

/-- A specified morphism resolving the elementary transformation is the projection
of the transported tower followed by the target pivot projection. The first
source pivot is extracted and the remaining indices keep their relative order.
The isomorphism of the tails identifies their strict boundaries and matches the
actual center ideals, including infinitely near centers over the pivot fiber. -/
theorem Ray.exists_ordered_mutation_factorization_of_resolves
    (hΦreg : Φ.IsRegular) (r : M.1 ⟶ (Ψ).algebraicRealization)
    (hr : have := isIntegral_internalBlowupTower b s d hΦreg
          have := isModification_internalBlowupTower_toBase b s d hΦreg
          (F).toRationalMap.comp q = r.toRationalMap) :
    ∃ k : Fin (n + 1), s k = ρ ∧ d k = c ∧
      (∀ a < k, (s a, d a) ≠ (ρ, c)) ∧
      ∃ (e : M.1 ≅ (tail(k)).1) (g : (tail(k)).1 ≅ (targetTail(k)).1),
        IsLift (E) (tail(k)).2.toTower (targetTail(k)).2.toTower g ∧
        e.hom ≫ (tail(k)).2.toTower.toBase ≫ (J₀).blowupToBase = F ∧
        M.2.boundaryι ≫ e.hom = (tail(k)).2.boundaryι ∧
        e.hom ≫ g.hom ≫ (targetTail(k)).2.toTower.toBase ≫ (J₁).blowupToBase = r ∧
        (tail(k)).2.boundaryι ≫ g.hom =
          (ρ.mutationBoundaryIso b hOpp c hΦreg).hom ≫ (targetTail(k)).2.boundaryι := by
  have := isIntegral_internalBlowupTower b s d hΦreg
  have := isModification_internalBlowupTower_toBase b s d hΦreg
  obtain ⟨k, hk₀, hk₁, hk, e, he, hb, hr'⟩ :=
    ρ.exists_ordered_pivot_factorization_of_resolves b c s d hOpp r hr
  obtain ⟨g, hg, hgb⟩ := ρ.exists_isLift_mutation_alongBoundary b hOpp c
    (fun a ↦ s (Fin.succAbove k a)) (fun a ↦ d (Fin.succAbove k a)) hΦreg
  refine ⟨k, hk₀, hk₁, hk, e, g, hg, he, hb, ?_, hgb⟩
  rw [hg.hom_toBase_assoc, hr']

end TauCeti.Toric.Fan
