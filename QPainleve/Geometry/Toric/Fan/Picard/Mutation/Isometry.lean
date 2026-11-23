/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import QPainleve.Geometry.Toric.Fan.Boundary.SelfIntersection
public import QPainleve.Geometry.Toric.Fan.Picard.Mutation.Basic
public import QPainleve.Geometry.Toric.Fan.Smooth
public import TauCeti.LinearAlgebra.BilinearForm.Prod

import Mathlib.LinearAlgebra.Basis.Prod

/-!
# The intersection isometry of toric mutation

The two ruling sections change self-intersection by `-1` and `+1` under the fan shear.
The remaining self-intersections and all intersections of distinct ray divisors agree.
Together with the fiber class of the ruling, these identities show that the marked Picard
equivalence preserves the entire intersection form, including the total exceptional classes.

The generator formulas describe the elementary transformation in §3.1 of
[Gross, Hacking and Keel, *Birational geometry of cluster algebras*][GHK].
The intersection calculation uses the toric wall relation
(Fulton, *Introduction to Toric Varieties*, §5.1).

[GHK]: https://arxiv.org/html/1309.2573v2#S3.SS1
-/

public noncomputable section

open AlgebraicGeometry LinearMap PointedCone
open TauCeti.AlgebraicGeometry (LineBundleClass)
open TauCeti.AlgebraicGeometry.Chow

namespace TauCeti.Toric.Fan

universe u

variable {N : Type} {V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Module.Basis (Fin 2) ℤ N)
  (p : Φ.Ray) (hop : hull ℝ {i (-p.primitiveGenerator)} ∈ Φ.cones)

local notation "v" => Ray.primitiveGenerator p
local notation "q" => Ray.ofPrimitiveGenerator p.isPrimitiveGenerator.isPrimitive.neg hop
local notation "hv" => Ray.primitiveGenerator_ne_zero p
local notation "hp" => Ray.hull_primitiveGenerator_mem p
local notation "Ψ" => Φ.mutationFan b hv hp hop
local notation "r" => Φ.mutationFanRayEquiv b hv hp hop
local notation "c" => Φ.mutationFanConeEquiv b hv hp hop
local notation "m" => (-b.detDualEquiv v)
local notation "f" => (fun ρ : Φ.Ray ↦ max (m ρ.primitiveGenerator) 0)

private theorem mutationCharacter_ne_zero_iff (ρ : Φ.Ray) :
    m ρ.primitiveGenerator ≠ 0 ↔ ρ ≠ p ∧ ρ ≠ q := by
  simp only [LinearMap.neg_apply, neg_ne_zero]
  constructor
  · intro h
    exact ⟨fun e ↦ h (by rw [e, b.detDualEquiv_self]),
      fun e ↦ h (by
        rw [e, Ray.primitiveGenerator_ofPrimitiveGenerator, map_neg,
          b.detDualEquiv_self, neg_zero])⟩
  · rintro ⟨h₁, h₂⟩ h
    rcases ρ.eq_or_eq_neg_of_detCharacter_eq_zero b p.isPrimitiveGenerator.isPrimitive h with
      he | he
    · exact h₁ (Ray.primitiveGenerator_injective he.symm)
    · exact h₂ (Ray.primitiveGenerator_injective (by simpa using congrArg Neg.neg he.symm))

private theorem pivot_ne_opposite : p ≠ q := by
  intro h
  have he := congrArg Ray.primitiveGenerator h
  simp only [Ray.primitiveGenerator_ofPrimitiveGenerator] at he
  obtain ⟨l, hl⟩ := isPrimitive_def.mp p.isPrimitiveGenerator.isPrimitive
  have hl' := congrArg l he
  rw [map_neg, hl] at hl'
  omega

private theorem mutationRayEquiv_generator (ρ : Φ.Ray) :
    (r ρ).primitiveGenerator = ρ.primitiveGenerator + f ρ • v := by
  have hm : m ρ.primitiveGenerator = b.det ![ρ.primitiveGenerator, v] := by
    rw [LinearMap.neg_apply, ← b.detDualEquiv_swap ρ.primitiveGenerator v,
      Module.Basis.detDualEquiv_apply]
  simp only [hm, mutationFanRayEquiv_primitiveGenerator]

private theorem mutationRayEquiv_le_cone (ρ : Φ.Ray) (σ : Φ.cones) :
    (r ρ).toCone ≤ c σ ↔ ρ.toCone ≤ σ := by
  rw [mutationFanRayEquiv_toCone, OrderIso.le_iff_le]

private theorem mutationRayEquiv_commonCone (ρ τ : Φ.Ray) :
    (∃ σ : (Ψ).cones, (r ρ).toCone ≤ σ ∧ (r τ).toCone ≤ σ) ↔
      ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ τ.toCone ≤ σ := by
  constructor
  · rintro ⟨σ, hρ, hτ⟩
    obtain ⟨σ, rfl⟩ := (c).surjective σ
    exact ⟨σ, (mutationRayEquiv_le_cone b p hop ρ σ).mp hρ,
      (mutationRayEquiv_le_cone b p hop τ σ).mp hτ⟩
  · rintro ⟨σ, hρ, hτ⟩
    exact ⟨c σ, (mutationRayEquiv_le_cone b p hop ρ σ).mpr hρ,
      (mutationRayEquiv_le_cone b p hop τ σ).mpr hτ⟩

include hop in
private theorem detCharacter_same_sign_of_commonCone {ρ τ : Φ.Ray}
    (h : ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ τ.toCone ≤ σ) :
    (0 ≤ m ρ.primitiveGenerator ∧ 0 ≤ m τ.primitiveGenerator) ∨
      (m ρ.primitiveGenerator ≤ 0 ∧ m τ.primitiveGenerator ≤ 0) := by
  obtain ⟨σ, hρ, hτ⟩ := h
  have hp' := hρ ρ.primitiveGenerator_mem
  have hq' := hτ τ.primitiveGenerator_mem
  simp only [LinearMap.neg_apply, neg_nonpos, neg_nonneg]
  have castEval (x : N) :
      Φ.lattice.realCharacter (b.detDualEquiv v).toAddMonoidHom (i x) =
        ((b.detDualEquiv v x : ℤ) : ℝ) :=
    Φ.lattice.realCharacter_apply _ _
  rcases Φ.detCharacter_nonneg_or_nonpos b hv hp hop σ with hs | hs
  · exact Or.inr ⟨by exact_mod_cast (castEval _ ▸ hs _ hp'),
      by exact_mod_cast (castEval _ ▸ hs _ hq')⟩
  · exact Or.inl ⟨by exact_mod_cast (castEval _ ▸ hs _ hp'),
      by exact_mod_cast (castEval _ ▸ hs _ hq')⟩

variable (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  [hproj : Φ.algebraicRealization.IsProjectiveOver ℂ]

local notation "hΨ" => Iff.mpr (Φ.isRegular_mutationFan_iff b hv hp hop) hΦ
local notation "d" => Φ.rayBoundarySelfIntersection hΦ
local notation "d'" => (Fan.rayBoundarySelfIntersection hΨ)

omit hproj in
private theorem mutationWallRelation (hc : Φ.IsComplete)
    [Φ.algebraicRealization.IsProjectiveOver ℂ]
    [hTarget : @Scheme.IsProjectiveOver ℂ _ (Fan.algebraicRealization Ψ)
      (Fan.algebraicRealizationOver Ψ)] (ρ : Φ.Ray) :
    ∃ prev next : Φ.Ray,
      b.detDualEquiv ρ.primitiveGenerator prev.primitiveGenerator = -1 ∧
      b.detDualEquiv ρ.primitiveGenerator next.primitiveGenerator = 1 ∧
      (∀ τ : Φ.Ray, (ρ ≠ τ ∧ ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ τ.toCone ≤ σ) ↔
        τ = prev ∨ τ = next) ∧
      prev.primitiveGenerator + d ρ • ρ.primitiveGenerator + next.primitiveGenerator = 0 ∧
      (d' (r ρ) - d ρ) • ρ.primitiveGenerator +
        (f prev + d' (r ρ) * f ρ + f next) • v = 0 := by
  classical
  let := Fintype.ofFinite (Ψ).Ray
  obtain ⟨prev, next, hprev, hnext, hneigh, hwall⟩ :=
    Φ.exists_rayBoundaryPoint_selfIntersection_relation b hΦ hc ρ
  have hne : prev ≠ next := by
    intro h
    rw [h, hnext] at hprev
    omega
  have hfilter :
      Finset.univ.filter (fun τ : (Ψ).Ray ↦ (r ρ) ≠ τ ∧
        ∃ σ : (Ψ).cones, (r ρ).toCone ≤ σ ∧ τ.toCone ≤ σ) = {r prev, r next} := by
    ext τ
    obtain ⟨τ, rfl⟩ := (r).surjective τ
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Equiv.apply_eq_iff_eq, ne_eq, mutationRayEquiv_commonCone]
      using hneigh τ
  have hdim : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  have hwall' := @rayBoundaryPoint_selfIntersection_smul_add_sum_eq_zero _ _ _ _ _ _
    Ψ hΨ hdim hTarget _ (r ρ)
  rw [hfilter, Finset.sum_pair ((r).injective.ne hne)] at hwall'
  simp only [← rayBoundarySelfIntersection_def] at hwall'
  rw [← rayBoundarySelfIntersection_def] at hwall
  refine ⟨prev, next, hprev, hnext, hneigh, hwall, ?_⟩
  calc
    _ = (d' (r ρ) • (r ρ).primitiveGenerator +
        ((r prev).primitiveGenerator + (r next).primitiveGenerator)) -
        (prev.primitiveGenerator + d ρ • ρ.primitiveGenerator + next.primitiveGenerator) := by
      simp only [mutationRayEquiv_generator, sub_smul, add_smul, smul_add, smul_smul]
      abel
    _ = 0 := by
      rw [hwall]
      simpa only [sub_zero] using hwall'

local notation "δ[" ρ "," τ "]" => (ite (ρ = τ) (1 : ℤ) 0)

omit hproj in
open Classical in
private theorem positiveCharacter_wall {prev ρ next : Φ.Ray}
    (hprev : b.detDualEquiv ρ.primitiveGenerator prev.primitiveGenerator = -1)
    (hnext : b.detDualEquiv ρ.primitiveGenerator next.primitiveGenerator = 1)
    (hcone₁ : ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ prev.toCone ≤ σ)
    (hcone₂ : ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ next.toCone ≤ σ)
    (hwall : prev.primitiveGenerator + d ρ • ρ.primitiveGenerator + next.primitiveGenerator = 0) :
    f prev + d ρ * f ρ + f next = δ[ρ,p] + δ[ρ,q] := by
  have hne := pivot_ne_opposite p hop
  have hzero : m v = 0 := by simp only [LinearMap.neg_apply, b.detDualEquiv_self, neg_zero]
  by_cases hρ : ρ = p
  · subst ρ
    simp only [LinearMap.neg_apply, hprev, hnext, b.detDualEquiv_self, ite_eq_right hne]
    norm_num
  by_cases hτ : ρ = q
  · have he : ρ.primitiveGenerator = -v := by simp [hτ]
    simp only [he, map_neg] at hprev hnext
    simp only [hprev, hnext, he, map_neg, hzero, neg_zero, ite_eq_left hτ, ite_eq_right hρ]
    norm_num
  have hm := (mutationCharacter_ne_zero_iff b p hop ρ).mpr ⟨hρ, hτ⟩
  rw [ite_eq_right hρ, ite_eq_right hτ, add_zero]
  have h₁ := detCharacter_same_sign_of_commonCone b p hop hcone₁
  have h₂ := detCharacter_same_sign_of_commonCone b p hop hcone₂
  rcases lt_or_gt_of_ne hm with hneg | hpos
  · have ha := (h₁.resolve_left fun h ↦ (not_le_of_gt hneg) h.1).2
    have hb := (h₂.resolve_left fun h ↦ (not_le_of_gt hneg) h.1).2
    simp only [max_eq_right ha, max_eq_right hb, max_eq_right hneg.le, mul_zero, add_zero]
  · have ha := (h₁.resolve_right fun h ↦ (not_le_of_gt hpos) h.1).2
    have hb := (h₂.resolve_right fun h ↦ (not_le_of_gt hpos) h.1).2
    simpa only [max_eq_left ha, max_eq_left hb, max_eq_left hpos.le, map_add, map_zsmul,
      Int.zsmul_eq_mul, map_zero] using congrArg m hwall

include hproj in
open Classical in
private theorem rayBoundarySelfIntersection_mutation (hc : Φ.IsComplete)
    [hTarget : @Scheme.IsProjectiveOver ℂ _ (Fan.algebraicRealization Ψ)
      (Fan.algebraicRealizationOver Ψ)] (ρ : Φ.Ray) :
    d' (r ρ) = d ρ - δ[ρ,p] + δ[ρ,q] := by
  obtain ⟨prev, next, hprev, hnext, hneigh, hwall, hshift⟩ :=
    mutationWallRelation b p hop hΦ hc (hTarget := hTarget) ρ
  have hsum := positiveCharacter_wall b p hop hΦ hprev hnext
    ((hneigh prev).mpr (Or.inl rfl)).2 ((hneigh next).mpr (Or.inr rfl)).2 hwall
  have hz : m v = 0 := by simp only [LinearMap.neg_apply, b.detDualEquiv_self, neg_zero]
  have inject (τ : Φ.Ray) := τ.isPrimitiveGenerator.isPrimitive.zsmul_left_injective
  have hne := pivot_ne_opposite p hop
  by_cases hρ : ρ = p
  · subst ρ
    simp only [hz, max_self, mul_zero, add_zero, ite_eq_right hne] at hsum hshift ⊢
    rw [hsum, ← add_smul] at hshift
    have h := (inject p) (hshift.trans (zero_smul ℤ v).symm)
    omega
  by_cases hτ : ρ = q
  · have he : ρ.primitiveGenerator = -v := by simp [hτ]
    simp only [he, map_neg, hz, neg_zero, max_self, mul_zero, add_zero,
      ite_eq_left hτ, ite_eq_right hρ] at hsum hshift ⊢
    rw [hsum, smul_neg, ← neg_smul, ← add_smul] at hshift
    have h := (inject p) (hshift.trans (zero_smul ℤ v).symm)
    omega
  have hm := (mutationCharacter_ne_zero_iff b p hop ρ).mpr ⟨hρ, hτ⟩
  have hd := congrArg m hshift
  simp only [map_add, map_zsmul, hz, smul_zero, add_zero, map_zero, Int.zsmul_eq_mul] at hd
  rcases mul_eq_zero.mp hd with h | h
  · simpa only [ite_eq_right hρ, ite_eq_right hτ, sub_zero, add_zero] using sub_eq_zero.mp h
  · exact (hm h).elim

local notation "Pic[" Ξ "]" => Additive (LineBundleClass (Fan.algebraicRealization Ξ))
local notation "A[" Ξ "," hΞ "," hProjective "]" =>
  (@intersectionBilinForm ℂ _ _ (Fan.algebraicRealization Ξ)
    (Fan.algebraicRealizationOver Ξ) hProjective _
    (Eq.mpr (congrArg (SmoothOfRelativeDimension 2) (Fan.algebraicRealization_over Ξ))
      (Eq.mp (congrArg
        (fun n ↦ SmoothOfRelativeDimension n (Fan.algebraicRealizationStructureMap Ξ))
        (Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)))
        (Fan.smoothOfRelativeDimension_algebraicRealizationStructureMap Ξ hΞ))))
local notation "D[" hΞ "," ρ "]" =>
  (Fan.rayDivisorToPicard _ hΞ (@Pi.single _ (fun _ ↦ ℤ) _ (Classical.decEq _) ρ 1))
local notation "F" => mutationFiberClass b p hΦ

omit hproj in
private theorem mutationFiberClass_eq_positiveCharacter [Nonempty Φ.cones] :
    F = Φ.rayDivisorToPicard hΦ f := by
  have he (x : N) : m x = b.det ![x, v] := by
    rw [LinearMap.neg_apply, ← b.detDualEquiv_swap x v, Module.Basis.detDualEquiv_apply]
  simp only [mutationFiberClass_eq, ← he]

include hc hproj in
open Classical in
private theorem intersection_mutationFiberClass_ray (ρ : Φ.Ray) :
    let : Nonempty Φ.cones := ⟨p.toCone⟩
    A[Φ,hΦ,hproj] D[hΦ,ρ] F = δ[ρ,p] + δ[ρ,q] := by
  let : Nonempty Φ.cones := ⟨p.toCone⟩
  obtain ⟨prev, next, hprev, hnext, hneigh, hwall⟩ :=
    Φ.exists_rayBoundaryPoint_selfIntersection_relation b hΦ hc ρ
  rw [← rayBoundarySelfIntersection_def] at hwall
  have hconePrev := ((hneigh prev).mpr (Or.inl rfl)).2
  have hconeNext := ((hneigh next).mpr (Or.inr rfl)).2
  have hprev' : b.detDualEquiv prev.primitiveGenerator ρ.primitiveGenerator = 1 := by
    rw [b.detDualEquiv_swap, hprev, neg_neg]
  let : SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ Spec (CommRingCat.of ℂ)) := by
    rw [Φ.algebraicRealization_over]
    simpa only [Module.finrank_eq_card_basis b, Fintype.card_fin] using
      Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  dsimp only
  rw [mutationFiberClass_eq_positiveCharacter,
    Φ.intersectionBilinForm_rayDivisorToPicard_single (decEq := Classical.decEq _) hΦ b hc f
      ⟨hprev', hconePrev.imp fun _ h ↦ h.symm⟩ ⟨hnext, hconeNext⟩]
  exact positiveCharacter_wall b p hop hΦ hprev hnext hconePrev hconeNext hwall

include hop hc hproj in
open Classical in
private theorem intersection_mutationFiberClass_self :
    let : Nonempty Φ.cones := ⟨p.toCone⟩
    A[Φ,hΦ,hproj] F F = 0 := by
  let : Nonempty Φ.cones := ⟨p.toCone⟩
  let := Fintype.ofFinite Φ.Ray
  have hsum : F = ∑ τ, f τ • D[hΦ,τ] := by
    rw [mutationFiberClass_eq_positiveCharacter, rayDivisorToPicard_apply]
    simp only [rayDivisorToPicard_single, one_smul]
  dsimp only
  -- Expand the first copy to pair each ray divisor with the unchanged fiber class.
  conv_lhs => arg 1; rw [hsum]
  rw [BilinForm.sum_left]
  apply Finset.sum_eq_zero
  intro τ _
  rw [BilinForm.smul_left, intersection_mutationFiberClass_ray b p hop hΦ hc]
  by_cases hp' : τ = p
  · subst τ
    simp [LinearMap.neg_apply, b.detDualEquiv_self]
  by_cases hq' : τ = q
  · subst τ
    simp only [Ray.primitiveGenerator_ofPrimitiveGenerator, map_neg, LinearMap.neg_apply,
      b.detDualEquiv_self, neg_zero, max_self, zero_mul]
  simp [hp', hq']

open Classical in
private theorem intersection_rayDivisor_mutation (hc : Φ.IsComplete)
    [hTarget : @Scheme.IsProjectiveOver ℂ _ (Fan.algebraicRealization Ψ)
      (Fan.algebraicRealizationOver Ψ)] (ρ τ : Φ.Ray) :
    let : Nonempty Φ.cones := ⟨p.toCone⟩
    let : Nonempty (Ψ).cones := ⟨(r p).toCone⟩
    A[Ψ,hΨ,hTarget] D[hΨ,r ρ] D[hΨ,r τ] =
      A[Φ,hΦ,hproj] D[hΦ,ρ] D[hΦ,τ] - δ[ρ,p] * δ[τ,p] + δ[ρ,q] * δ[τ,q] := by
  let : Nonempty Φ.cones := ⟨p.toCone⟩
  let : Nonempty (Ψ).cones := ⟨(r p).toCone⟩
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  let : SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ Spec (CommRingCat.of ℂ)) := by
    rw [Φ.algebraicRealization_over]
    exact hN ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let : SmoothOfRelativeDimension 2 ((Ψ).algebraicRealization ↘ Spec (CommRingCat.of ℂ)) := by
    rw [(Ψ).algebraicRealization_over]
    exact hN ▸ (Ψ).smoothOfRelativeDimension_algebraicRealizationStructureMap hΨ
  dsimp only
  rw [(Ψ).intersectionBilinForm_rayDivisorToPicard_single_single
      (decEq := Classical.decEq _) hΨ hN (r ρ) (r τ),
    Φ.intersectionBilinForm_rayDivisorToPicard_single_single (decEq := Classical.decEq _) hΦ hN ρ τ]
  by_cases h : ρ = τ
  · subst τ
    rw [ite_eq_left (rfl : (r ρ) = (r ρ)), ite_eq_left (rfl : ρ = ρ),
      rayBoundarySelfIntersection_mutation (hTarget := hTarget) b p hop hΦ hc]
    split_ifs <;> ring
  · rw [ite_eq_right ((r).injective.ne h), ite_eq_right h, mutationRayEquiv_commonCone]
    have hp' : δ[ρ,p] * δ[τ,p] = 0 := by split_ifs <;> simp_all
    have hq' : δ[ρ,q] * δ[τ,q] = 0 := by split_ifs <;> simp_all
    simp only [hp', hq', sub_zero, add_zero]

section Marking

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι → Φ.Ray) (k : ι)
  (hOpposite : hull ℝ {i (-(s k).primitiveGenerator)} ∈ Φ.cones)

local notation "pivot" => s k
local notation "opp" =>
  Ray.ofPrimitiveGenerator
    (IsPrimitive.neg (IsPrimitiveGenerator.isPrimitive (Ray.isPrimitiveGenerator (s k)))) hOpposite
local notation "hv₀" => Ray.primitiveGenerator_ne_zero (s k)
local notation "hp₀" => Ray.hull_primitiveGenerator_mem (s k)
local notation "Φ₁" => Φ.mutationFan b hv₀ hp₀ hOpposite
local notation "r₁" => Φ.mutationFanRayEquiv b hv₀ hp₀ hOpposite
local notation "h₁" => Iff.mpr (Φ.isRegular_mutationFan_iff b hv₀ hp₀ hOpposite) hΦ
local notation "F₀" => mutationFiberClass b (s k) hΦ
local notation "E(" j ")" => (@Pi.single ι (fun _ ↦ ℤ) _ _ j 1)
local notation "I" => mutationPicardEquiv b s k hOpposite hΦ
local notation "B[" Ξ "," hΞ "," hProjective "]" =>
  (LinearMap.BilinForm.prod A[Ξ,hΞ,hProjective]
    (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (ι → ℤ))))

omit hproj [Fintype ι] in
open Classical in
private theorem mutationPicardEquiv_ray (ρ : Φ.Ray) :
    let : Nonempty Φ.cones := ⟨(s k).toCone⟩
    let : Nonempty (Φ₁).cones := ⟨(r₁ (s k)).toCone⟩
    I (D[h₁,r₁ ρ], 0) =
      (D[hΦ,ρ] + δ[ρ,opp] • F₀, -(δ[ρ,pivot] + δ[ρ,opp]) • E(k)) := by
  let : Nonempty Φ.cones := ⟨(s k).toCone⟩
  let : Nonempty (Φ₁).cones := ⟨(r₁ (s k)).toCone⟩
  let := Classical.decEq Φ.Ray
  have h := mutationPicardEquiv_toric_single b s k hOpposite hΦ ρ
  have he : Equiv.decidableEq (Equiv.symm r₁) = Classical.decEq (Φ₁).Ray :=
    Subsingleton.elim _ _
  rw [he] at h
  dsimp only
  rw [h]
  congr 1
  · by_cases hx : ρ = opp
    · simp only [ite_eq_left hx, ite_eq_left hx.symm, one_smul]
    · simp only [ite_eq_right hx, ite_eq_right (Ne.symm hx), zero_smul]
  · have heq (τ : Φ.Ray) : (if τ = ρ then E(k) else 0) = (if ρ = τ then E(k) else 0) :=
      if_congr eq_comm rfl rfl
    simp only [heq, neg_smul, add_smul, ite_smul, one_smul, zero_smul]

omit [DecidableEq ι] in
private theorem markedForm_apply {Ξ : Fan i} [Nonempty Ξ.cones]
    [hProjective : Ξ.algebraicRealization.IsProjectiveOver ℂ] (hΞ : Ξ.IsRegular)
    (x y : Pic[Ξ] × (ι → ℤ)) :
    B[Ξ,hΞ,hProjective] x y = A[Ξ,hΞ,hProjective] x.1 y.1 - x.2 ⬝ᵥ y.2 := by
  simp [BilinForm.prod_apply, dotProductBilin_apply_apply, sub_eq_add_neg]

omit [DecidableEq ι] in
private theorem markedForm_comm {Ξ : Fan i} [Nonempty Ξ.cones]
    [hProjective : Ξ.algebraicRealization.IsProjectiveOver ℂ] (hΞ : Ξ.IsRegular)
    (x y : Pic[Ξ] × (ι → ℤ)) :
    B[Ξ,hΞ,hProjective] x y = B[Ξ,hΞ,hProjective] y x := by
  rw [markedForm_apply b hΞ x y, markedForm_apply b hΞ y x]
  simp only [intersectionBilinForm_apply]
  rw [classIntersectionNumber_comm x.1.toMul y.1.toMul, dotProduct_comm x.2 y.2]

open Classical in
private theorem mutationPicardEquiv_map_ray_pair (hc : Φ.IsComplete)
    [hTarget : @Scheme.IsProjectiveOver ℂ _ (Fan.algebraicRealization Φ₁)
      (Fan.algebraicRealizationOver Φ₁)] (ρ τ : Φ.Ray) :
    let : Nonempty Φ.cones := ⟨(s k).toCone⟩
    let : Nonempty (Φ₁).cones := ⟨(r₁ (s k)).toCone⟩
    B[Φ,hΦ,hproj] (I (D[h₁,r₁ ρ], 0)) (I (D[h₁,r₁ τ], 0)) =
      B[Φ₁,h₁,hTarget] (D[h₁,r₁ ρ], 0) (D[h₁,r₁ τ], 0) := by
  let : Nonempty Φ.cones := ⟨(s k).toCone⟩
  let : Nonempty (Φ₁).cones := ⟨(r₁ (s k)).toCone⟩
  dsimp only
  have hF (x : Φ.Ray) : A[Φ,hΦ,hproj] F₀ D[hΦ,x] = δ[x,pivot] + δ[x,opp] := by
    simpa only [intersectionBilinForm_apply, classIntersectionNumber_comm] using
      intersection_mutationFiberClass_ray b (s k) hOpposite hΦ hc x
  simp only [mutationPicardEquiv_ray,
    BilinForm.prod_apply, BilinForm.neg_apply, dotProductBilin_apply_apply,
    zero_dotProduct, neg_zero, add_zero, BilinForm.add_left, BilinForm.add_right,
    BilinForm.smul_left, BilinForm.smul_right, single_dotProduct, Pi.single_eq_same, mul_one, hF,
    intersection_mutationFiberClass_ray b (s k) hOpposite hΦ hc,
    intersection_mutationFiberClass_self b (s k) hOpposite hΦ hc,
    intersection_rayDivisor_mutation (hTarget := hTarget) b (s k) hOpposite hΦ hc]
  ring

open Classical in
private theorem mutationPicardEquiv_map_ray_exceptional (hc : Φ.IsComplete)
    [hTarget : @Scheme.IsProjectiveOver ℂ _ (Fan.algebraicRealization Φ₁)
      (Fan.algebraicRealizationOver Φ₁)] (ρ : Φ.Ray) (j : ι) :
    let : Nonempty Φ.cones := ⟨(s k).toCone⟩
    let : Nonempty (Φ₁).cones := ⟨(r₁ (s k)).toCone⟩
    B[Φ,hΦ,hproj] (I (D[h₁,r₁ ρ], 0)) (I (0, E(j))) =
      B[Φ₁,h₁,hTarget] (D[h₁,r₁ ρ], 0) (0, E(j)) := by
  let : Nonempty Φ.cones := ⟨(s k).toCone⟩
  let : Nonempty (Φ₁).cones := ⟨(r₁ (s k)).toCone⟩
  dsimp only
  rw [mutationPicardEquiv_ray]
  by_cases hj : j = k
  · subst j
    rw [mutationPicardEquiv_exceptional_pivot]
    simp only [BilinForm.prod_apply, BilinForm.neg_apply, dotProductBilin_apply_apply,
      BilinForm.add_left, BilinForm.smul_left, BilinForm.zero_right, zero_dotProduct,
      intersection_mutationFiberClass_ray b (s k) hOpposite hΦ hc,
      intersection_mutationFiberClass_self b (s k) hOpposite hΦ hc, dotProduct_neg,
      single_dotProduct, Pi.single_eq_same, mul_one]
    ring
  · rw [mutationPicardEquiv_exceptional_of_ne _ _ _ _ _ hj]
    simp only [BilinForm.prod_apply, BilinForm.neg_apply, dotProductBilin_apply_apply,
      BilinForm.zero_right, zero_dotProduct, smul_dotProduct, single_dotProduct,
      Pi.single_eq_of_ne (Ne.symm hj), one_mul, smul_zero, neg_zero, add_zero]

open Classical in
private theorem mutationPicardEquiv_map_exceptional_pair (hc : Φ.IsComplete)
    [hTarget : @Scheme.IsProjectiveOver ℂ _ (Fan.algebraicRealization Φ₁)
      (Fan.algebraicRealizationOver Φ₁)] (j l : ι) :
    let : Nonempty Φ.cones := ⟨(s k).toCone⟩
    let : Nonempty (Φ₁).cones := ⟨(r₁ (s k)).toCone⟩
    B[Φ,hΦ,hproj] (I (0, E(j))) (I (0, E(l))) = B[Φ₁,h₁,hTarget] (0, E(j)) (0, E(l)) := by
  let : Nonempty Φ.cones := ⟨(s k).toCone⟩
  let : Nonempty (Φ₁).cones := ⟨(r₁ (s k)).toCone⟩
  dsimp only
  by_cases hj : j = k <;> by_cases hl : l = k <;>
    simp [hj, hl, Ne.symm, markedForm_apply b hΦ,
      markedForm_apply (hProjective := hTarget) b h₁, dotProduct_single,
      intersection_mutationFiberClass_self b (s k) hOpposite hΦ hc, Pi.single_eq_of_ne]

/-- Toric mutation preserves the marked intersection form, the orthogonal sum of the toric
Picard pairing and the negative dot product on total exceptional coordinates. This includes
arbitrary repeated center labels on a ray. -/
def mutationPicardIsometry (hc : Φ.IsComplete)
    [hTarget : @Scheme.IsProjectiveOver ℂ _ (Fan.algebraicRealization Φ₁)
      (Fan.algebraicRealizationOver Φ₁)] :
    letI : Nonempty Φ.cones := ⟨(s k).toCone⟩
    letI : Nonempty (Φ₁).cones := ⟨(r₁ (s k)).toCone⟩
    B[Φ₁,h₁,hTarget].IsometryEquiv B[Φ,hΦ,hproj] := by
  letI : Nonempty Φ.cones := ⟨(s k).toCone⟩
  letI : Nonempty (Φ₁).cones := ⟨(r₁ (s k)).toCone⟩
  letI := Fintype.ofFinite (Φ₁).Ray
  letI := Classical.decEq (Φ₁).Ray
  refine { I with map_app' := ?_ }
  let π := ((Φ₁).rayDivisorToPicard h₁).toIntLinearMap.prodMap
    (LinearMap.id : (ι → ℤ) →ₗ[ℤ] (ι → ℤ))
  let β := (Pi.basisFun ℤ (Φ₁).Ray).prod (Pi.basisFun ℤ ι)
  have hπ : Function.Surjective π :=
    ((Φ₁).rayDivisorToPicard_surjective h₁).prodMap Function.surjective_id
  have hform : (B[Φ,hΦ,hproj]).comp ((I).toLinearMap.comp π) ((I).toLinearMap.comp π) =
      (B[Φ₁,h₁,hTarget]).comp π π := by
    apply BilinForm.ext_basis β
    intro a a'
    rcases a with ρ | j <;> rcases a' with τ | l <;>
      simp only [BilinForm.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, π, β,
        LinearMap.prodMap_apply, Module.Basis.prod_apply_inl_fst, Module.Basis.prod_apply_inl_snd,
        Module.Basis.prod_apply_inr_fst, Module.Basis.prod_apply_inr_snd, Pi.basisFun_apply,
        AddMonoidHom.coe_toIntLinearMap, LinearMap.id_apply, map_zero]
    · obtain ⟨ρ, rfl⟩ := (r₁).surjective ρ
      obtain ⟨τ, rfl⟩ := (r₁).surjective τ
      exact mutationPicardEquiv_map_ray_pair b hΦ s k hOpposite hc (hTarget := hTarget) ρ τ
    · obtain ⟨ρ, rfl⟩ := (r₁).surjective ρ
      exact mutationPicardEquiv_map_ray_exceptional b hΦ s k hOpposite hc (hTarget := hTarget) ρ l
    · obtain ⟨τ, rfl⟩ := (r₁).surjective τ
      rw [markedForm_comm b hΦ, markedForm_comm (hProjective := hTarget) b h₁]
      exact mutationPicardEquiv_map_ray_exceptional b hΦ s k hOpposite hc (hTarget := hTarget) τ j
    · exact mutationPicardEquiv_map_exceptional_pair b hΦ s k hOpposite hc (hTarget := hTarget) j l
  intro x y
  obtain ⟨x, rfl⟩ := hπ x
  obtain ⟨y, rfl⟩ := hπ y
  exact LinearMap.congr_fun (LinearMap.congr_fun hform x) y

/-- The intersection isometry has the original marked Picard mutation as its linear map. -/
@[simp]
theorem mutationPicardIsometry_toLinearEquiv (hc : Φ.IsComplete)
    [hTarget : @Scheme.IsProjectiveOver ℂ _ (Fan.algebraicRealization Φ₁)
      (Fan.algebraicRealizationOver Φ₁)] :
    (mutationPicardIsometry b hΦ s k hOpposite hc (hTarget := hTarget)).toLinearEquiv = I :=
  (rfl)

/-- On each marked class, the intersection isometry applies the Picard change of marking. -/
@[simp]
theorem mutationPicardIsometry_apply (hc : Φ.IsComplete)
    [hTarget : @Scheme.IsProjectiveOver ℂ _ (Fan.algebraicRealization Φ₁)
      (Fan.algebraicRealizationOver Φ₁)] (x : Pic[Φ₁] × (ι → ℤ)) :
    mutationPicardIsometry b hΦ s k hOpposite hc (hTarget := hTarget) x = I x :=
  (rfl)

end Marking

end TauCeti.Toric.Fan
