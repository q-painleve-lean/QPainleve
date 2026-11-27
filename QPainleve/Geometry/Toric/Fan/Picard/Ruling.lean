/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.FiniteFanScheme
public import QPainleve.Geometry.Toric.Fan.Ruling.Basic

import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import TauCeti.AlgebraicGeometry.LineBundle.ProjectiveLine
import TauCeti.AlgebraicGeometry.RationalPoint.IdealSheaf
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Section

/-!
# Divisors of character ruling fibers

The inverse image of a rational point under a nonconstant toric character ruling is
effective Cartier. At either coordinate point the Weil multiplicities are the
positive parts of the character pairings for that chart. Consequently the class of every rational
fiber is the class of that ray divisor. This is the fiber class used in the elementary
transformation of Gross, Hacking and Keel, *Birational geometry of cluster algebras*,
proof of Theorem 5.6.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme (ord_functionFieldMap)
open TauCeti.AlgebraicGeometry.Scheme.CartierDivisor

namespace TauCeti.Toric.Fan

variable (K : Type) [Field K] {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i) [Nonempty Φ.cones] (m : N →+ ℤ)
  (h : ∀ σ : Φ.cones, (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter m x) ∨
    ∀ x ∈ σ.val, Φ.lattice.realCharacter m x ≤ 0)
  (hm : m ≠ 0)

local notation "𝒳" => Φ.finiteFanScheme K
local notation "f" => Φ.characterRuling K m h
local notation "p₀" => projectiveLine.polynomialPoint K (RingHom.id K) 0 0

variable (p : Spec (.of K) ⟶ projectiveLine K)
  (hp : p ≫ (projectiveLine K ↘ Spec (.of K)) = 𝟙 _)

include hm hp in
/-- A rational fiber of a nonconstant character ruling is effective Cartier. -/
theorem isEffectiveCartier_characterRuling_fiber : (p.ker.comap f).IsEffectiveCartier := by
  have := Φ.isDominant_characterRuling K m h hm
  have hker := Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension p hp
  exact hker.isEffectiveCartier.comap_of_isDominant f

section CoordinateFiber

variable (k : Fin 2)

local notation "m[" k "]" => ite (k = (0 : Fin 2)) m (-m)
local notation "p[" k "]" => projectiveLine.polynomialPoint K (RingHom.id K) k 0
local notation "pointOver[" k "]" =>
  Eq.trans (projectiveLine.polynomialPoint_over K (RingHom.id K) k (0 : K))
    (Spec.map_id (CommRingCat.of K))

local notation "D[" k "]" => (Φ.isEffectiveCartier_characterRuling_fiber K m h hm p[k] pointOver[k])
local notation "I[" k "]" => Scheme.IdealSheafData.comap (Scheme.Hom.ker p[k]) f

private theorem coordinateCharacter_rev : m[k.rev] = -m[k] := by
  fin_cases k <;> simp

omit [Nonempty Φ.cones] in
include h in
private theorem nonneg_or_nonpos_coordinateCharacter (σ : Φ.cones) :
    (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter m[k] x) ∨
      ∀ x ∈ σ.val, Φ.lattice.realCharacter m[k] x ≤ 0 := by
  fin_cases k
  · simpa using h σ
  · rcases h σ with hpos | hneg
    · right
      intro x hx
      simpa using neg_nonpos.mpr (hpos x hx)
    · left
      intro x hx
      simpa using neg_nonneg.mpr (hneg x hx)

omit [Nonempty Φ.cones] in
private theorem notMem_support_coordinateFiber_of_mem_range_opposite_chart
    {x : 𝒳} (hx : f x ∈ Set.range (projectiveLine.polynomialChartι K k.rev)) :
    x ∉ I[k].support := by
  have : IsClosedImmersion p[k] := p[k].isClosedImmersion_of_comp_eq_id pointOver[k]
  rw [Scheme.IdealSheafData.support_comap]
  -- The support of the pulled-back ideal is the inverse image of the point.
  change f x ∉ (p[k].ker.support : Set (projectiveLine K))
  rw [Scheme.Hom.support_ker, p[k].isClosedEmbedding.isClosed_range.closure_eq]
  rintro ⟨z, hz⟩
  rw [← hz, projectiveLine.polynomialPoint_def, Scheme.Hom.comp_apply] at hx
  rw [projectiveLine.polynomialChartι_mem_range_iff] at hx
  -- Evaluation at the zero point sends the affine coordinate into every prime.
  change Polynomial.X ∉ z.asIdeal.comap (Polynomial.aeval (0 : K)).toRingHom at hx
  simp [Ideal.mem_comap] at hx

private theorem coeff_toWeilDivisor_coordinateFiber_of_nonneg_chart
    (σ : Φ.cones) (hσ : m[k] ∈ dualSemigroup Φ.lattice σ.val)
    (x : CodimensionOnePoint 𝒳) (hx : x.val ∈ Set.range (Φ.affineChartι K σ)) :
    WeilDivisor.coeff D[k].toCartierDivisor.toWeilDivisor x =
      (𝒳).ord (Φ.functionFieldCharacter K (ofAdd m[k])) x := by
  let j := Φ.affineChartι K σ
  obtain ⟨y, rfl⟩ := (CodimensionOnePoint.mem_range_mapOfIsOpenImmersion j).2 hx
  let a : dualSemigroup Φ.lattice σ.val := ⟨m[k], hσ⟩
  let b : Γ(affineChart K Φ.lattice σ, ⊤) :=
    (Scheme.ΓSpecIso (.of (affineChartRing K Φ.lattice σ.val))).inv
      (AddMonoidAlgebra.single a 1)
  have hlocal : I[k].comap j = Scheme.IdealSheafData.ofIdealTop (Ideal.span {b}) := by
    rw [← Scheme.IdealSheafData.comap_comp]
    simpa only [map_zero, sub_zero, Ideal.map_span, Set.image_singleton, j, b, a] using
      Φ.comap_ker_characterRuling_polynomialPoint K m h σ k hσ 0
  have : IsLocallyNoetherian (affineChart K Φ.lattice σ) := isLocallyNoetherian_of_isOpenImmersion j
  rw [D[k].coeff_toWeilDivisor_eq_ord_of_comap_eq_span_singleton j y b hlocal,
    CodimensionOnePoint.coe_mapOfIsOpenImmersion, ← ord_functionFieldMap j,
    Φ.functionFieldMap_affineChartι_character K σ a]
  rfl

private theorem coeff_toWeilDivisor_coordinateFiber_ray (hΦ : Φ.IsRegular) (ρ : Φ.Ray) :
    WeilDivisor.coeff D[k].toCartierDivisor.toWeilDivisor (Φ.rayBoundaryChartPoint (R := K) hΦ ρ) =
      max (m[k] ρ.primitiveGenerator) 0 := by
  have hx := (Φ.rayBoundaryChartPoint_mem_range_affineChartι_iff (R := K) hΦ ρ ρ.toCone).2 le_rfl
  rcases nonneg_or_nonpos_coordinateCharacter Φ m h k ρ.toCone with hpos | hneg
  · rw [coeff_toWeilDivisor_coordinateFiber_of_nonneg_chart K Φ m h hm k ρ.toCone
      ((mem_dualSemigroup Φ.lattice _).2 hpos) _ hx, Φ.ord_rayBoundaryChartPoint_character K hΦ]
    refine (max_eq_left ?_).symm
    exact_mod_cast (Φ.lattice.realCharacter_apply m[k] _ ▸ hpos _ ρ.primitiveGenerator_mem)
  · have hmem : m[k.rev] ∈
        dualSemigroup Φ.lattice ρ.toCone.val := by
      apply (mem_dualSemigroup Φ.lattice _).2
      intro x hx
      rw [coordinateCharacter_rev m k]
      simpa using hneg x hx
    have ht : f (Φ.rayBoundaryChartPoint (R := K) hΦ ρ).val ∈
        Set.range (projectiveLine.polynomialChartι K k.rev) := by
      obtain ⟨y, hy⟩ := hx
      rw [← hy, ← Scheme.Hom.comp_apply, Φ.affineToricChartι_comp_characterRuling K m h
        ρ.toCone k.rev hmem, Scheme.Hom.comp_apply]
      exact Set.mem_range_self _
    rw [(D[k].coeff_toWeilDivisor_eq_zero_iff _).mpr
      (notMem_support_coordinateFiber_of_mem_range_opposite_chart K Φ m h k ht)]
    refine (max_eq_right ?_).symm
    exact_mod_cast (Φ.lattice.realCharacter_apply m[k] _ ▸ hneg _ ρ.primitiveGenerator_mem)

/-- At the origin of either polynomial chart of the base, the fiber has
multiplicities given by the positive part of the corresponding signed character
on the primitive ray generators. -/
theorem toWeilDivisor_characterRuling_coordinateFiber (hΦ : Φ.IsRegular) :
    D[k].toCartierDivisor.toWeilDivisor =
      Φ.rayChartDivisorToWeilDivisor K hΦ (fun ρ ↦ max (m[k] ρ.primitiveGenerator) 0) := by
  apply WeilDivisor.ext
  intro x
  by_cases hx : x ∈ Set.range (Φ.rayBoundaryChartPoint (R := K) hΦ)
  · obtain ⟨ρ, rfl⟩ := hx
    rw [Φ.coeff_rayChartDivisorToWeilDivisor K,
      coeff_toWeilDivisor_coordinateFiber_ray K Φ m h hm k]
  · rw [Φ.coeff_rayChartDivisorToWeilDivisor_of_notMem_range K hΦ _ hx]
    let σ : Φ.cones :=
      ⟨⊥, Φ.bot_mem (Nonempty.some (inferInstance : Nonempty Φ.cones)).property⟩
    have hx' : x.val ∈ Set.range (Φ.affineChartι K σ) := by
      by_contra hnot
      exact hx (by rwa [Φ.range_rayBoundaryChartPoint (R := K) hΦ σ.property])
    have hσ : m[k] ∈ dualSemigroup Φ.lattice σ.val := by simp [σ]
    rw [coeff_toWeilDivisor_coordinateFiber_of_nonneg_chart K Φ m h hm k σ hσ x hx',
      Φ.ord_functionFieldCharacter_eq_zero_of_mem_range_zeroChart K m[k] hx']

end CoordinateFiber

local notation "zeroPoint_over" =>
  Eq.trans (projectiveLine.polynomialPoint_over K (RingHom.id K) 0 (0 : K))
    (Spec.map_id (CommRingCat.of K))

local notation "D₀" => (Φ.isEffectiveCartier_characterRuling_fiber K m h hm p₀ zeroPoint_over)

/-- The class of any rational fiber of the ruling is represented by the ray divisor whose
coefficients are the positive parts of the character evaluations. -/
theorem toLineBundleClass_characterRuling_fiber (hΦ : Φ.IsRegular) :
    let hI := Φ.isEffectiveCartier_characterRuling_fiber K m h hm p hp
    Additive.ofMul hI.toCartierDivisor.toLineBundleClass =
      Φ.rayChartDivisorToPicard K hΦ (fun ρ ↦ max (m ρ.primitiveGenerator) 0) := by
  dsimp only
  let h₁ :=
    (Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension p hp).isEffectiveCartier
  let h₀ :=
    (Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension p₀
      zeroPoint_over).isEffectiveCartier
  have heq : LineBundleClass.mk h₁.toInvertibleSheaf =
      LineBundleClass.mk h₀.toInvertibleSheaf := by
    apply Additive.ofMul.injective
    apply (projectiveLine.picardDegreeEquiv K).injective
    simp only [projectiveLine.picardDegreeEquiv_apply, toMul_ofMul,
      LineBundleClass.eulerDegree_mk]
    exact (p.eulerDegree_ker_of_smooth hp).trans
      ((p₀).eulerDegree_ker_of_smooth zeroPoint_over).symm
  have hc := congrArg (LineBundleClass.pullback f) heq
  rw [h₁.pullback_mk_toInvertibleSheaf (Φ.isEffectiveCartier_characterRuling_fiber K m h hm p hp),
    h₀.pullback_mk_toInvertibleSheaf (D₀)] at hc
  have := Φ.uniqueFactorizationMonoid_stalk_finiteFanScheme (R := K) hΦ
  have hzero := Φ.toWeilDivisor_characterRuling_coordinateFiber K m h hm 0 hΦ
  simp only [ite_true] at hzero
  rw [Φ.rayChartDivisorToPicard_def K, ← hzero, weilToLineBundleClassHom_toWeilDivisor]
  rw [Scheme.IdealSheafData.IsEffectiveCartier.toLineBundleClass_toCartierDivisor,
    Scheme.IdealSheafData.IsEffectiveCartier.toLineBundleClass_toCartierDivisor, hc]

end TauCeti.Toric.Fan
