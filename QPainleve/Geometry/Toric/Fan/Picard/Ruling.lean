/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Presentation
public import QPainleve.Geometry.Toric.Fan.Ruling

import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import TauCeti.AlgebraicGeometry.LineBundle.ProjectiveLine
import TauCeti.AlgebraicGeometry.RationalPoint.IdealSheaf
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Section

/-!
# Divisors of character ruling fibers

The inverse image of a rational point under a nonconstant toric character ruling is
effective Cartier. The fiber over zero has Weil multiplicity given by the positive
part of the character pairing on each ray. Consequently the class of every rational
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

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i) [Nonempty Φ.cones] (m : N →+ ℤ)
  (h : ∀ σ : Φ.cones, (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter m x) ∨
    ∀ x ∈ σ.val, Φ.lattice.realCharacter m x ≤ 0)
  (hm : m ≠ 0)

local notation "𝒳" => Φ.algebraicRealization
local notation "f" => Φ.characterRuling m h
local notation "p₀" => projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) 0 0

variable (p : Spec (.of ℂ) ⟶ projectiveLine ℂ)
  (hp : p ≫ (projectiveLine ℂ ↘ Spec (.of ℂ)) = 𝟙 _)

include hm hp in
/-- A rational fiber of a nonconstant character ruling is effective Cartier. -/
theorem isEffectiveCartier_characterRuling_fiber : (p.ker.comap f).IsEffectiveCartier := by
  have := Φ.isDominant_characterRuling m h hm
  have hker := Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension p hp
  exact hker.isEffectiveCartier.comap_of_isDominant f

local notation "zeroPoint_over" =>
  Eq.trans (projectiveLine.polynomialPoint_over ℂ (RingHom.id ℂ) 0 (0 : ℂ))
    (Spec.map_id (CommRingCat.of ℂ))

local notation "D₀" => (Φ.isEffectiveCartier_characterRuling_fiber m h hm p₀ zeroPoint_over)
local notation "I₀" => Scheme.IdealSheafData.comap (Scheme.Hom.ker p₀) f

omit [Nonempty Φ.cones] in
private theorem notMem_support_zeroFiber_of_mem_range_chart_one
    {x : 𝒳} (hx : f x ∈ Set.range (projectiveLine.polynomialChartι ℂ 1)) :
    x ∉ (I₀).support := by
  have : IsClosedImmersion p₀ := (p₀).isClosedImmersion_of_comp_eq_id zeroPoint_over
  rw [Scheme.IdealSheafData.support_comap]
  -- The support of the pulled-back ideal is the inverse image of the point.
  change f x ∉ ((p₀).ker.support : Set (projectiveLine ℂ))
  rw [Scheme.Hom.support_ker, (p₀).isClosedEmbedding.isClosed_range.closure_eq]
  rintro ⟨z, hz⟩
  rw [← hz, projectiveLine.polynomialPoint_def, Scheme.Hom.comp_apply] at hx
  have hrev : (0 : Fin 2).rev = 1 := by decide
  rw [← hrev, projectiveLine.polynomialChartι_mem_range_iff] at hx
  -- Evaluation at the zero point sends the affine coordinate into every prime.
  change Polynomial.X ∉ z.asIdeal.comap (Polynomial.aeval (0 : ℂ)).toRingHom at hx
  simp [Ideal.mem_comap] at hx

private theorem coeff_toWeilDivisor_zeroFiber_of_nonneg_chart
    (σ : Φ.cones) (hσ : m ∈ dualSemigroup Φ.lattice σ.val)
    (x : CodimensionOnePoint 𝒳) (hx : x.val ∈ Set.range (Φ.affineToricChartι σ)) :
    WeilDivisor.coeff (D₀).toCartierDivisor.toWeilDivisor x =
      (𝒳).ord (Φ.character (ofAdd m)) x := by
  let j := Φ.affineToricChartι σ
  obtain ⟨y, rfl⟩ := (CodimensionOnePoint.mem_range_mapOfIsOpenImmersion j).2 hx
  let a : dualSemigroup Φ.lattice σ.val := ⟨m, hσ⟩
  let b : Γ(Φ.affineToricChart σ, ⊤) :=
    (Scheme.ΓSpecIso (.of (affineCoordinateRing Φ.lattice σ.val))).inv
      (MonoidAlgebra.of ℂ _ (ofAdd a))
  have hlocal : (I₀).comap j = Scheme.IdealSheafData.ofIdealTop (Ideal.span {b}) := by
    rw [← Scheme.IdealSheafData.comap_comp]
    simpa only [ite_true, map_zero, sub_zero, Ideal.map_span, Set.image_singleton, j, b, a] using
      Φ.comap_ker_characterRuling_polynomialPoint m h σ 0 (by simpa only [ite_true] using hσ) 0
  have : IsLocallyNoetherian (Φ.affineToricChart σ) := isLocallyNoetherian_of_isOpenImmersion j
  rw [(D₀).coeff_toWeilDivisor_eq_ord_of_comap_eq_span_singleton j y b hlocal,
    CodimensionOnePoint.coe_mapOfIsOpenImmersion, ← ord_functionFieldMap j,
    Φ.functionFieldMap_affineToricChartι_character σ a]
  rfl

private theorem coeff_toWeilDivisor_zeroFiber_ray (hΦ : Φ.IsRegular) (ρ : Φ.Ray) :
    WeilDivisor.coeff (D₀).toCartierDivisor.toWeilDivisor (Φ.rayBoundaryPoint hΦ ρ) =
      max (m ρ.primitiveGenerator) 0 := by
  have hx := (Φ.rayBoundaryPoint_mem_range_affineToricChartι_iff hΦ ρ ρ.toCone).2 le_rfl
  rcases h ρ.toCone with hpos | hneg
  · rw [coeff_toWeilDivisor_zeroFiber_of_nonneg_chart Φ m h hm ρ.toCone
      ((mem_dualSemigroup Φ.lattice _).2 hpos) _ hx, Φ.ord_rayBoundaryPoint_character hΦ]
    refine (max_eq_left ?_).symm
    exact_mod_cast (Φ.lattice.realCharacter_apply m _ ▸ hpos _ ρ.primitiveGenerator_mem)
  · have hmem : (if (1 : Fin 2) = 0 then m else -m) ∈
        dualSemigroup Φ.lattice ρ.toCone.val := by
      apply (mem_dualSemigroup Φ.lattice _).2
      intro x hx
      simpa using hneg x hx
    have ht : f (Φ.rayBoundaryPoint hΦ ρ).val ∈
        Set.range (projectiveLine.polynomialChartι ℂ 1) := by
      obtain ⟨y, hy⟩ := hx
      rw [← hy, ← Scheme.Hom.comp_apply, Φ.affineToricChartι_comp_characterRuling m h
        ρ.toCone 1 hmem, Scheme.Hom.comp_apply]
      exact Set.mem_range_self _
    rw [((D₀).coeff_toWeilDivisor_eq_zero_iff _).mpr
      (notMem_support_zeroFiber_of_mem_range_chart_one Φ m h ht)]
    refine (max_eq_right ?_).symm
    exact_mod_cast (Φ.lattice.realCharacter_apply m _ ▸ hneg _ ρ.primitiveGenerator_mem)

/-- In the fiber over zero, the multiplicity of a ray is the positive part of the
character evaluation on its primitive generator. There are no other components. -/
theorem toWeilDivisor_characterRuling_zeroFiber (hΦ : Φ.IsRegular) :
    (D₀).toCartierDivisor.toWeilDivisor =
      Φ.rayDivisorToWeilDivisor hΦ (fun ρ ↦ max (m ρ.primitiveGenerator) 0) := by
  apply WeilDivisor.ext
  intro x
  by_cases hx : x ∈ Set.range (Φ.rayBoundaryPoint hΦ)
  · obtain ⟨ρ, rfl⟩ := hx
    rw [Φ.coeff_rayDivisorToWeilDivisor, coeff_toWeilDivisor_zeroFiber_ray Φ m h hm]
  · rw [Φ.coeff_rayDivisorToWeilDivisor_of_notMem_range hΦ _ hx]
    let j := Φ.denseTorusι inferInstance
    have hx' : x.val ∈ Set.range j := by
      by_contra hnot
      exact hx (by rwa [Φ.range_rayBoundaryPoint hΦ inferInstance])
    let σ : Φ.cones :=
      ⟨⊥, Φ.bot_mem (Nonempty.some (inferInstance : Nonempty Φ.cones)).property⟩
    have hσ : m ∈ dualSemigroup Φ.lattice σ.val := by simp [σ]
    have hx'' : x.val ∈ Set.range (Φ.affineToricChartι σ) := by
      simpa only [j, Φ.denseTorusι_eq_affineToricChartι inferInstance σ.property] using hx'
    rw [coeff_toWeilDivisor_zeroFiber_of_nonneg_chart Φ m h hm σ hσ x hx'',
      Φ.ord_character_eq_zero_of_mem_range_denseTorusι m hx']

/-- The class of any rational fiber of the ruling is represented by the ray divisor whose
coefficients are the positive parts of the character evaluations. -/
theorem toLineBundleClass_characterRuling_fiber (hΦ : Φ.IsRegular) :
    let hI := Φ.isEffectiveCartier_characterRuling_fiber m h hm p hp
    Additive.ofMul hI.toCartierDivisor.toLineBundleClass =
      Φ.rayDivisorToPicard hΦ (fun ρ ↦ max (m ρ.primitiveGenerator) 0) := by
  dsimp only
  let h₁ :=
    (Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension p hp).isEffectiveCartier
  let h₀ :=
    (Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension p₀
      zeroPoint_over).isEffectiveCartier
  have heq : LineBundleClass.mk h₁.toInvertibleSheaf =
      LineBundleClass.mk h₀.toInvertibleSheaf := by
    apply Additive.ofMul.injective
    apply (projectiveLine.picardDegreeEquiv ℂ).injective
    simp only [projectiveLine.picardDegreeEquiv_apply, toMul_ofMul,
      LineBundleClass.eulerDegree_mk]
    exact (p.eulerDegree_ker_of_smooth hp).trans
      ((p₀).eulerDegree_ker_of_smooth zeroPoint_over).symm
  have hc := congrArg (LineBundleClass.pullback f) heq
  rw [h₁.pullback_mk_toInvertibleSheaf (Φ.isEffectiveCartier_characterRuling_fiber m h hm p hp),
    h₀.pullback_mk_toInvertibleSheaf (D₀)] at hc
  have := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  rw [Φ.rayDivisorToPicard_def, ← toWeilDivisor_characterRuling_zeroFiber Φ m h hm,
    weilToLineBundleClassHom_toWeilDivisor]
  rw [Scheme.IdealSheafData.IsEffectiveCartier.toLineBundleClass_toCartierDivisor,
    Scheme.IdealSheafData.IsEffectiveCartier.toLineBundleClass_toCartierDivisor, hc]

end TauCeti.Toric.Fan
