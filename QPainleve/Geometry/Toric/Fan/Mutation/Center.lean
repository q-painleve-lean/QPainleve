/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.InternalCenter
public import QPainleve.Geometry.Toric.Fan.Mutation.Complement
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange

/-!
# Transport of internal centers under toric mutation

Off the pivot fiber, toric mutation carries a binomial center to the center on the
sheared ray with parameter `d * c ^ max (det(u, v)) 0`. The comparison identifies the
ideal sheaves used to lift the elementary transformation through further internal
blowups. It uses the ray chart form of the elementary transformation in Gross,
Hacking and Keel, [*Birational geometry of cluster algebras*][GHK], §3.1 and the proof of
Theorem 5.6.

[GHK]: https://arxiv.org/html/1309.2573v2#S3.SS1
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Multiplicative
open AddMonoidAlgebra

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Module.Basis (Fin 2) ℤ N) (ρ : Φ.Ray)

local notation "u" => ρ.primitiveGenerator
local notation "rankTwo" => (Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2))
local notation "χ(" x ")" => LinearMap.toAddMonoidHom (b.detDualEquiv x)

local notation "S(" σ ")" => dualSemigroup Φ.lattice (Subtype.val σ)
local notation "R(" σ ")" => AddMonoidAlgebra ℂ (S(σ))

private abbrev centerEval (d : ℂˣ) : R(ρ.toCone) →ₐ[ℂ] ℂ :=
  (ρ.binomialCenterEval rankTwo (m := χ(u)) (b.detDualEquiv_self u)
    (ρ.surjective_detCharacter b) d).comp
      (toMultiplicativeAlgEquiv ℂ ℂ (S(ρ.toCone))).toAlgHom

private theorem centerEval_single_eq_zero (d : ℂˣ) (a : S(ρ.toCone)) (r : ℂ)
    (ha : (a : N →+ ℤ) u ≠ 0) :
    centerEval b ρ d (single a r) = 0 := by
  simpa only [centerEval, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    toMultiplicativeAlgEquiv_single] using
    ρ.binomialCenterEval_single_eq_zero rankTwo (b.detDualEquiv_self u)
      (ρ.surjective_detCharacter b) d a r ha

private theorem centerEval_single_zsmul (d : ℂˣ) (a : S(ρ.toCone)) (r : ℂ) (n : ℤ)
    (ha : (a : N →+ ℤ) = n • χ(u)) :
    centerEval b ρ d (single a r) = r * (-(↑d⁻¹ : ℂ)) ^ n := by
  have hz : (n • χ(u)) u = 0 := by
    simp only [AddMonoidHom.zsmul_apply, LinearMap.toAddMonoidHom_coe, b.detDualEquiv_self,
      smul_zero]
  have he : a = ρ.chartCharacter hz := Subtype.ext (by simpa only [Ray.coe_chartCharacter] using ha)
  rw [he]
  simpa only [centerEval, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    toMultiplicativeAlgEquiv_single] using
    ρ.binomialCenterEval_single_zsmul rankTwo (b.detDualEquiv_self u)
      (ρ.surjective_detCharacter b) d n r

private theorem centerEval_toPoint (d : ℂˣ) :
    Spec.map (CommRingCat.ofHom (centerEval b ρ d).toRingHom) ≫
        Φ.additiveAffineToricChartι ρ.toCone =
      ρ.binomialCenter rankTwo (m := χ(u))
        (by simpa only [LinearMap.toAddMonoidHom_coe] using b.detDualEquiv_self u)
        (ρ.surjective_detCharacter b) d := by
  rw [additiveAffineToricChartι_def, Ray.binomialCenter_def, ← Spec.map_comp_assoc,
    ← CommRingCat.ofHom_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  simp [centerEval]

private def centerEvalOnCone (d : ℂˣ) (σ : Φ.cones) (hσ : σ = ρ.toCone) :
    R(σ) →ₐ[ℂ] ℂ :=
  hσ.symm ▸ centerEval b ρ d

private theorem centerEvalOnCone_single (d : ℂˣ) (σ : Φ.cones) (hσ : σ = ρ.toCone)
    (a : S(σ)) (a' : S(ρ.toCone)) (ha : a.val = a'.val) :
    centerEvalOnCone b ρ d σ hσ (single a 1) = centerEval b ρ d (single a' 1) := by
  subst σ
  obtain rfl := Subtype.ext ha
  rfl

private theorem centerEvalOnCone_toPoint (d : ℂˣ) (σ : Φ.cones) (hσ : σ = ρ.toCone) :
    Spec.map (CommRingCat.ofHom (centerEvalOnCone b ρ d σ hσ).toRingHom) ≫
        Φ.additiveAffineToricChartι σ =
      ρ.binomialCenter rankTwo (b.detDualEquiv_self u)
        (ρ.surjective_detCharacter b) d := by
  subst σ
  exact centerEval_toPoint b ρ d

variable {v : N} (hv : v ≠ 0) (hpos : PointedCone.hull ℝ {i v} ∈ Φ.cones)
  (hneg : PointedCone.hull ℝ {i (-v)} ∈ Φ.cones)

local notation "Ψ" => Φ.mutationFan b hv hpos hneg
local notation "τ" => Φ.mutationFanRayEquiv b hv hpos hneg ρ
local notation "u'" => Ray.primitiveGenerator τ
local notation "pivotChar" => χ(v)
local notation "δ" => b.det ![u, v]

private theorem coe_mutationFanRayEquiv_primitiveGenerator :
    u' = u + max (-pivotChar u) 0 • v := by
  rw [mutationFanRayEquiv_primitiveGenerator, ← b.detDualEquiv_apply, b.detDualEquiv_swap u v]
  rfl

private def raySide : Bool := decide (pivotChar u < 0)

private theorem signedPivot_mem :
    mutationChartCharacter b (v := v) (raySide b ρ (v := v)) ∈ S(ρ.toCone) := by
  rw [ρ.mem_rayDualSemigroup_iff]
  by_cases h : pivotChar u < 0
  · simpa only [raySide, h, decide_true, mutationChartCharacter_true,
      AddMonoidHom.neg_apply, neg_nonneg] using h.le
  · simpa only [raySide, h, decide_false, mutationChartCharacter_false] using not_lt.mp h

local notation "s" => raySide b ρ (v := v)
local notation "hs" => signedPivot_mem b ρ (v := v)
local notation "q" => (Subtype.mk (mutationChartCharacter b (v := v) s) hs : S(ρ.toCone))
local notation "e" =>
  Φ.mutationChartExponentEquiv b hv hpos hneg ρ.toCone s hs

include hv hpos hneg in
private theorem exponentEquiv_apply_ray
    (a : S(Φ.mutationFanConeEquiv b hv hpos hneg ρ.toCone)) :
    (e a : N →+ ℤ) u = a.val u' := by
  rw [mutationChartExponentEquiv_apply, coe_mutationFanRayEquiv_primitiveGenerator,
    map_add, map_zsmul]
  by_cases h : pivotChar u < 0
  · simp only [raySide, h, decide_true, ↓reduceIte, max_eq_left (neg_nonneg.mpr h.le),
      zsmul_eq_mul, Int.cast_id]
    ring
  · simp only [raySide, h, decide_false, Bool.false_eq_true, ↓reduceIte,
      max_eq_right (neg_nonpos.mpr (not_lt.mp h)), zero_smul, add_zero]

include hv hpos hneg in
private theorem targetCharacter_apply_pivot :
    χ(u') v = δ := by
  rw [← b.detDualEquiv_apply, coe_mutationFanRayEquiv_primitiveGenerator]
  simp only [LinearMap.toAddMonoidHom_coe, map_add, map_zsmul, LinearMap.add_apply,
    LinearMap.smul_apply, b.detDualEquiv_self, smul_zero, add_zero]

include hv hpos hneg in
private theorem exponentEquiv_char
    (a : S(Φ.mutationFanConeEquiv b hv hpos hneg ρ.toCone)) (n : ℤ)
    (ha : (a : N →+ ℤ) = n • χ(u')) :
    (e a : N →+ ℤ) = n • χ(u) := by
  have hdet : δ = -pivotChar u := by
    rw [← b.detDualEquiv_apply, b.detDualEquiv_swap u v]
    rfl
  ext x
  rw [mutationChartExponentEquiv_apply, ha]
  have hx : χ(u') x = χ(u) x + max (-pivotChar u) 0 * pivotChar x := by
    rw [coe_mutationFanRayEquiv_primitiveGenerator]
    simp
  by_cases h : pivotChar u < 0
  · simp only [raySide, h, decide_true, ↓reduceIte, AddMonoidHom.zsmul_apply, hx,
      targetCharacter_apply_pivot, hdet, max_eq_left (neg_nonneg.mpr h.le), zsmul_eq_mul,
      Int.cast_id]
    ring
  · simp only [raySide, h, decide_false, Bool.false_eq_true, ↓reduceIte,
      AddMonoidHom.zsmul_apply, hx, max_eq_right (neg_nonpos.mpr (not_lt.mp h)), zero_mul,
      add_zero]

variable (c d : ℂˣ)

local notation "B" => Φ.mutationChartBinomial s (Units.val c) q

private theorem centerEval_pivotBinomial_of_ne_zero (h : pivotChar u ≠ 0) :
    centerEval b ρ d B = if pivotChar u < 0 then (c : ℂ) else 1 := by
  have hq : Subtype.val q u ≠ 0 := by
    by_cases hn : pivotChar u < 0
    · simpa only [raySide, hn, decide_true, mutationChartCharacter_true,
        AddMonoidHom.neg_apply, neg_ne_zero] using h
    · simpa only [raySide, hn, decide_false, mutationChartCharacter_false] using h
  rw [mutationChartBinomial_eq, map_add, AlgHom.commutes, centerEval_single_eq_zero _ _ _ _ _ hq,
    add_zero]
  by_cases hn : pivotChar u < 0 <;> simp only [raySide, hn, decide_true, decide_false,
    Bool.cond_true, Bool.cond_false, ite_true, ite_false, Algebra.algebraMap_self_apply]

private theorem centerEval_pivotBinomial_of_zsmul (j : ℤ)
    (hj : pivotChar = j • χ(u)) :
    centerEval b ρ d B = 1 + (c : ℂ) * (-(↑d⁻¹ : ℂ)) ^ j := by
  have h : pivotChar u = 0 := by
    rw [hj, AddMonoidHom.zsmul_apply, LinearMap.toAddMonoidHom_coe, b.detDualEquiv_self, smul_zero]
  have hq : Subtype.val q = j • χ(u) := by
    simpa only [raySide, h, lt_irrefl, decide_false, mutationChartCharacter_false] using hj
  rw [mutationChartBinomial_eq, map_add, AlgHom.commutes,
    centerEval_single_zsmul b ρ d q _ j hq]
  simp only [raySide, h, lt_irrefl, decide_false, Bool.cond_false, map_one]

private theorem centerEval_pivotBinomial_ne_zero (hprim : IsPrimitive v)
    (hsame : u = v → d ≠ c) (hopp : u = -v → d * c ≠ 1) :
    centerEval b ρ d B ≠ 0 := by
  by_cases h : pivotChar u = 0
  · rcases ρ.eq_or_eq_neg_of_detCharacter_eq_zero b hprim h with hvu | hvu
    · rw [centerEval_pivotBinomial_of_zsmul b ρ c d 1 (by simp [hvu])]
      intro he
      apply hsame hvu.symm
      apply Units.ext
      have he' := congrArg (fun z : ℂ ↦ z * (d : ℂ)) he
      simp only [zpow_one, add_mul, one_mul, zero_mul] at he'
      rw [mul_assoc, neg_mul, Units.inv_mul, mul_neg_one] at he'
      exact (add_eq_zero_iff_eq_neg.mp he').trans (neg_neg _)
    · rw [centerEval_pivotBinomial_of_zsmul b ρ c d (-1) (by
        ext x
        simp only [hvu, map_neg, LinearMap.toAddMonoidHom_coe, LinearMap.neg_apply,
          neg_one_zsmul, AddMonoidHom.neg_apply])]
      intro he
      apply hopp (by simp [hvu])
      apply Units.ext
      simpa [zpow_neg_one, mul_comm] using
        (add_eq_zero_iff_eq_neg.mp he).symm
  · rw [centerEval_pivotBinomial_of_ne_zero b ρ c d h]
    split <;> simp

local notation "L" => Localization.Away B
local notation "C₁" => Φ.mutationFanConeEquiv b hv hpos hneg ρ.toCone
local notation "hCone" => Eq.symm (mutationFanRayEquiv_toCone Φ b hv hpos hneg ρ)
local notation "movedParameter" => (d * c ^ max δ 0)
local notation "hRuling₀" => Φ.detCharacter_nonneg_or_nonpos b hv hpos hneg
local notation "hRuling₁" => Φ.mutationDetCharacter_nonneg_or_nonpos b hv hpos hneg
local notation "U₀" => (Φ.mutationComplement b hRuling₀ (Units.val c))
local notation "U₁" => (mutationComplement Ψ b hRuling₁ (Units.val c))
local notation "E" => (Φ.mutationComplementIso b (Units.val c) hv hpos hneg)

private abbrev localizedCenterEval (hf : centerEval b ρ d B ≠ 0) : L →ₐ[ℂ] ℂ :=
  IsLocalization.Away.liftAlgHom B (isUnit_iff_ne_zero.mpr hf)

private theorem localizedCenterEval_algebraMap (hf : centerEval b ρ d B ≠ 0) (x : R(ρ.toCone)) :
    localizedCenterEval b ρ c d hf (algebraMap _ L x) = centerEval b ρ d x :=
  IsLocalization.Away.lift_eq B (isUnit_iff_ne_zero.mpr hf) x

private theorem localizedCenterEval_binomial_zpow (hf : centerEval b ρ d B ≠ 0) (n : ℤ) :
    localizedCenterEval b ρ c d hf
      (↑(awayBinomialUnit (cond s (c : ℂ) 1) (cond s 1 (c : ℂ)) q ^ n) : L) =
      (centerEval b ρ d B) ^ n := by
  let g := (localizedCenterEval b ρ c d hf).toMonoidHom
  have hbase : (Units.map g (awayBinomialUnit
      (cond s (c : ℂ) 1) (cond s 1 (c : ℂ)) q) : ℂ) = centerEval b ρ d B := by
    rw [Units.coe_map, coe_awayBinomialUnit]
    exact localizedCenterEval_algebraMap b ρ c d hf B
  rw [← hbase, ← Units.val_zpow_eq_zpow_val, ← map_zpow, Units.coe_map]
  rfl

private theorem centerEval_movedParameter_zpow (n : ℤ) :
    (-(↑d⁻¹ : ℂ)) ^ n * (centerEval b ρ d B) ^ (-(n * δ)) =
      (-(↑(movedParameter)⁻¹ : ℂ)) ^ n := by
  have hdet : δ = -pivotChar u := by
    rw [← b.detDualEquiv_apply, b.detDualEquiv_swap u v]
    rfl
  rcases lt_trichotomy (pivotChar u) 0 with h | h | h
  · rw [centerEval_pivotBinomial_of_ne_zero b ρ c d h.ne, ite_eq_left h,
      hdet, max_eq_left (neg_nonneg.mpr h.le)]
    have hpow : -(n * -pivotChar u) = pivotChar u * n := by ring
    rw [hpow, zpow_mul, ← mul_zpow]
    congr 1
    simp only [mul_inv_rev, Units.val_mul, Units.val_zpow_eq_zpow_val,
      Units.val_inv_eq_inv_val]
    rw [← zpow_neg, neg_neg]
    ring
  · simp [hdet, h]
  · rw [centerEval_pivotBinomial_of_ne_zero b ρ c d h.ne', ite_eq_right h.not_gt, hdet,
      max_eq_right (neg_nonpos.mpr h.le)]
    simp

include hv hpos hneg in
private theorem mutationChartAlgEquiv_eval (hf : centerEval b ρ d B ≠ 0)
    (a : S(C₁)) :
    localizedCenterEval b ρ c d hf
      (Φ.mutationChartAlgEquiv b hv hpos hneg ρ.toCone s hs (c : ℂ)
        (algebraMap (R(C₁)) _ (single a 1))) =
      centerEvalOnCone b τ movedParameter C₁ hCone (single a 1) := by
  let a' : S(Ray.toCone Ψ τ) := ⟨a.val, by rw [← hCone]; exact a.property⟩
  rw [centerEvalOnCone_single b τ movedParameter C₁ hCone a a' rfl]
  rw [mutationChartAlgEquiv_single, map_mul, localizedCenterEval_algebraMap]
  by_cases ha : a.val u' = 0
  · obtain ⟨n, hn⟩ := (τ).exists_zsmul_eq_of_apply_primitiveGenerator_eq_zero
      rankTwo (b.detDualEquiv_self u') ((τ).surjective_detCharacter b) ha
    have hsource := exponentEquiv_char b ρ hv hpos hneg a n hn.symm
    rw [centerEval_single_zsmul b ρ d _ _ n hsource,
      centerEval_single_zsmul b τ movedParameter a' _ n hn.symm,
      one_mul, one_mul, localizedCenterEval_binomial_zpow]
    have hdeg : a.val v = n * δ := by
      simpa only [AddMonoidHom.zsmul_apply, zsmul_eq_mul, Int.cast_id, targetCharacter_apply_pivot]
        using (DFunLike.congr_fun hn v).symm
    rw [hdeg]
    exact centerEval_movedParameter_zpow b ρ c d n
  · rw [centerEval_single_eq_zero b ρ d _ _ (by rwa [exponentEquiv_apply_ray]),
      centerEval_single_eq_zero b τ movedParameter a' _ ha, zero_mul]

include hv hpos hneg in
private theorem mutationChartAlgEquiv_eval_comp (hf : centerEval b ρ d B ≠ 0) :
    ((localizedCenterEval b ρ c d hf).comp
      (Φ.mutationChartAlgEquiv b hv hpos hneg ρ.toCone s hs (c : ℂ)).toAlgHom).comp
        (Algebra.algHom ℂ (R(C₁)) _) =
      centerEvalOnCone b τ movedParameter C₁ hCone := by
  apply AddMonoidAlgebra.algHom_ext
  · intro a
    exact mutationChartAlgEquiv_eval b ρ hv hpos hneg c d hf a
  · ext

include hv hpos hneg in
/-- The binomial center factors through the pivot-fiber complement. Its image under
the mutation isomorphism is the center on the sheared ray with the mutated parameter. -/
theorem exists_binomialCenter_mutationComplementIso (hprim : IsPrimitive v)
    (hsame : u = v → d ≠ c) (hopp : u = -v → d * c ≠ 1) :
    ∃ p : Spec (.of ℂ) ⟶ (U₀).toScheme,
      p ≫ (U₀).ι = ρ.binomialCenter rankTwo (m := χ(u)) (b.detDualEquiv_self u)
        (ρ.surjective_detCharacter b) d ∧
      p ≫ (E).hom ≫ (U₁).ι = (τ).binomialCenter rankTwo (m := χ(u')) (b.detDualEquiv_self u')
        ((τ).surjective_detCharacter b) movedParameter := by
  have hf := centerEval_pivotBinomial_ne_zero b ρ c d hprim hsame hopp
  let f := localizedCenterEval b ρ c d hf
  refine ⟨Spec.map (CommRingCat.ofHom f.toRingHom) ≫
    Φ.mutationComplementChartι b ρ.toCone s hs (c : ℂ) hRuling₀, ?_, ?_⟩
  · rw [Category.assoc, mutationComplementChartι_comp_ι, ← Spec.map_comp_assoc,
      ← CommRingCat.ofHom_comp]
    have hf' : f.toRingHom.comp (algebraMap (R(ρ.toCone)) L) =
        (centerEval b ρ d).toRingHom := by
      exact IsLocalization.Away.lift_comp B (isUnit_iff_ne_zero.mpr hf)
    rw [hf']
    exact centerEval_toPoint b ρ d
  · rw [Category.assoc, mutationComplementChartι_comp_mutationComplementIso_hom_assoc,
      mutationComplementChartι_comp_ι, ← Spec.map_comp_assoc,
      ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    have he := congrArg (fun g : R(C₁) →ₐ[ℂ] ℂ ↦ g.toRingHom)
      (mutationChartAlgEquiv_eval_comp b ρ hv hpos hneg c d hf)
    -- Read the composite of affine scheme maps as the composite of their algebra maps.
    exact (congrArg (fun g : R(C₁) →+* ℂ ↦
      Spec.map (CommRingCat.ofHom g) ≫ (Ψ).additiveAffineToricChartι C₁) he).trans
      (centerEvalOnCone_toPoint b τ movedParameter C₁ hCone)

local notation "hΦ" => Nonempty.intro (Ray.toCone Φ ρ)
local notation "hΨ" => Nonempty.intro C₁

/-- Away from the pivot fiber, mutation pulls the ideal of the moved center back to the ideal
of the original center. On the pivot and opposite rays the two assumptions exclude precisely
the points with ruling coordinate `-c⁻¹`. The formula applies to every other ray without a
noncollision assumption. -/
theorem mutationComplementIso_transports_internal_centers (hprim : IsPrimitive v)
    (hsame : u = v → d ≠ c) (hopp : u = -v → d * c ≠ 1) :
    (((τ).internalCenter (h₀ := hΨ) b movedParameter).val.map
        ((Ψ).boundaryIdeal hΨ).subschemeι).comap ((E).hom ≫ (U₁).ι) =
      ((ρ.internalCenter (h₀ := hΦ) b d).val.map (Φ.boundaryIdeal hΦ).subschemeι).comap (U₀).ι := by
  obtain ⟨p, hp, hp'⟩ :=
    exists_binomialCenter_mutationComplementIso b ρ hv hpos hneg c d hprim hsame hopp
  let : Nonempty Φ.cones := hΦ
  let : Nonempty (Ψ).cones := hΨ
  have := ρ.isClosedImmersion_binomialCenter rankTwo (b.detDualEquiv_self u)
    (ρ.surjective_detCharacter b) d
  have := (τ).isClosedImmersion_binomialCenter rankTwo (b.detDualEquiv_self u')
    ((τ).surjective_detCharacter b) movedParameter
  rw [Ray.map_internalCenter_subschemeι, Ray.map_internalCenter_subschemeι]
  have sourceSquare := IsPullback.of_vert_isIso_mono
    (fst := p) (snd := 𝟙 _) (f := (U₀).ι) (g := _)
      ⟨by simpa only [Category.id_comp] using hp⟩
  have targetSquare := IsPullback.of_vert_isIso_mono
    (fst := p) (snd := 𝟙 _) (f := (E).hom ≫ (U₁).ι) (g := _)
      ⟨by simpa only [Category.id_comp] using hp'⟩
  rw [← Scheme.IdealSheafData.ker_eq_comap_of_isPullback _ sourceSquare,
    ← Scheme.IdealSheafData.ker_eq_comap_of_isPullback _ targetSquare]

end TauCeti.Toric.Fan
