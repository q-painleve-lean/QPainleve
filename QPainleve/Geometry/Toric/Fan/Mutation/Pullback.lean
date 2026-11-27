/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.BaseChange.FunctionField
public import QPainleve.Geometry.Toric.Fan.Mutation.Complement

import Mathlib.AlgebraicGeometry.Group.Affine
import QPainleve.AlgebraicGeometry.Scheme.FunctionField

/-!
# Function field pullback of toric mutation

The isomorphism on the complements of the pivot fiber induces a pullback between
the function fields of the two toric realizations. Its action on every rational
character is the binomial twist from Gross, Hacking and Keel,
[*Birational geometry of cluster algebras*, §3.1](https://arxiv.org/html/1309.2573v2#S3.SS1).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory AddMonoidAlgebra Multiplicative

namespace TauCeti.Toric.Fan

variable {K : Type} [CommRing K] [IsDomain K] {N V : Type}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  (Φ : Fan i) (b : Module.Basis (Fin 2) ℤ N) {v : N} (c : K)
  (hv : v ≠ 0) (hpos : PointedCone.hull ℝ {i v} ∈ Φ.cones)
  (hneg : PointedCone.hull ℝ {i (-v)} ∈ Φ.cones)

local notation "Ψ" => mutationFan Φ b hv hpos hneg
local notation "h₀" => detCharacter_nonneg_or_nonpos Φ b hv hpos hneg
local notation "h₁" => mutationDetCharacter_nonneg_or_nonpos Φ b hv hpos hneg
local notation "U₀" => mutationComplement Φ b h₀ c
local notation "U₁" => mutationComplement Ψ b h₁ c
local notation "E" => mutationComplementIso Φ b c hv hpos hneg
local notation "m" => LinearMap.toAddMonoidHom (Module.Basis.detDualEquiv b v)

private def mutationZeroCone : Φ.cones := ⟨⊥, Φ.bot_mem hpos⟩

local notation "σ" => mutationZeroCone Φ hpos
local notation "τ" => mutationFanConeEquiv Φ b hv hpos hneg σ

private theorem mutationZeroCone_character_mem (a : N →+ ℤ) :
    a ∈ dualSemigroup Φ.lattice (σ).val := by
  simp [mutationZeroCone]

local notation "hs" =>
  mutationZeroCone_character_mem Φ hpos (mutationChartCharacter b (v := v) false)
local notation "ht" => mutationChartCharacter_mem_dualSemigroup_target Φ b hv hpos hneg σ false hs
local notation "q(" C "," H ")" =>
  (Subtype.mk (mutationChartCharacter b (v := v) false) H : dualSemigroup Φ.lattice (Subtype.val C))
local notation "R(" C ")" => AddMonoidAlgebra K (dualSemigroup Φ.lattice (Subtype.val C))
local notation "L(" F "," C "," H ")" => Localization.Away (mutationChartBinomial F false c q(C,H))
local notation "L₀" => L(Φ,σ,hs)
local notation "L₁" => L(Ψ,τ,ht)
local notation "incl(" D ")" =>
  @algebraMap (CommRingCat.of D) (Scheme.functionField (Spec (CommRingCat.of D))) _ _
    (instAlgebraCarrierFunctionFieldSpec (CommRingCat.of D))
local notation "A" => mutationChartAlgEquiv Φ b hv hpos hneg σ false hs c
local notation "twRing" => CommRingCat.ofHom (AlgHom.toRingHom (AlgEquiv.toAlgHom A))
local notation "tw" => Spec.map twRing
local notation "j₀" => mutationComplementChartι Φ b σ false hs c h₀
local notation "j₁" => mutationComplementChartι Ψ b τ false ht c h₁

include hv in
private theorem mutationZeroBinomial_ne_zero : Φ.mutationChartBinomial false c q(σ,hs) ≠ 0 := by
  have hq : q(σ,hs) ≠ 0 := by
    intro he
    exact hv ((mutationChartCharacter_eq_zero_iff b false).mp (congrArg Subtype.val he))
  intro he
  have h := congrArg (fun r : R(σ) ↦ r.coeff 0) he
  have hconst : (single (0 : dualSemigroup Φ.lattice (σ).val) (1 : K)).coeff 0 = 1 :=
    Finsupp.single_eq_same
  have hterm : (single q(σ,hs) c).coeff 0 = 0 := Finsupp.single_eq_of_ne hq.symm
  -- Take the constant coefficient in the semigroup algebra.
  change (((single 0 1 + single q(σ,hs) c : R(σ)).coeff) 0) = (0 : R(σ)).coeff 0 at h
  rw [coeff_add, coeff_zero] at h
  -- Evaluation of the sum of coefficients is pointwise.
  change (single (0 : dualSemigroup Φ.lattice (σ).val) (1 : K)).coeff 0 +
    (single q(σ,hs) c).coeff 0 = 0 at h
  rw [hconst, hterm, add_zero] at h
  exact one_ne_zero h

include hv in
private theorem isDomain_mutationZeroLocalization : IsDomain L₀ :=
  Localization.Away.isDomain (mutationZeroBinomial_ne_zero Φ b c hv hpos)

include hv hpos hneg in
/-- The complement of the pivot fiber in the source fan is integral. -/
theorem isIntegral_mutationComplement_source : IsIntegral (U₀).toScheme := by
  have : Nonempty Φ.cones := ⟨σ⟩
  have : IsDomain L₀ := isDomain_mutationZeroLocalization Φ b c hv hpos
  have : Nonempty (U₀).toScheme := ⟨j₀ (Classical.arbitrary (Spec (.of L₀)))⟩
  exact isIntegral_of_isOpenImmersion (U₀).ι

include hv hpos hneg in
/-- The complement of the pivot fiber in the mutated fan is integral. -/
theorem isIntegral_mutationComplement_target : IsIntegral (U₁).toScheme := by
  have := isIntegral_mutationComplement_source Φ b c hv hpos hneg
  exact IsIntegral.of_isIso (E).hom

/-- Pullback on function fields along the isomorphism of the pivot-fiber complements. -/
def mutationComplementPullback :
    letI : Nonempty Φ.cones := ⟨⟨_, hpos⟩⟩
    letI : Nonempty (Ψ).cones := ⟨Φ.mutationFanConeEquiv b hv hpos hneg ⟨_, hpos⟩⟩
    ((Ψ).finiteFanScheme K).functionField ⟶ (Φ.finiteFanScheme K).functionField := by
  letI : Nonempty Φ.cones := ⟨σ⟩
  letI : Nonempty (Ψ).cones := ⟨τ⟩
  have := isIntegral_mutationComplement_source Φ b c hv hpos hneg
  have := isIntegral_mutationComplement_target Φ b c hv hpos hneg
  exact ((E).hom ≫ (U₁).ι).functionFieldMap ≫ CategoryTheory.inv (U₀).ι.functionFieldMap

/-- The complement isomorphism induces an isomorphism on the function fields. -/
theorem isIso_mutationComplementPullback :
    letI : Nonempty Φ.cones := ⟨⟨_, hpos⟩⟩
    letI : Nonempty (Ψ).cones := ⟨Φ.mutationFanConeEquiv b hv hpos hneg ⟨_, hpos⟩⟩
    IsIso (Φ.mutationComplementPullback b c hv hpos hneg) := by
  let : Nonempty Φ.cones := ⟨σ⟩
  let : Nonempty (Ψ).cones := ⟨τ⟩
  let := isIntegral_mutationComplement_source Φ b c hv hpos hneg
  let := isIntegral_mutationComplement_target Φ b c hv hpos hneg
  rw [mutationComplementPullback]
  infer_instance

/-- The pullback on rational functions restricts to the actual morphism on the source complement. -/
@[reassoc]
theorem mutationComplementPullback_comp_functionFieldMap :
    letI : Nonempty Φ.cones := ⟨⟨_, hpos⟩⟩
    letI : Nonempty (Ψ).cones := ⟨Φ.mutationFanConeEquiv b hv hpos hneg ⟨_, hpos⟩⟩
    letI := isIntegral_mutationComplement_source Φ b c hv hpos hneg
    letI := isIntegral_mutationComplement_target Φ b c hv hpos hneg
    Φ.mutationComplementPullback b c hv hpos hneg ≫ (U₀).ι.functionFieldMap =
      ((E).hom ≫ (U₁).ι).functionFieldMap := by
  simp [mutationComplementPullback]

section LocalizedChart

variable [Nonempty Φ.cones] (s : Φ.cones)
  (hs' : mutationChartCharacter b (v := v) false ∈ dualSemigroup Φ.lattice s.val)
  (h' : ∀ t : Φ.cones, (∀ x ∈ t.val, 0 ≤ Φ.lattice.realCharacter
      (b.detDualEquiv v).toAddMonoidHom x) ∨
    ∀ x ∈ t.val, Φ.lattice.realCharacter (b.detDualEquiv v).toAddMonoidHom x ≤ 0)

local notation "D" => L(Φ,s,hs')
local notation "j" => mutationComplementChartι Φ b s false hs' c h'
local notation "U" => mutationComplement Φ b h' c

private theorem localizedChart_functionFieldMap_character (a : dualSemigroup Φ.lattice s.val) :
    ∀ [IsDomain D],
      (j ≫ (U).ι).functionFieldMap (Φ.functionFieldCharacter K (ofAdd a.val)) =
        incl(D) (algebraMap (R(s)) D (single a 1)) := by
  intro
  rw [Scheme.Hom.functionFieldMap_congr (Φ.mutationComplementChartι_comp_ι b s false hs' c h'),
    Scheme.Hom.functionFieldMap_comp, CommRingCat.comp_apply,
    Φ.functionFieldMap_affineChartι_character K s a,
    Scheme.Hom.functionFieldMap_SpecMap_algebraMap]
  rfl

omit [Nonempty Φ.cones] [IsDomain K] in
private theorem localizedChart_isOver : (j ≫ (U).ι).IsOver (Spec (.of K)) := by
  rw [mutationComplementChartι_comp_ι]
  let f := Algebra.algHom K (R(s)) D
  exact (inferInstance : (Spec.map (CommRingCat.ofHom f.toRingHom) ≫
    Φ.affineChartι K s).IsOver (Spec (.of K)))

end LocalizedChart

private theorem mutationComplementPullback_comp_localizedChart :
    letI : Nonempty Φ.cones := ⟨σ⟩
    letI : Nonempty (Ψ).cones := ⟨τ⟩
    letI : IsDomain L₀ := isDomain_mutationZeroLocalization Φ b c hv hpos
    letI : IsDomain L₁ := Function.Injective.isDomain (A) (A).injective
    letI : IsIso (twRing) := inferInstanceAs (IsIso (A).toRingEquiv.toCommRingCatIso.hom)
    Φ.mutationComplementPullback b c hv hpos hneg ≫ (j₀ ≫ (U₀).ι).functionFieldMap =
      (j₁ ≫ (U₁).ι).functionFieldMap ≫ (tw).functionFieldMap := by
  let : Nonempty Φ.cones := ⟨σ⟩
  let : Nonempty (Ψ).cones := ⟨τ⟩
  let : IsDomain L₀ := isDomain_mutationZeroLocalization Φ b c hv hpos
  let : IsDomain L₁ := Function.Injective.isDomain (A) (A).injective
  let : IsIso (twRing) := inferInstanceAs (IsIso (A).toRingEquiv.toCommRingCatIso.hom)
  let := isIntegral_mutationComplement_source Φ b c hv hpos hneg
  let := isIntegral_mutationComplement_target Φ b c hv hpos hneg
  have h : j₀ ≫ (E).hom ≫ (U₁).ι = tw ≫ j₁ ≫ (U₁).ι := by
    rw [← Category.assoc j₀, mutationComplementChartι_comp_mutationComplementIso_hom,
      Category.assoc]
  rw [Scheme.Hom.functionFieldMap_comp, ← Category.assoc,
    mutationComplementPullback_comp_functionFieldMap, ← Scheme.Hom.functionFieldMap_comp]
  exact (Scheme.Hom.functionFieldMap_congr h).trans (Scheme.Hom.functionFieldMap_comp _ _)

/-- The complement pullback preserves the scalars of the toric function fields. -/
theorem mutationComplementPullback_algebraMap (a : K) :
    letI : Nonempty Φ.cones := ⟨⟨_, hpos⟩⟩
    letI : Nonempty (Ψ).cones := ⟨Φ.mutationFanConeEquiv b hv hpos hneg ⟨_, hpos⟩⟩
    Φ.mutationComplementPullback b c hv hpos hneg
        (algebraMap K ((Ψ).finiteFanScheme K).functionField a) =
      algebraMap K (Φ.finiteFanScheme K).functionField a := by
  let : Nonempty Φ.cones := ⟨σ⟩
  let : Nonempty (Ψ).cones := ⟨τ⟩
  let : IsDomain L₀ := isDomain_mutationZeroLocalization Φ b c hv hpos
  let : IsDomain L₁ := Function.Injective.isDomain (A) (A).injective
  let : IsIso (twRing) := inferInstanceAs (IsIso (A).toRingEquiv.toCommRingCatIso.hom)
  have := Φ.localizedChart_isOver b c σ hs h₀
  have := (Ψ).localizedChart_isOver b c τ ht h₁
  have : (tw).IsOver (Spec (.of K)) :=
    inferInstanceAs ((Spec.map (CommRingCat.ofHom (A).toAlgHom.toRingHom)).IsOver (Spec (.of K)))
  apply (j₀ ≫ (U₀).ι).functionFieldMap.hom.injective
  have he := ConcreteCategory.congr_hom
    (Φ.mutationComplementPullback_comp_localizedChart b c hv hpos hneg)
    (algebraMap K ((Ψ).finiteFanScheme K).functionField a)
  simpa only [CommRingCat.comp_apply, Scheme.Hom.functionFieldMap_algebraMap] using he

/-- Pullback over the coefficient domain along the toric mutation on the pivot-fiber complements. -/
def mutationComplementPullbackAlgHom :
    letI : Nonempty Φ.cones := ⟨⟨_, hpos⟩⟩
    letI : Nonempty (Ψ).cones := ⟨Φ.mutationFanConeEquiv b hv hpos hneg ⟨_, hpos⟩⟩
    ((Ψ).finiteFanScheme K).functionField →ₐ[K] (Φ.finiteFanScheme K).functionField where
  toRingHom := (Φ.mutationComplementPullback b c hv hpos hneg).hom
  commutes' := Φ.mutationComplementPullback_algebraMap b c hv hpos hneg

@[simp]
theorem mutationComplementPullbackAlgHom_apply
    (a : letI : Nonempty (Ψ).cones := ⟨Φ.mutationFanConeEquiv b hv hpos hneg ⟨_, hpos⟩⟩
      ((Ψ).finiteFanScheme K).functionField) :
    letI : Nonempty Φ.cones := ⟨⟨_, hpos⟩⟩
    Φ.mutationComplementPullbackAlgHom b c hv hpos hneg a =
      Φ.mutationComplementPullback b c hv hpos hneg a := (rfl)

private theorem mutationZeroExponent_value (a : dualSemigroup Φ.lattice (σ).val) :
    ((Φ.mutationChartExponentEquiv b hv hpos hneg σ false hs).symm a).val = a.val := by
  let e := Φ.mutationChartExponentEquiv b hv hpos hneg σ false hs
  ext x
  have hx := congrArg (fun z : dualSemigroup Φ.lattice (σ).val ↦ z.val x) (e.apply_symm_apply a)
  simpa only [e, mutationChartExponentEquiv_apply, Bool.false_eq_true, ite_false] using hx

omit [IsDomain K] in
private theorem coe_mutationZeroBinomial [IsDomain (L₀)] :
    incl(L₀) (Units.val (awayBinomialUnit 1 c q(σ,hs))) =
      1 + algebraMap K (Spec (.of L₀)).functionField c *
        incl(L₀) (algebraMap (R(σ)) L₀ (single q(σ,hs) 1)) := by
  let f := (incl(L₀)).comp (algebraMap (R(σ)) L₀)
  have hbin : single (0 : dualSemigroup Φ.lattice (σ).val) 1 + single q(σ,hs) c =
      1 + algebraMap K (R(σ)) c * single q(σ,hs) 1 := by
    have hc : algebraMap K (R(σ)) c * single q(σ,hs) 1 = single q(σ,hs) c := by
      rw [← Algebra.smul_def]
      simp
    rw [hc]
    rfl
  have he : incl(L₀) (Units.val (awayBinomialUnit 1 c q(σ,hs))) =
      f (1 + algebraMap K (R(σ)) c * single q(σ,hs) 1) := by
    rw [coe_awayBinomialUnit]
    exact congrArg f hbin
  rw [he, map_add, map_one, map_mul]
  have hg (r : L₀) : ((Scheme.ΓSpecIso (.of L₀)).inv ≫
      (Spec (.of L₀)).germToFunctionField ⊤) r = incl(L₀) r := by
    rw [Scheme.ΓSpecIso_inv]
    rfl
  have hc : f (algebraMap K (R(σ)) c) = algebraMap K (Spec (.of L₀)).functionField c := by
    simp only [f, RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply K (R(σ)) L₀,
      Scheme.Spec.algebraMap_functionField_base, hg]
  rw [hc]
  rfl

/-- The actual toric mutation pulls a rational character back to that character
times the pivot binomial to the negative value of the character at the pivot. -/
theorem mutationComplementPullback_character (a : N →+ ℤ) :
    letI : Nonempty Φ.cones := ⟨⟨_, hpos⟩⟩
    letI : Nonempty (Ψ).cones := ⟨Φ.mutationFanConeEquiv b hv hpos hneg ⟨_, hpos⟩⟩
    Φ.mutationComplementPullback b c hv hpos hneg ((Ψ).functionFieldCharacter K (ofAdd a)) =
      Φ.functionFieldCharacter K (ofAdd a) *
        (1 + algebraMap K (Φ.finiteFanScheme K).functionField c *
          Φ.functionFieldCharacter K (ofAdd m)) ^ (-a v) := by
  let : Nonempty Φ.cones := ⟨σ⟩
  let : Nonempty (Ψ).cones := ⟨τ⟩
  let : IsDomain L₀ := isDomain_mutationZeroLocalization Φ b c hv hpos
  let : IsDomain L₁ := Function.Injective.isDomain (A) (A).injective
  let a₀ : dualSemigroup Φ.lattice (σ).val := ⟨a, mutationZeroCone_character_mem Φ hpos a⟩
  let a₁ := (Φ.mutationChartExponentEquiv b hv hpos hneg σ false hs).symm a₀
  have ha : a₁.val = a := mutationZeroExponent_value Φ b hv hpos hneg a₀
  have : IsIso (twRing) := inferInstanceAs (IsIso (A).toRingEquiv.toCommRingCatIso.hom)
  have := Φ.localizedChart_isOver b c σ hs h₀
  apply (j₀ ≫ (U₀).ι).functionFieldMap.hom.injective
  have he := ConcreteCategory.congr_hom
    (Φ.mutationComplementPullback_comp_localizedChart b c hv hpos hneg)
      ((Ψ).functionFieldCharacter K (ofAdd a₁.val))
  simp only [CommRingCat.comp_apply] at he
  rw [(Ψ).localizedChart_functionFieldMap_character b c τ ht h₁ a₁,
    Scheme.Hom.functionFieldMap_SpecMap_algebraMap (twRing)] at he
  rw [← ha, he, ha]
  simp only [CommRingCat.hom_ofHom, RingHom.coe_coe, AlgHom.toRingHom_eq_coe, AlgEquiv.coe_toAlgHom,
    mutationChartAlgEquiv_single, a₁, AddEquiv.apply_symm_apply, map_mul, map_add, map_one,
    map_zpow₀, Scheme.Hom.functionFieldMap_algebraMap K]
  have hpow (u : L₀ˣ) (n : ℤ) :
      incl(L₀) (Units.val (u ^ n)) = (incl(L₀) u.val) ^ n := by
    calc
      _ = (Units.map (incl(L₀)).toMonoidHom (u ^ n)).val := rfl
      _ = _ := by
        rw [map_zpow, Units.val_zpow_eq_zpow_val]
        rfl
  have hc : (j₀ ≫ (U₀).ι).functionFieldMap (Φ.functionFieldCharacter K (ofAdd a)) =
      incl(L₀) (algebraMap (R(σ)) L₀ (single a₀ 1)) :=
    Φ.localizedChart_functionFieldMap_character b c σ hs h₀ a₀
  have hm : (j₀ ≫ (U₀).ι).functionFieldMap (Φ.functionFieldCharacter K (ofAdd m)) =
      incl(L₀) (algebraMap (R(σ)) L₀ (single q(σ,hs) 1)) := by
    have hq : (q(σ,hs)).val = m := mutationChartCharacter_false b
    rw [← hq]
    exact Φ.localizedChart_functionFieldMap_character b c σ hs h₀ q(σ,hs)
  rw [hpow]
  -- Reduce the Boolean chart choice while keeping the localization ring fixed.
  change incl(L₀) (algebraMap (R(σ)) L₀ (single a₀ 1)) *
    incl(L₀) (Units.val (awayBinomialUnit 1 c q(σ,hs))) ^ (-a₁.val v) = _
  rw [coe_mutationZeroBinomial Φ b c hpos, hc, hm, ha]

end TauCeti.Toric.Fan
