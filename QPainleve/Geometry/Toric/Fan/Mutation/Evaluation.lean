/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.RationalMap
public import QPainleve.Algebra.Cluster.XMutation.Evaluation
public import QPainleve.Geometry.Toric.Fan.Evaluation
public import QPainleve.Geometry.Toric.Fan.Mutation.Resolution
public import QPainleve.SignedClusterModularGroup.CenterMutation

import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import QPainleve.Algebra.Cluster.Word.Chart
import QPainleve.Algebra.MvPolynomial.Laurent.FiniteType
import QPainleve.AlgebraicGeometry.RationalMap.Affine
import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic
import QPainleve.AlgebraicGeometry.RationalMap.Modification
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition

/-!
# Cluster X evaluation at fixed toric centers

Specializing the Laurent mutation chart at fixed centers sends its coordinates to scaled
determinant characters. Pullback along the toric elementary transformation commutes with
this specialization and cluster X mutation. The localization inverts the pivot binomial,
so the comparison takes place on the common rational domain. The evaluation maps
to this chart commute with the global isomorphism of the pivot blowups, also
after dominant refinements of the source blowup and after descent through
a modification of the source.

The character and charge formulas used here are those of Gross, Hacking and Keel,
[*Birational geometry of cluster algebras*, (1.2), (2.9), and §3.1]
(https://arxiv.org/html/1309.2573v2#S3.SS1).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative PointedCone
open QPainleve.Cluster TauCeti.AlgebraicGeometry TauCeti.LaurentRing

namespace TauCeti.Toric.Fan

variable (k : Type) [Field k]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {l : N →+ V} (Φ : Fan l) (b : Module.Basis (Fin 2) ℤ N)
  {ι : Type} [DecidableEq ι] (s : ι → Φ.Ray) (p : ι)
  (c : Multiplicative (ι → ℤ) →* kˣ)

local notation "u" j:arg => Ray.primitiveGenerator (Phi := Φ) (s j)
local notation "χ(" x ")" => LinearMap.toAddMonoidHom (b.detDualEquiv x)
local notation "c[" j "]" => c (ofAdd (Pi.single j 1))
local notation "K(" F ")" => Scheme.functionField (Fan.finiteFanScheme k F)
local notation "hΦ" => Nonempty.intro (Ray.toCone Φ (s p))

omit [DecidableEq ι] in
private theorem pivotCharacter_ne_zero : χ(u p) ≠ 0 := by
  intro h
  apply (s p).primitiveGenerator_ne_zero
  apply b.detDualEquiv.injective
  ext x
  simpa only [map_zero, LinearMap.zero_apply, LinearMap.toAddMonoidHom_coe,
    AddMonoidHom.zero_apply] using DFunLike.congr_fun h x

/-- Specialization of the localized X chart at a fixed center character. The pivot binomial
is nonzero because the pivot ray has a nonzero primitive generator. -/
def mutationChartEval :
    letI : Nonempty Φ.cones := hΦ
    XMutationChart k p →ₐ[k] K(Φ) := by
  let : Nonempty Φ.cones := hΦ
  let x j := Units.map (Φ.xEval k b s c).toMonoidHom (unitX j)
  refine xMutationChartEval p x ?_
  simpa [x] using (Φ.one_add_mul_functionFieldCharacter_ne_zero k (c[p] : k)
    (pivotCharacter_ne_zero Φ b s p)).isUnit

/-- The X coordinate at a fixed center is its center parameter times its charge character. -/
@[simp]
theorem mutationChartEval_X (j : ι) :
    letI : Nonempty Φ.cones := hΦ
    Φ.mutationChartEval k b s p c (algebraMap (LaurentRing k ι) (XMutationChart k p) (X j)) =
      algebraMap k K(Φ) (c[j] : k) * Φ.functionFieldCharacter k (ofAdd χ(u j)) := by
  simp [mutationChartEval]

/-- Forgetting the inverted binomial recovers evaluation on the Laurent coordinate ring. -/
@[simp]
theorem mutationChartEval_comp_algebraMap :
    letI : Nonempty Φ.cones := hΦ
    (Φ.mutationChartEval k b s p c).comp
      (IsScalarTower.toAlgHom k (LaurentRing k ι) (XMutationChart k p)) = Φ.xEval k b s c := by
  let : Nonempty Φ.cones := hΦ
  apply LaurentRing.algHom_ext
  intro j
  simp

section SchemeEvaluation

variable [Finite ι]

/-- The fixed-center X evaluation as a rational map to the open mutation chart of the
independent X torus. Its coordinates are the scaled determinant characters. -/
def mutationChartEvaluation :
    (Φ.finiteFanScheme k) ⤏ Spec (.of (XMutationChart k p)) :=
  letI : Nonempty Φ.cones := hΦ
  Scheme.RationalMap.ofAffineAlgHom (Φ.mutationChartEval k b s p c)

instance : (Φ.mutationChartEvaluation k b s p c).IsOver
    ((Φ.finiteFanScheme k) ↘ Spec (.of k)) (Spec.algebraMap k (XMutationChart k p)) := by
  let : Nonempty Φ.cones := hΦ
  unfold mutationChartEvaluation
  infer_instance

/-- The generic-point map of fixed-center evaluation is induced by specialization of the
localized Laurent chart. -/
@[simp]
theorem fromFunctionField_mutationChartEvaluation :
    letI : Nonempty Φ.cones := hΦ
    (Φ.mutationChartEvaluation k b s p c).fromFunctionField =
      Spec.map (CommRingCat.ofHom (Φ.mutationChartEval k b s p c).toRingHom) := by
  let : Nonempty Φ.cones := hΦ
  unfold mutationChartEvaluation
  exact Scheme.RationalMap.fromFunctionField_ofAffineAlgHom _

/-- Including the pivot chart into the X torus recovers the evaluation map with no
choice of pivot. -/
@[simp]
theorem mutationChartEvaluation_compHom :
    letI : Nonempty Φ.cones := hΦ
    (Φ.mutationChartEvaluation k b s p c).compHom
      (Spec.algebraMap (LaurentRing k ι) (XMutationChart k p)) = Φ.xEvaluation k b s c := by
  let : Nonempty Φ.cones := hΦ
  let incl := IsScalarTower.toAlgHom k (LaurentRing k ι) (XMutationChart k p)
  have heval : (Φ.mutationChartEval k b s p c).comp incl = Φ.xEval k b s c :=
    Φ.mutationChartEval_comp_algebraMap k b s p c
  apply Scheme.RationalMap.eq_of_fromFunctionField_eq
  unfold mutationChartEvaluation
  rw [fromFunctionField_xEvaluation]
  have hincl : Spec.algebraMap (LaurentRing k ι) (XMutationChart k p) =
      Spec.map (CommRingCat.ofHom incl.toRingHom) := by
    rw [Spec.algebraMap, Spec.map_inj]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact (IsScalarTower.toAlgHom_apply k (LaurentRing k ι) (XMutationChart k p) x).symm
  rw [hincl]
  have h := Scheme.RationalMap.ofAffineAlgHom_compHom (Φ.mutationChartEval k b s p c) incl
  rw [heval] at h
  simpa only [Scheme.RationalMap.fromFunctionField_ofAffineAlgHom] using
    congrArg Scheme.RationalMap.fromFunctionField h

/-- Pullback through a subdivision preserves fixed-center evaluation into the
localized mutation chart, with the same pivot label and binomial. The comparison
holds after any dominant morphism into the subdividing fan scheme. -/
theorem IsSubdivision.comp_mutationChartEvaluation {Ψ : Fan l}
    (h : Φ.IsSubdivision Ψ) (s : ι → Ψ.Ray) {W : Scheme} [PreirreducibleSpace W]
    (f : W ⟶ (Φ.finiteFanScheme k)) [IsDominant f] :
    letI : Nonempty Φ.cones := ⟨Ray.toCone Φ (h.liftRay (s p))⟩
    letI : Nonempty Ψ.cones := ⟨Ray.toCone Ψ (s p)⟩
    letI := h.toFanHom.isDominant_finiteFanSchemeHom_of_injective_dualMap k inferInstance (by
      intro m n hmn
      simpa only [h.toFanHom_latticeMap, AddMonoidHom.comp_id] using hmn)
    (f ≫ h.toFanHom.finiteFanSchemeHom k).toRationalMap.comp (Ψ.mutationChartEvaluation k b s p c) =
      f.toRationalMap.comp (Φ.mutationChartEvaluation k b (h.liftRay ∘ s) p c) := by
  let : Nonempty Φ.cones := ⟨Ray.toCone Φ (h.liftRay (s p))⟩
  have := h.toFanHom.isDominant_finiteFanSchemeHom_of_injective_dualMap k inferInstance (by
    intro m n hmn
    simpa only [h.toFanHom_latticeMap, AddMonoidHom.comp_id] using hmn)
  let : Nonempty Ψ.cones := ⟨Ray.toCone Ψ (s p)⟩
  let incl := Spec.algebraMap (LaurentRing k ι) (XMutationChart k p)
  have : IsOpenImmersion incl :=
    Scheme.isOpenImmersion_SpecMap_localizationAway (R := .of (LaurentRing k ι)) (1 + X p)
  simp only [← Scheme.Hom.toRationalMap_compHom, ← Scheme.RationalMap.comp_toRationalMap,
    Scheme.RationalMap.comp_assoc]
  refine congrArg (f.toRationalMap.comp ·) ?_
  apply Scheme.Hom.rationalMap_compHom_injective incl
  simpa only [incl, ← Scheme.RationalMap.comp_compHom, mutationChartEvaluation_compHom] using
    h.comp_xEvaluation k b s c

end SchemeEvaluation

variable [Fintype ι] (hOpposite : hull ℝ {l (-(s p).primitiveGenerator)} ∈ Φ.cones)

local notation "hpos" => Ray.hull_primitiveGenerator_mem (Φ := Φ) (s p)
local notation "hv" => Ray.primitiveGenerator_ne_zero (Φ := Φ) (s p)
local notation "Ψ" => mutationFan (i := l) Φ b (v := u p) hv hpos hOpposite
local notation "s′" => mutationFanCenterRays (i := l) Φ b s p hOpposite
local notation "ω" => b.detDualEquiv.toLinearMap
local notation "ε" => chargeExchangeMatrix ω (rayChargeMap s)
local notation "a(" j ")" => (ε j p)
local notation "c′" => MonoidHom.comp c (AddMonoidHom.toMultiplicative
  (AddEquiv.toAddMonoidHom (LinearEquiv.toAddEquiv (chargeMutationEquiv ε p))))
local notation "P" =>
  (mutationComplementPullbackAlgHom (i := l) Φ b (c[p] : k) (v := u p) hv hpos hOpposite :
    K(Ψ) →ₐ[k] K(Φ))
local notation "M" => xMutationChartEquiv k p (fun j ↦ a(j))

local notation "hΨ" => Nonempty.intro (Ray.toCone Ψ (s′ p))

local notation "X₀(" j ")" => Φ.mutationChartEval k b s p c
  (xMutationChartUnitX k p j : XMutationChart k p)

private theorem comp_eval_unitX_self :
    letI : Nonempty Φ.cones := hΦ
    letI : Nonempty (Fan.cones Ψ) := hΨ
    P (mutationChartEval k (l := l) Ψ b s′ p c′ (xMutationChartUnitX k p p : XMutationChart k p)) =
      (X₀(p))⁻¹ := by
  let : Nonempty Φ.cones := hΦ
  let : Nonempty (Fan.cones Ψ) := hΨ
  have hchar : χ(-(u p)) = -χ(u p) := by
    ext x
    simp only [LinearMap.toAddMonoidHom_coe, AddMonoidHom.neg_apply, map_neg,
      LinearMap.neg_apply]
  simp only [val_xMutationChartUnitX, mutationChartEval_X]
  rw [mutationFanCenterRays_primitiveGenerator_self,
    centerMutation_character_apply_self, map_mul, AlgHom.commutes,
    mutationComplementPullbackAlgHom_apply, mutationComplementPullback_character, hchar]
  simp only [AddMonoidHom.neg_apply, LinearMap.toAddMonoidHom_coe, b.detDualEquiv_self, neg_zero,
    zpow_zero, one_mul, Units.val_inv_eq_inv_val, map_inv₀, ofAdd_neg, map_inv, mul_inv_rev,
    mul_comm]

open scoped Int in
private theorem comp_eval_unitX_of_ne {j : ι} (hj : j ≠ p) :
    letI : Nonempty Φ.cones := hΦ
    letI : Nonempty (Fan.cones Ψ) := hΨ
    P (mutationChartEval k (l := l) Ψ b s′ p c′ (xMutationChartUnitX k p j : XMutationChart k p)) =
      X₀(j) * X₀(p) ^ max (a(j)) 0 * (1 + X₀(p)) ^ (-a(j)) := by
  let : Nonempty Φ.cones := hΦ
  let : Nonempty (Fan.cones Ψ) := hΨ
  let n : ℤ := max (a(j)) 0
  have hω : (ω : LinearMap.BilinForm ℤ N).IsAlt := b.detDualEquiv_self
  have hcharge : (s′ j).primitiveGenerator = u j + n • u p := by
    rw [mutationFanCenterRays_primitiveGenerator_of_ne _ _ _ _ _ hj]
    simp only [n, chargeExchangeMatrix_apply, rayChargeMap_single, LinearEquiv.coe_coe,
      Module.Basis.detDualEquiv_apply]
  have hpair : χ(u j + n • u p) (u p) = a(j) := by
    simp [LinearMap.add_apply, LinearMap.smul_apply, b.detDualEquiv_self]
  have hchar : χ(u j + n • u p) = χ(u j) + n • χ(u p) := by
    ext x
    simp only [LinearMap.toAddMonoidHom_coe, AddMonoidHom.add_apply, AddMonoidHom.zsmul_apply,
      map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply]
  simp only [val_xMutationChartUnitX, mutationChartEval_X]
  rw [centerMutation_character_apply_of_ne _ _ _ k hω c hj,
    map_mul, AlgHom.commutes, mutationComplementPullbackAlgHom_apply,
    mutationComplementPullback_character, hcharge, hpair, hchar]
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, ofAdd_add, ofAdd_zsmul,
    map_zpow, n, posPart_def, mul_zpow]
  -- Treat the two pivot factors as field elements for the final rearrangement.
  generalize algebraMap k K(Φ) (c[p] : k) = cp,
    Φ.functionFieldCharacter k (ofAdd χ(u p)) = zp
  ring

/-- The actual toric mutation pullback commutes with fixed-center X evaluation on the
whole localized Laurent chart. The target uses the mutated rays and the monomial change
of center parameters. -/
theorem mutationComplementPullback_comp_mutationChartEval :
    letI : Nonempty Φ.cones := hΦ
    letI : Nonempty (Fan.cones Ψ) := hΨ
    AlgHom.comp P (mutationChartEval k (l := l) Ψ b s′ p c′) =
      (Φ.mutationChartEval k b s p c).comp (AlgEquiv.toAlgHom M) := by
  let : Nonempty Φ.cones := hΦ
  let : Nonempty (Fan.cones Ψ) := hΨ
  apply Localization.algHom_ext
  apply LaurentRing.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, Algebra.algHom, IsScalarTower.toAlgHom_apply,
    ← val_xMutationChartUnitX, AlgEquiv.toAlgHom_apply]
  let evalUnits := Units.map (Φ.mutationChartEval k b s p c : XMutationChart k p →* K(Φ))
  by_cases hj : j = p
  · subst j
    rw [comp_eval_unitX_self]
    have h := congrArg (fun x ↦ (evalUnits x : K(Φ)))
      (map_xMutationChartUnitX_self k p (fun j ↦ a(j)))
    simpa only [evalUnits, map_inv, Units.val_inv_eq_inv_val, Units.coe_map,
      MonoidHom.coe_ofClass, AlgHom.coe_toMonoidHom] using h.symm
  · rw [comp_eval_unitX_of_ne _ _ _ _ _ _ _ hj]
    have h := congrArg (fun x ↦ (evalUnits x : K(Φ)))
      (map_xMutationChartUnitX_of_ne k p (fun j ↦ a(j)) hj)
    simpa only [evalUnits, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val,
      Units.coe_map, MonoidHom.coe_ofClass, AlgHom.coe_toMonoidHom, val_xMutationChartBinomial,
      map_add, map_one] using h.symm

/-- The generic point of a fixed-center surface evaluates inside the domain of the
independent X mutation. The value there is evaluation on the mutated surface pulled
back by the elementary transformation. -/
theorem exists_lift_xRationalMap_mutate (B : SkewExchangeMatrix ι)
    (hB : ∀ j, B.matrix j p = a(j)) :
    letI : Nonempty Φ.cones := hΦ
    letI : Nonempty (Fan.cones Ψ) := hΨ
    let f := ((Generator.mutate p).toStep B).toPath.xRationalMap k
    ∃ g : Spec K(Φ) ⟶ f.toPartialMap.domain,
      g ≫ f.toPartialMap.domain.ι = (Φ.xEvaluation k b s c).fromFunctionField ∧
      g ≫ f.toPartialMap.hom = Spec.map (CommRingCat.ofHom (P).toRingHom) ≫
        ((Ψ).xEvaluation k b s′ c′).fromFunctionField := by
  let : Nonempty Φ.cones := hΦ
  let : Nonempty (Fan.cones Ψ) := hΨ
  dsimp only
  let a := Φ.mutationChartEval k b s p c
  let incl := IsScalarTower.toAlgHom k (LaurentRing k ι) (XMutationChart k p)
  have hincl : a.comp incl = Φ.xEval k b s c := Φ.mutationChartEval_comp_algebraMap k b s p c
  obtain ⟨g, hg, hg'⟩ := Quiver.Path.exists_lift_xRationalMap_mutate k B p
  have hcol : (fun j ↦ B.matrix j p) = (fun j ↦ ε j p) := funext hB
  refine ⟨Spec.map (CommRingCat.ofHom a.toRingHom) ≫ g, ?_, ?_⟩
  · rw [Category.assoc, hg]
    erw [← Spec.map_comp, fromFunctionField_xEvaluation]
    exact congrArg (fun h : LaurentRing k ι →ₐ[k] K(Φ) ↦
      Spec.map (CommRingCat.ofHom h.toRingHom)) hincl
  · rw [Category.assoc, hg', hcol]
    erw [← Spec.map_comp, fromFunctionField_xEvaluation, ← Spec.map_comp, Spec.map_inj]
    apply CommRingCat.hom_ext
    have heval := Φ.mutationComplementPullback_comp_mutationChartEval k b s p c hOpposite
    have h := congrArg (fun f ↦ AlgHom.comp f incl) heval
    dsimp only [incl] at h
    simp only [AlgHom.comp_assoc, mutationChartEval_comp_algebraMap] at h
    exact congrArg AlgHom.toRingHom h.symm

section Pivot

local notation "I₀" => Ray.mutationSourceCenterIdeal b (s p) c[p]
local notation "I₁" => Ray.mutationTargetCenterIdeal b (s p) hOpposite c[p]
local notation "e" => Ray.mutationBlowupIso b (s p) hOpposite c[p]
local notation "π₀" => Scheme.IdealSheafData.blowupToBase I₀
local notation "π₁" => Scheme.IdealSheafData.blowupToBase I₁

/-- Fixed-center X evaluation commutes with the global mutation isomorphism on the
pivot blowups, after any dominant refinement of the source. Both sides are rational
maps to the open mutation chart, so the square holds on a common dense open. -/
theorem mutationBlowupIso_mutationChartEvaluation {W : Scheme} [IsIntegral W]
    (f : W ⟶ (I₀).blowup) [IsDominant f] :
    letI : Nonempty Φ.cones := hΦ
    letI : Nonempty (Fan.cones Ψ) := hΨ
    letI := (s p).isIntegral_mutationSourceBlowup k b hOpposite c[p]
    letI := (s p).isModification_mutationSourceBlowupToBase k b hOpposite c[p]
    letI := (s p).isModification_mutationTargetBlowupToBase k b hOpposite c[p]
    (f ≫ (e).hom ≫ π₁).toRationalMap.comp ((Ψ).mutationChartEvaluation k b s′ p c′) =
      ((f ≫ π₀).toRationalMap.comp (Φ.mutationChartEvaluation k b s p c)).compHom
        (Spec.map (CommRingCat.ofHom (M).toAlgHom.toRingHom)) := by
  let : Nonempty Φ.cones := hΦ
  let : Nonempty (Fan.cones Ψ) := hΨ
  have := (s p).isIntegral_mutationSourceBlowup k b hOpposite c[p]
  have := (s p).isIntegral_mutationTargetBlowup k b hOpposite c[p]
  have := (s p).isModification_mutationSourceBlowupToBase k b hOpposite c[p]
  have := (s p).isModification_mutationTargetBlowupToBase k b hOpposite c[p]
  let g := f ≫ π₀
  let h := f ≫ (e).hom ≫ π₁
  let a := Φ.mutationChartEval k b s p c
  let a' := (Ψ).mutationChartEval k b s′ p c′
  have : IsDominant g := inferInstanceAs (IsDominant (f ≫ π₀))
  have : IsDominant h := inferInstanceAs (IsDominant (f ≫ (e).hom ≫ π₁))
  let : W.Over (Spec (.of k)) := ⟨g ≫ Φ.finiteFanSchemeToSpec k⟩
  have : g.IsOver (Spec (.of k)) := ⟨by rw [Φ.finiteFanScheme_over k]; rfl⟩
  have : h.IsOver (Spec (.of k)) := ⟨by
    rw [finiteFanScheme_over k]
    -- Use the chosen base morphism so the comparison is between the two composites.
    change h ≫ (Ψ).finiteFanSchemeToSpec k = g ≫ Φ.finiteFanSchemeToSpec k
    simpa only [h, g, Category.assoc] using
      congrArg (f ≫ ·) ((s p).mutationBlowupIso_hom_comp_toBase b hOpposite c[p])⟩
  have hfield : h.functionFieldAlgHom k = (g.functionFieldAlgHom k).comp P := by
    ext z
    simpa only [Scheme.Hom.functionFieldAlgHom_apply, AlgHom.comp_apply,
      mutationComplementPullbackAlgHom_apply, CommRingCat.comp_apply] using
      ConcreteCategory.congr_hom
        ((s p).functionFieldMap_comp_mutationBlowupIso k b hOpposite c[p] f) z
  have heval : (P).comp a' = a.comp (M).toAlgHom :=
    Φ.mutationComplementPullback_comp_mutationChartEval k b s p c hOpposite
  -- The projections are over the chosen structure morphism of the refinement.
  change h.toRationalMap.comp (Scheme.RationalMap.ofAffineAlgHom a') =
    (g.toRationalMap.comp (Scheme.RationalMap.ofAffineAlgHom a)).compHom
      (Spec.map (CommRingCat.ofHom (M).toAlgHom.toRingHom))
  simp only [Scheme.RationalMap.comp_ofAffineAlgHom, Scheme.RationalMap.ofAffineAlgHom_compHom]
  rw [hfield, AlgHom.comp_assoc, heval, AlgHom.comp_assoc]

/-- The resolved toric mutation commutes with fixed-center evaluation into the independent
X torus. On the source the X mutation is the chart isomorphism followed by the
inclusion of that chart into the torus. -/
theorem mutationBlowupIso_xEvaluation {W : Scheme} [IsIntegral W]
    (f : W ⟶ (I₀).blowup) [IsDominant f] :
    letI : Nonempty Φ.cones := hΦ
    letI : Nonempty (Fan.cones Ψ) := hΨ
    letI := (s p).isIntegral_mutationSourceBlowup k b hOpposite c[p]
    letI := (s p).isModification_mutationSourceBlowupToBase k b hOpposite c[p]
    letI := (s p).isModification_mutationTargetBlowupToBase k b hOpposite c[p]
    (f ≫ (e).hom ≫ π₁).toRationalMap.comp ((Ψ).xEvaluation k b s′ c′) =
      (((f ≫ π₀).toRationalMap.comp (Φ.mutationChartEvaluation k b s p c)).compHom
        (Spec.map (CommRingCat.ofHom (M).toAlgHom.toRingHom))).compHom
          (Spec.algebraMap (LaurentRing k ι) (XMutationChart k p)) := by
  let : Nonempty Φ.cones := hΦ
  let : Nonempty (Fan.cones Ψ) := hΨ
  have := (s p).isIntegral_mutationSourceBlowup k b hOpposite c[p]
  have := (s p).isModification_mutationSourceBlowupToBase k b hOpposite c[p]
  have := (s p).isModification_mutationTargetBlowupToBase k b hOpposite c[p]
  have h := Φ.mutationBlowupIso_mutationChartEvaluation k b s p c hOpposite f
  rw [← mutationChartEvaluation_compHom k (p := p), Scheme.RationalMap.comp_compHom, h]

/-- Fixed-center evaluations descend through the modifications in a mutation
contraction square. On the base the X-mutation equality uses the localized
source chart and the full X torus as target. The projections to the two
toric models are those of the same dominant refinement of the pivot blowup. -/
theorem exists_xEvaluation_of_mutation_contraction {X X' W : Scheme}
    [IsIntegral X] [IsIntegral X'] [IsIntegral W]
    (q : W ⟶ X) [IsModification q] (g : X ≅ X')
    (f : W ⟶ (I₀).blowup) [IsDominant f] :
    letI : Nonempty Φ.cones := hΦ
    letI : Nonempty (Fan.cones (Ψ)) := hΨ
    letI := (s p).isIntegral_mutationSourceBlowup k b hOpposite c[p]
    letI := (s p).isModification_mutationSourceBlowupToBase k b hOpposite c[p]
    letI := (s p).isModification_mutationTargetBlowupToBase k b hOpposite c[p]
    ∃ a : X ⤏ Spec (.of (XMutationChart k p)), ∃ a' : X' ⤏ Spec (.of (LaurentRing k ι)),
      q.toRationalMap.comp a =
        (f ≫ π₀).toRationalMap.comp (Φ.mutationChartEvaluation k b s p c) ∧
      (q ≫ g.hom).toRationalMap.comp a' =
        (f ≫ (e).hom ≫ π₁).toRationalMap.comp ((Ψ).xEvaluation k b s′ c′) ∧
      g.hom.toRationalMap.comp a' =
        (a.compHom (Spec.map (CommRingCat.ofHom (M).toAlgHom.toRingHom))).compHom
          (Spec.algebraMap (LaurentRing k ι) (XMutationChart k p)) := by
  let : Nonempty Φ.cones := hΦ
  let : Nonempty (Ψ).cones := hΨ
  have := (s p).isIntegral_mutationSourceBlowup k b hOpposite c[p]
  have := (s p).isModification_mutationSourceBlowupToBase k b hOpposite c[p]
  have := (s p).isModification_mutationTargetBlowupToBase k b hOpposite c[p]
  obtain ⟨a, ha, -⟩ := q.existsUnique_rationalMap_comp_eq_of_isModification
    ((f ≫ π₀).toRationalMap.comp (Φ.mutationChartEvaluation k b s p c))
  obtain ⟨a', ha', -⟩ := (q ≫ g.hom).existsUnique_rationalMap_comp_eq_of_isModification
    ((f ≫ (e).hom ≫ π₁).toRationalMap.comp ((Ψ).xEvaluation k b s′ c′))
  refine ⟨a, a', ha, ha', ?_⟩
  apply Scheme.RationalMap.comp_left_injective q.toRationalMap
  dsimp only
  simp only [← Scheme.RationalMap.comp_assoc, Scheme.RationalMap.comp_toRationalMap,
    Scheme.Hom.toRationalMap_compHom, Scheme.RationalMap.comp_compHom, ha, ha']
  exact Φ.mutationBlowupIso_xEvaluation k b s p c hOpposite f

end Pivot

end TauCeti.Toric.Fan
