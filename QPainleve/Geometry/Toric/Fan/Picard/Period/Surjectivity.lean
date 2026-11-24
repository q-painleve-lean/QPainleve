/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Period.CenterVariation
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.Basic

import QPainleve.AlgebraicGeometry.Cohomology.Projective
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.IntersectionNumber.ClosedPoint
import QPainleve.Geometry.Toric.Fan.Boundary.ProjectiveLine
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveLine.Basic
import TauCeti.AlgebraicGeometry.Curves.ProjectiveLine
import TauCeti.AlgebraicGeometry.LineBundle.BaseChange
import TauCeti.AlgebraicGeometry.Scheme.DiscreteValuationStalk
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.PicZero
import TauCeti.LinearAlgebra.Submodule.Primitive

/-!
# Surjectivity of periods of ordered toric blowups

The marked class of a charge relation restricts to a multidegree-zero line bundle
on the fixed boundary of the ordered internal blowup model. Its period varies by
the inverse restriction of the center character to the charge kernel. Every
character of that kernel is realized by some choice of centers.

The comparison with the period after a nodal contraction uses the marked restriction
and oriented conductor subdivision formulas. The center calculation follows
[Gross, Hacking and Keel, Proposition 2.9](https://arxiv.org/html/1211.6367v5#S2).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower TopologicalSpace
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData
open Scheme (IdealSheafData NodalCycleNumbering)

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] {n : ℕ}
  (hΦ : Φ.IsRegular) (b : Module.Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Z" => Φ.algebraicRealization
local notation "D" => Fan.boundaryIdeal Φ inferInstance
local notation "C" => IdealSheafData.subscheme D
local notation "ν" => IdealSheafData.blowupToBase (Scheme.singularLocus ℂ C)
local notation "K" => LinearMap.ker (rayChargeMap s)
local notation "PicZero" => MonoidHom.ker (pullbackHom ν)
local notation "hdim" => (Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2))
local notation "J[" c "]" => (fun j ↦ Ray.internalCenter b (s j) (c j))
local notation "model[" c "]" => alongBoundary (subschemeι D) (J[c])
local notation "I[" ρ "," c "]" =>
  LineBundleClass.mk
    (IsEffectiveCartier.toInvertibleSheaf (Subtype.property (Ray.internalCenter b ρ c)))

variable [PrestableFamily ((Φ.boundaryIdeal inferInstance).subscheme ↘ Spec (.of ℂ))]

include hΦ b in
private theorem normalizedComponent_genus_eq_zero
    (v : irreducibleComponents (Scheme.singularLocus ℂ C).blowup) :
    ((C).blowupComponent v).toScheme.genus ℂ = 0 := by
  obtain ⟨ρ, rfl⟩ := (Φ.boundaryNormalizationComponentEquiv hΦ).surjective v
  let e := ρ.boundaryNormalizationComponentIso hΦ
  let : IsProper ((Φ.rayBoundaryIdeal hΦ ρ).subscheme ↘ S) :=
    ρ.isProper_boundaryComponent_of_prestableFamily hΦ
  let p := ρ.boundaryIsoProjectiveLine hΦ hdim (b.detDualEquiv_self _)
    (ρ.surjective_detCharacter b)
  let : e.hom.IsOver S := ρ.isOver_boundaryNormalizationComponentIso_hom hΦ
  let : p.hom.IsOver S := ρ.isOver_boundaryIsoProjectiveLine_hom hΦ hdim
    (b.detDualEquiv_self _) (ρ.surjective_detCharacter b)
  have h := (e.hom ≫ p.hom).finrank_cohomology_trivial_of_isIso ℂ 1
  have hp := projectiveLine.genus_eq_zero ℂ
  rw [Scheme.genus_def] at hp ⊢
  exact h.trans hp

include b in
private theorem ray_isCurveOver (ρ : Φ.Ray) :
    (Φ.rayBoundaryIdeal hΦ ρ).subscheme.IsCurveOver ℂ := by
  let : IsProper ((Φ.rayBoundaryIdeal hΦ ρ).subscheme ↘ S) :=
    ρ.isProper_boundaryComponent_of_prestableFamily hΦ
  let : (projectiveLine ℂ).IsCurveOver ℂ := projectiveLine.isCurveOver ℂ
  let p := ρ.boundaryIsoProjectiveLine hΦ hdim (b.detDualEquiv_self _)
    (ρ.surjective_detCharacter b)
  have hp := p.hom.topologicalKrullDim_eq_of_isClosedMap_of_surjective p.hom.isClosedMap
  exact Scheme.isCurveOver_iff.mpr
    ⟨inferInstance, inferInstance, hp.trans (Scheme.IsCurveOver.topologicalKrullDim_eq_one ℂ)⟩

include b in
private theorem eulerDegree_pullback_internalCenter (ρ τ : Φ.Ray) (c : ℂˣ) :
    eulerDegree ℂ (pullback (τ.boundaryComponentι hΦ) (I[ρ,c])) =
      if ρ = τ then -1 else 0 := by
  classical
  have := ray_isCurveOver hΦ b τ
  let z := ρ.binomialCenterOnBoundary hdim (b.detDualEquiv_self _) (ρ.surjective_detCharacter b) c
  have : IsClosedImmersion z := ρ.isClosedImmersion_binomialCenterOnBoundary
    hdim (b.detDualEquiv_self _) (ρ.surjective_detCharacter b) c
  let q := z (IsLocalRing.closedPoint ℂ)
  have hq : IsClosed ({q} : Set C) := by
    have hrange : Set.range z = {q} :=
      Set.range_eq_singleton fun y ↦ congrArg z (Subsingleton.elim y _)
    rw [← hrange]
    exact z.isClosedEmbedding.isClosed_range
  have hJ : (ρ.internalCenter b c).val = ((C).fromSpecResidueField q).ker :=
    (ρ.internalCenter_val b c).trans z.ker_eq_ker_fromSpecResidueField
  have hI : ((C).fromSpecResidueField q).ker.IsEffectiveCartier :=
    hJ ▸ (ρ.internalCenter b c).property
  rw [mk_toInvertibleSheaf_congr _ hI hJ, ← intersectionNumber_def,
    intersectionNumber_mk_ker_fromSpecResidueField (τ.boundaryComponentι hΦ) hq hI]
  have hmem : q ∈ Set.range (τ.boundaryComponentι hΦ) ↔ ρ = τ :=
    ρ.binomialCenterOnBoundary_mem_range_boundaryComponentι_iff hΦ hdim
      (b.detDualEquiv_self _) (ρ.surjective_detCharacter b) c τ
  simp only [hmem]

variable [Φ.algebraicRealization.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ Spec (.of ℂ))]

local notation "A" => Chow.intersectionBilinForm ℂ Z
local notation "Qform" =>
  LinearMap.BilinForm.prod A (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin n → ℤ)))

variable [LinearMap.IsPerfPair
  ((Chow.intersectionBilinForm ℂ Φ.algebraicRealization).prod
    (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin n → ℤ))))]

local notation "mark" =>
  LinearEquiv.symm (boundaryOrthogonalEquivChargeKernel hΦ s Qform)
local notation "markedClass[" c "]" =>
  LinearMap.comp (QPainleve.BlowupTower.picardHom (WithBoundary.toTower (Sigma.snd (model[c]))))
    (LinearMap.comp
      (Submodule.subtype
        (LinearMap.BilinForm.orthogonal Qform (LinearMap.range (markedBoundaryMap hΦ s))))
      (LinearEquiv.toLinearMap mark))

private def orderedRestriction (c : Fin n → ℂˣ) :
    Multiplicative K →* LineBundleClass C :=
  (pullbackHom (model[c]).2.boundaryι).comp (markedClass[c]).toAddMonoidHom.toMultiplicativeLeft

omit [PrestableFamily ((Φ.boundaryIdeal inferInstance).subscheme ↘ Spec (.of ℂ))] in
private theorem orderedRestriction_apply (c : Fin n → ℂˣ) (x : K) :
    orderedRestriction hΦ b s c (Multiplicative.ofAdd x) =
      pullback (subschemeι D) ((mark x).val.1).toMul *
        ∏ j, I[s j,c j] ^ (x : Fin n → ℤ) j := by
  rw [orderedRestriction, MonoidHom.comp_apply, pullbackHom_apply]
  -- Evaluate the marked class as a Picard pullback with its exceptional coefficients.
  change pullback (model[c]).2.boundaryι (((model[c]).2.toTower.picardHom (mark x).val).toMul) = _
  rw [← Prod.mk.eta (p := (mark x).val), pullback_picardHom_alongBoundary,
    boundaryOrthogonalEquivChargeKernel_symm_snd]
  simp only [Pi.neg_apply, neg_neg]

private theorem orderedRestriction_mem_ker (c : Fin n → ℂˣ) (x : K) :
    orderedRestriction hΦ b s c (Multiplicative.ofAdd x) ∈ PicZero := by
  classical
  rw [MonoidHom.mem_ker, pullbackHom_apply, (C).pullback_blowupToBase_singularLocus_eq_one_iff
      (normalizedComponent_genus_eq_zero hΦ b), orderedRestriction_apply]
  intro v
  obtain ⟨ρ, rfl⟩ := (Φ.boundaryNormalizationComponentEquiv hΦ).surjective v
  let e := ρ.boundaryNormalizationComponentIso hΦ
  have := ray_isCurveOver hΦ b ρ
  rw [← ρ.boundaryNormalizationComponentIso_hom_boundaryComponentι hΦ,
    ← pullback_comp, eulerDegree_pullback_of_isIso e.hom (comp_over e.hom S)]
  let R := (Φ.rayBoundaryIdeal hΦ ρ).subscheme
  let : TauCeti.AlgebraicGeometry.IsRegular R := Φ.isRegular_rayBoundary hΦ ρ
  have : IsNoetherian R := Scheme.IsCurveOver.isNoetherian ℂ R
  have : R.IsProjectiveOver ℂ :=
    Scheme.IsProjectiveOver.of_isClosedImmersion ℂ (Φ.rayBoundaryIdeal hΦ ρ).subschemeι
  let : Fact (∀ y : R, Order.coheight y ≤ 1) := ⟨fun y ↦ by
    exact_mod_cast (coheight_le_topologicalKrullDim y).trans
      (Scheme.IsCurveOver.topologicalKrullDim_eq_one ℂ).le⟩
  let := Scheme.Modules.moduleFinite_cohomology_of_isProjectiveOver ℂ
    (InvertibleSheaf.trivial R).obj 1
  let d := eulerDegreeHom ℂ R
  have hd (L : LineBundleClass (Φ.rayBoundaryIdeal hΦ ρ).subscheme) :
      d (Additive.ofMul L) = eulerDegree ℂ L := by
    rw [eulerDegreeHom_apply, toMul_ofMul]
  have ht : d (Additive.ofMul (pullback (ρ.boundaryComponentι hΦ)
        (pullback (subschemeι D) ((mark x).val.1).toMul))) =
      ∑ j, (if s j = ρ then 1 else 0) * (x : Fin n → ℤ) j := by
    have h := boundaryOrthogonalEquivChargeKernel_symm_fst_pairing hΦ s A x (Pi.single ρ 1)
    have hZ := topologicalKrullDim_eq_of_smoothOfRelativeDimension (Z ↘ S) (n := 2)
    let := (Z ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    simp only [rayDivisorToPicard_single, one_smul, Chow.intersectionBilinForm_apply,
      toMul_ofMul, Pi.single_apply] at h
    rw [hd, pullback_comp,
      ρ.boundaryComponentι_subschemeι, ← intersectionNumber_def,
      Fan.rayBoundaryIdeal_def]
    rw [← Chow.classIntersectionNumber_primeDivisorClass_eq_intersectionNumber ℂ hZ,
      Chow.classIntersectionNumber_comm]
    exact h
  -- The degree homomorphism adds the degrees of the tensor factors.
  rw [← hd]
  rw [pullback_mul, ofMul_mul, map_add, ht, ← pullbackHom_apply, map_prod, ofMul_prod, map_sum]
  simp only [pullbackHom_apply, pullback_zpow, ofMul_zpow, map_zsmul,
    hd, eulerDegree_pullback_internalCenter hΦ b]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : s j = ρ
  · simp only [hj, ↓reduceIte, one_mul, smul_eq_mul, mul_neg, mul_one, add_neg_cancel]
  · simp only [hj, ↓reduceIte, zero_mul, smul_zero, add_zero]

variable {α : Type*}
  {p : α → ((Φ.boundaryIdeal inferInstance).subscheme ↘ Spec (.of ℂ)).smoothLocus}
  {a : ℕ} [NeZero a]
  (B : NodalCycleNumbering p a)

/-- Restriction of marked charge classes on the ordered internal blowup to the fixed
toric boundary, with values in the kernel of pullback to the normalization. -/
def orderedBoundaryRestriction (c : Fin n → ℂˣ) : Multiplicative K →* PicZero :=
  (orderedRestriction hΦ b s c).codRestrict PicZero fun x ↦
    orderedRestriction_mem_ker hΦ b s c x.toAdd

/-- The marked restriction pulls back the line-bundle class in the ordered Picard
marking along the boundary embedding. -/
@[simp]
theorem coe_orderedBoundaryRestriction (c : Fin n → ℂˣ) (x : K) :
    (orderedBoundaryRestriction hΦ b s c (Multiplicative.ofAdd x)).val =
      pullback (model[c]).2.boundaryι ((markedClass[c] x).toMul) := by
  rw [orderedBoundaryRestriction, MonoidHom.codRestrict_apply, Subgroup.coe_mk,
    orderedRestriction, MonoidHom.comp_apply, pullbackHom_apply]
  rfl

/-- The period character obtained by restricting marked charge classes on the ordered
internal blowup to its boundary, identified with the original toric boundary. -/
def orderedBoundaryPeriod (c : Fin n → ℂˣ) : Multiplicative K →* ℂˣ :=
  ((C).nodalPicardCycleMulEquiv B.endpoint_eq).toMonoidHom.comp
    (orderedBoundaryRestriction hΦ b s c)

/-- The ordered period is the oriented gluing product of the marked restriction. -/
@[simp]
theorem orderedBoundaryPeriod_apply (c : Fin n → ℂˣ) (x : Multiplicative K) :
    orderedBoundaryPeriod hΦ b s B c x =
      (C).nodalPicardCycleMulEquiv B.endpoint_eq (orderedBoundaryRestriction hΦ b s c x) := (rfl)

variable (r : ZMod a ≃ Φ.Ray)
  (hcomp : ∀ j, (Φ.boundaryIdeal inferInstance).subscheme.dualGraphVertexEquiv p (B.vertex j) =
    Φ.boundaryNormalizationComponentEquiv hΦ (r j))
  (hdet : ∀ j, b.detDualEquiv (r j).primitiveGenerator (r (j + 1)).primitiveGenerator = 1)
  (hnodes : ∀ j, ∃ σ : Φ.cones, (r j).toCone ≤ σ ∧ (r (j + 1)).toCone ≤ σ ∧
    (Φ.boundaryIdeal inferInstance).subschemeι
      ((Φ.boundaryIdeal inferInstance).subscheme.dualGraphEdgeEquiv p (B.edge j)).val =
      Φ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ))

include hcomp hdet hnodes in
/-- In the positive determinant orientation, the ratio of ordered boundary periods
is the inverse center ratio evaluated at the charge relation. -/
theorem orderedBoundaryPeriod_div (c d : Fin n → ℂˣ) (x : K) :
    orderedBoundaryPeriod hΦ b s B c (Multiplicative.ofAdd x) /
      orderedBoundaryPeriod hΦ b s B d (Multiplicative.ofAdd x) =
        ∏ j, (d j / c j) ^ (x : Fin n → ℤ) j := by
  obtain ⟨L, hL, hperiod⟩ := exists_prod_internalCenterRatio_nodalPicardCycleMulEquiv hΦ r
    B.endpoint_eq hcomp b hdet hnodes s c d (x : Fin n → ℤ)
  have hratio : orderedBoundaryRestriction hΦ b s c (Multiplicative.ofAdd x) /
      orderedBoundaryRestriction hΦ b s d (Multiplicative.ofAdd x) = L := by
    apply Subtype.ext
    rw [Subgroup.coe_div, hL]
    -- The toric part is the same for both boundary restrictions.
    change orderedRestriction hΦ b s c (Multiplicative.ofAdd x) /
      orderedRestriction hΦ b s d (Multiplicative.ofAdd x) = _
    rw [orderedRestriction_apply, orderedRestriction_apply, mul_div_mul_left_eq_div]
  rw [orderedBoundaryPeriod_apply, orderedBoundaryPeriod_apply, ← hperiod, ← hratio, map_div]

include hcomp hdet hnodes in
/-- Multiplying the marked period by the restricted center monomial gives a value
independent of the reference center. -/
theorem orderedBoundaryPeriod_mul_torusCharacter (c d : Fin n → ℂˣ) (x : K) :
    orderedBoundaryPeriod hΦ b s B c (Multiplicative.ofAdd x) *
        torusCharacter c (x : Fin n → ℤ) =
      orderedBoundaryPeriod hΦ b s B d (Multiplicative.ofAdd x) *
        torusCharacter d (x : Fin n → ℤ) := by
  have h := orderedBoundaryPeriod_div hΦ b s B r hcomp hdet hnodes c d x
  simp only [div_zpow, Finset.prod_div_distrib, ← torusCharacter_def] at h
  simpa only [mul_comm (torusCharacter d _)] using div_eq_div_iff_mul_eq_mul.mp h

include hcomp hdet hnodes in
/-- Every charge-kernel character is the period of an ordered internal blowup in
the positive determinant orientation. All choices of centers, including repetitions,
are allowed. -/
theorem orderedBoundaryPeriod_surjective :
    Function.Surjective (orderedBoundaryPeriod hΦ b s B) := by
  classical
  intro a
  have := Φ.lattice.free
  let e := (rayChargeMap s).quotKerEquivRange
  have hfree : Module.IsTorsionFree ℤ ((Fin n → ℤ) ⧸ K) :=
    e.injective.moduleIsTorsionFree _ (map_smul e)
  obtain ⟨T, hT⟩ := (Submodule.exists_isCompl_iff_isTorsionFree_quotient K).mpr hfree
  let χ := (orderedBoundaryPeriod hΦ b s B 1 / a).comp
    ((K).projectionOnto T hT).toAddMonoidHom.toMultiplicative
  let c (j : Fin n) := χ (Multiplicative.ofAdd (Pi.single j 1))
  have hc (μ : Fin n → ℤ) : torusCharacter c μ = χ (Multiplicative.ofAdd μ) := by
    conv_rhs => rw [pi_eq_sum_univ' μ, ofAdd_sum, map_prod]
    simp only [torusCharacter_def, c, ofAdd_zsmul, map_zpow]
  refine ⟨c, MonoidHom.ext fun x ↦ ?_⟩
  have h := orderedBoundaryPeriod_mul_torusCharacter hΦ b s B r hcomp hdet hnodes c 1 x.toAdd
  rw [torusCharacter_one, mul_one, hc] at h
  have hproj : (K).projectionOnto T hT (x.toAdd : Fin n → ℤ) = x.toAdd :=
    Submodule.projectionOnto_apply_left hT x.toAdd
  -- The character extension restricts to the prescribed ratio on the kernel.
  have hχ : χ (Multiplicative.ofAdd (x.toAdd : Fin n → ℤ)) =
      orderedBoundaryPeriod hΦ b s B 1 x / a x := by
    simp only [χ, MonoidHom.comp_apply]
    change (orderedBoundaryPeriod hΦ b s B 1 / a)
      (Multiplicative.ofAdd ((K).projectionOnto T hT (x.toAdd : Fin n → ℤ))) = _
    rw [hproj, MonoidHom.div_apply, ofAdd_toAdd]
  rw [hχ, ofAdd_toAdd] at h
  simpa only [div_div_cancel] using eq_div_iff_mul_eq'.mpr h

section Contraction

variable {c : Fin n → ℂˣ} {X Y : Scheme}
  [X.Over (Spec (.of ℂ))] [X.IsProjectiveOver ℂ] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of ℂ))]
  [LinearMap.IsPerfPair (Chow.intersectionBilinForm ℂ X)]
  {D₀ : X.IdealSheafData} {d : ℕ} {T : QPainleve.BlowupTower X d Y}
  (hT : IsNodalBoundaryTower D₀ (X ↘ Spec (.of ℂ)) (𝟙 X) T)
  (e : Y ≅ (alongBoundary (Φ.boundaryIdeal inferInstance).subschemeι
    (fun j ↦ (s j).internalCenter b (c j))).1)
  (he : e.inv ≫ T.toBase ≫ (X ↘ Spec (.of ℂ)) =
    (alongBoundary (Φ.boundaryIdeal inferInstance).subschemeι
      (fun j ↦ (s j).internalCenter b (c j))).2.toTower.toBase ≫
      (Φ.algebraicRealization ↘ Spec (.of ℂ)))
  (hD : ((D₀.comap T.toBase).comap e.inv).support =
    (alongBoundary (Φ.boundaryIdeal inferInstance).subschemeι
      (fun j ↦ (s j).internalCenter b (c j))).2.boundaryι.ker.support)
  [PrestableFamily (D₀.subscheme ↘ Spec (.of ℂ))]
  (hCartier : D₀.IsEffectiveCartier)
  (hgenus : ∀ v : irreducibleComponents (D₀.subscheme.singularLocus ℂ).blowup,
    ((D₀.subscheme).blowupComponent v).toScheme.genus ℂ = 0)
  {β : Type*} {q : β → (D₀.subscheme ↘ Spec (.of ℂ)).smoothLocus} {k : ℕ} [NeZero k]
  (B₀ : NodalCycleNumbering q k)

local notation "C₀" => IdealSheafData.subscheme D₀
local notation "g" => toricBoundaryToBase (J[c]) e hD
local notation "ν₀" => IdealSheafData.blowupToBase (Scheme.singularLocus ℂ C₀)
local notation "branch[" W "]" => Scheme.branchSchemeToBlowup ℂ W
local notation "nodes[" W "]" => IdealSheafData.subscheme (Scheme.singularLocus ℂ W)
local notation "m" => (fun j ↦
  LinearMap.toAddMonoidHom (b.detDualEquiv (Ray.primitiveGenerator (s j))))

/-- The ordered period agrees with the period on the contracted surface whenever
the boundary projection is an oriented conductor subdivision. -/
theorem markedBoundaryPeriod_eq_orderedBoundaryPeriod
    {gν : ((C).singularLocus ℂ).blowup ⟶ ((C₀).singularLocus ℂ).blowup}
    (hν : CommSq ν gν g ν₀)
    (hnode : Set.MapsTo g ((C).singularLocus ℂ).support ((C₀).singularLocus ℂ).support)
    (keep : nodes[C₀] ↪ nodes[C])
    (hkeep : ∀ z j,
      gν (branch[C] ((C).branchOrderOfDualGraph p B.order (keep z) j).val) =
        branch[C₀] ((C₀).branchOrderOfDualGraph q B₀.order z j).val)
    (hcollapse : ∀ z ∉ Set.range keep,
      gν (branch[C] ((C).branchOrderOfDualGraph p B.order z 1).val) =
        gν (branch[C] ((C).branchOrderOfDualGraph p B.order z 0).val)) :
    markedBoundaryPeriod hΦ b s hT e he hD hCartier hgenus B₀ =
      orderedBoundaryPeriod hΦ b s B c := by
  apply MonoidHom.ext
  intro x
  rw [← ofAdd_toAdd x, orderedBoundaryPeriod_apply]
  obtain ⟨L, hL, hperiod⟩ := exists_pullback_markedBoundaryPeriod hΦ b s hT e he hD
    hCartier hgenus B₀ B hν hnode keep hkeep hcollapse x.toAdd
  rw [← hperiod]
  apply congrArg ((C).nodalPicardCycleMulEquiv B.endpoint_eq)
  apply Subtype.ext
  simp only [hL, orderedBoundaryRestriction, MonoidHom.codRestrict_apply, Subgroup.coe_mk,
    orderedRestriction_apply]
  refine pullback_toricBoundaryToBase_picardBoundaryOrthogonalEquivChargeKernel_symm (J[c]) e hD
    hΦ hdim s m (fun j ↦ b.detDualEquiv_self _) (fun j ↦ (s j).surjective_detCharacter b)
    c (fun j ↦ (s j).internalCenter_val b (c j)) hT he x.toAdd (mark x.toAdd).val.1 ?_
  simpa only [Chow.intersectionBilinForm_apply] using
    boundaryOrthogonalEquivChargeKernel_symm_fst_pairing hΦ s A x.toAdd

end Contraction

end TauCeti.Toric.Fan
