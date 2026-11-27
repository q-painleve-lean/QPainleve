/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Subdivision
public import QPainleve.Geometry.Toric.Fan.Picard.Period.CenterVariation
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.Basic

import QPainleve.AlgebraicGeometry.Cohomology.Projective
import QPainleve.LinearAlgebra.Basis.DiagonalTorus
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

variable (F : Type) [Field F] [IsAlgClosed F]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] {n : ℕ}
  (hΦ : Φ.IsRegular) (b : Module.Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray)

local notation "S" => Spec (CommRingCat.of F)
local notation "Z" => (Φ.finiteFanScheme F)
local notation "D" => Fan.toricBoundaryIdeal F Φ inferInstance
local notation "C" => IdealSheafData.subscheme D
local notation "ν" => IdealSheafData.blowupToBase (Scheme.singularLocus F C)
local notation "K" => LinearMap.ker (rayChargeMap s)
local notation "PicZero" => MonoidHom.ker (pullbackHom ν)
local notation "hdim" => (Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2))
local notation "J[" c "]" => (fun j ↦ Ray.internalCenter F b (s j) (c j))
local notation "model[" c "]" => alongBoundary (subschemeι D) (J[c])
local notation "I[" ρ "," c "]" =>
  LineBundleClass.mk
    (IsEffectiveCartier.toInvertibleSheaf (Subtype.property (Ray.internalCenter F b ρ c)))

variable [PrestableFamily ((Φ.toricBoundaryIdeal F inferInstance).subscheme ↘ Spec (.of F))]

variable [(Φ.finiteFanScheme F).IsProjectiveOver F]
  [SmoothOfRelativeDimension 2 ((Φ.finiteFanScheme F) ↘ Spec (.of F))]

local notation "A" => Chow.intersectionBilinForm F Z
local notation "Qform" =>
  LinearMap.BilinForm.prod A (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin n → ℤ)))

variable [LinearMap.IsPerfPair
  ((Chow.intersectionBilinForm F (Φ.finiteFanScheme F)).prod
    (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin n → ℤ))))]

local notation "mark" =>
  LinearEquiv.symm (boundaryOrthogonalEquivChargeKernel F hΦ s Qform)
local notation "markedClass[" c "]" =>
  LinearMap.comp (QPainleve.BlowupTower.picardHom (WithBoundary.toTower (Sigma.snd (model[c]))))
    (LinearMap.comp
      (Submodule.subtype
        (LinearMap.BilinForm.orthogonal Qform (LinearMap.range (markedBoundaryMap F hΦ s))))
      (LinearEquiv.toLinearMap mark))

private def orderedRestriction (c : Fin n → Fˣ) :
    Multiplicative K →* LineBundleClass C :=
  (pullbackHom (model[c]).2.boundaryι).comp (markedClass[c]).toAddMonoidHom.toMultiplicativeLeft

omit [PrestableFamily ((Φ.toricBoundaryIdeal F inferInstance).subscheme ↘ Spec (.of F))] in
private theorem orderedRestriction_apply (c : Fin n → Fˣ) (x : K) :
    orderedRestriction F hΦ b s c (Multiplicative.ofAdd x) =
      pullback (subschemeι D) ((mark x).val.1).toMul *
        ∏ j, I[s j,c j] ^ (x : Fin n → ℤ) j := by
  rw [orderedRestriction, MonoidHom.comp_apply, pullbackHom_apply]
  -- Evaluate the marked class as a Picard pullback with its exceptional coefficients.
  change pullback (model[c]).2.boundaryι (((model[c]).2.toTower.picardHom (mark x).val).toMul) = _
  rw [← Prod.mk.eta (p := (mark x).val), pullback_picardHom_alongBoundary,
    boundaryOrthogonalEquivChargeKernel_symm_snd]
  simp only [Pi.neg_apply, neg_neg]

private theorem orderedRestriction_mem_ker (c : Fin n → Fˣ) (x : K) :
    orderedRestriction F hΦ b s c (Multiplicative.ofAdd x) ∈ PicZero := by
  classical
  rw [MonoidHom.mem_ker, pullbackHom_apply, (C).pullback_blowupToBase_singularLocus_eq_one_iff
      (boundaryNormalizationComponent_genus_eq_zero F hΦ b), orderedRestriction_apply]
  intro v
  obtain ⟨ρ, rfl⟩ := (Φ.boundaryNormalizationComponentEquiv F hΦ).surjective v
  let e := ρ.boundaryNormalizationComponentIso F hΦ
  let := ρ.isProper_boundaryComponent_of_prestableFamily F hΦ
  have := ρ.isCurveOver_boundaryComponent F hΦ hdim (b.detDualEquiv_self _)
    (ρ.surjective_detCharacter b)
  rw [← ρ.boundaryNormalizationComponentIso_hom_boundaryComponentι F hΦ,
    ← pullback_comp, eulerDegree_pullback_of_isIso e.hom (comp_over e.hom S)]
  let R := (Φ.rayDivisorIdeal F hΦ ρ).subscheme
  let : TauCeti.AlgebraicGeometry.IsRegular R := Φ.isRegular_rayBoundary F hΦ ρ
  have : IsNoetherian R := Scheme.IsCurveOver.isNoetherian F R
  have : R.IsProjectiveOver F :=
    Scheme.IsProjectiveOver.of_isClosedImmersion F (Φ.rayDivisorIdeal F hΦ ρ).subschemeι
  let : Fact (∀ y : R, Order.coheight y ≤ 1) := ⟨fun y ↦ by
    exact_mod_cast (coheight_le_topologicalKrullDim y).trans
      (Scheme.IsCurveOver.topologicalKrullDim_eq_one F).le⟩
  let := Scheme.Modules.moduleFinite_cohomology_of_isProjectiveOver F
    (InvertibleSheaf.trivial R).obj 1
  let d := eulerDegreeHom F R
  have hd (L : LineBundleClass (Φ.rayDivisorIdeal F hΦ ρ).subscheme) :
      d (Additive.ofMul L) = eulerDegree F L := by
    rw [eulerDegreeHom_apply, toMul_ofMul]
  have ht : d (Additive.ofMul (pullback (ρ.boundaryComponentι F hΦ)
        (pullback (subschemeι D) ((mark x).val.1).toMul))) =
      ∑ j, (if s j = ρ then 1 else 0) * (x : Fin n → ℤ) j := by
    have h := boundaryOrthogonalEquivChargeKernel_symm_fst_pairing F hΦ s A x (Pi.single ρ 1)
    have hZ := topologicalKrullDim_eq_of_smoothOfRelativeDimension (Z ↘ S) (n := 2)
    let := (Z ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    simp only [rayChartDivisorToPicard_single, one_smul, Chow.intersectionBilinForm_apply,
      toMul_ofMul, Pi.single_apply] at h
    rw [hd, pullback_comp,
      ρ.boundaryComponentι_subschemeι F hΦ, ← intersectionNumber_def F,
      Φ.rayDivisorIdeal_def F hΦ]
    rw [← Chow.classIntersectionNumber_primeDivisorClass_eq_intersectionNumber F hZ,
      Chow.classIntersectionNumber_comm]
    exact h
  -- The degree homomorphism adds the degrees of the tensor factors.
  rw [← hd]
  rw [pullback_mul, ofMul_mul, map_add, ht, ← pullbackHom_apply, map_prod, ofMul_prod, map_sum]
  simp only [pullbackHom_apply, pullback_zpow, ofMul_zpow, map_zsmul,
    hd, Ray.eulerDegree_pullback_internalCenter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : s j = ρ
  · simp only [hj, ↓reduceIte, one_mul, smul_eq_mul, mul_neg, mul_one, add_neg_cancel]
  · simp only [hj, ↓reduceIte, zero_mul, smul_zero, add_zero]

variable {α : Type*}
  {p : α → ((Φ.toricBoundaryIdeal F inferInstance).subscheme ↘ Spec (.of F)).smoothLocus}
  {a : ℕ} [NeZero a]
  (B : NodalCycleNumbering p a)

/-- Restriction of marked charge classes on the ordered internal blowup to the fixed
toric boundary, with values in the kernel of pullback to the normalization. -/
def orderedBoundaryRestriction (c : Fin n → Fˣ) : Multiplicative K →* PicZero :=
  (orderedRestriction F hΦ b s c).codRestrict PicZero fun x ↦
    orderedRestriction_mem_ker F hΦ b s c x.toAdd

/-- The marked restriction pulls back the line-bundle class in the ordered Picard
marking along the boundary embedding. -/
@[simp]
theorem coe_orderedBoundaryRestriction (c : Fin n → Fˣ) (x : K) :
    (orderedBoundaryRestriction F hΦ b s c (Multiplicative.ofAdd x)).val =
      pullback (model[c]).2.boundaryι ((markedClass[c] x).toMul) := by
  rw [orderedBoundaryRestriction, MonoidHom.codRestrict_apply, Subgroup.coe_mk,
    orderedRestriction, MonoidHom.comp_apply, pullbackHom_apply]
  rfl

/-- In the ordered internal blowup model, the restricted charge class is obtained by
applying the Picard marking and restricting to the strict boundary. -/
theorem coe_orderedBoundaryRestriction_eq_pullback_internalBlowupPicardMarking
    (c : Fin n → Fˣ) (x : K) :
    (orderedBoundaryRestriction F hΦ b s c (Multiplicative.ofAdd x)).val =
      pullback (internalBlowupTower F b s c).2.boundaryι
        (internalBlowupPicardMarking F b s c hΦ (mark x).val).toMul := by
  rw [coe_orderedBoundaryRestriction, internalBlowupPicardMarking_apply,
    internalBlowupTower_eq_alongBoundary]
  rfl

/-- The period character obtained by restricting marked charge classes on the ordered
internal blowup to its boundary, identified with the original toric boundary. -/
def orderedBoundaryPeriod (c : Fin n → Fˣ) : Multiplicative K →* Fˣ :=
  ((C).nodalPicardCycleMulEquiv B.endpoint_eq).toMonoidHom.comp
    (orderedBoundaryRestriction F hΦ b s c)

/-- The ordered period is the oriented gluing product of the marked restriction. -/
@[simp]
theorem orderedBoundaryPeriod_apply (c : Fin n → Fˣ) (x : Multiplicative K) :
    orderedBoundaryPeriod F hΦ b s B c x =
      (C).nodalPicardCycleMulEquiv B.endpoint_eq (orderedBoundaryRestriction F hΦ b s c x) := (rfl)

private theorem ne_center_of_orderedBoundaryPeriod_injective {c : Fin n → Fˣ}
    (hc : Function.Injective (orderedBoundaryPeriod F hΦ b s B c))
    {j l : Fin n} (hjl : j ≠ l) (hray : s j = s l) : c j ≠ c l := by
  classical
  intro hcenter
  let x : K := ⟨Pi.single j 1 - Pi.single l 1, by
    simp only [LinearMap.mem_ker, map_sub, rayChargeMap_single, hray, sub_self]⟩
  have hx (u : Fin n → ℤ) : ∑ t, u t * (x : Fin n → ℤ) t = u j - u l := by
    simp [x, mul_sub, Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_zero]
  obtain ⟨_, _, huniq⟩ :=
    existsUnique_rayDivisorToPicard_pairing_eq_charge F hΦ s A x
  have htoric : (mark x).val.1 = 0 := by
    have hzero (u : Φ.Ray → ℤ) : A (Φ.rayChartDivisorToPicard F hΦ u) 0 =
        ∑ t, u (s t) * (x : Fin n → ℤ) t := by
      have hsum := hx (u ∘ s)
      simpa [Function.comp_apply, hray] using hsum.symm
    exact (huniq _ (boundaryOrthogonalEquivChargeKernel_symm_fst_pairing F hΦ s A x)).trans
      (huniq _ hzero).symm
  have hsingle (v : Fin n) :
      ∏ t, I[s t,c t] ^ ((Pi.single v 1 : Fin n → ℤ) t) = I[s v,c v] := by
    rw [Finset.prod_eq_single v]
    · simp
    · intro u _ huv
      simp [Pi.single_eq_of_ne huv]
    · simp
  have hprod : ∏ t, I[s t,c t] ^ (x : Fin n → ℤ) t = 1 := by
    simp only [x, Pi.sub_apply, zpow_sub, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
      hsingle, hray, hcenter, mul_inv_cancel]
  have hres : orderedBoundaryRestriction F hΦ b s c (Multiplicative.ofAdd x) = 1 := by
    apply Subtype.ext
    -- Compute in the ambient Picard group using the ordered restriction formula.
    change orderedRestriction F hΦ b s c (Multiplicative.ofAdd x) = 1
    rw [orderedRestriction_apply, htoric, hprod, toMul_zero, pullback_one, mul_one]
  have hperiod : orderedBoundaryPeriod F hΦ b s B c (Multiplicative.ofAdd x) = 1 := by
    rw [orderedBoundaryPeriod_apply, hres, map_one]
  have hzero := Multiplicative.ofAdd.injective
    (hc (hperiod.trans ((orderedBoundaryPeriod F hΦ b s B c).map_one.symm)))
  have hval := congrArg (fun y : K ↦ (y : Fin n → ℤ) j) hzero
  simp [x, hjl] at hval

/-- An injective ordered boundary period forces the original boundary centers at
distinct labels to have disjoint supports. -/
theorem pairwise_disjoint_internalCenters_of_orderedBoundaryPeriod_injective {c : Fin n → Fˣ}
    (hc : Function.Injective (orderedBoundaryPeriod F hΦ b s B c)) :
    Pairwise fun j l ↦ Disjoint ((J[c] j).val.support : Set C) ((J[c] l).val.support : Set C) := by
  intro j l hjl
  have hpair : (s j, c j) ≠ (s l, c l) := fun h ↦
    ne_center_of_orderedBoundaryPeriod_injective F hΦ b s B hc hjl (congrArg Prod.fst h)
      (congrArg Prod.snd h)
  simpa only [Scheme.IdealSheafData.map_id] using
    (disjoint_support_map_internalCenter_iff F b (𝟙 C) (s j) (s l) (c j) (c l)).mpr hpair

variable (r : ZMod a ≃ Φ.Ray)
  (hcomp : ∀ j,
    (Φ.toricBoundaryIdeal F inferInstance).subscheme.dualGraphVertexEquiv p (B.vertex j) =
      Φ.boundaryNormalizationComponentEquiv F hΦ (r j))
  (hdet : ∀ j, b.detDualEquiv (r j).primitiveGenerator (r (j + 1)).primitiveGenerator = 1)
  (hnodes : ∀ j, ∃ σ : Φ.cones, (r j).toCone ≤ σ ∧ (r (j + 1)).toCone ≤ σ ∧
    (Φ.toricBoundaryIdeal F inferInstance).subschemeι
      ((Φ.toricBoundaryIdeal F inferInstance).subscheme.dualGraphEdgeEquiv p (B.edge j)).val =
      (Φ.distinguishedSection (R := F) σ) (IsLocalRing.closedPoint F))

include hcomp hdet hnodes in
/-- In the positive determinant orientation, the ratio of ordered boundary periods
is the inverse center ratio evaluated at the charge relation. -/
theorem orderedBoundaryPeriod_div (c d : Fin n → Fˣ) (x : K) :
    orderedBoundaryPeriod F hΦ b s B c (Multiplicative.ofAdd x) /
      orderedBoundaryPeriod F hΦ b s B d (Multiplicative.ofAdd x) =
        ∏ j, (d j / c j) ^ (x : Fin n → ℤ) j := by
  obtain ⟨L, hL, hperiod⟩ := exists_prod_internalCenterRatio_nodalPicardCycleMulEquiv F hΦ r
    B.endpoint_eq hcomp b hdet hnodes s c d (x : Fin n → ℤ)
  have hratio : orderedBoundaryRestriction F hΦ b s c (Multiplicative.ofAdd x) /
      orderedBoundaryRestriction F hΦ b s d (Multiplicative.ofAdd x) = L := by
    apply Subtype.ext
    rw [Subgroup.coe_div, hL]
    -- The toric part is the same for both boundary restrictions.
    change orderedRestriction F hΦ b s c (Multiplicative.ofAdd x) /
      orderedRestriction F hΦ b s d (Multiplicative.ofAdd x) = _
    rw [orderedRestriction_apply, orderedRestriction_apply, mul_div_mul_left_eq_div]
  rw [orderedBoundaryPeriod_apply, orderedBoundaryPeriod_apply, ← hperiod, ← hratio, map_div]

include hcomp hdet hnodes in
/-- Multiplying the marked period by the restricted center monomial gives a value
independent of the reference center. -/
theorem orderedBoundaryPeriod_mul_torusCharacter (c d : Fin n → Fˣ) (x : K) :
    orderedBoundaryPeriod F hΦ b s B c (Multiplicative.ofAdd x) *
        torusCharacter c (x : Fin n → ℤ) =
      orderedBoundaryPeriod F hΦ b s B d (Multiplicative.ofAdd x) *
        torusCharacter d (x : Fin n → ℤ) := by
  have h := orderedBoundaryPeriod_div F hΦ b s B r hcomp hdet hnodes c d x
  simp only [div_zpow, Finset.prod_div_distrib, ← torusCharacter_def] at h
  simpa only [mul_comm (torusCharacter d _)] using div_eq_div_iff_mul_eq_mul.mp h

include hcomp hdet hnodes in
/-- Ordered boundary periods agree exactly when the center characters agree on all
charge relations. -/
theorem orderedBoundaryPeriod_eq_iff (c d : Fin n → Fˣ) :
    orderedBoundaryPeriod F hΦ b s B c = orderedBoundaryPeriod F hΦ b s B d ↔
      ∀ x ∈ (rayChargeMap s).ker, (∏ j, c j ^ x j) = ∏ j, d j ^ x j := by
  constructor
  · intro h x hx
    have hp := orderedBoundaryPeriod_mul_torusCharacter F hΦ b s B r hcomp hdet hnodes c d ⟨x, hx⟩
    rw [h, mul_right_inj] at hp
    simpa only [torusCharacter_def] using hp
  · intro h
    apply MonoidHom.ext
    intro x
    have hp := orderedBoundaryPeriod_mul_torusCharacter F hΦ b s B r hcomp hdet hnodes c d x.toAdd
    rw [ofAdd_toAdd, torusCharacter_def, torusCharacter_def, h _ x.toAdd.property,
      mul_left_inj] at hp
    exact hp

include hcomp hdet hnodes in
/-- Every charge-kernel character is the period of an ordered internal blowup in
the positive determinant orientation. All choices of centers, including repetitions,
are allowed. -/
theorem orderedBoundaryPeriod_surjective :
    Function.Surjective (orderedBoundaryPeriod F hΦ b s B) := by
  classical
  intro a
  have := Φ.lattice.free
  let e := (rayChargeMap s).quotKerEquivRange
  have hfree : Module.IsTorsionFree ℤ ((Fin n → ℤ) ⧸ K) :=
    e.injective.moduleIsTorsionFree _ (map_smul e)
  obtain ⟨T, hT⟩ := (Submodule.exists_isCompl_iff_isTorsionFree_quotient K).mpr hfree
  let χ := (orderedBoundaryPeriod F hΦ b s B 1 / a).comp
    ((K).projectionOnto T hT).toAddMonoidHom.toMultiplicative
  let c (j : Fin n) := χ (Multiplicative.ofAdd (Pi.single j 1))
  refine ⟨c, MonoidHom.ext fun x ↦ ?_⟩
  have h := orderedBoundaryPeriod_mul_torusCharacter F hΦ b s B r hcomp hdet hnodes c 1 x.toAdd
  rw [torusCharacter_one, mul_one, torusCharacter_of_pi_single] at h
  have hproj : (K).projectionOnto T hT (x.toAdd : Fin n → ℤ) = x.toAdd :=
    Submodule.projectionOnto_apply_left hT x.toAdd
  -- The character extension restricts to the prescribed ratio on the kernel.
  have hχ : χ (Multiplicative.ofAdd (x.toAdd : Fin n → ℤ)) =
      orderedBoundaryPeriod F hΦ b s B 1 x / a x := by
    simp only [χ, MonoidHom.comp_apply]
    change (orderedBoundaryPeriod F hΦ b s B 1 / a)
      (Multiplicative.ofAdd ((K).projectionOnto T hT (x.toAdd : Fin n → ℤ))) = _
    rw [hproj, MonoidHom.div_apply, ofAdd_toAdd]
  rw [hχ, ofAdd_toAdd] at h
  simpa only [div_div_cancel] using eq_div_iff_mul_eq'.mpr h

section Contraction

variable {c : Fin n → Fˣ} {X Y : Scheme}
  [X.Over (Spec (.of F))] [X.IsProjectiveOver F] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of F))]
  [LinearMap.IsPerfPair (Chow.intersectionBilinForm F X)]
  {D₀ : X.IdealSheafData} {d : ℕ} {T : QPainleve.BlowupTower X d Y}
  (hT : IsNodalBoundaryTower D₀ (X ↘ Spec (.of F)) (𝟙 X) T)
  (e : Y ≅ (alongBoundary (Φ.toricBoundaryIdeal F inferInstance).subschemeι
    (fun j ↦ (s j).internalCenter F b (c j))).1)
  (he : e.inv ≫ T.toBase ≫ (X ↘ Spec (.of F)) =
    (alongBoundary (Φ.toricBoundaryIdeal F inferInstance).subschemeι
      (fun j ↦ (s j).internalCenter F b (c j))).2.toTower.toBase ≫
      ((Φ.finiteFanScheme F) ↘ Spec (.of F)))
  (hD : ((D₀.comap T.toBase).comap e.inv).support =
    (alongBoundary (Φ.toricBoundaryIdeal F inferInstance).subschemeι
      (fun j ↦ (s j).internalCenter F b (c j))).2.boundaryι.ker.support)
  [PrestableFamily (D₀.subscheme ↘ Spec (.of F))]
  (hCartier : D₀.IsEffectiveCartier)
  (hgenus : ∀ v : irreducibleComponents (D₀.subscheme.singularLocus F).blowup,
    ((D₀.subscheme).blowupComponent v).toScheme.genus F = 0)
  {β : Type*} {q : β → (D₀.subscheme ↘ Spec (.of F)).smoothLocus} {k : ℕ} [NeZero k]
  (B₀ : NodalCycleNumbering q k)

local notation "g" => toricBoundaryToBase F (J[c]) e hD
local notation "m" => (fun j ↦
  LinearMap.toAddMonoidHom (b.detDualEquiv (Ray.primitiveGenerator (s j))))

/-- The ordered period agrees with the period on the contracted surface whenever
the boundary projection is an oriented conductor subdivision. -/
theorem markedBoundaryPeriod_eq_orderedBoundaryPeriod
    (hsub : Scheme.Hom.IsOrientedCycleSubdivision g B B₀) :
    markedBoundaryPeriod F hΦ b s hT e he hD hCartier hgenus B₀ =
      orderedBoundaryPeriod F hΦ b s B c := by
  obtain ⟨_, hν, hnode, keep, hkeep, hcollapse⟩ := hsub
  apply MonoidHom.ext
  intro x
  rw [← ofAdd_toAdd x, orderedBoundaryPeriod_apply]
  obtain ⟨L, hL, hperiod⟩ := exists_pullback_markedBoundaryPeriod F hΦ b s hT e he hD
    hCartier hgenus B₀ B hν hnode keep hkeep hcollapse x.toAdd
  rw [← hperiod]
  apply congrArg ((C).nodalPicardCycleMulEquiv B.endpoint_eq)
  apply Subtype.ext
  simp only [hL, orderedBoundaryRestriction, MonoidHom.codRestrict_apply, Subgroup.coe_mk,
    orderedRestriction_apply]
  refine pullback_toricBoundaryToBase_picardBoundaryOrthogonalEquivChargeKernel_symm F (J[c]) e hD
    hΦ hdim s m (fun j ↦ b.detDualEquiv_self _) (fun j ↦ (s j).surjective_detCharacter b)
    c (fun j ↦ (s j).internalCenter_val F b (c j)) hT he x.toAdd (mark x.toAdd).val.1 ?_
  simpa only [Chow.intersectionBilinForm_apply] using
    boundaryOrthogonalEquivChargeKernel_symm_fst_pairing F hΦ s A x.toAdd

end Contraction

end TauCeti.Toric.Fan
