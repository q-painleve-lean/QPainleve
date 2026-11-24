/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Automorphism
public import QPainleve.Geometry.Toric.Fan.TorusAction.Comparison
public import QPainleve.Geometry.Toric.Fan.TorusAction.NodalDescent
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic
import QPainleve.AlgebraicGeometry.RationalMap.FunctionField
import TauCeti.AlgebraicGeometry.Noetherian

/-!
# Translation invariance of fixed-center evaluations on contractions

A translating lift between ordered toric blowup models intertwines the fixed-center
rational evaluations on their contractions. In particular the quotient-character
automorphisms of a toric presentation fix its evaluation at every center. This is
the evaluation consequence of the torus action in
[Gross, Hacking and Keel, Proposition 2.6](https://arxiv.org/html/1211.6367v5#S2).
The comparison uses `Fan.torusTranslation_comp_xEvaluation` on the toric surface
and `Fan.toricPresentationCharacterHom_isLift` on the ordered models.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative QPainleve.BlowupTower TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]
  {n : ℕ} (b : Module.Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "center" a:arg => (fun j : Fin n ↦ a (ofAdd (Pi.single j 1)))
local notation "Y" a:arg => (Sigma.fst (internalBlowupTower b s (center a)))
local notation "T" a:arg => WithBoundary.toTower (Sigma.snd (internalBlowupTower b s (center a)))
local notation "π" a:arg => toBase (T a)
local notation "ι" a:arg => WithBoundary.boundaryι
  (Sigma.snd (internalBlowupTower b s (center a)))

variable {c d : Multiplicative (Fin n → ℤ) →* ℂˣ} (hΦ : Φ.IsRegular)
  {X X' : Scheme} [IsIntegral X] [IsIntegral X']
  {p : (internalBlowupTower b s (fun j ↦ c (ofAdd (Pi.single j 1)))).1 ⟶ X}
  {q : (internalBlowupTower b s (fun j ↦ d (ofAdd (Pi.single j 1)))).1 ⟶ X'}
  [IsModification p] [IsModification q]

open Scheme.RationalMap in
/-- If the square of contractions commutes with a translating lift, pulling back
the target evaluation along the lower map recovers the source evaluation. The
upper lift can match repeated centers and the charge image can have any rank. -/
theorem comp_contractedXEvaluation_of_isLift_torusTranslation
    {χ : Multiplicative (N →+ ℤ) →* ℂˣ} {t : Y c ≅ Y d}
    (ht : IsLift (Φ.torusTranslation χ) (T c) (T d) t)
    {f : X ⟶ X'} (hf : p ≫ f = t.hom ≫ q) :
    let : IsDominant f := IsDominant.of_comp p f (H := hf.symm ▸ inferInstance)
    f.toRationalMap.comp (contractedXEvaluation b s d hΦ q) =
      contractedXEvaluation b s c hΦ p := by
  let : IsDominant f := IsDominant.of_comp p f (H := hf.symm ▸ inferInstance)
  have hcenter :=
    (exists_isLift_internalBlowupTower_torusTranslation_iff b s (center c) (center d) χ).mp ⟨t, ht⟩
  let charge := ((addMonoidHomLequivInt ℤ).symm.toLinearMap.comp
    (b.detDualEquiv.toLinearMap.comp (rayChargeMap s))).toAddMonoidHom
  have hd : d = c / χ.comp charge.toMultiplicative := by
    apply MonoidHom.toAdditiveRight.injective
    apply AddMonoidHom.toIntLinearMap_injective
    apply (Pi.basisFun ℤ (Fin n)).ext
    intro j
    simpa only [Pi.basisFun_apply, AddMonoidHom.coe_toIntLinearMap, MonoidHom.coe_toAdditiveRight,
      MonoidHom.div_apply, MonoidHom.comp_apply, AddMonoidHom.coe_toMultiplicative,
      Function.comp_apply, toAdd_ofAdd, LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply,
      rayChargeMap_single, LinearEquiv.coe_coe, addMonoidHomLequivInt_symm_apply, charge]
      using congrArg Additive.ofMul (eq_div_iff_mul_eq'.mpr (hcenter j))
  have heval : (Φ.torusTranslation χ).hom.toRationalMap.comp (Φ.xEvaluation b s d) =
      Φ.xEvaluation b s c := by
    rw [hd]
    exact Φ.torusTranslation_comp_xEvaluation b s c χ
  have := isIntegral_internalBlowupTower b s (center c) hΦ
  have := isModification_internalBlowupTower_toBase b s (center c) hΦ
  simpa only [compHom_id] using
    comp_contractedXEvaluation_of_common_model b s c hΦ p b s d hΦ q (𝟙 _) t.hom f
      (by simpa only [Category.id_comp] using hf) (𝟙 _) (by
        simp only [Category.id_comp, compHom_id, ht.hom_toBase, ← Scheme.Hom.toRationalMap_compHom,
          ← comp_toRationalMap, comp_assoc, heval])

/-- Every quotient-character automorphism of a contracted toric presentation
fixes its fixed-center rational X evaluation. -/
@[simp]
theorem toricPresentationCharacterHom_comp_contractedXEvaluation
    [IsNoetherian X] (f : X ⟶ S) [SmoothOfRelativeDimension 2 f]
    {W : Scheme} {m : ℕ} {U : QPainleve.BlowupTower X m W} (hU : IsClosedPointTower X U)
    (e : W ≅ Y c) (hc : Φ.IsComplete)
    (z : Multiplicative (N ⧸ (rayChargeMap s).range) →* ℂˣ) :
    let : IsModification U.toBase := hU.isModification_of_smoothOfRelativeDimension_two f
    (toricPresentationCharacterHom b s (center c) hΦ f e hU hc z).asIso.hom.toRationalMap.comp
      (contractedXEvaluation b s c hΦ (e.inv ≫ U.toBase)) =
        contractedXEvaluation b s c hΦ (e.inv ≫ U.toBase) := by
  let : IsModification U.toBase := hU.isModification_of_smoothOfRelativeDimension_two f
  have htop := internalBlowupPicardBoundaryAutMulEquiv_isLift b s (center c) hΦ hc z
  have hbottom := (toricPresentationCharacterHom_isLift b s (center c) hΦ f e hU hc z).hom_toBase
  apply comp_contractedXEvaluation_of_isLift_torusTranslation b s hΦ htop
  simpa only [Category.assoc, Aut.autMulEquivOfIso_apply_asIso, Iso.trans_hom,
    Iso.symm_hom, Iso.symm_inv, Iso.inv_hom_id_assoc] using
    (congrArg (e.inv ≫ ·) hbottom).symm

/-- A Picard-trivial automorphism over the base that fixes each boundary component
and each nodal branch preserves fixed-center X evaluation on the original surface
of a toric presentation. The branch condition gives an ordered lift through the
specified nodal blowups before applying the quotient-character classification. -/
theorem comp_contractedXEvaluation_eq_of_fixes_nodal_branches
    [X.Over S] [QuasiCompact (X ↘ S)] [SmoothOfRelativeDimension 2 (X ↘ S)]
    {D : X.IdealSheafData} (hD : D.IsEffectiveCartier)
    (hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S))
    {W : Scheme} {m : ℕ} {U : QPainleve.BlowupTower X m W}
    (hU : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) U)
    (e : W ≅ Y c) (hc : Φ.IsComplete)
    (he : e.hom ≫ π c ≫ Φ.algebraicRealizationStructureMap = U.toBase ≫ X ↘ S)
    (hB : (D.comap U.toBase).support = ((ι c).ker.comap e.hom).support)
    (a : Aut X) (ha : a.asIso.hom ≫ X ↘ S = X ↘ S)
    (hPic : ∀ L, LineBundleClass.pullback a.asIso.hom L = L)
    (hfix : ∀ x : CodimensionOnePoint X, (x : X) ∈ D.support → a.asIso.hom x = x)
    (d : D.subscheme ≅ D.subscheme) (hd : d.hom ≫ D.subschemeι = D.subschemeι ≫ a.asIso.hom)
    (hbranches :
      letI : D.subscheme.Over S := ⟨D.subschemeι ≫ X ↘ S⟩
      letI : d.hom.IsOver S := ⟨((reassoc_of% hd) _).trans (congrArg (D.subschemeι ≫ ·) ha)⟩
      letI : SyntomicOfRelativeDimension 1 (D.subscheme ↘ S) := hN.syntomic
      ∀ y : (D.subscheme.singularLocus ℂ).blowup,
        (D.subscheme.singularLocus ℂ).blowupToBase y ∈ (D.subscheme.singularLocus ℂ).support →
          (d.singularLocusBlowupIso (R := ℂ)).hom y = y) :
    let : IsModification U.toBase :=
      hU.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (X ↘ S)
    a.asIso.hom.toRationalMap.comp (contractedXEvaluation b s c hΦ (e.inv ≫ U.toBase)) =
      contractedXEvaluation b s c hΦ (e.inv ≫ U.toBase) := by
  let : IsModification U.toBase :=
    hU.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (X ↘ S)
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  obtain ⟨g, hg, -⟩ := hU.exists_isLift_of_fixes_nodal_branches hD hN a.asIso d ha hd hbranches
  obtain ⟨z, rfl⟩ :=
    (mem_range_toricPresentationCharacterHom_iff b s (center c) hΦ (X ↘ S) e he hB
      hU.isClosedPointTower hc a).mpr ⟨ha, hPic, hfix, g, hg⟩
  exact toricPresentationCharacterHom_comp_contractedXEvaluation b s hΦ (X ↘ S)
    hU.isClosedPointTower e hc z

end TauCeti.Toric.Fan
