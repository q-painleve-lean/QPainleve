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

variable (K : Type) [Field K] [IsAlgClosed K]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]
  {n : ℕ} (b : Module.Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray)

local notation "center" a:arg => (fun j : Fin n ↦ a (ofAdd (Pi.single j 1)))
local notation "Y" a:arg => (Sigma.fst (internalBlowupTower K b s (center a)))
local notation "T" a:arg => WithBoundary.toTower (Sigma.snd (internalBlowupTower K b s (center a)))
local notation "π" a:arg => toBase (T a)
local notation "ι" a:arg => WithBoundary.boundaryι
  (Sigma.snd (internalBlowupTower K b s (center a)))

variable {c d : Multiplicative (Fin n → ℤ) →* Kˣ} (hΦ : Φ.IsRegular)
  {X X' : Scheme} [IsIntegral X] [IsIntegral X']
  {p : (internalBlowupTower K b s (fun j ↦ c (ofAdd (Pi.single j 1)))).1 ⟶ X}
  {q : (internalBlowupTower K b s (fun j ↦ d (ofAdd (Pi.single j 1)))).1 ⟶ X'}
  [IsModification p] [IsModification q]

open Scheme.RationalMap in
/-- If the square of contractions commutes with a translating lift, pulling back
the target evaluation along the lower map recovers the source evaluation. The
upper lift can match repeated centers and the charge image can have any rank. -/
theorem comp_contractedXEvaluation_of_isLift_torusTranslation
    {χ : Multiplicative (N →+ ℤ) →* Kˣ} {t : Y c ≅ Y d}
    (ht : IsLift (Φ.torusTranslationIso K χ) (T c) (T d) t)
    {f : X ⟶ X'} (hf : p ≫ f = t.hom ≫ q) :
    let : IsDominant f := IsDominant.of_comp p f (H := hf.symm ▸ inferInstance)
    f.toRationalMap.comp (contractedXEvaluation K b s d hΦ q) =
      contractedXEvaluation K b s c hΦ p := by
  let : IsDominant f := IsDominant.of_comp p f (H := hf.symm ▸ inferInstance)
  have hcenter :=
    (exists_isLift_internalBlowupTower_torusTranslation_iff K b s (center c) (center d) χ).mp
      ⟨t, ht⟩
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
  have heval : (Φ.torusTranslationIso K χ).hom.toRationalMap.comp (Φ.xEvaluation K b s d) =
      Φ.xEvaluation K b s c := by
    rw [hd]
    exact Φ.torusTranslation_comp_xEvaluation K b s c χ
  have := isIntegral_internalBlowupTower K b s (center c) hΦ
  have := isModification_internalBlowupTower_toBase K b s (center c) hΦ
  simpa only [compHom_id] using
    comp_contractedXEvaluation_of_common_model K b s c hΦ p b s d hΦ q (𝟙 _) t.hom f
      (by simpa only [Category.id_comp] using hf) (𝟙 _) (by
        simp only [Category.id_comp, compHom_id, ht.hom_toBase, ← Scheme.Hom.toRationalMap_compHom,
          ← comp_toRationalMap, comp_assoc, heval])

variable {b s} in
/-- A contracted translation intertwines the fixed-center X evaluations. -/
theorem ContractedToricTranslation.comp_contractedXEvaluation {e : X ≅ X'}
    (t : ContractedToricTranslation K b s p q e) :
    e.hom.toRationalMap.comp (contractedXEvaluation K b s d hΦ q) =
      contractedXEvaluation K b s c hΦ p :=
  comp_contractedXEvaluation_of_isLift_torusTranslation K b s hΦ t.isLift t.commutes

/-- Every quotient-character automorphism of a contracted toric presentation
fixes its fixed-center rational X evaluation. -/
@[simp]
theorem toricPresentationCharacterHom_comp_contractedXEvaluation
    [IsNoetherian X] (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 2 f]
    {W : Scheme} {m : ℕ} {U : QPainleve.BlowupTower X m W} (hU : IsClosedPointTower X U)
    (e : W ≅ Y c) (hc : Φ.IsComplete)
    (z : Multiplicative (N ⧸ (rayChargeMap s).range) →* Kˣ) :
    let : IsModification U.toBase := hU.isModification_of_smoothOfRelativeDimension_two f
    (toricPresentationCharacterHom K b s (center c) hΦ f e hU hc z).asIso.hom.toRationalMap.comp
      (contractedXEvaluation K b s c hΦ (e.inv ≫ U.toBase)) =
        contractedXEvaluation K b s c hΦ (e.inv ≫ U.toBase) := by
  let : IsModification U.toBase := hU.isModification_of_smoothOfRelativeDimension_two f
  have htop := internalBlowupPicardBoundaryAutMulEquiv_isLift K b s (center c) hΦ hc z
  have hbottom := (toricPresentationCharacterHom_isLift K b s (center c) hΦ f e hU hc z).hom_toBase
  apply comp_contractedXEvaluation_of_isLift_torusTranslation K b s hΦ htop
  simpa only [Category.assoc, Aut.autMulEquivOfIso_apply_asIso, Iso.trans_hom,
    Iso.symm_hom, Iso.symm_inv, Iso.inv_hom_id_assoc] using
    (congrArg (e.inv ≫ ·) hbottom).symm

/-- A Picard-trivial automorphism over the base that fixes each boundary component
and each nodal branch preserves fixed-center X evaluation on the original surface
of a toric presentation. The branch condition gives an ordered lift through the
specified nodal blowups before applying the quotient-character classification. -/
theorem comp_contractedXEvaluation_eq_of_fixes_nodal_branches
    [X.Over (Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of K))]
    {D : X.IdealSheafData} (hD : D.IsEffectiveCartier)
    (hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ Spec (.of K)))
    {W : Scheme} {m : ℕ} {U : QPainleve.BlowupTower X m W}
    (hU : IsNodalBoundaryTower D (X ↘ Spec (.of K)) (𝟙 X) U)
    (e : W ≅ Y c) (hc : Φ.IsComplete)
    (he : e.hom ≫ π c ≫ (Φ.finiteFanSchemeToSpec K) = U.toBase ≫ X ↘ Spec (.of K))
    (hB : (D.comap U.toBase).support = ((ι c).ker.comap e.hom).support)
    (a : Aut X) (ha : a.asIso.hom ≫ X ↘ Spec (.of K) = X ↘ Spec (.of K))
    (hPic : ∀ L, LineBundleClass.pullback a.asIso.hom L = L)
    (hfix : ∀ x : CodimensionOnePoint X, (x : X) ∈ D.support → a.asIso.hom x = x)
    (d : D.subscheme ≅ D.subscheme) (hd : d.hom ≫ D.subschemeι = D.subschemeι ≫ a.asIso.hom)
    (hbranches :
      letI : D.subscheme.Over (Spec (.of K)) := ⟨D.subschemeι ≫ X ↘ Spec (.of K)⟩
      letI : d.hom.IsOver (Spec (.of K)) :=
        ⟨((reassoc_of% hd) _).trans (congrArg (D.subschemeι ≫ ·) ha)⟩
      letI : SyntomicOfRelativeDimension 1 (D.subscheme ↘ Spec (.of K)) := hN.syntomic
      ∀ y : (D.subscheme.singularLocus K).blowup,
        (D.subscheme.singularLocus K).blowupToBase y ∈ (D.subscheme.singularLocus K).support →
          (d.singularLocusBlowupIso (R := K)).hom y = y) :
    let : IsModification U.toBase :=
      hU.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (X ↘ Spec (.of K))
    a.asIso.hom.toRationalMap.comp (contractedXEvaluation K b s c hΦ (e.inv ≫ U.toBase)) =
      contractedXEvaluation K b s c hΦ (e.inv ≫ U.toBase) := by
  let : IsModification U.toBase :=
    hU.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (X ↘ Spec (.of K))
  have : Smooth (X ↘ Spec (.of K)) := SmoothOfRelativeDimension.smooth 2 _
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of K))
  obtain ⟨g, hg, -⟩ := hU.exists_isLift_of_fixes_nodal_branches hD hN a.asIso d ha hd hbranches
  obtain ⟨z, rfl⟩ :=
    (mem_range_toricPresentationCharacterHom_iff K b s (center c) hΦ (X ↘ Spec (.of K)) e he hB
      hU.isClosedPointTower hc a).mpr ⟨ha, hPic, hfix, g, hg⟩
  exact toricPresentationCharacterHom_comp_contractedXEvaluation K b s hΦ (X ↘ Spec (.of K))
    hU.isClosedPointTower e hc z

end TauCeti.Toric.Fan
