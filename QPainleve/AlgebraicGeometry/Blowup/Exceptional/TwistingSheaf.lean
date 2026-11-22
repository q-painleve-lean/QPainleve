/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.Exceptional
public import TauCeti.AlgebraicGeometry.IdealSheaf.Module
public import TauCeti.AlgebraicGeometry.NormalCone.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.LocalTriviality
import TauCeti.Algebra.Regular.SMul
import TauCeti.AlgebraicGeometry.IdealSheaf.Image
import TauCeti.AlgebraicGeometry.IdealSheaf.Locality
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Quasicoherent

/-!
# The exceptional ideal as a twisting sheaf

On the blowup of `Spec R` along an ideal `I`, the ideal sheaf of the exceptional divisor is
the Rees twisting sheaf `𝒪(1)`. On the standard open of `aT`, the comparison takes the
standard generator `aT` of the twist to the pullback of `a`. This formula identifies the
restriction of `𝒪(1)` to the exceptional divisor with its conormal sheaf.

The construction uses Tau Ceti's affine blowup charts, the standard trivializations of
`Proj.twistingSheaf`, and the comparison `Scheme.Hom.conormalObjIsoPullbackKer`.
See [The Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS).
-/

public section

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace Polynomial
  reesAlgebra
open AlgebraicGeometry.Scheme.IdealSheafData
open TauCeti.AlgebraicGeometry

namespace QPainleve

open Proj

universe u

variable {R : Type u} [CommRing R] {I : Ideal R}

private abbrev chartOpen (a : I) : (Proj (grade I)).Opens :=
  basicOpen (grade I) (monomialDegreeOne a.property)

private theorem iSup_chartOpen_eq_top (I : Ideal R) :
    (⨆ a : I, chartOpen a) = ⊤ := by
  simpa only [opensRange_affineBlowupι] using
    (iSup_opensRange_affineBlowupι (I := I) (s := fun a : I ↦ (a : R)) (by simp))

private def inverseVariableOnChart (a : I) :
    Γ(twistingSheaf (grade I) (-1), chartOpen a) :=
  twistingSheaf.const (i := 1) (j := 0) (by decide)
    (gradeZeroEquiv I a : reesAlgebra I) (monomialDegreeOne a.property)
    (gradeZeroEquiv I a).property (monomialDegreeOne_mem_grade a.property) _ le_rfl

private theorem inverseVariableOnChart_compatible (a b : I) :
    (twistingSheaf (grade I) (-1)).presheaf.map (homOfLE inf_le_left).op
        (inverseVariableOnChart a) =
      (twistingSheaf (grade I) (-1)).presheaf.map (homOfLE inf_le_right).op
        (inverseVariableOnChart b) := by
  simp only [inverseVariableOnChart, twistingSheaf.res_const]
  apply twistingSheaf.const_ext
  apply Subtype.ext
  simp [coe_gradeZeroEquiv, coe_monomialDegreeOne, C_mul_monomial, mul_comm]

private theorem exists_inverseVariable (I : Ideal R) :
    ∃ s : Γ(twistingSheaf (grade I) (-1), ⊤), ∀ a : I,
      (twistingSheaf (grade I) (-1)).presheaf.map (chartOpen a).leTop.op s =
        inverseVariableOnChart a := by
  let F := twistingSheaf (grade I) (-1)
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat (Proj (grade I)))
    chartOpen ⊤ (fun a ↦ (chartOpen a).leTop) (iSup_chartOpen_eq_top I).ge
    inverseVariableOnChart inverseVariableOnChart_compatible
  exact ⟨s, hs⟩

private def inverseVariable (I : Ideal R) : Γ(twistingSheaf (grade I) (-1), ⊤) :=
  (exists_inverseVariable I).choose

private theorem res_inverseVariable (a : I) :
    (twistingSheaf (grade I) (-1)).presheaf.map (chartOpen a).leTop.op (inverseVariable I) =
      inverseVariableOnChart a :=
  (exists_inverseVariable I).choose_spec a

private abbrev structureMap (I : Ideal R) : Proj (grade I) ⟶ Spec (.of R) :=
  toSpecZero (grade I) ≫ Spec.map (gradeZeroEquiv I).toCommRingCatIso.hom

private def coefficientSection (U : (Proj (grade I)).Opens) (a : R) :
    Γ(Proj (grade I), U) :=
  (Proj (grade I)).presheaf.map U.leTop.op
    ((toSpecZero (grade I)).appTop ((Scheme.ΓSpecIso _).inv (gradeZeroEquiv I a)))

private theorem coefficientSection_eq_appLE (U : (Proj (grade I)).Opens) (a : R) :
    coefficientSection (I := I) U a =
      (structureMap I).appLE ⊤ U le_top ((Scheme.ΓSpecIso (.of R)).inv a) := by
  let f : CommRingCat.of R ⟶ CommRingCat.of (grade I 0) := (gradeZeroEquiv I).toCommRingCatIso.hom
  have h : (Scheme.ΓSpecIso _).inv (gradeZeroEquiv I a) =
      (Spec.map f).appTop ((Scheme.ΓSpecIso (.of R)).inv a) :=
    ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality f) a
  rw [coefficientSection, h]
  rfl

private theorem coefficientSection_apply (U : (Proj (grade I)).Opens) (a : R) (x : U) :
    ((coefficientSection (I := I) U a).val x).val =
      Localization.mk (gradeZeroEquiv I a : reesAlgebra I) 1 :=
  val_toSpecZero_appTop_apply (gradeZeroEquiv I a) ⟨x.val, trivial⟩

private def twistingSheafToStructureSheaf (I : Ideal R) :
    twistingSheaf (grade I) 1 ⟶ 𝟙_ (Proj (grade I)).Modules :=
  { val.app := fun U ↦ ConcreteCategory.ofHom (C := ModuleCat Γ(Proj (grade I), U.unop)) <|
      (sectionsLinearEquivTwistingSheafZero (grade I) U.unop).symm.toLinearMap.comp
        ((twistingSheaf.mul (grade I) U.unop 1 (-1)).flip
          ((twistingSheaf (grade I) (-1)).presheaf.map U.unop.leTop.op (inverseVariable I)))
    val.naturality := by
      intro U V i
      ext s
      apply Subtype.ext
      funext x
      -- Restriction keeps the values of both factors in the localization at x.
      exact HomogeneousLocalization.val_injective _ rfl }

private theorem twistingSheafToStructureSheaf_app (U : (Proj (grade I)).Opens)
    (s : Γ(twistingSheaf (grade I) 1, U)) :
    (twistingSheafToStructureSheaf I).app U s =
      (sectionsLinearEquivTwistingSheafZero (grade I) U).symm
        (twistingSheaf.mul (grade I) U 1 (-1) s
          ((twistingSheaf (grade I) (-1)).presheaf.map U.leTop.op (inverseVariable I))) :=
  rfl

private theorem twistingSheafToStructureSheaf_app_chartGenerator (a : I)
    (U : (Proj (grade I)).Opens) (hU : U ≤ chartOpen a) :
    (twistingSheafToStructureSheaf I).app U
        (twistingSheaf.chartGenerator 1 (monomialDegreeOne a.property)
          (monomialDegreeOne_mem_grade a.property) U hU) =
      coefficientSection U (a : R) := by
  have hres :
      (twistingSheaf (grade I) (-1)).presheaf.map U.leTop.op (inverseVariable I) =
        (twistingSheaf (grade I) (-1)).presheaf.map (homOfLE hU).op (inverseVariableOnChart a) := by
    rw [← res_inverseVariable, ← Functor.map_comp_apply, ← op_comp]
    rfl
  apply (sectionsLinearEquivTwistingSheafZero (grade I) U).injective
  apply twistingSheaf.ext
  intro x
  simp only [twistingSheafToStructureSheaf_app, hres, LinearEquiv.apply_symm_apply,
    twistingSheaf.mul_apply, twistingSheaf.chartGenerator_apply, inverseVariableOnChart,
    twistingSheaf.res_const, twistingSheaf.const_apply,
    sectionsLinearEquivTwistingSheafZero_apply_apply, coefficientSection_apply, Localization.mk_mul]
  apply Localization.mk_eq_mk_iff.mpr
  apply Localization.r_of_eq
  simp [mul_comm]

private abbrev chartι (a : I) :=
  affineBlowupι (Localization.Away (a : R)) a.property

private abbrev chartAlgebra (a : I) :=
  I.affineBlowup (a : R) (Localization.Away (a : R))

private theorem chartOpen_le_preimage (a : I) : ⊤ ≤ chartι a ⁻¹ᵁ chartOpen a := by
  have h : (chartι a).opensRange = chartOpen a :=
    opensRange_affineBlowupι (Localization.Away (a : R)) a.property
  exact h ▸ (fun x _ ↦ ⟨x, rfl⟩ : ⊤ ≤ chartι a ⁻¹ᵁ (chartι a).opensRange)

private def chartRingHom (a : I) :=
  (chartι a).appLE (chartOpen a) ⊤ (chartOpen_le_preimage a)

private instance (a : I) : IsIso (chartRingHom a) := by
  have hImage : (chartι a) ''ᵁ ⊤ = chartOpen a := (chartι a).image_top_eq_opensRange.trans
    (opensRange_affineBlowupι (Localization.Away (a : R)) a.property)
  unfold chartRingHom
  apply ((chartι a).appLE_congr (chartOpen_le_preimage a) hImage.symm rfl
    (fun {_ _} f ↦ IsIso f)).mpr
  rw [← Scheme.Hom.appIso_hom']
  infer_instance

private theorem chartRingHom_coefficientSection (a : I) :
    chartRingHom a (coefficientSection (chartOpen a) (a : R)) =
      (Scheme.ΓSpecIso (.of (chartAlgebra a))).inv (algebraMap R (chartAlgebra a) a) := by
  have hComp : (structureMap I).appLE ⊤ (chartOpen a) le_top ≫ chartRingHom a =
      (chartι a ≫ structureMap I).appTop :=
    (Scheme.Hom.appLE_comp_appLE (chartι a) (structureMap I) ⊤ (chartOpen a) ⊤
      le_top (chartOpen_le_preimage a)).trans (Scheme.Hom.appLE_eq_app _)
  rw [coefficientSection_eq_appLE, ← CommRingCat.comp_apply, hComp]
  unfold chartι structureMap
  rw [affineBlowupι_toSpecZero]
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap R (chartAlgebra a)))) (a : R)).symm

private theorem isAffineOpen_chartOpen (a : I) : IsAffineOpen (chartOpen a) :=
  isAffineOpen_basicOpen _ _ (monomialDegreeOne_mem_grade a.property) one_pos

private theorem regular_coefficientSection (a : I) (U : (Proj (grade I)).Opens)
    (hU : U ≤ chartOpen a) : IsSMulRegular Γ(Proj (grade I), U) (coefficientSection U (a : R)) := by
  let Y := Spec (.of (chartAlgebra a))
  have hChart : IsSMulRegular Γ(Y, ⊤)
      (chartRingHom a (coefficientSection (chartOpen a) (a : R))) := by
    rw [chartRingHom_coefficientSection]
    exact Scheme.isSMulRegular_ΓSpecIso_inv (Ideal.isRegular_algebraMap_affineBlowup
      (I := I) (a := (a : R)) (S := Localization.Away (a : R))).left
  have h := (TauCeti.isSMulRegular_map_iff (asIso (chartRingHom a)).commRingCatIsoToRingEquiv
    (coefficientSection (chartOpen a) (a : R))).mp hChart
  have hres := (isAffineOpen_chartOpen a).isSMulRegular_map hU h
  have hRestriction : (Proj (grade I)).presheaf.map (homOfLE hU).op
      (coefficientSection (chartOpen a) (a : R)) = coefficientSection U (a : R) := by
    simp only [coefficientSection, ← Functor.map_comp_apply, ← op_comp]
    rfl
  exact hRestriction ▸ hres

private theorem twistingSheafToStructureSheaf_app_chartSectionsLinearEquiv (a : I)
    (U : (Proj (grade I)).Opens) (hU : U ≤ chartOpen a) (r : Γ(Proj (grade I), U)) :
    (twistingSheafToStructureSheaf I).app U
        (twistingSheaf.chartSectionsLinearEquiv 1 (monomialDegreeOne a.property)
          (monomialDegreeOne_mem_grade a.property) U hU r) =
      r * coefficientSection U (a : R) := by
  rw [twistingSheaf.chartSectionsLinearEquiv_apply]
  exact ((twistingSheafToStructureSheaf I).app_smul r
    (twistingSheaf.chartGenerator 1 (monomialDegreeOne a.property)
      (monomialDegreeOne_mem_grade a.property) U hU)).trans
    (congrArg (r * ·) (twistingSheafToStructureSheaf_app_chartGenerator a U hU))

private theorem injective_twistingSheafToStructureSheaf_app_of_le (a : I)
    (U : (Proj (grade I)).Opens) (hU : U ≤ chartOpen a) :
    Function.Injective ((twistingSheafToStructureSheaf I).app U) := by
  let e := twistingSheaf.chartSectionsLinearEquiv 1 (monomialDegreeOne a.property)
    (monomialDegreeOne_mem_grade a.property) U hU
  intro s t h
  obtain ⟨r, rfl⟩ := e.surjective s
  obtain ⟨q, rfl⟩ := e.surjective t
  congr 1
  apply regular_coefficientSection a U hU
  have hm : r * coefficientSection U (a : R) = q * coefficientSection U (a : R) :=
    (twistingSheafToStructureSheaf_app_chartSectionsLinearEquiv a U hU r).symm.trans
      (h.trans (twistingSheafToStructureSheaf_app_chartSectionsLinearEquiv a U hU q))
  simpa only [smul_eq_mul, mul_comm] using hm

private instance (I : Ideal R) : Mono (twistingSheafToStructureSheaf I) := by
  apply (SheafOfModules.forget _).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro U s t h
  refine TopCat.Presheaf.IsSheaf.section_ext (twistingSheaf (grade I) 1).isSheaf fun x hx ↦ ?_
  obtain ⟨a, ha⟩ := Opens.mem_iSup.mp ((iSup_chartOpen_eq_top I).ge (Opens.mem_top x))
  refine ⟨U.unop ⊓ chartOpen a, inf_le_left, ⟨hx, ha⟩,
    injective_twistingSheafToStructureSheaf_app_of_le a _ inf_le_right ?_⟩
  let i : U.unop ⊓ chartOpen a ⟶ U.unop := homOfLE inf_le_left
  have hs := (twistingSheafToStructureSheaf I).mapPresheaf.naturality_apply i.op s
  have ht := (twistingSheafToStructureSheaf I).mapPresheaf.naturality_apply i.op t
  exact (hs.trans (congrArg
    ((𝟙_ (Proj (grade I)).Modules).presheaf.map i.op) h)).trans ht.symm

private theorem ideal_exceptional_chartOpen (a : I) :
    (affineBlowupExceptionalIdeal R I).ideal ⟨chartOpen a, isAffineOpen_chartOpen a⟩ =
      Ideal.span {coefficientSection (chartOpen a) (a : R)} := by
  have he : Function.Bijective (chartRingHom a).hom :=
    ConcreteCategory.bijective_of_isIso _
  have hComap := ideal_comap_of_le (affineBlowupExceptionalIdeal R I) (chartι a)
    ⟨chartOpen a, isAffineOpen_chartOpen a⟩ ⟨⊤, isAffineOpen_top _⟩ (chartOpen_le_preimage a)
  apply (Ideal.relIsoOfBijective _ he).symm.injective
  -- The two ideals can be compared on the spectrum of the affine chart algebra.
  change Ideal.map (chartRingHom a).hom _ = Ideal.map (chartRingHom a).hom _
  change _ = Ideal.map (chartRingHom a).hom _ at hComap
  rw [← hComap, affineBlowupExceptionalIdeal_comap_affineBlowupι,
    Ideal.map_span, Set.image_singleton]
  let Y := Spec (.of (chartAlgebra a))
  simp only [ofIdealTop_ideal, homOfLE_refl, op_id, chartRingHom_coefficientSection]
  -- Write the restriction on the chart as the presheaf map of its identity open inclusion.
  change Ideal.map (Y.presheaf.map (𝟙 (op ⊤))).hom _ = _
  rw [Y.presheaf.map_id, CommRingCat.hom_id, Ideal.map_id]

private theorem imageIdeal_twistingSheafToStructureSheaf (a : I) :
    (twistingSheafToStructureSheaf I).imageIdeal (chartOpen a) =
      Ideal.span {coefficientSection (chartOpen a) (a : R)} := by
  ext r
  rw [Scheme.Modules.Hom.mem_imageIdeal, Ideal.mem_span_singleton']
  let e := twistingSheaf.chartSectionsLinearEquiv 1 (monomialDegreeOne a.property)
    (monomialDegreeOne_mem_grade a.property) (chartOpen a) le_rfl
  refine e.surjective.exists.trans ?_
  exact exists_congr fun c ↦
    Iff.of_eq (congrArg (· = r)
      (twistingSheafToStructureSheaf_app_chartSectionsLinearEquiv a _ le_rfl c))

private theorem imageIdealSheaf_twistingSheafToStructureSheaf (I : Ideal R) :
    (twistingSheafToStructureSheaf I).imageIdealSheaf = affineBlowupExceptionalIdeal R I := by
  refine ext_of_comap_openCover ((Proj (grade I)).openCoverOfIsOpenCover chartOpen
    (iSup_chartOpen_eq_top I)) ?_
  intro a
  change I at a
  -- The open cover is given by the inclusions of the standard opens.
  change (twistingSheafToStructureSheaf I).imageIdealSheaf.comap (chartOpen a).ι =
    (affineBlowupExceptionalIdeal R I).comap (chartOpen a).ι
  rw [comap_ι_eq_ofIdealTop _ ⟨chartOpen a, isAffineOpen_chartOpen a⟩,
    comap_ι_eq_ofIdealTop _ ⟨chartOpen a, isAffineOpen_chartOpen a⟩,
    Scheme.Modules.Hom.imageIdealSheaf_ideal, imageIdeal_twistingSheafToStructureSheaf,
    ideal_exceptional_chartOpen]

/-- The scheme-theoretic exceptional ideal of an affine blowup is its Rees twist `𝒪(1)`. -/
def affineBlowupExceptionalIdealIsoTwistingSheaf (R : Type u) [CommRing R] (I : Ideal R) :
    (affineBlowupExceptionalIdeal R I).sheaf ≅ twistingSheaf (grade I) 1 :=
  ((twistingSheafToStructureSheaf I).imageIdealSheafIso ≪≫
    eqToIso (congrArg Scheme.IdealSheafData.sheaf
      (imageIdealSheaf_twistingSheafToStructureSheaf I))).symm

/-- In the standard Rees trivialization, the exceptional ideal inclusion sends the twist
generator `aT` to the pullback of `a`. The formula holds on every open inside the chart. -/
@[simp]
theorem affineBlowupExceptionalIdealIsoTwistingSheaf_inv_app_chartGenerator
    (a : I) (U : (Proj (grade I)).Opens)
    (hU : U ≤ basicOpen (grade I) (monomialDegreeOne a.property)) :
    (affineBlowupExceptionalIdeal R I).sheafι.app U
      ((affineBlowupExceptionalIdealIsoTwistingSheaf R I).inv.app U
        (twistingSheaf.chartGenerator 1 (monomialDegreeOne a.property)
          (monomialDegreeOne_mem_grade a.property) U hU)) =
      (toSpecZero (grade I) ≫ Spec.map (gradeZeroEquiv I).toCommRingCatIso.hom).appLE
        ⊤ U le_top ((Scheme.ΓSpecIso (.of R)).inv (a : R)) := by
  rw [← coefficientSection_eq_appLE, ← twistingSheafToStructureSheaf_app_chartGenerator a U hU]
  have h : (affineBlowupExceptionalIdealIsoTwistingSheaf R I).inv ≫
      (affineBlowupExceptionalIdeal R I).sheafι = twistingSheafToStructureSheaf I := by
    unfold affineBlowupExceptionalIdealIsoTwistingSheaf
    let J := (twistingSheafToStructureSheaf I).imageIdealSheaf
    let E := affineBlowupExceptionalIdeal R I
    have e : J = E := imageIdealSheaf_twistingSheafToStructureSheaf I
    have hι : eqToHom (congrArg Scheme.IdealSheafData.sheaf e) ≫ E.sheafι = J.sheafι := by
      simpa only [eqToHom_refl, Category.comp_id] using
        (eqToHom_naturality (f := Scheme.IdealSheafData.sheaf)
          (g := fun _ ↦ 𝟙_ (Proj (grade I)).Modules) Scheme.IdealSheafData.sheafι e).symm
    simp only [Iso.symm_inv, Iso.trans_hom, eqToIso.hom]
    exact (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) hι).trans (twistingSheafToStructureSheaf I).imageIdealSheafIso_hom_ι)
  exact congrArg (fun f ↦ f.app U (twistingSheaf.chartGenerator 1 (monomialDegreeOne a.property)
    (monomialDegreeOne_mem_grade a.property) U hU)) h

/-- The conormal sheaf of the exceptional divisor of an affine blowup is the restriction
of the Rees twist `𝒪(1)` to that divisor. -/
def affineBlowupExceptionalConormalIsoPullbackTwistingSheaf
    (R : Type u) [CommRing R] (I : Ideal R) :
    (affineBlowupExceptionalIdeal R I).subschemeι.conormal.obj ≅
      (Scheme.Modules.pullback (affineBlowupExceptionalIdeal R I).subschemeι).obj
        (twistingSheaf (grade I) 1) := by
  let J := affineBlowupExceptionalIdeal R I
  exact J.subschemeι.conormalObjIsoPullbackKer ≪≫ (Scheme.Modules.pullback J.subschemeι).mapIso
    (eqToIso (congrArg Scheme.IdealSheafData.sheaf J.ker_subschemeι) ≪≫
      affineBlowupExceptionalIdealIsoTwistingSheaf R I)

end QPainleve
