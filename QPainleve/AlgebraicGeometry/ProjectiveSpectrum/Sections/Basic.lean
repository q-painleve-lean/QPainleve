/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.LineBundle.Ratio
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Basic
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ChartEquality
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Naturality
import TauCeti.AlgebraicGeometry.Restrict
import TauCeti.RingTheory.MvPolynomial.Homogeneous

/-!
# Projective morphisms from generating sections of a line bundle

A family of global sections of an invertible sheaf whose nonvanishing loci cover
the scheme defines a morphism to polynomial projective space. On the open where
one section generates, the affine coordinates are the ratios to that section.

The affine comparison makes it possible to check closed immersions by inspecting
the coordinate rings on the standard projective charts. The construction uses
Mathlib's `Proj.fromOfGlobalSections` and Tau Ceti's
`fromOfGlobalSections_eq_of_unit_rescaling` and `fromOfGlobalSections_naturality`.
See the Stacks Project, [Tag 01ND](https://stacks.math.columbia.edu/tag/01ND).
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MvPolynomial hiding X
open HomogeneousLocalization
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules)
  [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M]

variable {R : Type u} [CommRing R] (f : X ⟶ Spec (.of R))
variable {ι : Type u} (s : ι → Γ(M, ⊤))

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "ℙ" => Proj (MvPolynomial.homogeneousSubmodule ι R)
local notation "Dₛ[" i "]" => M.nonvanishingLocus (s i)
local notation "res[" i "]" => M.presheaf.map (Quiver.Hom.op (homOfLE (le_top : Dₛ[i] ≤ ⊤)))

private theorem le_nonvanishingLocus_res (i : ι) :
    Dₛ[i] ≤ M.nonvanishingLocus (res[i] (s i)) := by
  rw [M.nonvanishingLocus_map, inf_idem]

private def chartEval (i : ι) : MvPolynomial ι R →+* Γ(Dₛ[i], ⊤) :=
  eval₂Hom ((Scheme.ΓSpecIso (.of R)).inv ≫ ((Dₛ[i]).ι ≫ f).appTop).hom
    (fun j ↦ (Dₛ[i]).topIso.inv (M.sectionRatio (res[i] (s j)) (res[i] (s i))
      (le_nonvanishingLocus_res M s i)))

private theorem chartEval_X (i j : ι) :
    chartEval M f s i (.X j) =
      (Dₛ[i]).topIso.inv (M.sectionRatio (res[i] (s j)) (res[i] (s i))
        (le_nonvanishingLocus_res M s i)) :=
  eval₂Hom_X' _ _ _

private theorem chartEval_X_self (i : ι) : chartEval M f s i (.X i) = 1 := by
  rw [chartEval_X, sectionRatio_self, map_one]

private theorem chartEval_irrelevant (i : ι) :
    (HomogeneousIdeal.irrelevant (homogeneousSubmodule ι R)).toIdeal.map
      (chartEval M f s i) = ⊤ := by
  rw [irrelevant_eq_span_X, Ideal.map_span, ← Set.range_comp, Ideal.eq_top_iff_one]
  exact Ideal.subset_span ⟨i, chartEval_X_self M f s i⟩

private def chartHom (i : ι) : (Dₛ[i]).toScheme ⟶ ℙ :=
  Proj.fromOfGlobalSections _ (chartEval M f s i) (chartEval_irrelevant M f s i)

private theorem restrict_chartEval_X {W : X.Opens} {i : ι} (h : W ≤ Dₛ[i]) (j : ι) :
    (X.homOfLE h).appTop (chartEval M f s i (.X j)) =
      W.topIso.inv (M.sectionRatio
        (M.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op (s j))
        (M.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op (s i))
        (by rw [M.nonvanishingLocus_map]; exact le_inf le_rfl h)) := by
  rw [chartEval_X]
  -- Transport restrictions through the section-ring isomorphisms of open subschemes.
  have he : (Dₛ[i]).topIso.inv ≫ (X.homOfLE h).appTop =
      X.presheaf.map (homOfLE h).op ≫ W.topIso.inv := by
    -- Naturality is written for the section functor, whose maps are restrictions.
    exact (X.restrictFunctorΓ.inv.naturality (homOfLE h).op).symm
  rw [← ConcreteCategory.comp_apply, he, ConcreteCategory.comp_apply, M.map_sectionRatio]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

private theorem fromOfGlobalSections_eq_of_X_unit_rescaling {S : Scheme.{u}}
    (p q : MvPolynomial ι R →+* Γ(S, ⊤)) (c : Γ(S, ⊤)ˣ)
    (hC : p.comp C = q.comp C) (hX : ∀ i, q (.X i) = c * p (.X i))
    (hp : (HomogeneousIdeal.irrelevant (homogeneousSubmodule ι R)).toIdeal.map p = ⊤)
    (hq : (HomogeneousIdeal.irrelevant (homogeneousSubmodule ι R)).toIdeal.map q = ⊤) :
    Proj.fromOfGlobalSections _ p hp = Proj.fromOfGlobalSections _ q hq := by
  have eval_eq (g : MvPolynomial ι R →+* Γ(S, ⊤)) :
      eval₂Hom (g.comp C) (fun k ↦ g (.X k)) = g := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro k
      simp
  have he (n : ℕ) (a : MvPolynomial ι R) (ha : a ∈ homogeneousSubmodule ι R n) :
      q a = c ^ n * p a := by
    calc
      q a = eval₂ (p.comp C) (fun k ↦ c * p (.X k)) a := by
        simpa only [← hC, hX, coe_eval₂Hom] using DFunLike.congr_fun (eval_eq q).symm a
      _ = c ^ n * p a := by
        simpa only [← coe_eval₂Hom, eval_eq] using
          (mem_homogeneousSubmodule _ _ |>.mp ha).eval₂_const_mul (p.comp C)
            (fun k ↦ p (.X k)) (c : Γ(S, ⊤))
  exact (TauCeti.ProjectiveSpectrum.fromOfGlobalSections_eq_of_unit_rescaling
    _ p q c he hp).symm

private theorem chartHom_compatible (i j : ι) :
    X.homOfLE (inf_le_left : Dₛ[i] ⊓ Dₛ[j] ≤ Dₛ[i]) ≫ chartHom M f s i =
      X.homOfLE (inf_le_right : Dₛ[i] ⊓ Dₛ[j] ≤ Dₛ[j]) ≫ chartHom M f s j := by
  let W := Dₛ[i] ⊓ Dₛ[j]
  let li : W ≤ Dₛ[i] := inf_le_left
  let lj : W ≤ Dₛ[j] := inf_le_right
  let r (k : ι) := M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (s k)
  have hi : W ≤ M.nonvanishingLocus (r i) := by
    rw [M.nonvanishingLocus_map]
    exact le_inf le_rfl li
  have hj : W ≤ M.nonvanishingLocus (r j) := by
    rw [M.nonvanishingLocus_map]
    exact le_inf le_rfl lj
  let a := M.sectionRatio (r i) (r j) hj
  have ha := M.isUnit_sectionRatio (r i) (r j) hi hj
  let c := ha.unit.map W.topIso.inv.hom.toMonoidHom
  have hc : (c : Γ(W, ⊤)) = W.topIso.inv a := congrArg W.topIso.inv ha.unit_spec
  let fi := (X.homOfLE li).appTop.hom.comp (chartEval M f s i)
  let fj := (X.homOfLE lj).appTop.hom.comp (chartEval M f s j)
  have hX (k : ι) : fj (.X k) = c * fi (.X k) := by
    dsimp only [fi, fj, RingHom.comp_apply]
    rw [restrict_chartEval_X M f s lj, restrict_chartEval_X M f s li, hc, ← map_mul]
    exact congrArg W.topIso.inv (M.sectionRatio_mul_sectionRatio (r k) (r i) (r j) hi hj).symm
  have hC : fi.comp C = fj.comp C := by
    have hbase : X.homOfLE li ≫ (Dₛ[i]).ι ≫ f =
        X.homOfLE lj ≫ (Dₛ[j]).ι ≫ f := by simp
    have he := congrArg (fun g : W.toScheme ⟶ Spec (.of R) ↦
      ((Scheme.ΓSpecIso (.of R)).inv ≫ g.appTop).hom) hbase
    ext r
    simpa only [fi, fj, chartEval, RingHom.comp_apply, eval₂Hom_C,
      Scheme.Hom.comp_appTop, Category.assoc, ConcreteCategory.comp_apply] using
      DFunLike.congr_fun he r
  unfold chartHom
  rw [Proj.fromOfGlobalSections_naturality, Proj.fromOfGlobalSections_naturality]
  exact fromOfGlobalSections_eq_of_X_unit_rescaling fi fj c hC hX
    (by dsimp only [fi]; rw [← Ideal.map_map, chartEval_irrelevant, Ideal.map_top])
    (by dsimp only [fj]; rw [← Ideal.map_map, chartEval_irrelevant, Ideal.map_top])

private theorem chartHom_glue (i j : ι) :
    pullback.fst (Dₛ[i]).ι (Dₛ[j]).ι ≫ chartHom M f s i =
      pullback.snd (Dₛ[i]).ι (Dₛ[j]).ι ≫ chartHom M f s j := by
  rw [← cancel_epi (isPullback_opens_inf Dₛ[i] Dₛ[j]).isoPullback.hom]
  simpa only [IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_assoc] using
    chartHom_compatible M f s i j

/-- A covering family of sections of an invertible sheaf gives a morphism to the
projective space with one homogeneous coordinate for each section. -/
def toProjectiveSpace (h : ⨆ i, Dₛ[i] = ⊤) : X ⟶ ℙ :=
  (X.openCoverOfIsOpenCover (fun i ↦ Dₛ[i]) (IsOpenCover.mk h)).glueMorphisms
    (chartHom M f s) (chartHom_glue M f s)

private theorem chartHom_comp_toSpecCoeff (i : ι) :
    chartHom M f s i ≫ Proj.toSpecCoeff (homogeneousSubmodule ι R) = (Dₛ[i]).ι ≫ f := by
  rw [chartHom, Proj.toSpecCoeff_def, Proj.fromOfGlobalSections_toSpecZero_assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hcoeff :
      (chartEval M f s i).comp
          ((algebraMap (homogeneousSubmodule ι R 0) _).comp
            (algebraMap R (homogeneousSubmodule ι R 0))) =
        ((Scheme.ΓSpecIso (.of R)).inv ≫ ((Dₛ[i]).ι ≫ f).appTop).hom := by
    ext r
    simp [chartEval, MvPolynomial.algebraMap_eq]
  rw [RingHom.comp_assoc, hcoeff]
  rw [CommRingCat.ofHom_hom, Spec.map_comp,
    ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

private theorem ι_toProjectiveSpace (h : ⨆ i, Dₛ[i] = ⊤) (i : ι) :
    (Dₛ[i]).ι ≫ M.toProjectiveSpace f s h = chartHom M f s i :=
  (X.openCoverOfIsOpenCover (fun j ↦ Dₛ[j]) (IsOpenCover.mk h)).ι_glueMorphisms
    (chartHom M f s) (chartHom_glue M f s) i

/-- The projective morphism preserves the structure morphism to the coefficient ring. -/
@[reassoc (attr := simp)]
theorem toProjectiveSpace_toSpecCoeff (h : ⨆ i, Dₛ[i] = ⊤) :
    M.toProjectiveSpace f s h ≫ Proj.toSpecCoeff (homogeneousSubmodule ι R) = f := by
  refine (X.openCoverOfIsOpenCover (fun j ↦ Dₛ[j]) (IsOpenCover.mk h)).hom_ext _ _ fun k ↦ ?_
  let i : ι := k
  -- The cover map is the inclusion of the corresponding nonvanishing open.
  change (Dₛ[i]).ι ≫ M.toProjectiveSpace f s h ≫ _ = (Dₛ[i]).ι ≫ f
  rw [← Category.assoc, ι_toProjectiveSpace, chartHom_comp_toSpecCoeff]

private theorem chartHom_preimage_basicOpen (i j : ι) :
    chartHom M f s i ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule ι R) (.X j) =
      (Dₛ[i]).ι ⁻¹ᵁ Dₛ[j] := by
  rw [chartHom, Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ one_pos
    ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R j)), chartEval_X]
  have hratio := M.basicOpen_eq_inf_nonvanishingLocus
    (homOfLE (le_top : Dₛ[i] ≤ ⊤)) (s j) (le_nonvanishingLocus_res M s i)
    (M.sectionRatio_smul (res[i] (s j)) (res[i] (s i))
      (le_nonvanishingLocus_res M s i))
  refine (Dₛ[i]).ι.image_injective ?_
  calc
    (Dₛ[i]).ι ''ᵁ _ = X.basicOpen _ := Scheme.Opens.ι_image_basicOpen_topIso_inv _ _
    _ = Dₛ[i] ⊓ Dₛ[j] := hratio
    _ = (Dₛ[i]).ι ''ᵁ ((Dₛ[i]).ι ⁻¹ᵁ Dₛ[j]) := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]

/-- The inverse image of the coordinate open `D₊(Xᵢ)` is the nonvanishing locus
of the generating section indexed by `i`. -/
@[simp]
theorem toProjectiveSpace_preimage_basicOpen (h : ⨆ i, Dₛ[i] = ⊤) (i : ι) :
    M.toProjectiveSpace f s h ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule ι R) (.X i) =
      Dₛ[i] := by
  ext x
  obtain ⟨k, y, rfl⟩ :=
    (X.openCoverOfIsOpenCover (fun j ↦ Dₛ[j]) (IsOpenCover.mk h)).exists_eq x
  let j : ι := k
  have hj := congrArg (fun O : (Dₛ[j]).toScheme.Opens ↦ y ∈ O)
    (chartHom_preimage_basicOpen M f s j i)
  -- The point on the cover maps to the point of the open subscheme in X.
  change (Dₛ[j]).ι y ∈ M.toProjectiveSpace f s h ⁻¹ᵁ _ ↔ (Dₛ[j]).ι y ∈ Dₛ[i]
  have he := congrArg (fun g : (Dₛ[j]).toScheme ⟶ ℙ ↦ g y)
    (ι_toProjectiveSpace M f s h j)
  have he' : M.toProjectiveSpace f s h ((Dₛ[j]).ι y) = chartHom M f s j y := he
  rw [Scheme.Hom.mem_preimage, he']
  exact Iff.of_eq hj

private theorem chartEval_isUnit (i : ι) : IsUnit (chartEval M f s i (.X i)) :=
  chartEval_X_self M f s i ▸ isUnit_one

private def chartRingHom (i : ι) :
    Away (homogeneousSubmodule ι R) (MvPolynomial.X i) →+* Γ(Dₛ[i], ⊤) :=
  Away.lift (homogeneousSubmodule ι R) (chartEval M f s i) (chartEval_isUnit M f s i)

/-- The morphism from the nonvanishing open of a section to the corresponding
affine chart of projective space. -/
def toProjectiveSpaceChart (i : ι) :
    (Dₛ[i]).toScheme ⟶ Spec (.of (Away (homogeneousSubmodule ι R) (MvPolynomial.X i))) :=
  (Dₛ[i]).toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (chartRingHom M f s i))

/-- The affine chart morphism is the restriction of the projective morphism. -/
@[reassoc]
theorem toProjectiveSpaceChart_awayι (h : ⨆ i, Dₛ[i] = ⊤) (i : ι) :
    M.toProjectiveSpaceChart f s i ≫ Proj.awayι (homogeneousSubmodule ι R) (MvPolynomial.X i)
        ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R i)) one_pos =
      (Dₛ[i]).ι ≫ M.toProjectiveSpace f s h := by
  rw [ι_toProjectiveSpace, chartHom,
    Proj.fromOfGlobalSections_eq_toSpecΓ_awayLift (chartEval M f s i)
      (chartEval_irrelevant M f s i) one_pos
      ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R i)) (chartEval_isUnit M f s i)]
  exact Category.assoc _ _ _

private theorem toProjectiveSpaceChart_appTop (i : ι) :
    (Scheme.ΓSpecIso _).inv ≫ (M.toProjectiveSpaceChart f s i).appTop =
      CommRingCat.ofHom (chartRingHom M f s i) := by
  have happ {Y : Scheme.{u}} {B : CommRingCat.{u}} (d : B ⟶ Γ(Y, ⊤)) :
      (Scheme.ΓSpecIso B).inv ≫ (Y.toSpecΓ ≫ Spec.map d).appTop = d := by
    rw [Scheme.Hom.comp_appTop, ← Scheme.ΓSpecIso_inv_naturality_assoc,
      Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]
  exact happ (Y := (Dₛ[i]).toScheme) (CommRingCat.ofHom (chartRingHom M f s i))

/-- The affine chart morphism evaluates a normalized coordinate as a ratio to the
generating section. -/
@[simp]
theorem toProjectiveSpaceChart_appTop_awayXRatio (i j : ι) :
    (M.toProjectiveSpaceChart f s i).appTop.hom
        ((Scheme.ΓSpecIso _).inv.hom (TauCeti.MvPolynomial.awayXRatio (R := R) i j)) =
      (Dₛ[i]).topIso.inv (M.sectionRatio (res[i] (s j)) (res[i] (s i))
        (by rw [M.nonvanishingLocus_map, inf_idem])) := by
  have h := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    (toProjectiveSpaceChart_appTop M f s i)) (TauCeti.MvPolynomial.awayXRatio (R := R) i j)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h
  rw [h]
  -- The bundled commutative-ring morphism has underlying degree-zero evaluation.
  change chartRingHom M f s i (TauCeti.MvPolynomial.awayXRatio i j) = _
  rw [chartRingHom, TauCeti.MvPolynomial.awayXRatio_def, Away.lift_mk]
  have hunit : (chartEval_isUnit M f s i).unit = 1 :=
    Units.ext ((chartEval_isUnit M f s i).unit_spec.trans (chartEval_X_self M f s i))
  simpa [hunit] using chartEval_X M f s i j

private theorem isClosedImmersion_toProjectiveSpace_iff_chart
    (h : ⨆ i, Dₛ[i] = ⊤) :
    IsClosedImmersion (M.toProjectiveSpace f s h) ↔
      ∀ i : ι, IsClosedImmersion (M.toProjectiveSpaceChart f s i) := by
  let D (i : ι) : (ℙ).Opens := Proj.basicOpen (homogeneousSubmodule ι R) (.X i)
  have hD : ⨆ i, D i = ⊤ := Proj.iSup_basicOpen_eq_top _ _ (irrelevant_eq_span_X ι R).le
  have he (i : ι) :
      IsClosedImmersion (M.toProjectiveSpace f s h ∣_ (D i)) ↔
        IsClosedImmersion (M.toProjectiveSpaceChart f s i) := by
    let j := Proj.awayι (homogeneousSubmodule ι R) (MvPolynomial.X i)
      ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R i)) one_pos
    have hj : j.opensRange = D i := Proj.opensRange_awayι _ _ _ _
    have hp : M.toProjectiveSpace f s h ⁻¹ᵁ j.opensRange = (Dₛ[i]).ι.opensRange := by
      rw [hj, Scheme.Opens.opensRange_ι]
      exact M.toProjectiveSpace_preimage_basicOpen f s h i
    let e := (M.toProjectiveSpace f s h).morphismRestrictArrowIso
      (j := j) (M.toProjectiveSpaceChart f s i) (M.toProjectiveSpaceChart_awayι f s h i).symm hp
    rw [← hj]
    exact MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion e
  constructor
  · intro _ i
    exact (he i).mp inferInstance
  · intro H
    exact IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion) D hD
      (fun i ↦ (he i).mpr (H i))

private theorem surjective_chartRingHom_iff (i : ι) :
    Function.Surjective (chartRingHom M f s i) ↔ Function.Surjective (chartEval M f s i) := by
  refine ⟨fun h b ↦ ?_, (chartEval M f s i).lift_surjective_of_eval_surjective i
    (chartEval_X_self M f s i)⟩
  obtain ⟨z, rfl⟩ := h b
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective _ ((mem_homogeneousSubmodule _ _).mpr
    (isHomogeneous_X R i)) z
  refine ⟨p, ?_⟩
  rw [chartRingHom, Away.lift_mk]
  have hu : (chartEval_isUnit M f s i).unit = 1 :=
    Units.ext ((chartEval_isUnit M f s i).unit_spec.trans (chartEval_X_self M f s i))
  simp [hu]

/-- The projective morphism is a closed immersion exactly when each nonvanishing
open is affine and its sections are generated over the base by the normalized
coordinates. The evaluation map in the criterion sends `Xⱼ` to the ratio of
the restrictions of `s j` and `s i`. -/
theorem isClosedImmersion_toProjectiveSpace_iff (h : ⨆ i, Dₛ[i] = ⊤) :
    IsClosedImmersion (M.toProjectiveSpace f s h) ↔
      ∀ i : ι, IsAffine (Dₛ[i]).toScheme ∧
        Function.Surjective (eval₂Hom
          ((Scheme.ΓSpecIso (.of R)).inv ≫ ((Dₛ[i]).ι ≫ f).appTop).hom
          (fun j ↦ (Dₛ[i]).topIso.inv (M.sectionRatio (res[i] (s j)) (res[i] (s i))
            (by rw [M.nonvanishingLocus_map, inf_idem])))) := by
  rw [isClosedImmersion_toProjectiveSpace_iff_chart]
  refine forall_congr' fun i ↦ ?_
  have hs : Function.Surjective (M.toProjectiveSpaceChart f s i).appTop ↔
      Function.Surjective (chartRingHom M f s i) := by
    let e := Scheme.ΓSpecIso (.of (Away (homogeneousSubmodule ι R) (MvPolynomial.X i)))
    have he : Function.Surjective e.inv :=
      ((ConcreteCategory.isIso_iff_bijective e.inv).mp inferInstance).surjective
    have H := Function.Surjective.of_comp_iff (M.toProjectiveSpaceChart f s i).appTop he
    have hh := congrArg (fun g : CommRingCat.of _ ⟶ Γ(Dₛ[i], ⊤) ↦
      Function.Surjective g) (toProjectiveSpaceChart_appTop M f s i)
    exact H.symm.trans (Iff.of_eq hh)
  refine ⟨fun _ ↦ ?_, fun ⟨ha, hsurj⟩ ↦ ?_⟩
  · obtain ⟨ha, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine
      (M.toProjectiveSpaceChart f s i)
    exact ⟨ha, (surjective_chartRingHom_iff M f s i).mp (hs.mp hsurj)⟩
  · exact IsClosedImmersion.of_surjective_of_isAffine _
      (hs.mpr ((surjective_chartRingHom_iff M f s i).mpr hsurj))

private theorem span_eq_top_of_frame_coordinates (h : ⨆ i, Dₛ[i] = ⊤)
    {W : X.Opens} (hW : IsAffineOpen W) (e : Γ(M, W)) (he : W ≤ M.nonvanishingLocus e)
    (a : ι → Γ(X, W)) (ha : ∀ i, a i • e = M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (s i)) :
    Ideal.span (Set.range a) = ⊤ := by
  apply hW.iSup_basicOpen_eq_self_iff.mp
  rw [iSup_range']
  conv_lhs => arg 1; intro i; rw [M.basicOpen_eq_inf_nonvanishingLocus _ (s i) he (ha i)]
  rw [← inf_iSup_eq, h, inf_top_eq]

private theorem frameEval_irrelevant (h : ⨆ i, Dₛ[i] = ⊤) {W : X.Opens}
    (hW : IsAffineOpen W) (e : Γ(M, W)) (he : W ≤ M.nonvanishingLocus e)
    (a : ι → Γ(X, W)) (ha : ∀ i, a i • e = M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (s i)) :
    (HomogeneousIdeal.irrelevant (homogeneousSubmodule ι R)).toIdeal.map
      (eval₂Hom ((Scheme.ΓSpecIso (.of R)).inv ≫ (W.ι ≫ f).appTop).hom
        (fun j ↦ W.topIso.inv (a j))) = ⊤ := by
  rw [irrelevant_eq_span_X, Ideal.map_span, ← Set.range_comp]
  have hc := span_eq_top_of_frame_coordinates M s h hW e he a ha
  rw [← Ideal.map_top (f := W.topIso.inv.hom), ← hc, Ideal.map_span, ← Set.range_comp]
  simp only [Function.comp_def, eval₂Hom_X']

private theorem chartHom_eq_fromOfGlobalSections_of_frame {V W : X.Opens} {i : ι}
    (e : Γ(M, W)) (he : W ≤ M.nonvanishingLocus e)
    (a : ι → Γ(X, W)) (ha : ∀ i, a i • e = M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (s i))
    (hp : (HomogeneousIdeal.irrelevant (homogeneousSubmodule ι R)).toIdeal.map
      (eval₂Hom ((Scheme.ΓSpecIso (.of R)).inv ≫ (W.ι ≫ f).appTop).hom
        (fun j ↦ W.topIso.inv (a j))) = ⊤)
    (hle : V ≤ W) (hle' : V ≤ Dₛ[i]) :
    X.homOfLE hle' ≫ chartHom M f s i =
      X.homOfLE hle ≫ Proj.fromOfGlobalSections (homogeneousSubmodule ι R)
        (eval₂Hom ((Scheme.ΓSpecIso (.of R)).inv ≫ (W.ι ≫ f).appTop).hom
          (fun j ↦ W.topIso.inv (a j))) hp := by
  let p := eval₂Hom ((Scheme.ΓSpecIso (.of R)).inv ≫ (W.ι ≫ f).appTop).hom
    (fun j ↦ W.topIso.inv (a j))
  unfold chartHom
  rw [Proj.fromOfGlobalSections_naturality, Proj.fromOfGlobalSections_naturality]
  let L := X.homOfLE hle'
  let K := X.homOfLE hle
  let q₀ := L.appTop.hom.comp (chartEval M f s i)
  let q₁ := K.appTop.hom.comp p
  let r (j : ι) := M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (s j)
  let b := M.presheaf.map (homOfLE hle).op e
  have hb : V ≤ M.nonvanishingLocus b := by
    rw [M.nonvanishingLocus_map]
    exact le_inf le_rfl (hle.trans he)
  have hr : V ≤ M.nonvanishingLocus (r i) := by
    rw [M.nonvanishingLocus_map]
    exact le_inf le_rfl hle'
  have hframe (j : ι) : M.sectionRatio (r j) b hb = X.presheaf.map (homOfLE hle).op (a j) := by
    apply (M.sectionRatio_eq_iff hb).mpr
    rw [← M.map_smul, ha]
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    rfl
  have hu := M.isUnit_sectionRatio (r i) b hr hb
  let c := hu.unit.map V.topIso.inv.hom.toMonoidHom
  have hc : (c : Γ(V, ⊤)) = V.topIso.inv (M.sectionRatio (r i) b hb) :=
    congrArg V.topIso.inv hu.unit_spec
  have hC : q₀.comp C = q₁.comp C := by
    have hh : L ≫ (Dₛ[i]).ι ≫ f = K ≫ W.ι ≫ f := by simp [L, K]
    have hh' := congrArg (fun g : V.toScheme ⟶ Spec (.of R) ↦
      ((Scheme.ΓSpecIso (.of R)).inv ≫ g.appTop).hom) hh
    ext u
    simpa only [q₀, q₁, p, chartEval, RingHom.comp_apply, eval₂Hom_C,
      Scheme.Hom.comp_appTop, Category.assoc, ConcreteCategory.comp_apply] using
      DFunLike.congr_fun hh' u
  have hX (j : ι) : q₁ (.X j) = c * q₀ (.X j) := by
    have hh : W.topIso.inv ≫ K.appTop =
        X.presheaf.map (homOfLE hle).op ≫ V.topIso.inv :=
      (X.restrictFunctorΓ.inv.naturality (homOfLE hle).op).symm
    dsimp only [q₀, q₁, RingHom.comp_apply, p]
    rw [eval₂Hom_X', ← ConcreteCategory.comp_apply, hh, ConcreteCategory.comp_apply,
      ← hframe j, restrict_chartEval_X M f s hle', hc, ← map_mul]
    exact congrArg V.topIso.inv (M.sectionRatio_mul_sectionRatio (r j) (r i) b hr hb).symm
  exact fromOfGlobalSections_eq_of_X_unit_rescaling q₀ q₁ c hC hX _ _

/-- In a frame on an affine open, the projective morphism is the ordinary
evaluation map of the frame coordinates. The coordinates generate the unit
ideal there. -/
theorem ι_toProjectiveSpace_eq_fromOfGlobalSections (h : ⨆ i, Dₛ[i] = ⊤)
    {W : X.Opens} (hW : IsAffineOpen W) (e : Γ(M, W)) (he : W ≤ M.nonvanishingLocus e)
    (a : ι → Γ(X, W)) (ha : ∀ i, a i • e = M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (s i)) :
    let p := eval₂Hom ((Scheme.ΓSpecIso (.of R)).inv ≫ (W.ι ≫ f).appTop).hom
      (fun i ↦ W.topIso.inv (a i))
    ∃ hp : (HomogeneousIdeal.irrelevant (homogeneousSubmodule ι R)).toIdeal.map p = ⊤,
      W.ι ≫ M.toProjectiveSpace f s h = Proj.fromOfGlobalSections _ p hp := by
  let p := eval₂Hom ((Scheme.ΓSpecIso (.of R)).inv ≫ (W.ι ≫ f).appTop).hom
    (fun i ↦ W.topIso.inv (a i))
  let hp := frameEval_irrelevant M f s h hW e he a ha
  refine ⟨hp, ?_⟩
  let V (i : ι) := W ⊓ Dₛ[i]
  have hV : ⨆ i, V i = W := by rw [← inf_iSup_eq, h, inf_top_eq]
  rw [← cancel_epi (X.isoOfEq hV).hom]
  refine (Scheme.Opens.iSupOpenCover V).hom_ext _ _ fun k ↦ ?_
  let i : ι := k
  have hle : V i ≤ W := inf_le_left
  have hle' : V i ≤ Dₛ[i] := inf_le_right
  have h' : X.homOfLE hle ≫ W.ι ≫ M.toProjectiveSpace f s h =
      X.homOfLE hle' ≫ chartHom M f s i := by
    rw [← ι_toProjectiveSpace M f s h i]
    simp
  have hloc := chartHom_eq_fromOfGlobalSections_of_frame M f s e he a ha hp hle hle'
  have hi : X.homOfLE (le_iSup V i) ≫ (X.isoOfEq hV).hom = X.homOfLE hle := by
    rw [X.isoOfEq_hom]
    exact X.homOfLE_homOfLE (le_iSup V i) _
  -- The member of the supremum cover is the open V i itself.
  change (X.homOfLE (le_iSup V i) ≫ (X.isoOfEq hV).hom) ≫
      W.ι ≫ M.toProjectiveSpace f s h =
    (X.homOfLE (le_iSup V i) ≫ (X.isoOfEq hV).hom) ≫ Proj.fromOfGlobalSections _ p hp
  rw [hi]
  exact h'.trans hloc

end AlgebraicGeometry.Scheme.Modules
