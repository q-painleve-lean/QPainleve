/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.Ample
public import Mathlib.AlgebraicGeometry.Birational.RationalMap
import QPainleve.AlgebraicGeometry.LineBundle.Power
import QPainleve.AlgebraicGeometry.LineBundle.SectionExtension
import Mathlib.RingTheory.Localization.Integer

/-!
# Global sections representing rational maps to projective space

A finite family of sections of a line bundle defines a partial map on the nonvanishing
open of any one of its sections that is nonzero at the generic point. Conversely, on a
quasi-compact, quasi-separated integral scheme with an ample line bundle, every rational
map to finite-dimensional projective space over the base has such a presentation.
The sections give the linear system used to study the base points of the specified map.

The construction clears the denominators of the normalized coordinates on one affine
open and extends them using `Scheme.Modules.exists_sections_mul_tensorPow`, a finite-family
form of the extension principle of the Stacks Project, Lemma 28.18.2 (tag 01PW).
-/

public section

open CategoryTheory MonoidalCategory Opposite TopologicalSpace
open MvPolynomial HomogeneousLocalization
open TauCeti TauCeti.AlgebraicGeometry TauCeti.MvPolynomial

universe u

noncomputable section

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R ι : Type u} [CommRing R]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule ι R
local notation "ℙ" => Proj 𝒜
local notation "η[" X "]" => genericPoint X
local notation "B[" i "]" => Away 𝒜 (MvPolynomial.X i)
local notation "j[" i "]" =>
  Proj.awayι 𝒜 (MvPolynomial.X i)
    (Iff.mpr (mem_homogeneousSubmodule _ _) (isHomogeneous_X R i)) one_pos

namespace Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules)
  [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M]
  (f : X ⟶ Spec (.of R)) (s : ι → Γ(M, ⊤))

local notation "D[" i "]" => M.nonvanishingLocus (s i)

/-- A family of global sections represents a partial projective map on the nonvanishing
open of a chosen section whenever that open is dense. -/
def partialMapToProjectiveSpace (i : ι) (hi : Dense (D[i] : Set X)) : X.PartialMap ℙ where
  domain := D[i]
  dense_domain := hi
  hom := M.toProjectiveSpaceChart f s i ≫ j[i]

/-- The chosen section's nonvanishing locus is the domain of this representative. -/
@[simp]
theorem partialMapToProjectiveSpace_domain (i : ι) (hi : Dense (D[i] : Set X)) :
    (M.partialMapToProjectiveSpace f s i hi).domain = D[i] := (rfl)

/-- The representing morphism is evaluation in the chosen standard affine chart. -/
theorem partialMapToProjectiveSpace_hom (i : ι) (hi : Dense (D[i] : Set X)) :
    (M.partialMapToProjectiveSpace f s i hi).hom =
      X.homOfLE (M.partialMapToProjectiveSpace_domain f s i hi).le ≫
        M.toProjectiveSpaceChart f s i ≫ j[i] := by
  simp [partialMapToProjectiveSpace]

/-- The partial map given by projective sections preserves the base morphism. -/
instance isOver_partialMapToProjectiveSpace (i : ι) (hi : Dense (D[i] : Set X)) :
    (M.partialMapToProjectiveSpace f s i hi).IsOver f (Proj.toSpecCoeff 𝒜) :=
  ⟨by
    simpa only [partialMapToProjectiveSpace, Category.assoc, Proj.awayι_toSpecCoeff] using
      M.toProjectiveSpaceChart_toSpecCoeff f s i⟩

/-- Choosing a different dense coordinate open gives the same rational map. -/
theorem toRationalMap_partialMapToProjectiveSpace_eq (i j : ι)
    (hi : Dense (D[i] : Set X)) (hj : Dense (D[j] : Set X)) :
    (M.partialMapToProjectiveSpace f s i hi).toRationalMap =
      (M.partialMapToProjectiveSpace f s j hj).toRationalMap := by
  apply Scheme.PartialMap.toRationalMap_eq_iff.mpr
  exact ⟨D[i] ⊓ D[j], hi.inter_of_isOpen_left hj (D[i]).isOpen,
    inf_le_left, inf_le_right, M.toProjectiveSpaceChart_awayι_eq_on_inf f s i j⟩

/-- When the sections generate everywhere, the partial map represents their projective
morphism. -/
theorem toRationalMap_partialMapToProjectiveSpace (h : ⨆ i, D[i] = ⊤)
    (i : ι) (hi : Dense (D[i] : Set X)) :
    (M.partialMapToProjectiveSpace f s i hi).toRationalMap =
      (M.toProjectiveSpace f s h).toRationalMap := by
  apply Scheme.PartialMap.toRationalMap_eq_iff.mpr
  refine ⟨D[i], hi, by simp, le_top, ?_⟩
  -- Both restrictions have source the chosen coordinate open.
  change X.homOfLE (le_rfl : D[i] ≤ D[i]) ≫ (M.toProjectiveSpaceChart f s i ≫ j[i]) =
    X.homOfLE (le_top : D[i] ≤ ⊤) ≫ X.topIso.hom ≫ M.toProjectiveSpace f s h
  simpa only [Scheme.homOfLE_rfl, Category.id_comp, Scheme.topIso_hom,
    Scheme.homOfLE_ι_assoc] using M.toProjectiveSpaceChart_awayι f s h i

variable {M f s}

private theorem genericProjectiveChart_preimage_awayXRatio [IsIntegral X] (i j : ι)
    (hi : η[X] ∈ D[i]) :
    (Spec.preimage ((D[i]).fromSpecStalkOfMem _ hi ≫ M.toProjectiveSpaceChart f s i)).hom
        (awayXRatio (R := R) i j) =
      X.presheaf.germ (D[i]) η[X] hi
        (M.sectionRatio (M.presheaf.map (D[i]).leTop.op (s j))
          (M.presheaf.map (D[i]).leTop.op (s i)) (by rw [nonvanishingLocus_map, inf_idem])) := by
  generalize hg' : M.toProjectiveSpaceChart f s i = g
  have hg : (D[i]).toSpecΓ ≫ Spec.map
      ((Scheme.ΓSpecIso _).inv ≫ g.appTop ≫ (D[i]).topIso.hom) = g := by
    have ht : Spec.map (D[i]).topIso.inv ≫ Spec.map (D[i]).topIso.hom = 𝟙 _ := by
      rw [← Spec.map_comp, Iso.hom_inv_id, Spec.map_id]
    simp only [Spec.map_comp, Opens.toSpecΓ, Category.assoc, reassoc_of% ht,
      ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rw [← hg, Opens.fromSpecStalkOfMem_toSpecΓ_assoc, ← Spec.map_comp, Spec.preimage_map]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, ← hg']
  have h := toProjectiveSpaceChart_appTop_awayXRatio M f s i j
  erw [h, Iso.inv_hom_id_apply]
  rfl

end Scheme.Modules

open Scheme.Modules

private theorem exists_global_sections_of_ratios {X : Scheme.{u}} [IsIntegral X]
    [CompactSpace X] [QuasiSeparatedSpace X] {A : LineBundleClass X} (hA : A.IsAmple)
    [Finite ι] (c : ι → X.functionField) (i : ι) (hci : c i = 1) :
    ∃ (L : InvertibleSheaf X) (s : ι → Γ(L.obj, ⊤)),
      let D := L.obj.nonvanishingLocus (s i)
      ∃ hD : η[X] ∈ D, ∀ j,
        X.presheaf.germ D η[X] hD (L.obj.sectionRatio (L.obj.presheaf.map D.leTop.op (s j))
          (L.obj.presheaf.map D.leTop.op (s i))
          (by rw [nonvanishingLocus_map, inf_idem])) = c j := by
  obtain ⟨_, _, L, _, e, hη, hU⟩ := hA.exists_isAffineOpen_nonvanishingLocus η[X]
  let U := L.obj.nonvanishingLocus e
  have : Nonempty U := ⟨⟨_, hη⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors Γ(X, U)) c
  choose a ha using hb
  have hb' : X.presheaf.germ U η[X] hη b ≠ 0 := fun h ↦
    nonZeroDivisors.ne_zero b.property (X.germToFunctionField_injective U
      (h.trans (map_zero _).symm))
  have hai : a i = b := (IsFractionRing.injective Γ(X, U) X.functionField) (by
    simpa only [hci, Algebra.smul_def, mul_one] using ha i)
  obtain ⟨n, hn, s, hs⟩ := exists_sections_mul_tensorPow L e a
  let M : InvertibleSheaf X := ⟨tensorPow L.obj n, inferInstance⟩
  let D := (tensorPow L.obj n).nonvanishingLocus (s i)
  let eU := tensorPowSection (L.obj.presheaf.map U.leTop.op e) n
  have heU : (tensorPow L.obj n).nonvanishingLocus eU = U := by
    rw [nonvanishingLocus_tensorPowSection _ hn, nonvanishingLocus_map, inf_idem]
  have hW : X.basicOpen (b : Γ(X, U)) = U ⊓ D := by
    rw [← hai]
    exact (tensorPow L.obj n).basicOpen_eq_inf_nonvanishingLocus U.leTop (s i) heU.ge (hs i).symm
  have hηD : η[X] ∈ D := (hW.le.trans inf_le_right)
    ((X.mem_basicOpen _ _ hη).mpr (isUnit_iff_ne_zero.mpr hb'))
  refine ⟨M, s, hηD, fun j ↦ ?_⟩
  have hg := (tensorPow L.obj n).germ_sectionRatio_mul_eq_of_restrict_eq_smul hη hηD
    (s j) (s i) eU heU.ge (by rw [nonvanishingLocus_map, inf_idem]) (a j) (a i) (hs j) (hs i)
  have hnum : X.presheaf.germ U η[X] hη (a j) =
      X.presheaf.germ U η[X] hη b * c j := by
    simpa only [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using ha j
  rw [hai, hnum, mul_comm _ (c j)] at hg
  exact mul_right_cancel₀ hb' hg

namespace Proj

private theorem eq_of_awayXRatio {K : Type u} [CommRing K] (i : ι)
    (p q : Spec (.of K) ⟶ Spec (.of B[i]))
    (hc : p ≫ j[i] ≫ Proj.toSpecCoeff 𝒜 = q ≫ j[i] ≫ Proj.toSpecCoeff 𝒜)
    (h : ∀ j, (Spec.preimage p).hom (awayXRatio (R := R) i j) =
      (Spec.preimage q).hom (awayXRatio (R := R) i j)) : p = q := by
  rw [awayι_toSpecCoeff] at hc
  have hcoeff (r : R) :
      (Spec.preimage p).hom (algebraMap R B[i] r) =
        (Spec.preimage q).hom (algebraMap R B[i] r) := by
    have hpq := congrArg Spec.preimage hc
    rw [Spec.preimage_comp, Spec.preimage_comp, Spec.preimage_map] at hpq
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hpq) r
  let : Algebra R K := ((Spec.preimage p).hom.comp (algebraMap R B[i])).toAlgebra
  let p' : B[i] →ₐ[R] K := ⟨(Spec.preimage p).hom, fun _ ↦ rfl⟩
  let q' : B[i] →ₐ[R] K := ⟨(Spec.preimage q).hom, fun r ↦ (hcoeff r).symm⟩
  have hpq : p' = q' := AlgHom.ext_of_adjoin_eq_top (adjoin_range_awayXRatio i)
    (Set.eqOn_range.mpr (funext h))
  exact Spec.preimage_injective (CommRingCat.hom_ext (congrArg AlgHom.toRingHom hpq))

end Proj

namespace Scheme.RationalMap

variable {X : Scheme.{u}} [IsIntegral X] [CompactSpace X] [QuasiSeparatedSpace X]
  [Finite ι]

/-- Every rational map over the coefficient ring to polynomial projective space is
represented by global sections of a line bundle, provided the source has an ample
line bundle. The partial map uses a coordinate section that is nonzero at the
generic point and represents the specified rational map. -/
theorem exists_projective_section_presentation (g : X ⤏ ℙ) (f : X ⟶ Spec (.of R))
    [g.IsOver f (Proj.toSpecCoeff 𝒜)] {A : LineBundleClass X} (hA : A.IsAmple) :
    ∃ (L : InvertibleSheaf X) (s : ι → Γ(L.obj, ⊤)) (i : ι)
      (hi : Dense (L.obj.nonvanishingLocus (s i) : Set X)),
      (L.obj.partialMapToProjectiveSpace f s i hi).toRationalMap = g := by
  classical
  obtain ⟨p, hp, rfl⟩ := g.exists_partialMap_over f (Proj.toSpecCoeff 𝒜)
  let F := p.fromFunctionField
  let z : Spec X.functionField := (⊥ : PrimeSpectrum X.functionField)
  have : Subsingleton (Spec X.functionField : Type u) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum X.functionField))
  let 𝒰 := Proj.polynomialAffineOpenCover R ι
  let i : ι := 𝒰.idx (F z)
  obtain ⟨x, hx⟩ := 𝒰.covers (F z)
  have hsub : Set.range F ⊆ Set.range j[i] := by
    rintro _ ⟨y, rfl⟩
    exact ⟨x, hx.trans (congrArg F (Subsingleton.elim z y))⟩
  let q := IsOpenImmersion.lift j[i] F hsub
  have hq : q ≫ j[i] = F := IsOpenImmersion.lift_fac _ _ _
  let c (j : ι) : X.functionField := (Spec.preimage q).hom (awayXRatio (R := R) i j)
  have hci : c i = 1 := by simp [c, awayXRatio_self]
  obtain ⟨L, s, hD, hs⟩ := exists_global_sections_of_ratios hA c i hci
  let D := L.obj.nonvanishingLocus (s i)
  have hdense : Dense (D : Set X) := D.isOpen.dense ⟨_, hD⟩
  refine ⟨L, s, i, hdense, RationalMap.eq_of_fromFunctionField_eq _ _ ?_⟩
  let q' : Spec X.functionField ⟶ Spec (.of B[i]) :=
    D.fromSpecStalkOfMem _ hD ≫ L.obj.toProjectiveSpaceChart f s i
  have hF : F ≫ Proj.toSpecCoeff 𝒜 = X.fromSpecStalk η[X] ≫ f := by
    simp only [F, PartialMap.fromSpecStalkOfMem, Category.assoc,
      PartialMap.over p f (Proj.toSpecCoeff 𝒜), Opens.fromSpecStalkOfMem_ι_assoc]
  have hq' : q' ≫ j[i] ≫ Proj.toSpecCoeff 𝒜 = X.fromSpecStalk η[X] ≫ f := by
    calc
      _ = D.fromSpecStalkOfMem _ hD ≫ L.obj.toProjectiveSpaceChart f s i ≫ j[i] ≫
          Proj.toSpecCoeff 𝒜 := Category.assoc _ _ _
      _ = D.fromSpecStalkOfMem _ hD ≫ D.ι ≫ f := by
        rw [Proj.awayι_toSpecCoeff, toProjectiveSpaceChart_toSpecCoeff]
      _ = _ := Opens.fromSpecStalkOfMem_ι_assoc D _ hD f
  have hqq' : q' = q := Proj.eq_of_awayXRatio i _ _
    (hq'.trans ((Category.assoc q _ _).symm.trans
      ((congrArg (· ≫ Proj.toSpecCoeff 𝒜) hq).trans hF)).symm) fun j ↦
      (genericProjectiveChart_preimage_awayXRatio i j hD).trans (hs j)
  rw [RationalMap.fromFunctionField_toRationalMap, RationalMap.fromFunctionField_toRationalMap]
  exact (congrArg (· ≫ j[i]) hqq').trans hq

end Scheme.RationalMap

end AlgebraicGeometry
