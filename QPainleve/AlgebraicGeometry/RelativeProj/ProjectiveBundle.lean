/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.SymmetricAlgebra
public import QPainleve.AlgebraicGeometry.VectorBundle.Affine
public import TauCeti.AlgebraicGeometry.RelativeProj.Map
public import TauCeti.AlgebraicGeometry.RelativeProj.TwistingSheaf
public import TauCeti.AlgebraicGeometry.VectorBundle.Quasicoherent

import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Pullback

/-!
# Affine charts of projective bundles

The relative projective spectrum of a sheaf's symmetric algebra is covered by
the projective spectra of symmetric algebras of its affine sections. A basis of
sections gives a polynomial projective-space chart. These identifications
respect the projections to the base and the twisting sheaves. On an inclusion
of affine charts, the coordinates change by the matrix of the restriction of
sections in the two frames. Fixed-rank vector bundles admit these charts near
each point of the base.

We use the quotient convention of [Stacks, Section 27.21][stacks-01OA] and the
graded section comparison `gradedSymmetricAlgebraSectionsEquiv`.

[stacks-01OA]: https://stacks.math.columbia.edu/tag/01OA
-/

public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Proj CategoryTheory
open TauCeti.AlgebraicGeometry CategoryTheory.CommMon

universe u

namespace TauCeti.AlgebraicGeometry.QuasicoherentSheaf

variable {X : Scheme.{u}} (F : QuasicoherentSheaf X) (U : X.AffineZariskiSite)

local notation "A[" F "]" =>
  ObjectProperty.FullSubcategory.obj (Functor.obj (gradedSymmetricAlgebra X) F)
local notation "R[" U "]" => CommRingCat.carrier (Functor.obj
  (PresheafedSpace.presheaf (SheafedSpace.toPresheafedSpace
    (LocallyRingedSpace.toSheafedSpace (Scheme.toLocallyRingedSpace X))))
  (Opposite.op (Scheme.AffineZariskiSite.toOpens U)))
local notation "M[" F "," U "]" => ModuleCat.carrier (Functor.obj
  (Scheme.Modules.sectionsFunctor (Scheme.AffineZariskiSite.toOpens U))
  (ObjectProperty.FullSubcategory.obj F))
local notation "𝒮[" F "," U "]" => TauCeti.SymmetricAlgebra.homogeneousSubmodule R[U] M[F,U]
local notation "𝒢[" F "," U "]" =>
  CommMon.gradedSectionsGrading A[F] (Scheme.AffineZariskiSite.toOpens U)

private def toGradedSections : 𝒮[F,U] →+*ᵍ 𝒢[F,U] where
  toRingHom := (gradedSymmetricAlgebraSectionsEquiv F U.property).toRingHom
  map_mem {n x} := (gradedSymmetricAlgebraSectionsEquiv_mem_grade_iff F U.property n x).mpr

private def fromGradedSections : 𝒢[F,U] →+*ᵍ 𝒮[F,U] where
  toRingHom := (gradedSymmetricAlgebraSectionsEquiv F U.property).symm.toRingHom
  map_mem {n x} hx := by
    let e := gradedSymmetricAlgebraSectionsEquiv F U.property
    exact (gradedSymmetricAlgebraSectionsEquiv_mem_grade_iff F U.property n (e.symm x)).mp
      (by rw [e.apply_symm_apply]; exact hx)

private theorem fromGradedSections_irrelevant_le :
    HomogeneousIdeal.irrelevant 𝒮[F,U] ≤
      (HomogeneousIdeal.irrelevant 𝒢[F,U]).map (fromGradedSections F U) :=
  HomogeneousIdeal.irrelevant_le_map_of_surjective _
    (gradedSymmetricAlgebraSectionsEquiv F U.property).symm.surjective

/-- The affine chart of the projective bundle is the projective spectrum of the
symmetric algebra of the sections on the affine open. -/
def projSymmetricAlgebraSectionsIso : Proj 𝒮[F,U] ≅ Proj 𝒢[F,U] :=
  mapIso (fromGradedSections F U) (toGradedSections F U)
    (gradedSymmetricAlgebraSectionsEquiv F U.property).symm_apply_apply
    (gradedSymmetricAlgebraSectionsEquiv F U.property).apply_symm_apply

private theorem projSymmetricAlgebraSectionsIso_hom :
    (F.projSymmetricAlgebraSectionsIso U).hom =
      map (fromGradedSections F U) (fromGradedSections_irrelevant_le F U) :=
  mapIso_hom _ _ _ _

/-- The affine symmetric algebra comparison commutes with the projections to the
spectrum of the section ring. -/
@[reassoc (attr := simp)]
theorem projSymmetricAlgebraSectionsIso_hom_toSpecCoeff :
    (F.projSymmetricAlgebraSectionsIso U).hom ≫ toSpecCoeff 𝒢[F,U] =
      TauCeti.SymmetricAlgebra.projToSpec R[U] M[F,U] := by
  rw [projSymmetricAlgebraSectionsIso_hom, TauCeti.SymmetricAlgebra.projToSpec_def,
    ← toSpecCoeff_def]
  apply map_toSpecCoeff
  intro r
  apply Subtype.ext
  rw [GradedRingHom.gradedZeroRingHom_apply_coe, SetLike.GradeZero.coe_algebraMap,
    SetLike.GradeZero.coe_algebraMap]
  exact (gradedSymmetricAlgebraSectionsEquiv F U.property).symm.commutes r

/-- The affine symmetric algebra comparison pulls back every integral twist to the
same twist on the projective spectrum of the symmetric algebra of sections. -/
def projSymmetricAlgebraSectionsIsoPullbackTwistingSheafIso (n : ℤ) :
    (Scheme.Modules.pullback (F.projSymmetricAlgebraSectionsIso U).hom).obj
      (twistingSheaf 𝒢[F,U] n) ≅ twistingSheaf 𝒮[F,U] n := by
  rw [projSymmetricAlgebraSectionsIso_hom]
  refine pullbackTwistingSheafIso (fromGradedSections F U) (fromGradedSections_irrelevant_le F U)
    (fun a : 𝒢[F,U] 1 ↦ a.val) Subtype.property ?_ n
  exact iSup_basicOpen_eq_top_of_adjoin_eq_top _
    (CommMon.isGeneratedInDegreeOne_iff.mp
      (isGeneratedInDegreeOne_gradedSymmetricAlgebra F) U.toOpens U.property)

section Map

variable {F} {G : QuasicoherentSheaf X} (q : F ⟶ G)

local notation "φ" =>
  InducedCategory.Hom.hom (CategoryTheory.Functor.map (gradedSymmetricAlgebra X) q)
local notation "qΓ" => ModuleCat.Hom.hom (CategoryTheory.Functor.map
  (Scheme.Modules.sectionsFunctor (Scheme.AffineZariskiSite.toOpens U)) (InducedCategory.Hom.hom q))

private theorem fromGradedSections_comp_map :
    (fromGradedSections G U).comp (gradedSectionsGradedHom φ U.toOpens) =
      (SymmetricAlgebra.gradedMap R[U] qΓ).comp (fromGradedSections F U) := by
  ext a : 1
  let e := gradedSymmetricAlgebraSectionsEquiv F U.property
  obtain ⟨x, rfl⟩ := e.surjective a
  have h := gradedSymmetricAlgebraSectionsEquiv_naturality F q U.property x
  erw [GradedRingHom.comp_apply, GradedRingHom.comp_apply, gradedSectionsGradedHom_apply,
    SymmetricAlgebra.gradedMap_apply]
  exact ((gradedSymmetricAlgebraSectionsEquiv G U.property).symm_apply_eq.mpr h).trans
    (congrArg (SymmetricAlgebra.map R[U] qΓ) (e.symm_apply_apply x)).symm

/-- On an affine open of the base, the relative projective morphism induced
by a map of quasicoherent sheaves is the projective spectrum of the symmetric
algebra map on sections. -/
@[reassoc]
theorem projSymmetricAlgebraSectionsIso_hom_comp_relativeProjMap (hφ)
    (hq : HomogeneousIdeal.irrelevant 𝒮[G,U] ≤
      (HomogeneousIdeal.irrelevant 𝒮[F,U]).map (SymmetricAlgebra.gradedMap R[U] qΓ)) :
    (G.projSymmetricAlgebraSectionsIso U).hom ≫
        (relativeProjFunctorMap φ hφ).app U =
      Proj.map (SymmetricAlgebra.gradedMap R[U] qΓ) hq ≫
        (F.projSymmetricAlgebraSectionsIso U).hom := by
  rw [projSymmetricAlgebraSectionsIso_hom, projSymmetricAlgebraSectionsIso_hom,
    relativeProjFunctorMap_app]
  refine (Proj.map_comp _ _ _ _).symm.trans
    ((Proj.map_congr (fromGradedSections_comp_map U q) _ _).trans (Proj.map_comp _ _ _ _))

end Map

local notation "ι₀[" j "]" =>
  CategoryTheory.Functor.map (Scheme.AffineZariskiSite.toOpensFunctor X) j

section Restriction

variable {U} {V : X.AffineZariskiSite} (j : V ⟶ U)

/-- Restriction on the symmetric algebras of affine sections, with scalars
restricted along the corresponding homomorphism of section rings. -/
def symmetricAlgebraSectionsRestrict : 𝒮[F,U] →+*ᵍ 𝒮[F,V] where
  toRingHom := SymmetricAlgebra.mapₛₗ
    ((ModuleCat.semilinearMapAddEquiv (X.presheaf.map (ι₀[j]).op).hom _ _).symm
      (PresheafOfModulesOfCommRing.map (R := X.presheaf) F.obj.val (ι₀[j]).op))
  map_mem := SymmetricAlgebra.mapₛₗ_mem_homogeneousSubmodule _

/-- Restriction of coefficients in the symmetric algebra of affine sections. -/
@[simp]
theorem symmetricAlgebraSectionsRestrict_algebraMap (r : R[U]) :
    dsimp% only [Scheme.Modules.sectionsFunctor_obj, sheafCompose_obj_obj, Functor.comp_obj,
      CommRingCat.forgetToRingCat_obj]
      (F.symmetricAlgebraSectionsRestrict j (algebraMap R[U] (SymmetricAlgebra R[U] M[F,U]) r)) =
      algebraMap R[V] (SymmetricAlgebra R[V] (F.obj.val.obj (Opposite.op V.toOpens)))
        (X.presheaf.map (ι₀[j]).op r) :=
  SymmetricAlgebra.mapₛₗ_algebraMap _ r

/-- Restriction of a degree-one generator in the symmetric algebra of affine sections. -/
@[simp]
theorem symmetricAlgebraSectionsRestrict_ι (m : F.obj.val.obj (Opposite.op U.toOpens)) :
    dsimp% only [Scheme.Modules.sectionsFunctor_obj, sheafCompose_obj_obj, Functor.comp_obj,
      CommRingCat.forgetToRingCat_obj]
      (F.symmetricAlgebraSectionsRestrict j (SymmetricAlgebra.ι R[U] M[F,U] m)) =
      SymmetricAlgebra.ι R[V] (F.obj.val.obj (Opposite.op V.toOpens))
        (F.obj.val.map (ι₀[j]).op m) :=
  SymmetricAlgebra.mapₛₗ_ι _ m

private theorem fromGradedSections_comp_restrict :
    (fromGradedSections F V).comp (A[F].restrictGradedSectionsGradedHom (ι₀[j])) =
      (F.symmetricAlgebraSectionsRestrict j).comp (fromGradedSections F U) := by
  ext a : 1
  let e := gradedSymmetricAlgebraSectionsEquiv F U.property
  obtain ⟨x, rfl⟩ := e.surjective a
  have h := gradedSymmetricAlgebraSectionsEquiv_restrict F U.property V.property (ι₀[j]) x
  erw [GradedRingHom.comp_apply, GradedRingHom.comp_apply,
    restrictGradedSectionsGradedHom_apply]
  exact ((gradedSymmetricAlgebraSectionsEquiv F V.property).symm_apply_eq.mpr h).trans
    (congrArg (F.symmetricAlgebraSectionsRestrict j) (e.symm_apply_apply x)).symm

/-- The symmetric-algebra restriction induces a morphism on projective spectra
for any inclusion in the affine Zariski site. -/
theorem irrelevant_le_map_symmetricAlgebraSectionsRestrict :
    HomogeneousIdeal.irrelevant 𝒮[F,V] ≤
      (HomogeneousIdeal.irrelevant 𝒮[F,U]).map (F.symmetricAlgebraSectionsRestrict j) := by
  have h := HomogeneousIdeal.irrelevant_le_map_comp
    (A[F].irrelevant_le_map_restrictGradedSections_toOpensFunctor j)
    (fromGradedSections_irrelevant_le F V)
  erw [fromGradedSections_comp_restrict F j, HomogeneousIdeal.map_comp] at h
  have hU : (HomogeneousIdeal.irrelevant 𝒢[F,U]).map (fromGradedSections F U) ≤
      HomogeneousIdeal.irrelevant 𝒮[F,U] := by
    apply (HomogeneousIdeal.map_le_iff_le_comap _).mpr
    exact (HomogeneousIdeal.irrelevant_le _).mpr fun n hn a ha ↦
      HomogeneousIdeal.mem_irrelevant_of_mem _ hn ((fromGradedSections F U).map_mem ha)
  exact h.trans (HomogeneousIdeal.map_mono _ hU)

/-- The symmetric-algebra chart comparison intertwines restriction of sections
with the transition morphism in the relative Proj diagram. -/
@[reassoc]
theorem projSymmetricAlgebraSectionsIso_hom_restrict :
    (F.projSymmetricAlgebraSectionsIso V).hom ≫ A[F].relativeProjFunctor.map j =
      Proj.map (F.symmetricAlgebraSectionsRestrict j)
        (F.irrelevant_le_map_symmetricAlgebraSectionsRestrict j) ≫
        (F.projSymmetricAlgebraSectionsIso U).hom := by
  have hj : A[F].relativeProjFunctor.map j =
      Proj.map (A[F].restrictGradedSectionsGradedHom (ι₀[j]))
        (A[F].irrelevant_le_map_restrictGradedSections_toOpensFunctor j) :=
    A[F].relativeProjGluingData_functor_map j
  rw [projSymmetricAlgebraSectionsIso_hom, projSymmetricAlgebraSectionsIso_hom, hj]
  refine (Proj.map_comp _ _ _ _).symm.trans
    ((Proj.map_congr (fromGradedSections_comp_restrict F j) _ _).trans (Proj.map_comp _ _ _ _))

end Restriction

attribute [local instance] MvPolynomial.gradedAlgebra

variable {ι : Type u}
  (b : Module.Basis ι Γ(X, U.toOpens) ((Scheme.Modules.sectionsFunctor U.toOpens).obj F.obj))

local notation "𝒫[" U "," ι "]" => MvPolynomial.homogeneousSubmodule ι R[U]

private abbrev polynomialChartIso :
    Proj 𝒫[U,ι] ≅ Proj 𝒢[F,U] :=
  b.polynomialProjIso ≪≫ F.projSymmetricAlgebraSectionsIso U

private theorem polynomialChartIso_hom_toSpecCoeff :
    (polynomialChartIso F U b).hom ≫ toSpecCoeff 𝒢[F,U] = toSpecCoeff 𝒫[U,ι] := by
  rw [polynomialChartIso, Iso.trans_hom, Category.assoc,
    F.projSymmetricAlgebraSectionsIso_hom_toSpecCoeff U, b.polynomialProjIso_hom_over]

/-- A frame of sections on an affine open gives the polynomial projective-space
chart of the native relative projective spectrum. -/
def relativeProjPolynomialChart : Proj 𝒫[U,ι] ⟶ A[F].relativeProj :=
  (polynomialChartIso F U b).hom ≫ A[F].relativeProjCover.f U

/-- The polynomial chart is the scheme-theoretic preimage of its affine base open. -/
theorem isPullback_relativeProjPolynomialChart :
    IsPullback (toSpecCoeff 𝒫[U,ι] ≫ U.property.isoSpec.inv)
      (F.relativeProjPolynomialChart U b) U.toOpens.ι A[F].relativeProjToBase := by
  refine (A[F].isPullback_relativeProjCover U).of_iso' (polynomialChartIso F U b)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ (Category.comp_id _).symm (by simp) (by simp)
  exact (Category.assoc ..).symm.trans
    ((congrArg (· ≫ U.property.isoSpec.inv) (polynomialChartIso_hom_toSpecCoeff F U b)).trans
      (Category.comp_id _).symm)

/-- The polynomial chart is an open immersion into the relative projective spectrum. -/
instance isOpenImmersion_relativeProjPolynomialChart :
    IsOpenImmersion (F.relativeProjPolynomialChart U b) :=
  MorphismProperty.of_isPullback (F.isPullback_relativeProjPolynomialChart U b) inferInstance

/-- The polynomial chart lies over the given affine open. -/
@[reassoc (attr := simp)]
theorem relativeProjPolynomialChart_toBase :
    F.relativeProjPolynomialChart U b ≫ A[F].relativeProjToBase =
      toSpecCoeff 𝒫[U,ι] ≫ U.property.fromSpec :=
  (F.isPullback_relativeProjPolynomialChart U b).w.symm.trans (Category.assoc ..)

/-- The polynomial chart pulls back the relative twisting sheaf to the corresponding
twisting sheaf of polynomial projective space. -/
def relativeProjPolynomialChartPullbackTwistingSheafIso (n : ℤ) :
    (Scheme.Modules.pullback (F.relativeProjPolynomialChart U b)).obj
      (A[F].relativeProjTwistingSheaf n) ≅ twistingSheaf 𝒫[U,ι] n := by
  let e := b.polynomialProjIso.hom
  let f := (F.projSymmetricAlgebraSectionsIso U).hom
  let j := A[F].relativeProjCover.f U
  let L := A[F].relativeProjTwistingSheaf n
  let τ := ((Scheme.Modules.restrictFunctorIsoPullback j).app L).symm ≪≫
    A[F].restrictRelativeProjTwistingSheafIso n U
  let σ := (Scheme.Modules.pullbackComp e f).symm.app (twistingSheaf 𝒢[F,U] n) ≪≫
    (Scheme.Modules.pullback e).mapIso
      (F.projSymmetricAlgebraSectionsIsoPullbackTwistingSheafIso U n)
  exact (Scheme.Modules.pullbackComp (e ≫ f) j).symm.app L ≪≫
    (Scheme.Modules.pullback (e ≫ f)).mapIso τ ≪≫ σ ≪≫
    b.polynomialProjIsoPullbackTwistingSheafIso n

section PolynomialRestriction

variable {U} {V : X.AffineZariskiSite} (j : V ⟶ U)
  {κ : Type u}
  (c : Module.Basis κ Γ(X, V.toOpens) ((Scheme.Modules.sectionsFunctor V.toOpens).obj F.obj))

/-- Restriction of the polynomial coordinate rings in two affine frames. Its degree-one
part is the semilinear restriction of sections written in the two bases. -/
def polynomialSectionsRestrict : 𝒫[U,ι] →+*ᵍ 𝒫[V,κ] :=
  c.toPolynomialGradedHom.comp ((F.symmetricAlgebraSectionsRestrict j).comp
    b.fromPolynomialGradedHom)

/-- The coefficients of a polynomial restrict as functions on the affine base. -/
@[simp]
theorem polynomialSectionsRestrict_C (r : R[U]) :
    F.polynomialSectionsRestrict b j c (MvPolynomial.C r) =
      MvPolynomial.C (X.presheaf.map (ι₀[j]).op r) := by
  rw [polynomialSectionsRestrict, GradedRingHom.comp_apply, GradedRingHom.comp_apply,
    Module.Basis.fromPolynomialGradedHom_apply, ← MvPolynomial.algebraMap_eq,
    AlgEquiv.commutes]
  -- The restriction formula uses presheaf sections, while the frames use the sections functor.
  erw [symmetricAlgebraSectionsRestrict_algebraMap, Module.Basis.toPolynomialGradedHom_apply]
  exact (SymmetricAlgebra.equivMvPolynomial c).commutes _

/-- Each variable pulls back to the linear combination of target variables given by
the coordinates of its restricted basis section. -/
@[simp]
theorem polynomialSectionsRestrict_X (i : ι) :
    F.polynomialSectionsRestrict b j c (MvPolynomial.X i) =
      (c.repr (F.obj.val.map (ι₀[j]).op (b i))).sum
        (fun k a ↦ a • MvPolynomial.X k) := by
  rw [polynomialSectionsRestrict, GradedRingHom.comp_apply, GradedRingHom.comp_apply,
    Module.Basis.fromPolynomialGradedHom_apply, SymmetricAlgebra.equivMvPolynomial_symm_X]
  erw [symmetricAlgebraSectionsRestrict_ι, Module.Basis.toPolynomialGradedHom_apply]
  let m := F.obj.val.map (ι₀[j]).op (b i)
  let f := (SymmetricAlgebra.equivMvPolynomial c).toLinearMap ∘ₗ SymmetricAlgebra.ι R[V] M[F,V]
  have h := congrArg f (c.linearCombination_repr m)
  rw [Finsupp.linearCombination_apply, map_finsuppSum] at h
  have h' : (c.repr m).sum (fun k a ↦ a • MvPolynomial.X k) = f m := by
    simpa only [f, LinearMap.comp_apply, map_smul, AlgEquiv.toLinearMap_apply,
      SymmetricAlgebra.equivMvPolynomial_ι_apply] using h
  exact h'.symm

/-- Restriction in polynomial coordinates induces the projective chart transition. -/
theorem irrelevant_le_map_polynomialSectionsRestrict :
    HomogeneousIdeal.irrelevant 𝒫[V,κ] ≤
      (HomogeneousIdeal.irrelevant 𝒫[U,ι]).map (F.polynomialSectionsRestrict b j c) :=
  HomogeneousIdeal.irrelevant_le_map_comp
    (HomogeneousIdeal.irrelevant_le_map_comp
      (HomogeneousIdeal.irrelevant_le_map_of_surjective _ b.fromPolynomialGradedHom_surjective)
      (F.irrelevant_le_map_symmetricAlgebraSectionsRestrict j))
    (HomogeneousIdeal.irrelevant_le_map_of_surjective _ c.toPolynomialGradedHom_surjective)

private theorem map_polynomialSectionsRestrict :
    Proj.map (F.polynomialSectionsRestrict b j c)
        (F.irrelevant_le_map_polynomialSectionsRestrict b j c) =
      c.polynomialProjIso.hom ≫
        Proj.map (F.symmetricAlgebraSectionsRestrict j)
          (F.irrelevant_le_map_symmetricAlgebraSectionsRestrict j) ≫ b.polynomialProjIso.inv := by
  rw [Module.Basis.polynomialProjIso_hom, Module.Basis.polynomialProjIso_inv]
  exact (Proj.map_comp _ _ _ _).trans (congrArg (_ ≫ ·) (Proj.map_comp _ _ _ _))

private theorem polynomialProjIso_hom_restrict :
    (polynomialChartIso F V c).hom ≫
        A[F].relativeProjFunctor.map j =
      Proj.map (F.polynomialSectionsRestrict b j c)
        (F.irrelevant_le_map_polynomialSectionsRestrict b j c) ≫
        (polynomialChartIso F U b).hom := by
  rw [polynomialChartIso, Iso.trans_hom, Iso.trans_hom, map_polynomialSectionsRestrict F b j c]
  refine (Category.assoc ..).trans ?_
  rw [F.projSymmetricAlgebraSectionsIso_hom_restrict j]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

/-- Changing polynomial frames over an affine inclusion gives the base change of
the source projective space along the restriction of the coefficient ring. -/
theorem isPullback_map_polynomialSectionsRestrict :
    IsPullback (Proj.map (F.polynomialSectionsRestrict b j c)
        (F.irrelevant_le_map_polynomialSectionsRestrict b j c))
      (toSpecCoeff 𝒫[V,κ]) (toSpecCoeff 𝒫[U,ι]) (Spec.map (X.presheaf.map (ι₀[j]).op)) := by
  refine (A[F].equifibered_relativeProjToSpec j).of_iso'
    (polynomialChartIso F V c) (polynomialChartIso F U b) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · exact polynomialProjIso_hom_restrict F b j c
  · exact (polynomialChartIso_hom_toSpecCoeff F V c).trans (Category.comp_id _).symm
  · exact (polynomialChartIso_hom_toSpecCoeff F U b).trans (Category.comp_id _).symm
  · exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- The polynomial transition given by restricting a frame and expressing it in a
new frame commutes with the inclusions into the same relative projective spectrum. -/
@[reassoc]
theorem map_polynomialSectionsRestrict_comp_relativeProjPolynomialChart :
    Proj.map (F.polynomialSectionsRestrict b j c)
        (F.irrelevant_le_map_polynomialSectionsRestrict b j c) ≫ F.relativeProjPolynomialChart U b =
      F.relativeProjPolynomialChart V c := by
  let e := (polynomialChartIso F U b).hom
  let d := (polynomialChartIso F V c).hom
  let p := Proj.map (F.polynomialSectionsRestrict b j c)
    (F.irrelevant_le_map_polynomialSectionsRestrict b j c)
  let u := A[F].relativeProjCover.f U
  calc
    p ≫ F.relativeProjPolynomialChart U b = (p ≫ e) ≫ u := (Category.assoc p e u).symm
    _ = (d ≫ A[F].relativeProjFunctor.map j) ≫ u :=
      congrArg (· ≫ u) (polynomialProjIso_hom_restrict F b j c).symm
    _ = F.relativeProjPolynomialChart V c :=
      (Category.assoc ..).trans
        (congrArg (d ≫ ·) (Limits.colimit.w (A[F].relativeProjGluingData.functor) j))

/-- Over the same open, the polynomial transition between any two frames is an isomorphism. -/
theorem isIso_map_polynomialSectionsRestrict_id
    (c : Module.Basis κ Γ(X, U.toOpens) ((Scheme.Modules.sectionsFunctor U.toOpens).obj F.obj)) :
    IsIso (Proj.map (F.polynomialSectionsRestrict b (𝟙 U) c)
      (F.irrelevant_le_map_polynomialSectionsRestrict b (𝟙 U) c)) := by
  have h := F.isPullback_map_polynomialSectionsRestrict b (𝟙 U) c
  erw [CategoryTheory.Functor.map_id, Spec.map_id] at h
  exact h.isIso_fst_of_isIso

/-- The projective transition from a frame to itself over the identity is the identity. -/
@[simp]
theorem map_polynomialSectionsRestrict_id :
    Proj.map (F.polynomialSectionsRestrict b (𝟙 U) b)
      (F.irrelevant_le_map_polynomialSectionsRestrict b (𝟙 U) b) = 𝟙 _ := by
  apply (cancel_mono (F.relativeProjPolynomialChart U b)).mp
  rw [F.map_polynomialSectionsRestrict_comp_relativeProjPolynomialChart b (𝟙 U) b,
    Category.id_comp]

/-- Projective frame transitions compose along inclusions of the affine opens. -/
theorem map_polynomialSectionsRestrict_comp {W : X.AffineZariskiSite} (k : W ⟶ V) {ν : Type u}
    (d : Module.Basis ν Γ(X, W.toOpens) ((Scheme.Modules.sectionsFunctor W.toOpens).obj F.obj)) :
    Proj.map (F.polynomialSectionsRestrict b (k ≫ j) d)
        (F.irrelevant_le_map_polynomialSectionsRestrict b (k ≫ j) d) =
      Proj.map (F.polynomialSectionsRestrict c k d)
          (F.irrelevant_le_map_polynomialSectionsRestrict c k d) ≫
        Proj.map (F.polynomialSectionsRestrict b j c)
          (F.irrelevant_le_map_polynomialSectionsRestrict b j c) := by
  apply (cancel_mono (F.relativeProjPolynomialChart U b)).mp
  rw [Category.assoc, F.map_polynomialSectionsRestrict_comp_relativeProjPolynomialChart b (k ≫ j) d,
    F.map_polynomialSectionsRestrict_comp_relativeProjPolynomialChart b j c,
    F.map_polynomialSectionsRestrict_comp_relativeProjPolynomialChart c k d]

end PolynomialRestriction

end TauCeti.AlgebraicGeometry.QuasicoherentSheaf

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.FixedRank

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Over an affine neighbourhood of any base point, the projective bundle of a rank-`r`
vector bundle is polynomial projective space on `r` variables. The chart identifies every
relative twist with the corresponding polynomial twist. The neighbourhood can be taken
inside any prescribed open containing the point. -/
theorem exists_relativeProjPolynomialChart {X : Scheme.{u}} {r : ℕ} (E : FixedRank X r)
    {x : X} {W : X.Opens} (hx : x ∈ W) :
    let F := (FiniteLocallyFreeSheaf.toQuasicoherent X).obj E.obj
    let A := ((gradedSymmetricAlgebra X).obj F).obj
    ∃ (U : X.AffineZariskiSite) (_ : x ∈ U.toOpens) (_ : U.toOpens ≤ W),
      let P := MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin r)) Γ(X, U.toOpens)
      ∃ j : Proj P ⟶ A.relativeProj,
        IsPullback (toSpecCoeff P ≫ U.property.isoSpec.inv) j U.toOpens.ι A.relativeProjToBase ∧
        ∀ n : ℤ, Nonempty ((Scheme.Modules.pullback j).obj (A.relativeProjTwistingSheaf n) ≅
          twistingSheaf P n) := by
  obtain ⟨V, hV, hxV, hVW, ⟨b⟩⟩ := E.exists_isAffineOpen_basis_sections_le hx
  let U : X.AffineZariskiSite := ⟨V, hV⟩
  let F := (FiniteLocallyFreeSheaf.toQuasicoherent X).obj E.obj
  have b' : Module.Basis (ULift.{u} (Fin r)) Γ(X, V)
      ((Scheme.Modules.sectionsFunctor V).obj F.obj) := by
    simpa only [F, FiniteLocallyFreeSheaf.toQuasicoherent_obj_obj] using b
  exact ⟨U, hxV, hVW, F.relativeProjPolynomialChart U b',
    F.isPullback_relativeProjPolynomialChart U b',
    fun n ↦ ⟨F.relativeProjPolynomialChartPullbackTwistingSheafIso U b' n⟩⟩

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.FixedRank
