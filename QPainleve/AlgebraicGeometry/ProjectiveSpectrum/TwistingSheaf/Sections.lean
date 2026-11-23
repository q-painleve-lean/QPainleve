/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections
public import QPainleve.AlgebraicGeometry.LineBundle.Pullback
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Ample
import QPainleve.AlgebraicGeometry.LineBundle.FrameComparison
import TauCeti.AlgebraicGeometry.Restrict

/-!
# The twisting sheaf of a projective morphism defined by sections

The morphism defined by a generating family of sections of an invertible
sheaf pulls back the tautological twisting sheaf to that sheaf. The
isomorphism takes each pulled-back homogeneous coordinate to its defining
section. See the Stacks Project, [Tag 01ND](https://stacks.math.columbia.edu/tag/01ND).
-/

public noncomputable section

open CategoryTheory TopologicalSpace Opposite MvPolynomial
open TauCeti.AlgebraicGeometry
open HomogeneousLocalization

namespace AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] {ι : Type u}

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "𝒜" => MvPolynomial.homogeneousSubmodule ι R
local notation "ℙ" => Proj 𝒜
local notation "𝒪₁" => Proj.twistingSheaf 𝒜 1

namespace Proj

private theorem X_mem_degree_one (i : ι) : MvPolynomial.X i ∈ 𝒜 1 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X R i)

private theorem iSup_coordinateOpens : ⨆ i : ι, Proj.basicOpen 𝒜 (MvPolynomial.X i) = ⊤ :=
  Proj.iSup_basicOpen_eq_top _ _ (MvPolynomial.irrelevant_eq_span_X ι R).le

/-- Every integral twist on polynomial projective space is invertible. -/
instance isInvertible_polynomialTwistingSheaf (n : ℤ) :
    SheafOfModules.isInvertible ℙ (Proj.twistingSheaf 𝒜 n) :=
  Proj.isInvertible_twistingSheaf_of_iSup_eq_top MvPolynomial.X (X_mem_degree_one R)
    (iSup_coordinateOpens (ι := ι) R) n

/-- A homogeneous coordinate as a global section of the first twisting sheaf. -/
def polynomialCoordinateSection (i : ι) : Γ(𝒪₁, ⊤) :=
  Proj.toTwistingSheaf 𝒜 (n := 1) rfl ⊤ ⟨MvPolynomial.X i, X_mem_degree_one R i⟩

/-- A coordinate section generates precisely on its standard open. -/
@[simp]
theorem nonvanishingLocus_polynomialCoordinateSection (i : ι) :
    (𝒪₁).nonvanishingLocus (polynomialCoordinateSection R i) =
      Proj.basicOpen 𝒜 (MvPolynomial.X i) :=
  Proj.twistingSheaf.nonvanishingLocus_toTwistingSheaf MvPolynomial.X
    (X_mem_degree_one R) (iSup_coordinateOpens (ι := ι) R) 1
      ⟨MvPolynomial.X i, X_mem_degree_one R i⟩

private theorem polynomialCoordinateSection_restrict (i j : ι) :
    let U := Proj.basicOpen 𝒜 (MvPolynomial.X i)
    (𝒪₁).presheaf.map U.leTop.op (polynomialCoordinateSection R j) =
      Proj.awayToSection 𝒜 (MvPolynomial.X i) (TauCeti.MvPolynomial.awayXRatio i j) •
        Proj.twistingSheaf.chartGenerator 1 (MvPolynomial.X i)
          (X_mem_degree_one R i) U le_rfl := by
  dsimp only [polynomialCoordinateSection]
  rw [Proj.res_toTwistingSheaf]
  simpa only [TauCeti.MvPolynomial.awayXRatio_def, pow_one, Int.cast_ofNat_Int] using
    Proj.twistingSheaf.toTwistingSheaf_eq_smul_chartGenerator 1
      (⟨MvPolynomial.X j, X_mem_degree_one R j⟩ : 𝒜 1) (X_mem_degree_one R i)

end Proj

namespace Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules) [SheafOfModules.isInvertible X M]
  (f : X ⟶ Spec (.of R)) (s : ι → Γ(M, ⊤))
  (h : ⨆ i, M.nonvanishingLocus (s i) = ⊤)

local notation "g" => M.toProjectiveSpace f s h
local notation "U[" i "]" => M.nonvanishingLocus (s i)
local notation "D[" i "]" => Proj.basicOpen 𝒜 (MvPolynomial.X i)
local notation "L" => Functor.obj (pullback g) 𝒪₁
local notation "t" => fun j ↦
  Scheme.Hom.pullbackSectionsLE g 𝒪₁ ⊤ ⊤ (Eq.ge (Scheme.Hom.preimage_top g))
    (Proj.polynomialCoordinateSection R j)

private theorem le_preimage_coordinateOpen (i : ι) : U[i] ≤ g ⁻¹ᵁ D[i] :=
  (M.toProjectiveSpace_preimage_basicOpen f s h i).ge

private theorem toProjectiveSpace_appLE_awayXRatio (i j : ι) :
    (g).appLE D[i] U[i] (le_preimage_coordinateOpen R M f s h i)
        (Proj.awayToSection 𝒜 (MvPolynomial.X i) (TauCeti.MvPolynomial.awayXRatio i j)) =
      M.sectionRatio (M.presheaf.map (U[i]).leTop.op (s j))
        (M.presheaf.map (U[i]).leTop.op (s i)) (by simp) := by
  let e := Proj.basicOpenIsoSpec 𝒜 (MvPolynomial.X i) (Proj.X_mem_degree_one R i) one_pos
  let c := M.toProjectiveSpaceChart f s i
  let z : Away 𝒜 (MvPolynomial.X i) := TauCeti.MvPolynomial.awayXRatio i j
  let hU := le_preimage_coordinateOpen R M f s h i
  have heq : (g).resLE D[i] U[i] hU = c ≫ e.inv := by
    apply (cancel_mono (D[i]).ι).mp
    rw [Scheme.Hom.resLE_comp_ι, Category.assoc, Proj.basicOpenIsoSpec_inv_ι,
      M.toProjectiveSpaceChart_awayι]
  have heval : (D[i]).topIso.hom ≫ (g).appLE D[i] U[i] hU ≫ (U[i]).topIso.inv =
      (c ≫ e.inv).appTop :=
    ((g).resLE_app_top hU).symm.trans
      (congrArg Scheme.Hom.appTop heq)
  apply (ConcreteCategory.bijective_of_isIso (U[i]).topIso.inv).1
  have hv := ConcreteCategory.congr_hom heval
    ((D[i]).topIso.inv (Proj.awayToSection 𝒜 (MvPolynomial.X i) z))
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply] at hv
  rw [hv]
  have hz : (D[i]).topIso.inv (Proj.awayToSection 𝒜 (MvPolynomial.X i) z) =
      e.hom.appTop ((Scheme.ΓSpecIso _).inv z) := by
    have he' : (Proj.basicOpenToSpec 𝒜 (MvPolynomial.X i)).appTop = _ :=
      Proj.basicOpenToSpec_app_top 𝒜 (MvPolynomial.X i)
    rw [Proj.basicOpenIsoSpec_hom, he']
    simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
    rfl
  rw [hz, Scheme.Hom.comp_appTop]
  have hc : e.hom.appTop ≫ e.inv.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, e.inv_hom_id, Scheme.Hom.id_appTop]
  have hc' := ConcreteCategory.congr_hom hc ((Scheme.ΓSpecIso _).inv z)
  simp only [CommRingCat.comp_apply, CommRingCat.id_apply] at hc'
  simp only [CommRingCat.comp_apply, hc']
  exact M.toProjectiveSpaceChart_appTop_awayXRatio f s i j

private theorem pullbackSectionsLE_coordinate (i j : ι) :
    (L).presheaf.map (U[i]).leTop.op (t j) =
      (g).pullbackSectionsLE 𝒪₁ D[i] U[i] (le_preimage_coordinateOpen R M f s h i)
        ((𝒪₁).presheaf.map (D[i]).leTop.op (Proj.polynomialCoordinateSection R j)) := by
  let htop : U[i] ≤ g ⁻¹ᵁ ⊤ := le_top.trans (g).preimage_top.ge
  refine Eq.trans ?_ ((g).pullbackSectionsLE_map 𝒪₁ ⊤ U[i] htop (D[i]).leTop
    (le_preimage_coordinateOpen R M f s h i) (Proj.polynomialCoordinateSection R j)).symm
  simp only [Scheme.Hom.pullbackSectionsLE_apply, ← Functor.map_comp_apply]
  rfl

private theorem pullbackCoordinate_restrict (i j : ι) :
    (L).presheaf.map (U[i]).leTop.op (t j) =
      M.sectionRatio (M.presheaf.map (U[i]).leTop.op (s j))
        (M.presheaf.map (U[i]).leTop.op (s i)) (by simp) •
          (L).presheaf.map (U[i]).leTop.op (t i) := by
  rw [pullbackSectionsLE_coordinate R M f s h i j, pullbackSectionsLE_coordinate R M f s h i i,
    Proj.polynomialCoordinateSection_restrict R i j,
    map_smulₛₗ, Proj.polynomialCoordinateSection_restrict R i i,
    TauCeti.MvPolynomial.awayXRatio_self, map_one, one_smul]
  exact congrArg (· • _) (toProjectiveSpace_appLE_awayXRatio R M f s h i j)

private theorem le_nonvanishingLocus_pullbackCoordinate (i : ι) :
    U[i] ≤ (L).nonvanishingLocus (t i) := by
  let d := Proj.polynomialCoordinateSection R i
  have hD := Proj.nonvanishingLocus_polynomialCoordinateSection R i
  have hp : U[i] ≤ (L).nonvanishingLocus ((g).pullbackSections 𝒪₁ ⊤ d) := by
    calc
      U[i] ≤ g ⁻¹ᵁ D[i] := le_preimage_coordinateOpen R M f s h i
      _ = g ⁻¹ᵁ (𝒪₁).nonvanishingLocus d := congrArg ((g) ⁻¹ᵁ ·) hD.symm
      _ ≤ _ := (g).preimage_nonvanishingLocus_le 𝒪₁ d
  have he : t i = (L).presheaf.map (homOfLE (g).preimage_top.ge).op
      ((g).pullbackSections 𝒪₁ ⊤ d) :=
    (g).pullbackSectionsLE_apply 𝒪₁ ⊤ ⊤ (g).preimage_top.ge d
  rw [he, nonvanishingLocus_map]
  exact le_inf le_top hp

private theorem sectionRatio_pullbackCoordinate (i j : ι) :
    (L).sectionRatio ((L).presheaf.map (U[i]).leTop.op (t j))
        ((L).presheaf.map (U[i]).leTop.op (t i))
        ((L).le_nonvanishingLocus_map (U[i]).leTop (t i)
          (le_nonvanishingLocus_pullbackCoordinate R M f s h i)) =
      M.sectionRatio (M.presheaf.map (U[i]).leTop.op (s j))
        (M.presheaf.map (U[i]).leTop.op (s i)) (by simp) :=
  ((L).sectionRatio_eq_iff _).2 (pullbackCoordinate_restrict R M f s h i j).symm

/-- The pullback of the first twisting sheaf along the morphism defined by a
generating family of sections is the line bundle of those sections. -/
def pullbackTwistingSheafOneToProjectiveSpace : L ≅ M :=
  (L).isoOfSectionRatios M t s (fun i ↦ U[i])
    (le_nonvanishingLocus_pullbackCoordinate R M f s h) (fun _ ↦ le_rfl)
    (sectionRatio_pullbackCoordinate R M f s h) h

/-- The comparison sends the pulled-back homogeneous coordinates to the defining sections. -/
@[simp]
theorem pullbackTwistingSheafOneToProjectiveSpace_hom_app (i : ι) :
    (M.pullbackTwistingSheafOneToProjectiveSpace R f s h).hom.app ⊤ (t i) = s i := by
  exact isoOfSectionRatios_hom_app L M t s (fun i ↦ U[i])
    (le_nonvanishingLocus_pullbackCoordinate R M f s h) (fun _ ↦ le_rfl)
      (sectionRatio_pullbackCoordinate R M f s h) h i

/-- The comparison is characterized by its values on the pulled-back homogeneous coordinates. -/
theorem eq_pullbackTwistingSheafOneToProjectiveSpace_hom_iff (φ : L ⟶ M) :
    φ = (M.pullbackTwistingSheafOneToProjectiveSpace R f s h).hom ↔
      ∀ i, φ.app ⊤ (t i) = s i := by
  refine ⟨fun he i ↦ he.symm ▸ M.pullbackTwistingSheafOneToProjectiveSpace_hom_app R f s h i, ?_⟩
  exact eq_isoOfSectionRatios_hom L M t s (fun i ↦ U[i])
    (le_nonvanishingLocus_pullbackCoordinate R M f s h) (fun _ ↦ le_rfl)
    (sectionRatio_pullbackCoordinate R M f s h) h φ

end Scheme.Modules

end AlgebraicGeometry
