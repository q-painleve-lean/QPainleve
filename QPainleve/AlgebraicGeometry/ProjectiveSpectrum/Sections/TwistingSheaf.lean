/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Ample
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections
import QPainleve.AlgebraicGeometry.LineBundle.Pullback
import QPainleve.AlgebraicGeometry.LineBundle.Frame
import TauCeti.RingTheory.MvPolynomial.Homogeneous
import TauCeti.AlgebraicGeometry.Restrict

/-!
# The twisting sheaf of a projective morphism from sections

Pulling back the tautological sections of `𝒪(1)` along the morphism defined by a generating
family of a line bundle recovers that line bundle with its given sections. On each standard
open, the comparison is multiplication by the prescribed frame section. This is the
pullback computation in the Stacks Project, [Lemma 27.13.1](https://stacks.math.columbia.edu/tag/01NE).
-/

public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] {ι : Type u}

local notation "𝒜" => MvPolynomial.homogeneousSubmodule ι R
local notation "T" => Proj.twistingSheaf 𝒜 1
local notation "U[" i "]" => Proj.basicOpen 𝒜 (MvPolynomial.X i)

private theorem X_mem_degreeOne (i : ι) : MvPolynomial.X i ∈ 𝒜 1 :=
  (MvPolynomial.mem_homogeneousSubmodule ..).mpr (MvPolynomial.isHomogeneous_X R i)

private theorem iSup_coordinateOpen : (⨆ i : ι, U[i]) = ⊤ :=
  Proj.iSup_basicOpen_eq_top _ _ (MvPolynomial.irrelevant_eq_span_X ι R).le

namespace Proj

/-- Twisting sheaves on polynomial projective space are invertible. -/
instance isInvertible_polynomialTwistingSheaf (n : ℤ) :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible (Proj 𝒜) (Proj.twistingSheaf 𝒜 n) :=
  Proj.isInvertible_twistingSheaf_of_iSup_eq_top _ (X_mem_degreeOne (R := R))
    (iSup_coordinateOpen (R := R) (ι := ι)) n

/-- The global section of `𝒪(1)` on polynomial projective space given by the variable `X i`. -/
def polynomialCoordinateSection (i : ι) : Γ(T, ⊤) :=
  Proj.toTwistingSheaf 𝒜 rfl ⊤ ⟨MvPolynomial.X i, X_mem_degreeOne i⟩

/-- A coordinate section is the image of its homogeneous variable in the first twist. -/
theorem polynomialCoordinateSection_def (i : ι) :
    polynomialCoordinateSection (R := R) i =
      Proj.toTwistingSheaf 𝒜 (rfl : (1 : ℤ) = 1) ⊤
        ⟨MvPolynomial.X i, (MvPolynomial.mem_homogeneousSubmodule ..).mpr
          (MvPolynomial.isHomogeneous_X R i)⟩ := (rfl)

/-- A homogeneous coordinate section is nonvanishing exactly on its standard open. -/
@[simp]
theorem nonvanishingLocus_polynomialCoordinateSection (i : ι) :
    (T).nonvanishingLocus (polynomialCoordinateSection (R := R) i) = U[i] :=
  Proj.twistingSheaf.nonvanishingLocus_toTwistingSheaf _ (X_mem_degreeOne (R := R))
    (iSup_coordinateOpen (R := R) (ι := ι)) 1 _

/-- On a standard open, each coordinate section is its normalized ratio times the frame
section of that open. -/
theorem res_polynomialCoordinateSection_eq_smul (i j : ι) :
    (T).presheaf.map (U[i]).leTop.op (Proj.polynomialCoordinateSection (R := R) j) =
      Proj.awayToSection 𝒜 (MvPolynomial.X i) (TauCeti.MvPolynomial.awayXRatio i j) •
        (T).presheaf.map (U[i]).leTop.op (Proj.polynomialCoordinateSection (R := R) i) := by
  have hi := Proj.twistingSheaf.toTwistingSheaf_eq_smul_chartGenerator
    1 (⟨MvPolynomial.X i, X_mem_degreeOne (R := R) i⟩ : 𝒜 1) (X_mem_degreeOne i)
  have hj := Proj.twistingSheaf.toTwistingSheaf_eq_smul_chartGenerator
    1 (⟨MvPolynomial.X j, X_mem_degreeOne (R := R) j⟩ : 𝒜 1) (X_mem_degreeOne i)
  simp only [Proj.polynomialCoordinateSection, Proj.res_toTwistingSheaf]
  rw [hj, hi]
  simp only [← TauCeti.MvPolynomial.awayXRatio_def, TauCeti.MvPolynomial.awayXRatio_self,
    map_one, one_smul]

end Proj

namespace Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules)
  [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M]
  (f : X ⟶ Spec (.of R)) (s : ι → Γ(M, ⊤))

local notation "D[" i "]" => M.nonvanishingLocus (s i)

private theorem toProjectiveSpace_appLE_awayXRatio
    (h : (⨆ i, M.nonvanishingLocus (s i)) = ⊤) (i j : ι) :
    (M.toProjectiveSpace f s h).appLE U[i] D[i]
      ((M.toProjectiveSpace_preimage_basicOpen f s h i).ge)
      (Proj.awayToSection 𝒜 (MvPolynomial.X i) (TauCeti.MvPolynomial.awayXRatio i j)) =
      M.sectionRatio (M.presheaf.map (D[i]).leTop.op (s j))
        (M.presheaf.map (D[i]).leTop.op (s i))
        (by rw [M.nonvanishingLocus_map, inf_idem]) := by
  let g := M.toProjectiveSpace f s h
  let hD : D[i] ≤ g ⁻¹ᵁ U[i] := (M.toProjectiveSpace_preimage_basicOpen f s h i).ge
  let e := Proj.basicOpenIsoSpec 𝒜 (MvPolynomial.X i) (X_mem_degreeOne (R := R) i) one_pos
  have he : g.resLE U[i] D[i] hD ≫ e.hom = M.toProjectiveSpaceChart f s i := by
    apply (cancel_mono (e.inv ≫ (U[i]).ι)).mp
    rw [Category.assoc, Iso.hom_inv_id_assoc, Scheme.Hom.resLE_comp_ι]
    exact (M.toProjectiveSpaceChart_awayι f s h i).symm.trans
      (congrArg (M.toProjectiveSpaceChart f s i ≫ ·)
        (Proj.basicOpenIsoSpec_inv_ι 𝒜 _ (X_mem_degreeOne i) one_pos).symm)
  have happ := congrArg (fun k ↦ k.appTop.hom
    ((Scheme.ΓSpecIso _).inv.hom (TauCeti.MvPolynomial.awayXRatio (R := R) i j))) he
  rw [M.toProjectiveSpaceChart_appTop_awayXRatio, Scheme.Hom.comp_appTop] at happ
  have heapp : e.hom.appTop = (Scheme.ΓSpecIso _).hom ≫
      Proj.awayToSection 𝒜 (MvPolynomial.X i) ≫ (U[i]).topIso.inv :=
    Proj.basicOpenToSpec_app_top _ _
  rw [heapp] at happ
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    Iso.inv_hom_id_apply] at happ
  -- The pullback on the two open subschemes includes their top-section identifications.
  have hrs : (g.resLE U[i] D[i] hD).appTop =
      (U[i]).topIso.hom ≫ g.appLE U[i] D[i] hD ≫ (D[i]).topIso.inv :=
    Scheme.Hom.resLE_app_top g hD
  rw [hrs] at happ
  apply (ConcreteCategory.bijective_of_isIso (D[i]).topIso.inv).injective
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    Iso.inv_hom_id_apply] at happ
  exact happ

/-- The pullback of `𝒪(1)` along the map defined by covering sections is isomorphic to the
line bundle, carrying each pulled-back homogeneous coordinate to its defining section. -/
theorem exists_iso_pullbackTwistingSheaf_toProjectiveSpace
    (h : (⨆ i, M.nonvanishingLocus (s i)) = ⊤) :
    ∃ e : (pullback (M.toProjectiveSpace f s h)).obj T ≅ M,
      ∀ i, e.hom.app ⊤ ((M.toProjectiveSpace f s h).pullbackSections T ⊤
        (Proj.polynomialCoordinateSection (R := R) i)) = s i := by
  let g := M.toProjectiveSpace f s h
  let L := (pullback g).obj T
  let t (i : ι) : Γ(L, ⊤) := g.pullbackSections T ⊤ (Proj.polynomialCoordinateSection (R := R) i)
  have hD (i : ι) : D[i] ≤ g ⁻¹ᵁ U[i] := (M.toProjectiveSpace_preimage_basicOpen f s h i).ge
  have ht (i : ι) : D[i] ≤ L.nonvanishingLocus (t i) := by
    have hv := (T).nonvanishingLocus_pullbackSections g
      (Proj.polynomialCoordinateSection (R := R) i)
    rw [Proj.nonvanishingLocus_polynomialCoordinateSection] at hv
    exact (hD i).trans hv.ge
  apply L.exists_iso_of_sectionRatios M h ht (fun _ ↦ le_rfl)
  intro i j r hr
  have hcoordinate := toProjectiveSpace_appLE_awayXRatio M f s h i j
  have he (k : ι) : L.presheaf.map (D[i]).leTop.op (t k) =
      g.pullbackSectionsLE T U[i] D[i] (hD i)
        ((T).presheaf.map (U[i]).leTop.op (Proj.polynomialCoordinateSection (R := R) k)) := by
    rw [g.pullbackSectionsLE_map T ⊤ (D[i]) _ (U[i]).leTop (hD i),
      g.pullbackSectionsLE_apply]
    rfl
  have hc := congrArg (g.pullbackSectionsLE T U[i] D[i] (hD i))
    (Proj.res_polynomialCoordinateSection_eq_smul (R := R) i j)
  rw [map_smulₛₗ, ← he, ← he] at hc
  have hi : D[i] ≤ L.nonvanishingLocus (L.presheaf.map (D[i]).leTop.op (t i)) := by
    rw [L.nonvanishingLocus_map]
    exact le_inf le_rfl (ht i)
  have heq := L.injective_smul_of_le_nonvanishingLocus hi (hr.trans hc)
  rw [heq, hcoordinate, M.sectionRatio_smul]

variable (R) (h : (⨆ i, M.nonvanishingLocus (s i)) = ⊤)

local notation "g" => M.toProjectiveSpace f s h
local notation "L" => Functor.obj (pullback g) T
local notation "t" => fun i ↦ Scheme.Hom.pullbackSectionsLE g T ⊤ ⊤
  (Eq.ge (Scheme.Hom.preimage_top g)) (Proj.polynomialCoordinateSection (R := R) i)

/-- The isomorphism from the pullback of `𝒪(1)` to the line bundle defining the morphism. -/
def pullbackTwistingSheafOneToProjectiveSpace : L ≅ M :=
  (M.exists_iso_pullbackTwistingSheaf_toProjectiveSpace f s h).choose

/-- The comparison sends the pulled-back homogeneous coordinates to the defining sections. -/
@[simp]
theorem pullbackTwistingSheafOneToProjectiveSpace_hom_app (i : ι) :
    (M.pullbackTwistingSheafOneToProjectiveSpace R f s h).hom.app ⊤ (t i) = s i := by
  have hi : t i = (g).pullbackSections T ⊤ (Proj.polynomialCoordinateSection (R := R) i) :=
    (g).pullbackSectionsLE_self T ⊤ (Proj.polynomialCoordinateSection (R := R) i)
  exact (congrArg ((M.pullbackTwistingSheafOneToProjectiveSpace R f s h).hom.app ⊤)
    hi).trans ((M.exists_iso_pullbackTwistingSheaf_toProjectiveSpace f s h).choose_spec i)

/-- The comparison is characterized by its values on the pulled-back homogeneous coordinates. -/
theorem eq_pullbackTwistingSheafOneToProjectiveSpace_hom_iff (φ : L ⟶ M) :
    φ = (M.pullbackTwistingSheafOneToProjectiveSpace R f s h).hom ↔
      ∀ i, φ.app ⊤ (t i) = s i := by
  refine ⟨fun he i ↦ he.symm ▸ M.pullbackTwistingSheafOneToProjectiveSpace_hom_app R f s h i, ?_⟩
  intro hφ
  apply hom_ext_of_covering_sections h (s := t)
  · intro i
    rw [Scheme.Hom.pullbackSectionsLE_apply, nonvanishingLocus_map,
      nonvanishingLocus_pullbackSections, Proj.nonvanishingLocus_polynomialCoordinateSection,
      M.toProjectiveSpace_preimage_basicOpen, top_inf_eq]
  · intro i
    exact (hφ i).trans (M.pullbackTwistingSheafOneToProjectiveSpace_hom_app R f s h i).symm

end Scheme.Modules

end AlgebraicGeometry
