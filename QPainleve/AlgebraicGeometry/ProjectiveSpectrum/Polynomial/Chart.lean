/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.RingTheory.MvPolynomial.ProjectiveChart
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.StandardSmooth
public import TauCeti.AlgebraicGeometry.Modules.GlobalSections
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Basic
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.BaseChange

/-!
# Standard affine charts of projective space

The functions on a standard open of polynomial projective space form a polynomial
algebra on the remaining coordinates. These affine charts give smoothness of the
structure map and its relative dimension.
-/

public noncomputable section

open CategoryTheory Opposite
open MvPolynomial TauCeti.MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable (R : Type u) [CommRing R] {n : ℕ}

local notation "𝒜" => homogeneousSubmodule (Fin (n + 1)) R
local notation "ℙ" => Proj 𝒜
local notation "U[" i "]" => basicOpen 𝒜 (X i)

/-- The coefficient morphism supplies the base algebra on chart sections. -/
local instance polynomialFinOver : (ℙ).Over (Spec (.of R)) := ⟨toSpecCoeff 𝒜⟩

private theorem X_mem_one (i : Fin (n + 1)) : X i ∈ 𝒜 1 :=
  (mem_homogeneousSubmodule ..).mpr (isHomogeneous_X R i)

private theorem basicOpenToSpec_comp (i : Fin (n + 1)) :
    (basicOpenToSpec 𝒜 (X i)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R
          (HomogeneousLocalization.Away 𝒜 (X i)))) =
      (U[i]).ι ≫ toSpecCoeff 𝒜 := by
  rw [← cancel_epi (basicOpenIsoSpec 𝒜 _ (X_mem_one R i) one_pos).inv,
    ← basicOpenIsoSpec_hom 𝒜 _ (X_mem_one R i) one_pos, Iso.inv_hom_id_assoc,
    basicOpenIsoSpec_inv_ι_assoc, awayι_toSpecCoeff]

/-- The affine coordinate functions of a standard projective chart, as a polynomial algebra
over the coefficient ring. -/
def polynomialChartSectionsEquiv (i : Fin (n + 1)) :
    letI : Algebra R Γ(ℙ, U[i]) :=
      (((ℙ).baseRingToStructurePresheaf R).app (op U[i])).hom.toAlgebra
    MvPolynomial (Fin n) R ≃ₐ[R] Γ(ℙ, U[i]) := by
  letI : Algebra R Γ(ℙ, U[i]) :=
    (((ℙ).baseRingToStructurePresheaf R).app (op U[i])).hom.toAlgebra
  let e := (basicOpenIsoAway 𝒜 _ (X_mem_one R i) one_pos).commRingCatIsoToRingEquiv
  refine { __ := (mvPolynomialEquivAwayX R i).toRingEquiv.trans e, commutes' := ?_ }
  intro r
  -- The ring equivalence is the standard chart map on sections.
  change e (mvPolynomialEquivAwayX R i (algebraMap R _ r)) = algebraMap R _ r
  rw [AlgEquiv.commutes]
  have h := congrArg (fun f : (U[i]).toScheme ⟶ Spec (.of R) ↦ f.appTop)
    (basicOpenToSpec_comp R i)
  have hs : (basicOpenToSpec 𝒜 (X i)).appTop =
      (Scheme.ΓSpecIso _).hom ≫ awayToSection 𝒜 (X i) ≫ (U[i]).topIso.inv :=
    basicOpenToSpec_app_top 𝒜 (X i)
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, hs] at h
  have hbase := congrArg ((Scheme.ΓSpecIso (.of R)).inv ≫ ·) h
  simp only [← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id_assoc] at hbase
  have hmap : (toSpecCoeff 𝒜).appTop ≫ (U[i]).ι.appTop =
      (toSpecCoeff 𝒜).appLE ⊤ U[i] le_top ≫ (U[i]).topIso.inv := rfl
  have h' : CommRingCat.ofHom (algebraMap R
        (HomogeneousLocalization.Away 𝒜 (X i))) ≫ awayToSection 𝒜 (X i) =
      (Scheme.ΓSpecIso (.of R)).inv ≫ (toSpecCoeff 𝒜).appLE ⊤ U[i] le_top := by
    apply (cancel_mono (U[i]).topIso.inv).mp
    simpa only [Category.assoc, hmap] using hbase
  rw [RingHom.algebraMap_toAlgebra, Scheme.baseRingToStructurePresheaf_app_eq_appLE]
  exact ConcreteCategory.congr_hom h' r

/-- A polynomial variable on a standard chart is the corresponding homogeneous ratio. -/
@[simp]
theorem polynomialChartSectionsEquiv_X (i : Fin (n + 1)) (j : Fin n) :
    letI : Algebra R Γ(ℙ, U[i]) :=
      (((ℙ).baseRingToStructurePresheaf R).app (op U[i])).hom.toAlgebra
    polynomialChartSectionsEquiv R i (X j) =
      awayToSection 𝒜 (X i) (awayXRatio (R := R) i (i.succAbove j)) :=
  congrArg (awayToSection 𝒜 (X i)) (mvPolynomialEquivAwayX_X R i j)

/-- Polynomial projective space with `n + 1` coordinates is smooth of relative dimension `n`. -/
instance smoothOfRelativeDimension_polynomial :
    SmoothOfRelativeDimension n (toSpecCoeff 𝒜) := by
  let a (i : Fin (n + 1)) := awayι 𝒜 (X i) (X_mem_one R i) one_pos
  let cover : (ℙ).OpenCover :=
    Scheme.Cover.mkOfCovers (Fin (n + 1)) _ a (fun x ↦ by
      have h := iSup_basicOpen_eq_top 𝒜 (X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R)
        (irrelevant_eq_span_X _ _).le
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (h.symm ▸
        (TopologicalSpace.Opens.mem_top x))
      have hmem : x ∈ (a i).opensRange := by
        simpa only [a, opensRange_awayι] using hi
      exact ⟨i, hmem⟩)
      (fun _ ↦ inferInstance)
  have (i : cover.I₀) : IsAffine (cover.X i) := inferInstanceAs (IsAffine (Spec _))
  refine HasRingHomProperty.of_source_openCover (P := @SmoothOfRelativeDimension n) cover fun i ↦ ?_
  apply (HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension n)).mp
  -- The cover map is the standard affine immersion.
  let j : Fin (n + 1) := i
  change SmoothOfRelativeDimension n (a j ≫ toSpecCoeff 𝒜)
  dsimp only [a]
  rw [awayι_toSpecCoeff,
    HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
  have h := Algebra.IsStandardSmoothOfRelativeDimension.mvPolynomial R (Fin n)
  rw [Nat.card_fin] at h
  let := h
  have := Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv n (mvPolynomialEquivAwayX R j)
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).mpr inferInstance)

section Overlap

variable {R}

/-- A normalized coordinate restricted to any subopen of its standard chart. -/
def polynomialCoordinateRatio {V : (ℙ).Opens} (i j : Fin (n + 1)) (h : V ≤ U[i]) : Γ(ℙ, V) :=
  (ℙ).presheaf.map (homOfLE h).op (awayToSection 𝒜 (X i) (awayXRatio (R := R) i j))

/-- On the whole chart, restriction of a normalized coordinate is the identity map. -/
@[simp]
theorem polynomialCoordinateRatio_self_open (i j : Fin (n + 1)) :
    polynomialCoordinateRatio i j (le_rfl : U[i] ≤ U[i]) =
      awayToSection 𝒜 (X i) (awayXRatio i j) := by
  simp [polynomialCoordinateRatio]

/-- The denominator coordinate restricts to one. -/
@[simp]
theorem polynomialCoordinateRatio_self {V : (ℙ).Opens} (i : Fin (n + 1)) (h : V ≤ U[i]) :
    polynomialCoordinateRatio i i h = 1 := by
  simp [polynomialCoordinateRatio]

/-- Restricting a coordinate ratio to a smaller open restricts its domain of definition. -/
@[simp]
theorem res_polynomialCoordinateRatio {V W : (ℙ).Opens} (f : W ⟶ V)
    (i j : Fin (n + 1)) (h : V ≤ U[i]) :
    (ℙ).presheaf.map f.op (polynomialCoordinateRatio i j h) =
      polynomialCoordinateRatio i j (f.le.trans h) := by
  simp only [polynomialCoordinateRatio, ← Functor.map_comp_apply]
  rfl

/-- The value of a restricted normalized coordinate is the homogeneous fraction in the
localization at that point. -/
theorem val_polynomialCoordinateRatio {V : (ℙ).Opens} (i j : Fin (n + 1)) (h : V ≤ U[i]) (x : V) :
    ((polynomialCoordinateRatio i j h).val x).val =
      Localization.mk (X j) ⟨X i, h x.property⟩ := by
  rw [polynomialCoordinateRatio, awayXRatio_def]
  erw [val_awayToSection_mk_apply]
  simp only [pow_one]

/-- On a common subopen, coordinate ratios multiply by cancellation of the middle coordinate. -/
theorem polynomialCoordinateRatio_mul {V : (ℙ).Opens} (i j k : Fin (n + 1))
    (hi : V ≤ U[i]) (hj : V ≤ U[j]) :
    polynomialCoordinateRatio i j hi * polynomialCoordinateRatio j k hj =
      polynomialCoordinateRatio i k hi := by
  apply AlgebraicGeometry.Proj.ext
  refine funext fun (x : V) ↦ ?_
  have hmul : (polynomialCoordinateRatio i j hi * polynomialCoordinateRatio j k hj).val x =
      (polynomialCoordinateRatio i j hi).val x * (polynomialCoordinateRatio j k hj).val x := rfl
  rw [hmul]
  apply HomogeneousLocalization.val_injective
  let := x.val.isPrime
  rw [HomogeneousLocalization.val_mul, val_polynomialCoordinateRatio,
    val_polynomialCoordinateRatio, val_polynomialCoordinateRatio]
  rw [Localization.mk_mul]
  exact Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (by
    -- Cross multiplication compares products of the same homogeneous coordinates.
    change X i * (X j * X k) = (X i * X j) * X k
    ring))

end Overlap

end AlgebraicGeometry.Proj
