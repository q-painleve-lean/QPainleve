/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.SurfaceIntersection
public import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
import QPainleve.AlgebraicGeometry.Blowup.Exceptional.FirstKind
import QPainleve.AlgebraicGeometry.Blowup.Point.Cohomology
import QPainleve.AlgebraicGeometry.Blowup.Smooth
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.Cohomology.EulerCharacteristic
import TauCeti.AlgebraicGeometry.Curves.Normalization

/-!
# The intersection pairing on a point blowup

Pullback along a point blowup preserves the Euler-characteristic pairing. The exceptional
curve is orthogonal to the pullback and has square `-1` over an algebraically closed field.
The sign convention is that the positive exceptional class is the inverse of the class of
its ideal sheaf.

The intersection formulas are those of P. Hacking, *583C Lecture Notes (Compact Complex
Surfaces)*, Proposition 7.1. We use the cohomology comparison for point blowups and the
comparison of surface intersection with degree on the exceptional curve.
-/

public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}} (p : X)

local notation "Iₚ" => Scheme.Hom.ker (Scheme.fromSpecResidueField X p)
local notation "π" => blowupToBase Iₚ
local notation "E" => comap Iₚ π
local notation "eₚ" =>
  (LineBundleClass.mk
    (IsEffectiveCartier.toInvertibleSheaf (isEffectiveCartier_comap_blowupToBase Iₚ)))⁻¹

namespace TauCeti.AlgebraicGeometry.Chow

open LineBundleClass

variable (k : Type u) [Field k] [X.Over (Spec (.of k))]

/-- Pulling both classes back to the blowup of a regular closed point of local dimension two
preserves their intersection pairing. -/
theorem classIntersectionNumber_pullback_pointBlowup [IsLocallyNoetherian X]
    (hp : IsClosed ({p} : Set X)) [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) (a b : LineBundleClass X) :
    letI : (Iₚ).blowup.Over (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
    classIntersectionNumber k (Iₚ).blowup
      (pullback π a) (pullback π b) = classIntersectionNumber k X a b := by
  rw [X.ker_fromSpecResidueField_eq_vanishingIdeal p]
  let J := vanishingIdeal (X := X) ⟨closure {p}, isClosed_closure⟩
  let : J.blowup.Over (Spec (.of k)) := ⟨J.blowupToBase ≫ X ↘ Spec (.of k)⟩
  have hχ (c : LineBundleClass X) :
      eulerCharBelow k (pullback J.blowupToBase c) 3 = eulerCharBelow k c 3 := by
    obtain ⟨L, rfl⟩ := mk_surjective c
    have hfin (i : ℕ) :
        Module.finrank k (Scheme.Modules.Cohomology
          ((Scheme.Modules.pullback J.blowupToBase).obj L.obj) i) =
          Module.finrank k (Scheme.Modules.Cohomology L.obj i) :=
      (pointBlowupCohomologyLinearEquiv k hp hdim
        ((InvertibleSheaf.toFiniteLocallyFree X).obj L) i).finrank_eq.symm
    simp only [pullback_mk, eulerCharBelow_mk, InvertibleSheaf.pullback_obj_obj,
      Scheme.Modules.eulerCharBelow_succ, Scheme.Modules.eulerCharBelow_zero, hfin]
  dsimp only [J] at hχ
  simp only [classIntersectionNumber_eq, ← pullback_inv, ← pullback_mul,
    ← pullback_one (vanishingIdeal ⟨closure {p}, isClosed_closure⟩).blowupToBase, hχ]

variable [IsAlgClosed k] [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

private theorem classIntersectionNumber_mul_exceptional_zpow_pointBlowup
    (hp : IsClosed ({p} : Set X))
    (a b : LineBundleClass (Iₚ).blowup) (n : ℤ) :
    letI : (Iₚ).blowup.Over (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
    (Iₚ).blowup.IsProjectiveOver k →
    classIntersectionNumber k (Iₚ).blowup a (b * eₚ ^ n) =
      classIntersectionNumber k (Iₚ).blowup a b +
        n * LineBundleClass.intersectionNumber k (E).subschemeι a := by
  let : (Iₚ).blowup.Over (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
  intro hproj
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
  have : IsRegular X := IsRegular.of_smooth (X ↘ Spec (.of k))
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq
    (X ↘ Spec (.of k)) 2).mp inferInstance).2 p hp
  have hsmooth : SmoothOfRelativeDimension 2 (π ≫ X ↘ Spec (.of k)) := by
    rw [X.ker_fromSpecResidueField_eq_vanishingIdeal p]
    exact smoothOfRelativeDimension_blowup_closed_point (X ↘ Spec (.of k)) hp
  have hbound := (relativeDimensionLE_iff_of_field (d := 2) (π ≫ X ↘ Spec (.of k))).mp
    (inferInstanceAs (RelativeDimensionLE 2 (π ≫ X ↘ Spec (.of k))))
  have he := isExceptionalCurveOfFirstKind_comap_blowupToBase_of_closedPoint p hp hdim
  have := he.isIntegral_subscheme
  exact classIntersectionNumber_mul_zpow_inv_mk_toInvertibleSheaf k hbound
    (Iₚ).isEffectiveCartier_comap_blowupToBase he.topologicalKrullDim_subscheme a b n

omit [IsAlgClosed k] in
private theorem intersectionNumber_exceptional_pullback_pointBlowup
    (hp : IsClosed ({p} : Set X)) (a : LineBundleClass X) :
    letI : (Iₚ).blowup.Over (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
    LineBundleClass.intersectionNumber k (E).subschemeι (LineBundleClass.pullback π a) = 0 := by
  let : (Iₚ).blowup.Over (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
  have : IsRegular X := IsRegular.of_smooth (X ↘ Spec (.of k))
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq
    (X ↘ Spec (.of k)) 2).mp inferInstance).2 p hp
  obtain ⟨e, he, -⟩ := exists_iso_projectiveLine_pullback_exceptionalIdeal_of_closedPoint p hp hdim
  let q := projectiveLine (X.residueField p) ↘ Spec (.of (X.residueField p))
  have hcomp : (E).subschemeι ≫ π = (e.inv ≫ q) ≫ X.fromSpecResidueField p := by
    have hw : (e.hom ≫ (E).subschemeι) ≫ π = q ≫ X.fromSpecResidueField p := he.w
    rw [Category.assoc, ← hw, Category.assoc, Iso.inv_hom_id_assoc]
  rw [LineBundleClass.intersectionNumber_pullback]
  exact LineBundleClass.intersectionNumber_eq_zero_of_eq_comp k _
    (e.inv ≫ q) (X.fromSpecResidueField p) hcomp
    (t := IsLocalRing.closedPoint (X.residueField p))
    (fun _ ↦ specializes_of_eq (Subsingleton.elim _ _)) a

private theorem intersectionNumber_exceptional_pullback_mul_zpow_pointBlowup
    (hp : IsClosed ({p} : Set X)) (a : LineBundleClass X) (n : ℤ) :
    letI : (Iₚ).blowup.Over (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
    (Iₚ).blowup.IsProjectiveOver k →
    LineBundleClass.intersectionNumber k (E).subschemeι (LineBundleClass.pullback π a * eₚ ^ n) =
      -n := by
  let : (Iₚ).blowup.Over (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
  intro hproj
  have : (E).subscheme.IsProjectiveOver k :=
    Scheme.IsProjectiveOver.of_isClosedImmersion k (E).subschemeι
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
  have : IsRegular X := IsRegular.of_smooth (X ↘ Spec (.of k))
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq
    (X ↘ Spec (.of k)) 2).mp inferInstance).2 p hp
  have hE := isExceptionalCurveOfFirstKind_comap_blowupToBase_of_closedPoint p hp hdim
  have := hE.isIntegral_subscheme
  have hdimE := hE.topologicalKrullDim_subscheme.le
  have : RelativeDimensionLE 1 ((E).subscheme ↘ Spec (.of k)) :=
    (relativeDimensionLE_iff_of_field _).mpr hdimE
  have := Scheme.Modules.finiteDimensional_cohomology_trivial_of_topologicalKrullDim_le_one
    k (X := (E).subscheme) hdimE
  have hself : LineBundleClass.intersectionNumber k (E).subschemeι eₚ = -1 :=
    intersectionNumber_exceptional_of_smoothSurface k p hp
  simp only [LineBundleClass.intersectionNumber_mul_of_isIntegral,
    LineBundleClass.intersectionNumber_zpow_of_isIntegral,
    intersectionNumber_exceptional_pullback_pointBlowup p k hp, hself, zero_add, mul_neg_one]

/-- The intersection pairing on a projective point blowup of a smooth surface, in pullback and
exceptional coordinates, is the base pairing plus the rank-one pairing of square `-1`. -/
theorem classIntersectionNumber_pointBlowup
    (hp : IsClosed ({p} : Set X)) (a b : LineBundleClass X) (m n : ℤ) :
    letI : (Iₚ).blowup.Over (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
    (Iₚ).blowup.IsProjectiveOver k →
    classIntersectionNumber k (Iₚ).blowup
      (LineBundleClass.pullback π a * eₚ ^ m) (LineBundleClass.pullback π b * eₚ ^ n) =
        classIntersectionNumber k X a b - m * n := by
  let : (Iₚ).blowup.Over (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
  intro hproj
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : IsRegular X := IsRegular.of_smooth (X ↘ Spec (.of k))
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq
    (X ↘ Spec (.of k)) 2).mp inferInstance).2 p hp
  rw [classIntersectionNumber_mul_exceptional_zpow_pointBlowup p k hp _ _ _ hproj,
    intersectionNumber_exceptional_pullback_mul_zpow_pointBlowup p k hp _ _ hproj,
    classIntersectionNumber_comm (k := k) (pullback π a * eₚ ^ m)]
  simp only [classIntersectionNumber_mul_exceptional_zpow_pointBlowup p k hp _ _ _ hproj,
    intersectionNumber_exceptional_pullback_pointBlowup p k hp,
    classIntersectionNumber_pullback_pointBlowup p k hp hdim,
    classIntersectionNumber_comm (k := k) b a, mul_zero, add_zero]
  ring

end TauCeti.AlgebraicGeometry.Chow
