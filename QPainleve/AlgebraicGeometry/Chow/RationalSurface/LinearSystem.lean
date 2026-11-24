/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine
public import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme

import QPainleve.AlgebraicGeometry.CartierDivisor.DoublePoint
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Effectivity
import QPainleve.AlgebraicGeometry.Chow.SurfaceIntersection
import QPainleve.AlgebraicGeometry.Curves.Degree.Ample
import QPainleve.AlgebraicGeometry.Curves.GenusZero
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Stalk
import QPainleve.AlgebraicGeometry.LineBundle.Ample
import QPainleve.AlgebraicGeometry.TangentSpace
import TauCeti.AlgebraicGeometry.Curves.ProjectiveLine

/-!
# Self-intersection of projective-line divisors with regular linear systems

On a smooth projective rational surface, a projective-line divisor whose square
is at least two has enough sections to impose a double point. Consequently a
complete linear system all of whose members are regular has square at most one
when it contains a projective-line divisor.

See [Vakil, *Complex Algebraic Surfaces*, Class 17, §2][Vakil] for the double-point
argument in the classification of minimal rational surfaces.

[Vakil]: https://math.stanford.edu/~vakil/02-245/sclass17A.pdf
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace QPainleve
open Scheme.IdealSheafData Scheme.Modules
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open LineBundleClass

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [hRat : Scheme.IsRationalOver (X ↘ Spec (.of k))] {I : X.IdealSheafData}

local notation "S" => Spec (CommRingCat.of k)
local notation "B" => Chow.classIntersectionNumber k X
local notation "O(" h ")" => InvertibleSheaf.dual (IsEffectiveCartier.toInvertibleSheaf h)
local notation "cl(" h ")" => LineBundleClass.mk (O(h))

include hRat in
private theorem three_lt_finrank_globalSections_dual
    (hI : I.IsEffectiveCartier) (e : I.subscheme ≅ projectiveLine k)
    [e.hom.IsOver S] (hsq : 1 < B cl(hI) cl(hI)) :
    3 < Module.finrank k Γ((O(hI)).obj, ⊤) := by
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral X := hRat.isIntegral_of_smooth
  have : IsIntegral I.subscheme := IsIntegral.of_isIso e.inv
  have : I.subscheme.IsProjectiveOver k :=
    Scheme.IsProjectiveOver.of_isClosedImmersion k I.subschemeι
  have hdim : topologicalKrullDim I.subscheme = 1 :=
    e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq.trans
      (Scheme.IsCurveOver.topologicalKrullDim_eq_one k)
  have : I.subscheme.IsCurveOver k := Scheme.isCurveOver_iff.mpr
    ⟨inferInstance, inferInstance, hdim⟩
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  have hgen : I.subscheme.genus k = 0 :=
    Scheme.genus_eq_zero_iff_exists_iso_projectiveLine.mpr ⟨e, inferInstance⟩
  obtain ⟨H, hH⟩ := X.exists_isAmple_of_isProjectiveOver k
  have hdegree : 0 < B H cl(hI) := by
    rw [← inv_mk, Chow.classIntersectionNumber_eq_intersectionNumber_subschemeι k hX.le hI hdim]
    exact hH.intersectionNumber_pos I.subschemeι
  have := X.subsingleton_cohomology_two_of_self_pos_of_intersection_pos k (O(hI)) hH
    (by omega) hdegree
  have h₂ : Module.finrank k (Cohomology (O(hI)).obj 2) = 0 :=
    Module.finrank_zero_of_subsingleton
  have hadj := I.subschemeι.two_mul_genus_sub_two_eq_intersection_of_isRationalOver k
  dsimp only at hadj
  rw [LineBundleClass.mk_toInvertibleSheaf_congr _ hI I.ker_subschemeι, inv_mk, hgen] at hadj
  have hχ := eulerCharBelow_eq_riemannRoch_of_isRationalOver k cl(hI)
  rw [eulerCharBelow_mk, Scheme.Modules.eulerCharBelow_succ, Scheme.Modules.eulerCharBelow_two,
    finrank_cohomology_zero_eq_finrank_globalSections, h₂] at hχ
  omega

include hRat in
/-- A projective-line divisor on a smooth projective rational surface has square at most
one if every effective Cartier member of its complete linear system is regular. -/
theorem classIntersectionNumber_self_le_one_of_regular_linear_system
    (hI : I.IsEffectiveCartier) (e : I.subscheme ≅ projectiveLine k) [e.hom.IsOver S]
    (hregular : ∀ (J : X.IdealSheafData) (hJ : J.IsEffectiveCartier),
      cl(hJ) = cl(hI) → IsRegular J.subscheme) :
    B cl(hI) cl(hI) ≤ 1 := by
  by_contra! hsq
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral X := hRat.isIntegral_of_smooth
  have : IsRegular X := IsRegular.of_smooth (X ↘ S)
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ S)
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints (Set.univ_nonempty (α := X))
    isOpen_univ.isLocallyClosed
  have hdim := X.finrank_stalk_quotient_maximalIdeal_sq_of_isClosed (k := k) (n := 2) hx
  have : Module.Finite k (X.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ 2) :=
    Module.finite_of_finrank_pos (hdim.symm ▸ by decide)
  have hsections := hI.three_lt_finrank_globalSections_dual e hsq
  obtain ⟨s, hs, hord⟩ := (O(hI)).exists_two_le_stalkOrder_zeroIdeal_of_finrank_lt
    (k := k) x (hdim.symm ▸ hsections)
  let J := (O(hI)).zeroIdeal s
  let hJ := (O(hI)).isEffectiveCartier_zeroIdeal hs
  have : IsRegular J.subscheme := hregular J hJ ((O(hI)).mk_dual_toInvertibleSheaf_zeroIdeal hs)
  have hxJ : x ∈ J.support := (J.one_le_stalkOrder_iff x).mp (one_le_two.trans hord)
  obtain ⟨q, rfl⟩ := J.range_subschemeι.ge hxJ
  have horder : J.stalkOrder (J.subschemeι q) = 1 :=
    (hJ.stalkOrder_eq_one_iff_isRegularLocalRing q).mpr inferInstance
  exact (by decide : ¬ (2 : ℕ∞) ≤ 1) (horder ▸ hord)

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
