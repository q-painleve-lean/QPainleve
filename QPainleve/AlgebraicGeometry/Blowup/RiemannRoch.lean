/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Class
public import QPainleve.AlgebraicGeometry.Blowup.Smooth
public import QPainleve.AlgebraicGeometry.Modules.Differentials.Canonical
public import TauCeti.AlgebraicGeometry.Chow.SurfaceIntersection
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
import QPainleve.AlgebraicGeometry.Blowup.Exceptional.EulerCharacteristic
import QPainleve.AlgebraicGeometry.Blowup.Integral
import QPainleve.AlgebraicGeometry.Blowup.Picard
import QPainleve.AlgebraicGeometry.Blowup.Ramification
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct
import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme

/-!
# Riemann–Roch under a point blowup

On a smooth integral projective surface over an algebraically closed field, the Riemann–Roch
equation for a line bundle and for any exceptional twist of its pullback are equivalent. The
exceptional contribution to `L² - L · K` is `m(1-m)`, twice the change in Euler characteristic.
The Picard splitting then gives equivalence of the equations for all line bundles on the two
surfaces.

The argument uses the blowup identities in P. Hacking,
[*583C Lecture notes (Compact Complex Surfaces)*, Propositions 7.1 and 7.2]
(https://paulhacking.github.io/surfaces.pdf#page=35). The intersection calculation uses Tau Ceti's
`Chow.classIntersectionNumber_eq` and the Euler characteristic formula for exceptional twists.
-/

public section

open AlgebraicGeometry CategoryTheory Limits Order TopologicalSpace
open QPainleve TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.IdealSheafData LineBundleClass

namespace TauCeti.AlgebraicGeometry.Chow

universe u

variable (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))] (p : X)

local notation "Iₚ" =>
  vanishingIdeal (Closeds.mk (closure (Set.singleton p)) isClosed_closure)
local notation "Y" => blowup (Iₚ)
local notation "π" => blowupToBase (Iₚ)
local notation "E" => blowupExceptionalClass (Iₚ)
local notation:max "twist[" a ", " m "]" => (pullback π a * E ^ (m : ℤ))

local notation:max "rr[" S ", " a ", " K "]" =>
  (eulerCharBelow k a 3 = eulerCharBelow (X := S) k 1 3 +
    (classIntersectionNumber k S a a - classIntersectionNumber k S a K) / 2)

omit [IsIntegral X] in
private theorem eulerCharBelow_twist (hp : IsClosed ({p} : Set X))
    (a : LineBundleClass X) (m : ℤ) :
    letI : Scheme.Over Y (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
    eulerCharBelow k twist[a, m] 3 = eulerCharBelow k a 3 + m * (1 - m) / 2 := by
  -- Transport the scheme, structure map and exceptional class along the center equality.
  let P (J : X.IdealSheafData) : Prop :=
    let : J.blowup.Over (Spec (.of k)) := ⟨J.blowupToBase ≫ X ↘ Spec (.of k)⟩
    eulerCharBelow k (pullback J.blowupToBase a * J.blowupExceptionalClass ^ m) 3 =
      eulerCharBelow k a 3 + m * (1 - m) / 2
  have h : P (Scheme.Hom.ker (X.fromSpecResidueField p)) := by
    simpa only [P, blowupExceptionalClass_def, inv_zpow, zpow_neg] using
      eulerCharBelow_pointBlowup_exceptional_twist_of_smoothSurface p k hp a m
  exact (X.ker_fromSpecResidueField_eq_vanishingIdeal p) ▸ h

omit [IsIntegral X] in
private theorem sub_classIntersectionNumber_twist (hp : IsClosed ({p} : Set X))
    (a K : LineBundleClass X) (m : ℤ) :
    letI : Scheme.Over Y (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
    classIntersectionNumber k Y twist[a, m] twist[a, m] -
      classIntersectionNumber k Y twist[a, m] twist[K, 1] =
      m * (1 - m) + (classIntersectionNumber k X a a - classIntersectionNumber k X a K) := by
  let : Scheme.Over Y (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
  have hinv (c : LineBundleClass X) (r : ℤ) : (twist[c, r])⁻¹ = twist[c⁻¹, -r] := by
    simp only [mul_inv_rev, pullback_inv, zpow_neg]
    exact mul_comm _ _
  have hmul (c d : LineBundleClass X) (r s : ℤ) :
      twist[c, r] * twist[d, s] = twist[c * d, r + s] := by
    simp only [pullback_mul, zpow_add]
    ac_rfl
  -- The difference of Euler pairings can be computed using projectivity of the base alone.
  simp only [classIntersectionNumber_eq, hinv, hmul, eulerCharBelow_twist k p hp]
  -- Each product of consecutive integers is even, so the halves add exactly.
  have half (r : ℤ) : 2 * (r * (1 - r) / 2) = r * (1 - r) := by
    have heq : r * (1 - r) = -(r * (r - 1)) := by ring
    have hdiv : 2 ∣ r * (1 - r) := heq ▸ dvd_neg.mpr (Int.even_mul_pred_self r).two_dvd
    omega
  have hpoly : (-m + -m) * (1 - (-m + -m)) - -m * (1 - -m) +
      (-1) * (1 - (-1)) - (-m + -1) * (1 - (-m + -1)) = 2 * (m * (1 - m)) := by ring
  have hm := half (-m)
  have hmm := half (-m + -m)
  have h₁ := half (-1)
  have hm₁ := half (-m + -1)
  omega

/-- The surface Riemann–Roch equation for a line bundle is equivalent to that for any
exceptional twist of its pullback along a closed point blowup. -/
theorem eulerCharBelow_eq_riemannRoch_pointBlowup_iff (hp : IsClosed ({p} : Set X))
    (a : LineBundleClass X) (m : ℤ) :
    letI : Scheme.Over Y (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
    letI : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k)) :=
      smoothOfRelativeDimension_blowup_closed_point (X ↘ Spec (.of k)) hp
    rr[Y, twist[a, m], mk (canonicalBundle k Y 2)] ↔ rr[X, a, mk (canonicalBundle k X 2)] := by
  let : Scheme.Over Y (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
  have : Scheme.Hom.IsOver π (Spec (.of k)) := ⟨rfl⟩
  have : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k)) :=
    smoothOfRelativeDimension_blowup_closed_point (X ↘ Spec (.of k)) hp
  have : Smooth (Y ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral Y := isIntegral_blowup_closed_point (X ↘ Spec (.of k)) hp
  let K := mk (canonicalBundle k X 2)
  have hK : mk (canonicalBundle k Y 2) = twist[K, 1] := by
    have hram := ramificationIdealSheaf_blowup_of_smoothSurface k hp
    have hcart : (ramificationIdealSheaf k π).IsEffectiveCartier :=
      hram ▸ (Iₚ).isEffectiveCartier_comap_blowupToBase
    have hclass := LineBundleClass.mk_toInvertibleSheaf_congr hcart
      (Iₚ).isEffectiveCartier_comap_blowupToBase hram
    rw [mk_canonicalBundle_eq_pullback_mul_inv_ramification k π 2 hcart,
      hclass, zpow_one, blowupExceptionalClass_def]
  have hχ₁ : eulerCharBelow (X := Y) k 1 3 = eulerCharBelow (X := X) k 1 3 := by
    simpa only [pullback_one, zpow_zero, mul_one, zero_mul, Int.zero_ediv, add_zero] using
      eulerCharBelow_twist k p hp 1 0
  rw [hK, sub_classIntersectionNumber_twist k p hp, eulerCharBelow_twist k p hp, hχ₁]
  have hmul : 2 ∣ m * (1 - m) := by
    rw [show m * (1 - m) = -(m * (m - 1)) by ring]
    exact dvd_neg.mpr (Int.even_mul_pred_self m).two_dvd
  rw [Int.add_ediv_of_dvd_left hmul]
  dsimp only [K]
  omega

/-- The Riemann–Roch formula holds for all line bundle classes on a closed point blowup of
a smooth integral projective surface exactly when it holds for all classes on the base. -/
theorem forall_eulerCharBelow_eq_riemannRoch_pointBlowup_iff (hp : IsClosed ({p} : Set X)) :
    letI : Scheme.Over Y (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
    letI : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k)) :=
      smoothOfRelativeDimension_blowup_closed_point (X ↘ Spec (.of k)) hp
    (∀ a : LineBundleClass Y, rr[Y, a, mk (canonicalBundle k Y 2)]) ↔
      ∀ a : LineBundleClass X, rr[X, a, mk (canonicalBundle k X 2)] := by
  let : Scheme.Over Y (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
  have : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k)) :=
    smoothOfRelativeDimension_blowup_closed_point (X ↘ Spec (.of k)) hp
  have h (a : LineBundleClass X) (m : ℤ) := eulerCharBelow_eq_riemannRoch_pointBlowup_iff k p hp a m
  refine ⟨fun hY a ↦ (h a 0).mp (hY _), fun hX b ↦ ?_⟩
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
  have : Smooth (Y ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
  have : IsRegular X := IsRegular.of_smooth (X ↘ Spec (.of k))
  have : IsRegular Y := IsRegular.of_smooth (Y ↘ Spec (.of k))
  have : IsIntegral Y := isIntegral_blowup_closed_point (X ↘ Spec (.of k)) hp
  have hX₂ := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of k)) (n := 2)
  have hY₂ := topologicalKrullDim_eq_of_smoothOfRelativeDimension (Y ↘ Spec (.of k)) (n := 2)
  have hcod := coheight_eq_of_isClosed_of_smoothOfRelativeDimension (X ↘ Spec (.of k)) (n := 2) hp
  have : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) := fun x ↦
    IsRegular.uniqueFactorizationMonoid_stalk x
      (WithBot.coe_le_coe.mp ((coheight_le_topologicalKrullDim x).trans hX₂.le))
  have : ∀ y : Y, UniqueFactorizationMonoid ((Y).presheaf.stalk y) := fun y ↦
    IsRegular.uniqueFactorizationMonoid_stalk y
      (WithBot.coe_le_coe.mp ((coheight_le_topologicalKrullDim y).trans hY₂.le))
  have hs : ((Iₚ).support : Set X) = {p} :=
    (coe_support_vanishingIdeal _).trans hp.closure_eq
  have he := isExceptionalCurveOfFirstKind_comap_blowupToBase_of_closedPoint p hp
    (((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq (X ↘ Spec (.of k)) 2).mp
      inferInstance).2 p hp)
  rw [Scheme.ker_fromSpecResidueField_eq_vanishingIdeal] at he
  let e := picardBlowupEquiv (Iₚ) hs (by rw [hcod]; norm_num) he
  obtain ⟨⟨a, m⟩, ha⟩ := e.surjective (Additive.ofMul b)
  have hb : twist[a.toMul, m] = b := by
    simpa only [blowupExceptionalClass_def, toMul_ofMul] using
      (picardBlowupEquiv_apply_toMul (Iₚ) hs _ he (a, m)).symm.trans
      (congrArg Additive.toMul ha)
  rw [← hb]
  exact (h a.toMul m).mpr (hX a.toMul)

end TauCeti.AlgebraicGeometry.Chow
