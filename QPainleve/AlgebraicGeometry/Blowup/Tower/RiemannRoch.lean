/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Intersection

/-!
# Riemann–Roch across common point-blowup resolutions

In the ordered Picard marking of a point-blowup tower, each exceptional coefficient
contributes the same amount to twice the change in Euler characteristic and to the
change in the intersection numerator of Riemann–Roch. The doubled equation therefore
transfers both up and down a tower, including the parity of the intersection numerator.
Two towers with the same source over the base field transfer the equation between
their bases.

The intersection numerator is that of [Hacking, *Compact Complex Surfaces*, Theorem 5.2][Hacking].
The proof uses the Picard and canonical markings of a tower and the Euler characteristic
formula for exceptional twists.

[Hacking]: https://paulhacking.github.io/surfaces.pdf#page=30
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry LineBundleClass
open scoped BigOperators

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {X Y W : Scheme.{u}} {m n : ℕ}
variable (k : Type u) [Field k] [IsAlgClosed k]

local notation "base" => Spec (CommRingCat.of k)
local notation "K[" Z "]" => mk (canonicalBundle k Z 2)
local notation "euler[" Z ", " a "]" =>
  (2 * (eulerCharBelow k a 3 - eulerCharBelow (X := Z) k 1 3))
local notation "numerator[" Z ", " a "]" =>
  (Chow.classIntersectionNumber k Z a a - Chow.classIntersectionNumber k Z a K[Z])

variable [X.Over (Spec (.of k))] [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [IsIntegral X] [X.IsProjectiveOver k] {T : BlowupTower X m W}

/-- For any exceptional coefficients, the change in twice the Euler characteristic along a
tower equals the change in the Riemann–Roch intersection numerator. The formula uses the
total-transform exceptional classes and allows infinitely near centers. -/
theorem two_mul_eulerCharBelow_sub_eq_sub_intersectionNumerator_picardMarking
    (hT : IsClosedPointTower X T) (a : Additive (LineBundleClass X) × (Fin m → ℤ)) :
    let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ base)
    let : W.Over base := ⟨T.toBase ≫ X ↘ base⟩
    let : SmoothOfRelativeDimension 2 (W ↘ base) := hT.smoothOfRelativeDimension (X ↘ base)
    let b := (T.picardMarking hT (X ↘ base) a).toMul
    2 * (eulerCharBelow k b 3 - eulerCharBelow k a.1.toMul 3) =
      numerator[W, b] - numerator[X, a.1.toMul] := by
  let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ base)
  have hχ := two_mul_eulerCharBelow_sub_picardHom k hT a
  have hself := classIntersectionNumber_picardMarking k hT a a
  have hcanonical := classIntersectionNumber_picardMarking k hT a
    (Additive.ofMul K[X], fun _ ↦ 1)
  dsimp only at hχ hself hcanonical ⊢
  rw [picardMarking_canonicalClass] at hcanonical
  simp only [toMul_ofMul, mul_one] at hcanonical
  simp only [← picardMarking_apply T hT (X ↘ base), mul_sub, mul_one,
    Finset.sum_sub_distrib] at hχ
  omega

/-- The integral Riemann–Roch equation for a line bundle holds exactly when it holds for
the class with any specified exceptional coefficients in the point-blowup marking. -/
theorem eulerCharBelow_eq_riemannRoch_picardMarking_iff
    (hT : IsClosedPointTower X T) (a : Additive (LineBundleClass X) × (Fin m → ℤ)) :
    let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ base)
    let : W.Over base := ⟨T.toBase ≫ X ↘ base⟩
    let : SmoothOfRelativeDimension 2 (W ↘ base) := hT.smoothOfRelativeDimension (X ↘ base)
    let b := (T.picardMarking hT (X ↘ base) a).toMul
    (euler[W, b] = numerator[W, b]) ↔
      euler[X, a.1.toMul] = numerator[X, a.1.toMul] := by
  have hχ := two_mul_eulerCharBelow_sub_eq_sub_intersectionNumerator_picardMarking k hT a
  have hχ₁ := two_mul_eulerCharBelow_sub_picardHom k hT 0
  dsimp only at hχ hχ₁ ⊢
  simp only [map_zero, toMul_zero, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero] at hχ₁
  omega

/-- Riemann–Roch for every line bundle transfers in both directions along a point-blowup
tower. The equation is stated after multiplying by two, so it includes the parity
congruence of the canonical class. -/
theorem forall_eulerCharBelow_eq_riemannRoch_iff
    (hT : IsClosedPointTower X T) :
    let : W.Over base := ⟨T.toBase ≫ X ↘ base⟩
    let : SmoothOfRelativeDimension 2 (W ↘ base) := hT.smoothOfRelativeDimension (X ↘ base)
    (∀ b : LineBundleClass W, euler[W, b] = numerator[W, b]) ↔
      ∀ a : LineBundleClass X, euler[X, a] = numerator[X, a] := by
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ base)
  constructor
  · intro h a
    exact (eulerCharBelow_eq_riemannRoch_picardMarking_iff k hT (Additive.ofMul a, 0)).mp (h _)
  · intro h b
    obtain ⟨a, ha⟩ := (T.picardMarking hT (X ↘ base)).surjective (Additive.ofMul b)
    rw [← toMul_ofMul b, ← ha]
    exact (eulerCharBelow_eq_riemannRoch_picardMarking_iff k hT a).mpr (h a.1.toMul)

variable [Y.Over (Spec (.of k))] [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]
  [IsIntegral Y] [Y.IsProjectiveOver k] {U : BlowupTower Y n W}

/-- For two smooth integral projective surfaces with a common resolution by closed point
blowups over the base field, the integral Riemann–Roch equation holds for every line bundle
on one surface exactly when it holds for every line bundle on the other. -/
theorem forall_eulerCharBelow_eq_riemannRoch_iff_of_common_resolution [W.Over base]
    [T.toBase.IsOver base] [U.toBase.IsOver base]
    (hT : IsClosedPointTower X T) (hU : IsClosedPointTower Y U) :
    (∀ a : LineBundleClass X, euler[X, a] = numerator[X, a]) ↔
      ∀ b : LineBundleClass Y, euler[Y, b] = numerator[Y, b] := by
  have transport (g g' : W ⟶ base) (h : g = g')
      (hg : SmoothOfRelativeDimension 2 g) (hg' : SmoothOfRelativeDimension 2 g') :
      (let : W.Over base := ⟨g⟩
       let : SmoothOfRelativeDimension 2 (W ↘ base) := hg
       ∀ c : LineBundleClass W, euler[W, c] = numerator[W, c]) ↔
      (let : W.Over base := ⟨g'⟩
       let : SmoothOfRelativeDimension 2 (W ↘ base) := hg'
       ∀ c : LineBundleClass W, euler[W, c] = numerator[W, c]) := by
    subst g'
    rfl
  have he := transport (T.toBase ≫ X ↘ base) (U.toBase ≫ Y ↘ base)
    ((comp_over T.toBase base).trans (comp_over U.toBase base).symm)
    (hT.smoothOfRelativeDimension (X ↘ base)) (hU.smoothOfRelativeDimension (Y ↘ base))
  exact (hT.forall_eulerCharBelow_eq_riemannRoch_iff k).symm.trans
    (he.trans (hU.forall_eulerCharBelow_eq_riemannRoch_iff k))

end QPainleve.BlowupTower.IsClosedPointTower
