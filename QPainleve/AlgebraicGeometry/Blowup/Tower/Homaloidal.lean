/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform
public import QPainleve.AlgebraicGeometry.Chow.Birational
public import QPainleve.AlgebraicGeometry.Chow.ProjectivePlane.Numerical

import QPainleve.AlgebraicGeometry.Blowup.Tower.Intersection
import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective

/-!
# Homaloidal intersection identities

On a point-blowup resolution of a birational map to the projective plane, the pullback
of a line has square one and canonical degree minus three. In the ordered Picard marking,
these two intersection numbers determine the sum of the multiplicities and the sum of
their squares, including at infinitely near points. These are the two identities used
in the proof of Lemma 8.12 in [Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public section

open AlgebraicGeometry CategoryTheory
open Scheme.IdealSheafData.IsEffectiveCartier (toInvertibleSheaf)
open TauCeti.AlgebraicGeometry LineBundleClass Chow TauCeti.SymmetricAlgebra

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {n : ℕ}
  {T : BlowupTower X n Y} [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "S" => Spec (CommRingCat.of k)
local notation "f" => (X ↘ S)
local notation "P" => Proj (homogeneousSubmodule k (Fin 3 → k))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle k (Fin 3 → k) 1)
local notation "B(" Z ")" => classIntersectionNumber k Z
local notation "K(" Z ")" => mk (canonicalBundle k Z 2)

/-- The homaloidal identities for a birational morphism to the projective plane on a
point-blowup tower. The identities use the base coordinate and the negatives of the
exceptional coordinates of the resolved line class. The exceptional basis consists of
total transforms. -/
theorem homaloidal_intersection_identities (hT : IsClosedPointTower X T)
    (g : Y ⟶ P) (hg : g ≫ (P ↘ S) = T.toBase ≫ f)
    (hbir : Scheme.BirationalOver g (𝟙 P)) :
    let : IsNoetherian X := isNoetherian_of_finiteType f
    let v := (T.picardMarking hT f).symm (Additive.ofMul (pullback g H))
    (∑ j, (v.2 j) ^ 2) = B(X) v.1.toMul v.1.toMul - 1 ∧
      (∑ j, -v.2 j) = -B(X) v.1.toMul K(X) - 3 := by
  let : IsNoetherian X := isNoetherian_of_finiteType f
  let : Y.Over S := ⟨T.toBase ≫ f⟩
  have : Y.IsProjectiveOver k := T.isProjectiveOver k
  have : IsIntegral Y := hT.isIntegral f
  have : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f
  have : g.IsOver S := ⟨hg⟩
  let v := (T.picardMarking hT f).symm (Additive.ofMul (pullback g H))
  have hv : (T.picardMarking hT f v).toMul = pullback g H :=
    congrArg Additive.toMul ((T.picardMarking hT f).apply_symm_apply _)
  have hsq := classIntersectionNumber_picardMarking k hT v v
  have hcanon := classIntersectionNumber_picardMarking k hT v (Additive.ofMul K(X), fun _ ↦ 1)
  have hK := picardMarking_canonicalClass k hT
  dsimp only at hsq hcanon hK
  rw [hv, g.classIntersectionNumber_pullback_of_birational hbir,
    classIntersectionNumber_projectivePlane, Module.Basis.picardTwistEquiv_apply_twist] at hsq
  rw [hv, hK, toMul_ofMul] at hcanon
  have hproj := g.classIntersectionNumber_pullback_canonicalBundle_of_birational (k := k) hbir H
  rw [classIntersectionNumber_projectivePlane, mk_canonicalBundle_projectivePlane,
    Module.Basis.picardTwistEquiv_apply_twist, Module.Basis.picardTwistEquiv_apply_twist] at hproj
  have hdegree := hproj.symm.trans hcanon
  simp only [← pow_two] at hsq
  simp only [one_mul, mul_one, toMul_ofMul] at hdegree
  have h₁ : (∑ j, v.2 j ^ 2) = B(X) v.1.toMul v.1.toMul - 1 := by omega
  have h₂ : (∑ j, -v.2 j) = -B(X) v.1.toMul K(X) - 3 := by
    rw [Finset.sum_neg_distrib]
    omega
  exact ⟨h₁, h₂⟩

/-- For a divisor whose strict transform has the resolved line class, the homaloidal
identities compute the sums of the actual orders at successive blowup centers. -/
theorem homaloidal_intersection_identities_strictTransform (hT : IsClosedPointTower X T)
    (g : Y ⟶ P) (hg : g ≫ (P ↘ S) = T.toBase ≫ f)
    (hbir : Scheme.BirationalOver g (𝟙 P)) {D : X.IdealSheafData} (hD : D.IsEffectiveCartier) :
    let : IsNoetherian X := isNoetherian_of_finiteType f
    let hD' := hT.isEffectiveCartier_strictTransform f hD
    (mk (toInvertibleSheaf hD'))⁻¹ = pullback g H →
      let a := (mk (toInvertibleSheaf hD))⁻¹
      (∑ j, (hT.strictTransformCoefficients D j) ^ 2) = B(X) a a - 1 ∧
        (∑ j, -hT.strictTransformCoefficients D j) = -B(X) a K(X) - 3 := by
  let : IsNoetherian X := isNoetherian_of_finiteType f
  dsimp only
  intro hclass
  have hm := hT.picardMarking_strictTransform f hD
  rw [hclass] at hm
  have he := (LinearEquiv.symm_apply_eq _).mpr hm.symm
  have h := hT.homaloidal_intersection_identities g hg hbir
  dsimp only at h
  rw [he] at h
  exact h

end QPainleve.BlowupTower.IsClosedPointTower
