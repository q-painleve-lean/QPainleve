/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Homaloidal
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Ramification

import QPainleve.AlgebraicGeometry.Blowup.Tower.Factorization
import QPainleve.AlgebraicGeometry.Blowup.Tower.Polarization
import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.AlgebraicGeometry.IdealSheaf.Restriction
import QPainleve.SignedClusterModularGroup.SarkisovDegree.Multiplicity
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Ample

/-!
# The degree-one stopping case for plane resolutions

A birational map of the projective plane of degree one comes from a projective
automorphism. On a specified point-blowup resolution the pullbacks of the two
hyperplane classes coincide, even if the resolution includes extra blowups.
Thus the resolving morphism factors through the projection by a unique automorphism
over the field. A common pole ideal on the resolution forces this automorphism to
identify the reduced boundaries. This is the plane stopping case in the proof of Theorem 8.4 in
[Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public section

open AlgebraicGeometry CategoryTheory Scheme.IdealSheafData
open TauCeti.AlgebraicGeometry LineBundleClass Chow TauCeti.SymmetricAlgebra

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {k : Type u} [Field k] [IsAlgClosed k]

local notation "S" => Spec (CommRingCat.of k)
local notation "P" => Proj (homogeneousSubmodule k (Fin 3 → k))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle k (Fin 3 → k) 1)
local notation "s" => (P ↘ S)
local notation "degree" => Module.Basis.picardTwistEquiv (Pi.basisFun k (Fin 3))

variable {Y : Scheme.{u}} {n : ℕ}
  {T : BlowupTower (Proj (homogeneousSubmodule k (Fin 3 → k))) n Y}

/-- A resolved birational plane map whose line class has plane degree one has no exceptional
coordinates. Its resolved line class is the pullback of the source hyperplane class. -/
theorem pullback_hyperplane_eq_of_plane_degree_one (hT : IsClosedPointTower P T)
    (g : Y ⟶ P) (hg : g ≫ s = T.toBase ≫ s) (hbir : Scheme.BirationalOver g (𝟙 P)) :
    let : IsNoetherian P := isNoetherian_of_finiteType s
    let v := (T.picardMarking hT s).symm (Additive.ofMul (pullback g H))
    degree v.1 = 1 → pullback g H = pullback T.toBase H := by
  intro _ v hd
  have hsq : ∑ j, (v.2 j) ^ 2 = classIntersectionNumber k P v.1.toMul v.1.toMul - 1 :=
    (hT.homaloidal_intersection_identities g hg hbir).1
  rw [classIntersectionNumber_projectivePlane, ofMul_toMul, hd] at hsq
  norm_num at hsq
  have hv₂ : v.2 = 0 := funext fun j ↦ sq_eq_zero_iff.mp
    (congrFun ((Fintype.sum_eq_zero_iff_of_nonneg fun i ↦ sq_nonneg (v.2 i)).mp hsq) j)
  have hv₁ : v.1 = Additive.ofMul H := (degree).injective
    (hd.trans ((Pi.basisFun k (Fin 3)).picardTwistEquiv_apply_twist 1).symm)
  have hv := congrArg Additive.toMul ((T.picardMarking hT s).apply_symm_apply
    (Additive.ofMul (pullback g H)))
  calc
    pullback g H = (T.picardHom (v.1, v.2)).toMul := by
      simpa only [picardMarking_apply, ofMul_toMul, toMul_ofMul, Prod.mk.eta] using hv.symm
    _ = pullback T.toBase H := by rw [hv₁, hv₂, picardHom_apply_zero, toMul_ofMul]

/-- A positive-degree plane resolution has degree one if none of its nonnegative base
orders exceeds one third of the plane degree. Orders include infinitely near centers. -/
theorem plane_degree_eq_one_of_no_high_multiplicity (hT : IsClosedPointTower P T)
    (g : Y ⟶ P) (hg : g ≫ s = T.toBase ≫ s) (hbir : Scheme.BirationalOver g (𝟙 P)) :
    let : IsNoetherian P := isNoetherian_of_finiteType s
    let v := (T.picardMarking hT s).symm (Additive.ofMul (pullback g H))
    0 < degree v.1 → (∀ j, 0 ≤ -v.2 j ∧ 3 * (-v.2 j) ≤ degree v.1) → degree v.1 = 1 := by
  intro _ v hd hm
  by_contra hne
  have hgt : 1 < degree v.1 := by omega
  have hsq : ∑ j, (v.2 j) ^ 2 = classIntersectionNumber k P v.1.toMul v.1.toMul - 1 :=
    (hT.homaloidal_intersection_identities g hg hbir).1
  have hsum : (∑ j, -v.2 j) = -classIntersectionNumber k P v.1.toMul
      (mk (canonicalBundle k P 2)) - 3 :=
    (hT.homaloidal_intersection_identities g hg hbir).2
  rw [classIntersectionNumber_projectivePlane, ofMul_toMul, ← pow_two] at hsq
  rw [classIntersectionNumber_projectivePlane, ofMul_toMul, mk_canonicalBundle_projectivePlane,
    Module.Basis.picardTwistEquiv_apply_twist] at hsum
  have hsum' : (∑ j, -v.2 j) = 3 * degree v.1 - 3 := by linarith only [hsum]
  obtain ⟨j, hj⟩ := exists_degree_lt_three_mul_of_plane_homaloidal hgt
    (fun j ↦ (hm j).1) (by simpa only [neg_sq] using hsq) hsum'
  exact (not_lt_of_ge (hm j).2) hj

/-- A specified birational plane resolution of degree one descends to a unique
automorphism of the plane over the coefficient field. The automorphism commutes
with the resolving morphism on the entire tower. -/
theorem existsUnique_iso_of_plane_degree_one (hT : IsClosedPointTower P T)
    (g : Y ⟶ P) (hg : g ≫ s = T.toBase ≫ s) (hbir : Scheme.BirationalOver g (𝟙 P)) :
    let : IsNoetherian P := isNoetherian_of_finiteType s
    let v := (T.picardMarking hT s).symm (Additive.ofMul (pullback g H))
    degree v.1 = 1 → ∃! e : P ≅ P, T.toBase ≫ e.hom = g ∧ e.hom ≫ s = s := by
  intro _ v hd
  let : Y.Over S := ⟨T.toBase ≫ s⟩
  have : Y.IsProjectiveOver k := T.isProjectiveOver k
  have : IsIntegral Y := hT.isIntegral s
  have : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension s
  have : g.IsOver S := ⟨hg⟩
  obtain ⟨m, Z, U, e, hU, he⟩ := g.exists_isClosedPointTower_factorization (k := k) hbir
  have hbase : T.toBase ≫ s = e.hom ≫ U.toBase ≫ s := by
    rw [← Category.assoc, he, hg]
  have hH : (H).IsAmple := by
    exact TauCeti.SymmetricAlgebra.isAmple_twistingSheaf k (Fin 3 → k) Nat.one_pos
  have hpull := hT.pullback_hyperplane_eq_of_plane_degree_one g hg hbir hd
  rw [← he] at hpull
  simpa only [he] using hT.existsUnique_iso_over_of_pullback_eq hU e hbase hH hH hpull.symm

/-- If the two plane boundaries give the same pole ideal on the resolution, the degree-one
automorphism also identifies their reductions. The pole conditions express the pullback
divisor as ramification minus total transform. -/
theorem existsUnique_iso_of_plane_degree_one_of_eq_poleIdeal (hT : IsClosedPointTower P T)
    (g : Y ⟶ P) (hg : g ≫ s = T.toBase ≫ s) (hbir : Scheme.BirationalOver g (𝟙 P))
    (D₀ D₁ : (P).IdealSheafData) (J : Y.IdealSheafData) :
    let : IsNoetherian P := isNoetherian_of_finiteType s
    let : Y.Over S := ⟨T.toBase ≫ s⟩
    letI : g.IsOver S := ⟨hg⟩
    letI : Smooth (Y ↘ S) := (hT.smoothOfRelativeDimension s).smooth
    let v := (T.picardMarking hT s).symm (Additive.ofMul (pullback g H))
    degree v.1 = 1 →
    D₀.comap T.toBase = J * hT.ramificationIdealSheafToBase k →
    D₁.comap g = J * ramificationIdealSheaf k g →
    ∃! e : P ≅ P, T.toBase ≫ e.hom = g ∧ e.hom ≫ s = s ∧
      D₁.radical.comap e.hom = D₀.radical := by
  intro _ _ v hd hD₀ hD₁
  have : g.IsOver S := ⟨hg⟩
  have : Smooth (Y ↘ S) := (hT.smoothOfRelativeDimension s).smooth
  obtain ⟨e, ⟨he, hes⟩, huniq⟩ := hT.existsUnique_iso_of_plane_degree_one g hg hbir hd
  have : e.hom.IsOver S := ⟨hes⟩
  have : T.toBase.IsOver S := ⟨rfl⟩
  have : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension s
  let R := hT.ramificationIdealSheafToBase k
  have hram : ramificationIdealSheaf k g = R := by
    calc
      _ = ramificationIdealSheaf k (T.toBase ≫ e.hom) := ramificationIdealSheaf_congr k he.symm
      _ = ramificationIdealSheaf k T.toBase := by
        rw [ramificationIdealSheaf_comp k T.toBase e.hom 2,
          ramificationIdealSheaf_eq_top_of_isOpenImmersion k e.hom, comap_top, mul_top]
      _ = R := (hT.ramificationIdealSheafToBase_def k).symm
  have hcart := hT.isEffectiveCartier_ramificationIdealSheafToBase k
  have heq : (D₁.comap e.hom).comap T.toBase = D₀.comap T.toBase := hcart.mul_left_cancel (by
    rw [← comap_comp, he, hD₁, hram, hD₀])
  have : Surjective T.toBase := hT.surjective s
  have hboundary := radical_eq_of_support_comap_eq T.toBase (congrArg support heq)
  rw [radical_comap_of_isOpenImmersion] at hboundary
  exact ⟨e, ⟨he, hes, hboundary⟩, fun _ h ↦ huniq _ ⟨h.1, h.2.1⟩⟩

end QPainleve.BlowupTower.IsClosedPointTower
