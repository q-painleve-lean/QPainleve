/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.BaseChange
public import TauCeti.RingTheory.MvPolynomial.HomogeneousLocalization

import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Basic
import TauCeti.RingTheory.MvPolynomial.Dehomogenization

/-!
# Coordinate charts of projective space

Dehomogenizing at a variable identifies the degree-zero localization with the
polynomial ring on the remaining variables. The inverse sends each variable to its
ratio with the distinguished homogeneous coordinate. At the scheme level, this
identifies the standard open with affine space over the coefficient ring.

The comparison uses Tau Ceti's generation of the chart by normalized coordinates
and its substitution `dehomogenize`.
-/

public noncomputable section

open CategoryTheory HomogeneousLocalization TauCeti

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

section CoordinateRing

variable {k : Type u} [CommRing k] {n : ℕ}

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k

open MvPolynomial in
private def awayToPolynomial (i : Fin (n + 1)) : Away 𝒜 (MvPolynomial.X i) →+*
    MvPolynomial (Fin n) k :=
  Away.lift 𝒜 (dehomogenize (R := k) i).toRingHom (by simp)

private theorem awayToPolynomial_algebraMap (i : Fin (n + 1)) (c : k) :
    awayToPolynomial i (algebraMap k (Away 𝒜 (MvPolynomial.X i)) c) = MvPolynomial.C c := by
  have hmap : algebraMap k (Away 𝒜 (MvPolynomial.X i)) c =
      algebraMap (𝒜 0) (Away 𝒜 (MvPolynomial.X i)) (algebraMap k (𝒜 0) c) := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_algebraMap]
    rfl
  rw [hmap, awayToPolynomial, Away.lift_algebraMap]
  exact (dehomogenize (R := k) i).commutes c

open MvPolynomial in
private theorem awayToPolynomial_ratio (i : Fin (n + 1)) (j : Fin n) :
    awayToPolynomial (k := k) i (TauCeti.MvPolynomial.awayXRatio i (i.succAbove j)) =
      MvPolynomial.X j := by
  rw [TauCeti.MvPolynomial.awayXRatio_def, awayToPolynomial, Away.lift_mk]
  simp

/-- Dehomogenization identifies a standard affine chart of polynomial projective space
with the polynomial ring on the remaining coordinates. -/
def awayCoordinateAlgEquiv (i : Fin (n + 1)) :
    Away 𝒜 (MvPolynomial.X i) ≃ₐ[k] MvPolynomial (Fin n) k := by
  classical
  let e := MvPolynomial.aeval (R := k)
    (fun j : Fin n ↦ TauCeti.MvPolynomial.awayXRatio (R := k) i (i.succAbove j))
  have hl : (awayToPolynomial (k := k) i).comp e.toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [e, awayToPolynomial_algebraMap, ← MvPolynomial.algebraMap_eq]
    · intro j
      simp [e, awayToPolynomial_ratio]
  have hs : Function.Surjective e := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval,
      ← TauCeti.MvPolynomial.adjoin_range_awayXRatio i]
    refine le_antisymm (Algebra.adjoin_mono ?_) (Algebra.adjoin_le ?_)
    · rintro _ ⟨j, rfl⟩
      exact ⟨i.succAbove j, rfl⟩
    · rintro _ ⟨j, rfl⟩
      by_cases hj : j = i
      · subst j
        simp
      · obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq hj
        exact Algebra.subset_adjoin ⟨a, rfl⟩
  have hleft : Function.LeftInverse (awayToPolynomial (k := k) i) e :=
    fun x ↦ DFunLike.congr_fun hl x
  exact (AlgEquiv.ofBijective e ⟨hleft.injective, hs⟩).symm

/-- On the standard chart with denominator `Xᵢ`, the ratio `Xⱼ / Xᵢ` for a remaining
coordinate is the corresponding polynomial variable. -/
@[simp]
theorem awayCoordinateAlgEquiv_apply_ratio (i : Fin (n + 1)) (j : Fin n) :
    awayCoordinateAlgEquiv (k := k) i (TauCeti.MvPolynomial.awayXRatio i (i.succAbove j)) =
      MvPolynomial.X j := by
  apply (awayCoordinateAlgEquiv (k := k) i).symm.injective
  rw [AlgEquiv.symm_apply_apply]
  exact (MvPolynomial.aeval_X (R := k) (fun a : Fin n ↦
    TauCeti.MvPolynomial.awayXRatio (R := k) i (i.succAbove a)) j).symm

end CoordinateRing

section AffineSpace

variable {R : Type u} [CommRing R] {d : ℕ}

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (d + 1)) R

private def affineSpaceChartIso (i : Fin (d + 1)) :
    𝔸(ULift.{u} (Fin d); Spec (.of R)) ≅ Spec (.of (Away 𝒜 (MvPolynomial.X i))) :=
  AffineSpace.SpecIso _ _ ≪≫ Scheme.Spec.mapIso
    ((awayCoordinateAlgEquiv (k := R) i).trans
      (MvPolynomial.renameEquiv R Equiv.ulift.symm)).toRingEquiv.toCommRingCatIso.op

/-- A standard coordinate open of polynomial projective space is affine space.
The affine variable indexed by `j` corresponds to the ratio `Xᵢ.succAbove j / Xᵢ`. -/
def basicOpenIsoAffineSpace (i : Fin (d + 1)) :
    (basicOpen 𝒜 (MvPolynomial.X i)).toScheme ≅ 𝔸(ULift.{u} (Fin d); Spec (.of R)) :=
  basicOpenIsoSpec 𝒜 _ ((MvPolynomial.mem_homogeneousSubmodule ..).mpr
    (MvPolynomial.isHomogeneous_X R i)) one_pos ≪≫ (affineSpaceChartIso i).symm

/-- The affine-space inclusion into the coordinate open lies over the coefficient ring. -/
@[reassoc (attr := simp)]
theorem basicOpenIsoAffineSpace_inv_toSpecCoeff (i : Fin (d + 1)) :
    (basicOpenIsoAffineSpace (R := R) i).inv ≫ (basicOpen 𝒜 (MvPolynomial.X i)).ι ≫
      toSpecCoeff 𝒜 = 𝔸(ULift.{u} (Fin d); Spec (.of R)) ↘ Spec (.of R) := by
  rw [basicOpenIsoAffineSpace, Iso.trans_inv, Category.assoc, Iso.symm_inv,
    basicOpenIsoSpec_inv_ι_assoc, awayι_toSpecCoeff, affineSpaceChartIso, Iso.trans_hom,
    Category.assoc, ← Iso.eq_inv_comp, AffineSpace.SpecIso_inv_over]
  rw [Scheme.Spec.mapIso_hom, Scheme.Spec_map, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact ((awayCoordinateAlgEquiv (k := R) i).trans
    (MvPolynomial.renameEquiv R Equiv.ulift.symm)).commutes r

end AffineSpace

end AlgebraicGeometry.Proj
