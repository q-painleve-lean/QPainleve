/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.Cremona
public import QPainleve.LinearAlgebra.BilinearForm.Conjugation
public import QPainleve.SignedClusterModularGroup.Boundary.Isometry
public import QPainleve.SignedClusterModularGroup.Realization.Boundary

import QPainleve.SignedClusterModularGroup.Boundary.Conjugation
import QPainleve.SignedClusterModularGroup.Boundary.Cremona

/-!
# Cremona isometries in the Picard marking

For a marked nef square-zero anticanonical cycle without internal `(-2)` curves,
the marked Picard action projects onto the Cremona isometry group of the surface.
For at least three boundary components this projection is an equivalence.
For one or two components the rotation group is the Cremona isometry group,
and the signed group has an extra direct factor of order two.

The marked comparisons transport the Cremona projection of the numbered cycle
through the Picard marking.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry
open Scheme Scheme.IdealSheafData LineBundleClass LinearMap
open QPainleve.SignedBoundaryIsometryGroup

universe u

namespace QPainleve.SignedClusterModularGroup.MarkedSurface

variable {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ} [NeZero n] {L : Type u}
  [AddCommGroup L] {B : LinearMap.BilinForm ℤ L} {X : Scheme.{u}}
  (M : MarkedSurface k n B X)

local notation "S" => Spec (CommRingCat.of k)
local notation "base" => (M.surface ↘ S)
local notation "D" => M.pair.hom.left.ker
local notation "hD" => M.isEffectiveCartier_boundaryIdeal
local notation "d" => M.boundaryClass hD
local notation "Cr" => Chow.cremonaIsometryGroup k M.surface

variable [IsRationalOver (M.surface ↘ Spec (CommRingCat.of k))]
  (hcan : letI : SmoothOfRelativeDimension 2 (M.surface ↘ Spec (CommRingCat.of k)) := M.smooth
    (LineBundleClass.mk M.isEffectiveCartier_boundaryIdeal.toInvertibleSheaf)⁻¹ =
      (LineBundleClass.mk (QPainleve.canonicalBundle k M.surface 2))⁻¹)
  (hnef : (LineBundleClass.mk M.isEffectiveCartier_boundaryIdeal.toInvertibleSheaf)⁻¹.IsNef k
    (M.surface ↘ Spec (CommRingCat.of k)))
  (hsq : let a := (LineBundleClass.mk M.isEffectiveCartier_boundaryIdeal.toInvertibleSheaf)⁻¹
    Chow.classIntersectionNumber k M.surface a a = 0)
  (hroot : letI : SmoothOfRelativeDimension 2 (M.surface ↘ Spec (CommRingCat.of k)) := M.smooth
    letI : M.surface.IsProjectiveOver k := M.projective
    letI : IsNoetherian M.surface :=
      isNoetherian_of_finiteType (M.surface ↘ Spec (CommRingCat.of k))
    letI := Scheme.Hom.uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
      (M.surface ↘ Spec (CommRingCat.of k))
    ∀ r : CodimensionOnePoint M.surface,
      Disjoint (closure {(r : M.surface)}) M.pair.hom.left.ker.support →
      Chow.classIntersectionNumber k M.surface (primeDivisorClass r) (primeDivisorClass r) ≠ -2)

local notation "a" =>
  (fun j ↦ Additive.ofMul (primeDivisorClass
    (boundaryPrimeEmbedding D (Scheme.NodalCycleNumbering.boundaryPrimeEquiv M.imageCycle hD j))))

omit [IsRationalOver (M.surface ↘ Spec (.of k))] in
private theorem marking_symm_imageCycle_class :
    letI : SmoothOfRelativeDimension 2 base := M.smooth
    letI : M.surface.IsProjectiveOver k := M.projective
    letI : IsNoetherian M.surface := isNoetherian_of_finiteType base
    letI := (base).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    letI := M.prestable_boundaryImage
    ∀ j : ZMod n, M.marking.symm (a j) = d ((1 : ℤˣ) • j + 0) := by
  let : SmoothOfRelativeDimension 2 base := M.smooth
  let : M.surface.IsProjectiveOver k := M.projective
  let : IsNoetherian M.surface := isNoetherian_of_finiteType base
  let := (base).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let := M.prestable_boundaryImage
  intro j
  simp only [M.boundaryPrimeEmbedding_imageCycle hD, one_smul, add_zero]
  have hj : M.marking (d j) = Additive.ofMul (primeDivisorClass (M.boundaryPrime hD j)) :=
    (M.picardMarking_apply (d j)).symm.trans (M.picardMarking_boundaryClass hD j)
  exact (congrArg M.marking.symm hj.symm).trans (M.marking.symm_apply_apply _)

local notation "markingCongr" =>
  SignedBoundaryIsometryGroup.congr M.marking.symm M.marking_symm_imageCycle_class

/-- The signed marked Picard isometry acts on the surface by conjugating through the marking.
For a square-zero anticanonical boundary without internal `(-2)` curves the action preserves
the effective classes and the canonical class. -/
def cremonaPicardHom :
    letI : SmoothOfRelativeDimension 2 base := M.smooth
    letI : M.surface.IsProjectiveOver k := M.projective
    signedBoundaryIsometryGroup B d →* Cr := by
  let : SmoothOfRelativeDimension 2 base := M.smooth
  let : M.surface.IsProjectiveOver k := M.projective
  let : IsNoetherian M.surface := isNoetherian_of_finiteType base
  let := (base).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let := M.prestable_boundaryImage
  exact (M.imageCycle.cremonaProjection hD (inv_injective hcan) hnef hsq hroot).comp
    (markingCongr).toMonoidHom

/-- The projection evaluates by conjugating the underlying marked isometry. -/
@[simp]
theorem cremonaPicardHom_apply (g : signedBoundaryIsometryGroup B d) :
    letI : SmoothOfRelativeDimension 2 base := M.smooth
    letI : M.surface.IsProjectiveOver k := M.projective
    (M.cremonaPicardHom hcan hnef hsq hroot g).val =
      M.marking.isometryGroupCongr (toIsometry B d g) := by
  let : SmoothOfRelativeDimension 2 base := M.smooth
  let : M.surface.IsProjectiveOver k := M.projective
  let : IsNoetherian M.surface := isNoetherian_of_finiteType base
  let := (base).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let := M.prestable_boundaryImage
  simp only [cremonaPicardHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  refine (M.imageCycle.val_cremonaProjection_apply hD (inv_injective hcan) hnef hsq hroot
    (markingCongr g)).trans ?_
  have hSymm : M.marking.symm.symm = M.marking := rfl
  simpa only [toIsometry_apply, hSymm] using
    congrArg Prod.fst (coe_congr M.marking.symm M.marking_symm_imageCycle_class g)

/-- Every Cremona isometry comes from a signed isometry of the marked boundary. -/
theorem cremonaPicardHom_surjective :
    letI : SmoothOfRelativeDimension 2 base := M.smooth
    letI : M.surface.IsProjectiveOver k := M.projective
    Function.Surjective (M.cremonaPicardHom hcan hnef hsq hroot) := by
  let : SmoothOfRelativeDimension 2 base := M.smooth
  let : M.surface.IsProjectiveOver k := M.projective
  let : IsNoetherian M.surface := isNoetherian_of_finiteType base
  let := (base).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let := M.prestable_boundaryImage
  exact (M.imageCycle.cremonaProjection_surjective hD (inv_injective hcan) hnef hsq hroot).comp
    (markingCongr).surjective

/-- For three or more components the Cremona projection determines the signed isometry. -/
def signedBoundaryIsometryEquivCremona (hn : 3 ≤ n) :
    letI : SmoothOfRelativeDimension 2 base := M.smooth
    letI : M.surface.IsProjectiveOver k := M.projective
    signedBoundaryIsometryGroup B d ≃* Cr := by
  let : SmoothOfRelativeDimension 2 base := M.smooth
  let : M.surface.IsProjectiveOver k := M.projective
  let : IsNoetherian M.surface := isNoetherian_of_finiteType base
  let := (base).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let := M.prestable_boundaryImage
  refine MulEquiv.ofBijective (M.cremonaPicardHom hcan hnef hsq hroot) ⟨?_, ?_⟩
  · exact (M.imageCycle.cremonaProjection_injective hD (inv_injective hcan) hnef hsq hroot hn).comp
      (markingCongr).injective
  · exact M.cremonaPicardHom_surjective hcan hnef hsq hroot

/-- The large-boundary equivalence is the Cremona Picard projection. -/
@[simp]
theorem signedBoundaryIsometryEquivCremona_apply (hn : 3 ≤ n)
    (g : signedBoundaryIsometryGroup B d) :
    letI : SmoothOfRelativeDimension 2 base := M.smooth
    letI : M.surface.IsProjectiveOver k := M.projective
    M.signedBoundaryIsometryEquivCremona hcan hnef hsq hroot hn g =
      M.cremonaPicardHom hcan hnef hsq hroot g :=
  (rfl)

/-- For one or two boundary components, every Cremona isometry is a unique marked rotation. -/
def boundaryRotationEquivCremona (hn : n ≤ 2) :
    letI : SmoothOfRelativeDimension 2 base := M.smooth
    letI : M.surface.IsProjectiveOver k := M.projective
    boundaryRotationGroup B d ≃* Cr := by
  let : SmoothOfRelativeDimension 2 base := M.smooth
  let : M.surface.IsProjectiveOver k := M.projective
  let : IsNoetherian M.surface := isNoetherian_of_finiteType base
  let := (base).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let := M.prestable_boundaryImage
  exact (boundaryRotationGroupCongr M.marking.symm M.marking_symm_imageCycle_class).trans
    (M.imageCycle.boundaryRotationEquivCremona hD (inv_injective hcan) hnef hsq hroot hn)

/-- The rotation equivalence acts by the same marked Picard projection at sign one. -/
@[simp]
theorem boundaryRotationEquivCremona_apply (hn : n ≤ 2) (g : boundaryRotationGroup B d) :
    letI : SmoothOfRelativeDimension 2 base := M.smooth
    letI : M.surface.IsProjectiveOver k := M.projective
    M.boundaryRotationEquivCremona hcan hnef hsq hroot hn g =
      M.cremonaPicardHom hcan hnef hsq hroot (rotationInclusion B d g) := by
  let : SmoothOfRelativeDimension 2 base := M.smooth
  let : M.surface.IsProjectiveOver k := M.projective
  let : IsNoetherian M.surface := isNoetherian_of_finiteType base
  let := (base).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let := M.prestable_boundaryImage
  simp only [boundaryRotationEquivCremona, MulEquiv.trans_apply, cremonaPicardHom,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, congr_rotationInclusion]
  exact M.imageCycle.boundaryRotationEquivCremona_apply hD (inv_injective hcan) hnef hsq hroot hn _

/-- For one or two boundary components the signed group is the direct product of Cremona
isometries and the sign group. -/
def signedBoundaryIsometryEquivCremonaProd (hn : n ≤ 2) :
    letI : SmoothOfRelativeDimension 2 base := M.smooth
    letI : M.surface.IsProjectiveOver k := M.projective
    signedBoundaryIsometryGroup B d ≃* Cr × ℤˣ := by
  let : SmoothOfRelativeDimension 2 base := M.smooth
  let : M.surface.IsProjectiveOver k := M.projective
  let : IsNoetherian M.surface := isNoetherian_of_finiteType base
  let := (base).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let := M.prestable_boundaryImage
  exact (markingCongr).trans
    (M.imageCycle.signedBoundaryIsometryEquivCremonaProd hD (inv_injective hcan) hnef hsq hroot hn)

/-- The two coordinates of the small-boundary equivalence are the Cremona projection and
the original sign. -/
@[simp]
theorem signedBoundaryIsometryEquivCremonaProd_apply (hn : n ≤ 2)
    (g : signedBoundaryIsometryGroup B d) :
    letI : SmoothOfRelativeDimension 2 base := M.smooth
    letI : M.surface.IsProjectiveOver k := M.projective
    M.signedBoundaryIsometryEquivCremonaProd hcan hnef hsq hroot hn g =
      (M.cremonaPicardHom hcan hnef hsq hroot g, sign B d g) := by
  let : SmoothOfRelativeDimension 2 base := M.smooth
  let : M.surface.IsProjectiveOver k := M.projective
  let : IsNoetherian M.surface := isNoetherian_of_finiteType base
  let := (base).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let := M.prestable_boundaryImage
  simp only [signedBoundaryIsometryEquivCremonaProd, MulEquiv.trans_apply, cremonaPicardHom,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  refine (M.imageCycle.signedBoundaryIsometryEquivCremonaProd_apply hD (inv_injective hcan)
    hnef hsq hroot hn (markingCongr g)).trans (Prod.ext rfl ?_)
  simpa only [SignedBoundaryIsometryGroup.sign_apply] using
    congrArg Prod.snd (coe_congr M.marking.symm M.marking_symm_imageCycle_class g)

end QPainleve.SignedClusterModularGroup.MarkedSurface
