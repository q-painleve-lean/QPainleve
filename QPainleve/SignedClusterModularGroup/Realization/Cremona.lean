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
import QPainleve.SignedClusterModularGroup.Realization.Reflection
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced

/-!
# Cremona isometries in the Picard marking

For a marked nef square-zero anticanonical cycle without internal `(-2)` curves,
the marked Picard action projects onto the Cremona isometry group of the surface.
For at least three boundary components this projection is an equivalence.
For one or two components the rotation group is the Cremona isometry group,
and the signed group has an extra direct factor of order two.

The geometric input is
`QPainleve.BoundaryCycle.range_toIsometry_eq_cremonaIsometryGroup_of_cycle_gram`.
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

include hcan hnef hsq hroot in
private theorem range_markedProjection :
    letI : SmoothOfRelativeDimension 2 base := M.smooth
    letI : M.surface.IsProjectiveOver k := M.projective
    (M.marking.isometryGroupCongr.toMonoidHom.comp (toIsometry B d)).range = Cr := by
  let : SmoothOfRelativeDimension 2 base := M.smooth
  let : M.surface.IsProjectiveOver k := M.projective
  let : IsNoetherian M.surface := isNoetherian_of_finiteType base
  let := (base).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let : PrestableFamily ((D).subscheme ↘ S) := M.prestable_boundaryImage
  let : IsReduced (D).subscheme :=
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := (D).subscheme ↘ S)).isReduced
  let p := (M.numberedBoundaryPrimes hD).trans (D).boundaryPrimeEmbedding
  let a := fun j ↦ Additive.ofMul (primeDivisorClass (p j))
  have hp (j : ZMod n) : p j = M.boundaryPrime hD j := Subtype.ext (by simp [p])
  have hmark (j : ZMod n) : M.marking (d j) = a j := by
    dsimp only [a]
    rw [← M.picardMarking_apply, M.picardMarking_boundaryClass, hp]
  have hgram (i j : ZMod n) :
      Chow.intersectionBilinForm k M.surface (a i) (a j) = (-2 : ℤ) * (if i = j then 1 else 0) +
        (if j = i + 1 then 1 else 0) + (if j = i - 1 then 1 else 0) := by
    rw [← hmark i, ← hmark j, ← M.picardMarking_apply, ← M.picardMarking_apply,
      M.intersectionBilinForm_picardMarking]
    exact M.intersectionForm_boundaryClass hD hnef hsq i j
  have hrange := QPainleve.BoundaryCycle.range_toIsometry_eq_cremonaIsometryGroup_of_cycle_gram
    k hD p (fun x ↦ by rw [funext hp, M.mem_range_boundaryPrime_iff])
    (inv_injective hcan) (hcan ▸ hnef) (hcan ▸ hsq) hgram hroot
  let e := SignedBoundaryIsometryGroup.congr
    (d₀ := d) (d₁ := a) M.marking.symm (ε := 1) (a := 0)
    (fun j ↦ by rw [one_smul, add_zero, ← hmark, BilinForm.IsometryEquiv.symm_apply_apply])
  have he (g : signedBoundaryIsometryGroup B d) :
      toIsometry _ a (e g) = M.marking.isometryGroupCongr (toIsometry B d g) := by
    rw [toIsometry_apply, coe_congr, toIsometry_apply]
    rfl
  rw [← hrange]
  ext g
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨e s, he s⟩
  · rintro ⟨s, rfl⟩
    exact ⟨e.symm s, by simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply] using (he (e.symm s)).symm⟩

/-- The signed marked Picard isometry acts on the surface by conjugating through the marking.
For a square-zero anticanonical boundary without internal `(-2)` curves the action preserves
the effective classes and the canonical class. -/
def cremonaPicardHom :
    letI : SmoothOfRelativeDimension 2 base := M.smooth
    letI : M.surface.IsProjectiveOver k := M.projective
    signedBoundaryIsometryGroup B d →* Cr := by
  let : SmoothOfRelativeDimension 2 base := M.smooth
  let : M.surface.IsProjectiveOver k := M.projective
  exact (MulEquiv.subgroupCongr (M.range_markedProjection hcan hnef hsq hroot)).toMonoidHom.comp
    (M.marking.isometryGroupCongr.toMonoidHom.comp (toIsometry B d)).rangeRestrict

/-- The projection evaluates by conjugating the underlying marked isometry. -/
@[simp]
theorem cremonaPicardHom_apply (g : signedBoundaryIsometryGroup B d) :
    letI : SmoothOfRelativeDimension 2 base := M.smooth
    letI : M.surface.IsProjectiveOver k := M.projective
    (M.cremonaPicardHom hcan hnef hsq hroot g).val =
      M.marking.isometryGroupCongr (toIsometry B d g) := by
  simp only [cremonaPicardHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.subgroupCongr_apply, MonoidHom.coe_rangeRestrict]

/-- Every Cremona isometry comes from a signed isometry of the marked boundary. -/
theorem cremonaPicardHom_surjective :
    letI : SmoothOfRelativeDimension 2 base := M.smooth
    letI : M.surface.IsProjectiveOver k := M.projective
    Function.Surjective (M.cremonaPicardHom hcan hnef hsq hroot) := by
  let : SmoothOfRelativeDimension 2 base := M.smooth
  let : M.surface.IsProjectiveOver k := M.projective
  exact (MulEquiv.subgroupCongr (M.range_markedProjection hcan hnef hsq hroot)).surjective.comp
    (MonoidHom.rangeRestrict_surjective _)

/-- For three or more components the Cremona projection determines the signed isometry. -/
def signedBoundaryIsometryEquivCremona (hn : 3 ≤ n) :
    letI : SmoothOfRelativeDimension 2 base := M.smooth
    letI : M.surface.IsProjectiveOver k := M.projective
    signedBoundaryIsometryGroup B d ≃* Cr := by
  let : SmoothOfRelativeDimension 2 base := M.smooth
  let : M.surface.IsProjectiveOver k := M.projective
  refine MulEquiv.ofBijective (M.cremonaPicardHom hcan hnef hsq hroot)
    ⟨fun g h hgh ↦ ?_, M.cremonaPicardHom_surjective hcan hnef hsq hroot⟩
  apply toIsometry_injective B d hn (M.boundaryClass_injective_of_nef_square_zero hD hnef hsq)
  apply M.marking.isometryGroupCongr.injective
  simpa only [M.cremonaPicardHom_apply] using congrArg Subtype.val hgh

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
  refine MulEquiv.ofBijective
    ((M.cremonaPicardHom hcan hnef hsq hroot).comp (rotationInclusion B d)) ⟨?_, ?_⟩
  · intro g h hgh
    apply Subtype.ext
    apply M.marking.isometryGroupCongr.injective
    simpa only [MonoidHom.comp_apply, M.cremonaPicardHom_apply, toIsometry_apply,
      coe_rotationInclusion] using congrArg Subtype.val hgh
  · intro g
    obtain ⟨s, rfl⟩ := M.cremonaPicardHom_surjective hcan hnef hsq hroot g
    let t := mulEquivProdOfLeTwo B d hn s
    refine ⟨t.1, Subtype.ext ?_⟩
    simp only [MonoidHom.comp_apply, M.cremonaPicardHom_apply, toIsometry_apply,
      coe_rotationInclusion]
    exact congrArg M.marking.isometryGroupCongr
      (congrArg Prod.fst (coe_mulEquivProdOfLeTwo_apply B d hn s))

/-- The rotation equivalence acts by the same marked Picard projection at sign one. -/
@[simp]
theorem boundaryRotationEquivCremona_apply (hn : n ≤ 2) (g : boundaryRotationGroup B d) :
    letI : SmoothOfRelativeDimension 2 base := M.smooth
    letI : M.surface.IsProjectiveOver k := M.projective
    M.boundaryRotationEquivCremona hcan hnef hsq hroot hn g =
      M.cremonaPicardHom hcan hnef hsq hroot (rotationInclusion B d g) :=
  (rfl)

/-- For one or two boundary components the signed group is the direct product of Cremona
isometries and the sign group. -/
def signedBoundaryIsometryEquivCremonaProd (hn : n ≤ 2) :
    letI : SmoothOfRelativeDimension 2 base := M.smooth
    letI : M.surface.IsProjectiveOver k := M.projective
    signedBoundaryIsometryGroup B d ≃* Cr × ℤˣ :=
  (mulEquivProdOfLeTwo B d hn).trans
    (MulEquiv.prodCongr (M.boundaryRotationEquivCremona hcan hnef hsq hroot hn) (MulEquiv.refl _))

/-- The two coordinates of the small-boundary equivalence are the Cremona projection and
the original sign. -/
@[simp]
theorem signedBoundaryIsometryEquivCremonaProd_apply (hn : n ≤ 2)
    (g : signedBoundaryIsometryGroup B d) :
    letI : SmoothOfRelativeDimension 2 base := M.smooth
    letI : M.surface.IsProjectiveOver k := M.projective
    M.signedBoundaryIsometryEquivCremonaProd hcan hnef hsq hroot hn g =
      (M.cremonaPicardHom hcan hnef hsq hroot g, sign B d g) := by
  let t := mulEquivProdOfLeTwo B d hn g
  have ht : (t.1.val, t.2) = g.val := coe_mulEquivProdOfLeTwo_apply B d hn g
  -- Reduce the application of `MulEquiv.prodCongr` to its two component maps.
  change (M.boundaryRotationEquivCremona hcan hnef hsq hroot hn t.1, t.2) = _
  rw [M.boundaryRotationEquivCremona_apply, SignedBoundaryIsometryGroup.sign_apply]
  have hsign : t.2 = g.val.2 := congrArg Prod.snd ht
  refine Prod.ext (Subtype.ext ?_) hsign
  simp only [M.cremonaPicardHom_apply, toIsometry_apply, coe_rotationInclusion]
  exact congrArg M.marking.isometryGroupCongr (congrArg Prod.fst ht)

end QPainleve.SignedClusterModularGroup.MarkedSurface
