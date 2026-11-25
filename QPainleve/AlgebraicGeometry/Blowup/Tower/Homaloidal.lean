/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.MovingBaseIdeal
public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.Basic
public import QPainleve.AlgebraicGeometry.Chow.Birational
public import QPainleve.AlgebraicGeometry.Chow.ProjectivePlane.Numerical
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.SymmetricAlgebra
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections.Resolution

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

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Scheme.IdealSheafData.IsEffectiveCartier (toInvertibleSheaf)
open TauCeti.AlgebraicGeometry LineBundleClass Chow TauCeti.SymmetricAlgebra

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {n : ℕ}
  {T : BlowupTower X n Y} [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "S" => Spec (CommRingCat.of k)
local notation "f" => (X ↘ S)
local notation "P" => Proj (homogeneousSubmodule k (Fin 3 → k))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle k (Fin 3 → k) 1)
local notation "B(" Z ")" => classIntersectionNumber k Z
local notation "K(" Z ")" => mk (canonicalBundle k Z 2)

section MovingPresentation

variable [PerfectField k]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The given resolution principalizes the moving base ideal. Its resolved hyperplane
class has base coordinate the presenting line bundle. Its exceptional coordinates
are the negatives of the successive base multiplicities. -/
theorem picardMarking_symm_pullback_hyperplane_of_baseIdeal (hT : IsClosedPointTower X T)
    (L : InvertibleSheaf X) (s : Fin 3 → Γ(L.obj, ⊤))
    (i : Fin 3) (hi : Dense (L.obj.nonvanishingLocus (s i) : Set X))
    (g : Y ⟶ P) (hg : g ≫ (P ↘ S) = T.toBase ≫ f)
    (hrep :
      let : IsNoetherian X := isNoetherian_of_finiteType f
      let : IsIntegral Y := hT.isIntegral f
      let b : Module.Basis (ULift.{u} (Fin 3)) k (Fin 3 → k) :=
        (Pi.basisFun k (Fin 3)).reindex Equiv.ulift.symm
      let : Surjective T.toBase := hT.surjective f
      (g ≫ b.polynomialProjIso.inv).toRationalMap = T.toBase.toRationalMap.comp
        (L.obj.partialMapToProjectiveSpace f (s ∘ ULift.down) (ULift.up i) hi).toRationalMap)
    (hmove : ∀ p : CodimensionOnePoint X, (p : X) ∉ (⨆ j, L.zeroIdeal (s j)).support) :
    let : IsNoetherian X := isNoetherian_of_finiteType f
    ((⨆ j, L.zeroIdeal (s j)).comap T.toBase).IsEffectiveCartier ∧
      (T.picardMarking hT f).symm (Additive.ofMul (pullback g H)) =
        (Additive.ofMul (mk L),
          fun j ↦ -(hT.baseMultiplicities (⨆ l, L.zeroIdeal (s l)) j : ℤ)) := by
  let : IsNoetherian X := isNoetherian_of_finiteType f
  have : IsIntegral Y := hT.isIntegral f
  have : Surjective T.toBase := hT.surjective f
  -- The presentation API puts the coordinate indices in the same universe as the schemes.
  let b : Module.Basis (ULift.{u} (Fin 3)) k (Fin 3 → k) :=
    (Pi.basisFun k (Fin 3)).reindex Equiv.ulift.symm
  let 𝒜 := MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 3)) k
  have hover : (g ≫ b.polynomialProjIso.inv) ≫ Proj.toSpecCoeff 𝒜 = T.toBase ≫ f := by
    rw [Category.assoc, ← b.polynomialProjIso_hom_over,
      Iso.inv_hom_id_assoc]
    exact hg
  obtain ⟨hI, hclass⟩ := L.pullback_twistingSheafOne_eq_of_resolving f
    (s ∘ ULift.down) (ULift.up i) hi T.toBase (g ≫ b.polynomialProjIso.inv) hover hrep
  have hbase : (⨆ j : ULift.{u} (Fin 3), L.zeroIdeal (s j.down)) = ⨆ j, L.zeroIdeal (s j) := by
    rw [iSup_ulift]
  have hJ : ((⨆ j, L.zeroIdeal (s j)).comap T.toBase).IsEffectiveCartier :=
    hbase ▸ hI
  have hJclass := mk_toInvertibleSheaf_congr hI hJ
    (congrArg (fun J : X.IdealSheafData ↦ J.comap T.toBase) hbase)
  let L₁ : InvertibleSheaf (Proj 𝒜) := ⟨Proj.twistingSheaf 𝒜 1, inferInstance⟩
  have he : pullback b.polynomialProjIso.hom H = mk L₁ := by
    rw [pullback_mk, mk_eq_mk_iff, InvertibleSheaf.pullback_obj_obj,
      Proj.symmetricAlgebraTwistingBundle_obj]
    exact ⟨b.polynomialProjIsoPullbackTwistingSheafIso 1⟩
  rw [hJclass, ← he, pullback_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id] at hclass
  have hm := hT.picardHom_movingBaseIdeal f hmove hJ (mk L)
  refine ⟨hJ, (LinearEquiv.symm_apply_eq _).mpr ?_⟩
  apply Additive.toMul.injective
  rw [picardMarking_apply, hm]
  exact hclass

end MovingPresentation

variable [IsAlgClosed k]

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
  have hcanon := hT.classIntersectionNumber_picardHom_canonicalBundle k v
  dsimp only at hsq hcanon
  rw [hv, g.classIntersectionNumber_pullback_of_birational hbir,
    classIntersectionNumber_projectivePlane, Module.Basis.picardTwistEquiv_apply_twist] at hsq
  rw [← picardMarking_apply T hT f, hv] at hcanon
  have hproj := g.classIntersectionNumber_pullback_canonicalBundle_of_birational (k := k) hbir H
  rw [classIntersectionNumber_projectivePlane, mk_canonicalBundle_projectivePlane,
    Module.Basis.picardTwistEquiv_apply_twist, Module.Basis.picardTwistEquiv_apply_twist] at hproj
  have hdegree := hproj.symm.trans hcanon
  simp only [← pow_two] at hsq
  simp only [one_mul] at hdegree
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

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The homaloidal identities for the successive base multiplicities of a projective
section presentation without a fixed divisor. The given birational morphism resolves
the specified presentation. The formulas use the common order of the whole linear
system at each center, including infinitely near centers. -/
theorem homaloidal_intersection_identities_baseIdeal (hT : IsClosedPointTower X T)
    (L : InvertibleSheaf X) (s : Fin 3 → Γ(L.obj, ⊤))
    (i : Fin 3) (hi : Dense (L.obj.nonvanishingLocus (s i) : Set X))
    (g : Y ⟶ P) (hg : g ≫ (P ↘ S) = T.toBase ≫ f)
    (hbir : Scheme.BirationalOver g (𝟙 P))
    (hrep :
      let : IsNoetherian X := isNoetherian_of_finiteType f
      let : IsIntegral Y := hT.isIntegral f
      let b : Module.Basis (ULift.{u} (Fin 3)) k (Fin 3 → k) :=
        (Pi.basisFun k (Fin 3)).reindex Equiv.ulift.symm
      let : Surjective T.toBase := hT.surjective f
      (g ≫ b.polynomialProjIso.inv).toRationalMap = T.toBase.toRationalMap.comp
        (L.obj.partialMapToProjectiveSpace f (s ∘ ULift.down) (ULift.up i) hi).toRationalMap)
    (hmove : ∀ p : CodimensionOnePoint X, (p : X) ∉ (⨆ j, L.zeroIdeal (s j)).support) :
    let m := hT.baseMultiplicities (⨆ j, L.zeroIdeal (s j))
    (∑ j, (m j : ℤ) ^ 2) = B(X) (mk L) (mk L) - 1 ∧
      (∑ j, (m j : ℤ)) = -B(X) (mk L) K(X) - 3 := by
  have hv := (hT.picardMarking_symm_pullback_hyperplane_of_baseIdeal L s i hi g hg hrep hmove).2
  have h := hT.homaloidal_intersection_identities g hg hbir
  dsimp only at h
  rw [hv] at h
  simpa only [neg_sq, neg_neg, toMul_ofMul] using h

end QPainleve.BlowupTower.IsClosedPointTower
