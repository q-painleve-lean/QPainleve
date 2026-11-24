/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Contraction
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

import QPainleve.AlgebraicGeometry.Blowup.Integral
import QPainleve.AlgebraicGeometry.Blowup.Intersection
import QPainleve.AlgebraicGeometry.Blowup.Projective.Global
import QPainleve.AlgebraicGeometry.Chow.ProperIntersection
import QPainleve.AlgebraicGeometry.Curves.Node.Intersection
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Integral
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.IdealSheaf.Stalk
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct

/-!
# Exceptional attachments under anticanonical blowdown

When the reduced union of a strict transform and the exceptional curve is nodal,
the attachment points are transverse. Their number equals the multiplicity at the
center. Consequently, an exceptional component of a nodal anticanonical boundary
meets its residual boundary in two distinct reduced points.

This is the attachment calculation for the corner contractions in
[Gross, Hacking and Keel, *Mirror symmetry for log Calabi–Yau surfaces I*,
Proposition 1.3](https://arxiv.org/html/1106.4977v3#S1.Thmproposition3).
-/

public section

open CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open Chow LineBundleClass

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} {p : X} (k : Type u) [Field k] [IsAlgClosed k]
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "I" => vanishingIdeal (Closeds.mk (closure (singleton p)) isClosed_closure)
local notation "π" => blowupToBase I
local notation "E" => comap I π
local notation "strict(" D ")" => Scheme.Hom.ker (blowupMap I (subschemeι D))
local notation "S" => Spec (CommRingCat.of k)
local notation "s" => (X ↘ S)

/-- If the strict transform together with the exceptional curve is nodal, its
scheme-theoretic intersection with the exceptional curve is reduced and the number
of attachment points is the stalk order of the divisor at the center. -/
theorem IsEffectiveCartier.ncard_strictTransform_inter_exceptional_of_nodal
    {D : X.IdealSheafData} (hD : D.IsEffectiveCartier) (hp : IsClosed ({p} : Set X))
    (hnodal : AtWorstNodalOfRelativeDimensionOne ((strict(D) * E).subschemeι ≫ π ≫ s)) :
    let J := strict(D) ⊔ E
    IsReduced J.subscheme ∧ (J.support : Set (I).blowup).ncard = (D.stalkOrder p).toNat ∧
      ∀ x ∈ J.support, J.stalkIdeal x = IsLocalRing.maximalIdeal ((I).blowup.presheaf.stalk x) := by
  let : (I).blowup.Over S := ⟨π ≫ s⟩
  have : Smooth s := SmoothOfRelativeDimension.smooth 2 _
  have : IsNoetherian X := isNoetherian_of_finiteType s
  have := isRegularLocalRing_stalk_of_smooth s p
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq s 2).mp inferInstance).2 p hp
  have : SmoothOfRelativeDimension 2 ((I).blowup ↘ S) :=
    smoothOfRelativeDimension_blowup_closed_point s hp
  have : (I).blowup.IsProjectiveOver k := (I).isProjectiveOver_blowup_of_isNoetherianRing k
  have : IsIntegral (I).blowup := isIntegral_blowup_closed_point s hp
  let hE := (I).isEffectiveCartier_comap_blowupToBase
  have : IsIntegral (E).subscheme := isIntegral_exceptional_blowup_closed_point hdim hp
  have : IsLocallyNoetherian (I).blowup := LocallyOfFiniteType.isLocallyNoetherian π
  let hS := hD.strictTransform_pointBlowup hp hdim
  have htotal : (D.comap π).IsEffectiveCartier := by
    rw [hD.totalTransform_eq_strictTransform_mul_pow_closedPoint hp hdim]
    exact TauCeti.isEffectiveCartier_mul hS (TauCeti.isEffectiveCartier_pow hE _)
  obtain ⟨_, -, homit⟩ := hD.exists_strictTransform_cartierDivisor hp hdim htotal
  have hη := (E).range_subschemeι.le (Set.mem_range_self (genericPoint (E).subscheme))
  have hSE := hS.comap_of_isIntegral (E).subschemeι
    (homit ⟨_, hE.coheight_subschemeι_genericPoint⟩ hη)
  have htrans (x : (I).blowup) (hx : x ∈ (strict(D) ⊔ E).support) :
      (strict(D) ⊔ E).stalkIdeal x = IsLocalRing.maximalIdeal ((I).blowup.presheaf.stalk x) := by
    rw [stalkIdeal_sup]
    exact hS.stalkIdeal_sup_eq_maximalIdeal_of_nodal_mul hE hnodal hx
  have hdimY := topologicalKrullDim_eq_of_smoothOfRelativeDimension ((I).blowup ↘ S) (n := 2)
  have hcount := classIntersectionNumber_eq_ncard_of_stalkIdeal_sup_eq_maximalIdeal k
    hdimY.le hS hE hSE (fun x hx ↦ (stalkIdeal_sup _ _ _).symm.trans (htrans x hx))
  rw [hD.toLineBundleClass_strictTransform_pointBlowup hp hdim] at hcount
  -- The center ideal in the intersection formula is the kernel of the residue-field point.
  let m := (D.stalkOrder p).toNat
  let a := (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹
  let pairingFormula (J : X.IdealSheafData) : Prop :=
    let : J.blowup.Over S := ⟨J.blowupToBase ≫ s⟩
    classIntersectionNumber k J.blowup
      (pullback J.blowupToBase a * J.blowupExceptionalClass⁻¹ ^ m)
      J.blowupExceptionalClass = m
  let center := (X.fromSpecResidueField p).ker
  have hpair : pairingFormula center := by
    let : center.blowup.Over S := ⟨center.blowupToBase ≫ s⟩
    have hproj := center.isProjectiveOver_blowup_of_isNoetherianRing k
    simpa only [pairingFormula, blowupExceptionalClass_def, pullback_one, one_mul, zpow_one,
      zpow_neg, zpow_natCast, inv_pow, classIntersectionNumber_one_right, mul_one,
      zero_sub, neg_neg]
      using classIntersectionNumber_pointBlowup p k hp a 1 (-(m : ℤ)) 1 hproj
  have hnum := (congrArg pairingFormula (X.ker_fromSpecResidueField_eq_vanishingIdeal p)).mp hpair
  rw [← blowupExceptionalClass_def] at hcount
  exact ⟨(strict(D) ⊔ E).isReduced_subscheme_of_stalkIdeal_eq_maximalIdeal htrans,
    Int.natCast_inj.mp (hcount.symm.trans hnum), htrans⟩

/-- If a nodal anticanonical boundary contains the exceptional curve of a closed-point
blowup, the strict transform of its schematic image meets that curve in two reduced
points. At each point the strict-transform and exceptional ideals generate the ambient
maximal ideal. -/
theorem IsEffectiveCartier.exceptional_attachments_of_anticanonical_boundary
    (hp : IsClosed ({p} : Set X)) {B : (I).blowup.IdealSheafData} (hB : B.IsEffectiveCartier)
    (hE : (E).support ≤ B.support)
    (hnodal : AtWorstNodalOfRelativeDimensionOne (B.subschemeι ≫ π ≫ s)) :
    let : (I).blowup.Over S := ⟨π ≫ s⟩
    let : SmoothOfRelativeDimension 2 ((I).blowup ↘ S) :=
      smoothOfRelativeDimension_blowup_closed_point s hp
    LineBundleClass.mk hB.toInvertibleSheaf =
      LineBundleClass.mk (QPainleve.canonicalBundle k (I).blowup 2) →
    let D := B.map π
    let J := strict(D) ⊔ E
    IsReduced J.subscheme ∧ (J.support : Set (I).blowup).ncard = 2 ∧
      ∀ x ∈ J.support, J.stalkIdeal x = IsLocalRing.maximalIdeal ((I).blowup.presheaf.stalk x) := by
  intro _ _ hcan D J
  have : IsNoetherian X := isNoetherian_of_finiteType s
  have : IsReduced B.subscheme := hnodal.isReduced
  obtain ⟨hD, -, -, -, hcases⟩ := hB.anticanonical_boundary_point_blowdown k hp hcan
  obtain ⟨hm, -, hstrict⟩ := hcases.resolve_left (fun h ↦ h.2.1 hE)
  have hnodal' : AtWorstNodalOfRelativeDimensionOne ((strict(D) * E).subschemeι ≫ π ≫ s) :=
    hstrict.symm ▸ hnodal
  simpa only [hm, ENat.toNat_ofNat] using hD.ncard_strictTransform_inter_exceptional_of_nodal k hp
    hnodal'

end AlgebraicGeometry.Scheme.IdealSheafData
