/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Intersection
public import QPainleve.AlgebraicGeometry.Chow.Nef
import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.IntersectionNumber.Nef.Pullback
import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme

/-!
# Orthogonality of a nef square-zero total transform

Pullback along a closed-point blowup tower preserves the intersection pairing.
Consequently, a nef effective Cartier divisor of square zero has zero intersection
with each prime divisor in its total transform. This applies to nodal boundary
towers, with the exceptional components included in the support.

The comparison uses the established Picard marking of a point-blowup tower and
the projection formula for degrees. See also the intersection calculation in
[Stacks Project, Section 55.12](https://stacks.math.columbia.edu/tag/0CEF).
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry
open LineBundleClass Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {X Y : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y}
  {k : Type u} [Field k] [IsIntegral X]

variable (k) [IsAlgClosed k] [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

/-- The total transform of a nef effective Cartier divisor of square zero has zero
intersection with every effective Cartier divisor supported on the total transform.
This includes each strict-transform and exceptional component of the total transform,
as well as a second total transform with the same support. -/
theorem classIntersectionNumber_totalTransform_eq_zero (hT : IsClosedPointTower X T)
    {D : X.IdealSheafData} (hD : D.IsEffectiveCartier)
    (hnef : IsNef k (X ↘ Spec (.of k)) (mk hD.toInvertibleSheaf)⁻¹)
    (hsq : Chow.classIntersectionNumber k X (mk hD.toInvertibleSheaf)⁻¹
      (mk hD.toInvertibleSheaf)⁻¹ = 0) {E : Y.IdealSheafData} (hE : E.IsEffectiveCartier)
    (hsub : E.support ≤ (D.comap T.toBase).support) :
    let : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ X ↘ Spec (.of k)⟩
    Chow.classIntersectionNumber k Y (pullback T.toBase (mk hD.toInvertibleSheaf)⁻¹)
      (mk hE.toInvertibleSheaf)⁻¹ = 0 := by
  dsimp only
  let f := X ↘ Spec (.of k)
  let : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ f⟩
  have : SmoothOfRelativeDimension 2 (T.toBase ≫ f) := hT.smoothOfRelativeDimension f
  have : Smooth (T.toBase ≫ f) := SmoothOfRelativeDimension.smooth 2 _
  have : IsNoetherian X := isNoetherian_of_finiteType f
  have : IsNoetherian Y := T.isNoetherian
  have : IsIntegral Y := hT.isIntegral f
  have : IsRegular Y := IsRegular.of_smooth (T.toBase ≫ f)
  have : Y.IsProjectiveOver k := T.isProjectiveOver k
  have : T.toBase.IsOver (Spec (.of k)) := ⟨rfl⟩
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension (T.toBase ≫ f) (n := 2)
  have htotal := hT.isEffectiveCartier_totalTransform f hD
  have (y : Y) : UniqueFactorizationMonoid (Y.presheaf.stalk y) :=
    IsRegular.uniqueFactorizationMonoid_stalk y (by
      exact WithBot.coe_le_coe.mp ((TauCeti.coheight_le_topologicalKrullDim y).trans_eq hdim))
  have hclass :
      (Scheme.CartierDivisor.weilToLineBundleClassHom Y
        htotal.toCartierDivisor.toWeilDivisor).toMul =
        pullback T.toBase (mk hD.toInvertibleSheaf)⁻¹ := by
    rw [Scheme.CartierDivisor.weilToLineBundleClassHom_toWeilDivisor, toMul_ofMul,
      IsEffectiveCartier.toLineBundleClass_toCartierDivisor, pullback_inv,
      hD.pullback_mk_toInvertibleSheaf htotal]
  have hnonneg := (Scheme.CartierDivisor.isEffective_iff_toWeilDivisor_nonneg _).mp
    htotal.isEffective_toCartierDivisor
  have hnef' := hclass.symm ▸ hnef.pullback T.toBase
  have horth := (Chow.classIntersectionNumber_weilToLineBundleClassHom_self_eq_zero_iff
    k hdim hnonneg hnef').mp (by rw [hclass, hT.classIntersectionNumber_pullback k, hsq])
  have hEclass := congrArg Additive.toMul
    (Scheme.CartierDivisor.weilToLineBundleClassHom_toWeilDivisor hE.toCartierDivisor)
  simp only [toMul_ofMul, IsEffectiveCartier.toLineBundleClass_toCartierDivisor] at hEclass
  rw [← hEclass, Chow.classIntersectionNumber_weilToLineBundleClassHom k hdim]
  apply Finset.sum_eq_zero
  intro p hp
  have hpE : (p : Y) ∈ E.support := by
    by_contra hnot
    exact (Finsupp.mem_support_iff.mp hp) ((hE.coeff_toWeilDivisor_eq_zero_iff p).mpr hnot)
  have hpTotal : p ∈ htotal.toCartierDivisor.toWeilDivisor.support :=
    Finsupp.mem_support_iff.mpr fun hzero ↦
      (htotal.coeff_toWeilDivisor_eq_zero_iff p).mp hzero (hsub hpE)
  simp only [← hclass, horth p hpTotal, mul_zero]

end QPainleve.BlowupTower.IsClosedPointTower
