/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Intersection
public import QPainleve.AlgebraicGeometry.Chow.Nef.Basic
import QPainleve.AlgebraicGeometry.Blowup.Tower.Contraction
import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.Chow.BoundaryMultiplicity
import QPainleve.AlgebraicGeometry.Chow.Isomorphism
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Dimension
import QPainleve.AlgebraicGeometry.IdealSheaf.Stalk
import QPainleve.AlgebraicGeometry.IntersectionNumber.Nef.Pullback
import QPainleve.AlgebraicGeometry.Morphisms.Modification.IsoLocus
import QPainleve.AlgebraicGeometry.Morphisms.Smooth.Factorial
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme

/-!
# Total transforms of nef divisors of square zero

Pullback along a closed-point blowup tower preserves the intersection pairing.
Consequently, a nef effective Cartier divisor of square zero has zero intersection
with each prime divisor in its total transform. This applies to nodal boundary
towers, with the exceptional components included in the support.

For a nonempty reduced divisor, a strict-transform component has multiplicity one.
This normalizes the total transform of a connected nef divisor of square zero, so
its support determines it among total transforms of such divisors.

The comparison uses the established Picard marking of a point-blowup tower and
the projection formula for degrees. See also the intersection calculation in
[Stacks Project, Section 55.12](https://stacks.math.columbia.edu/tag/0CEF).
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open LineBundleClass Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {X Y : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y}
  {k : Type u} [Field k] [IsIntegral X]

open Order in
/-- The total transform of a nonempty reduced effective Cartier divisor has a
prime component of multiplicity one. -/
theorem exists_coeff_totalTransform_eq_one [PerfectField k] [IsNoetherian X]
    (hT : IsClosedPointTower X T) (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 f]
    {D : X.IdealSheafData} [IsReduced D.subscheme] (hD : D.IsEffectiveCartier)
    (hne : (D.support : Set X).Nonempty) :
    let := T.isNoetherian
    let := hT.isIntegral f
    ∃ q : CodimensionOnePoint Y,
      (hT.isEffectiveCartier_totalTransform f hD).toCartierDivisor.toWeilDivisor q = 1 := by
  intro _ _
  obtain ⟨x, hx⟩ := hne
  obtain ⟨p, hp, -⟩ := hD.mem_support_iff_exists_codimensionOnePoint.mp hx
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  have : IsRegular X := IsRegular.of_smooth f
  have : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two f
  have hpIso := T.toBase.mem_isoLocus_of_coheight_eq_one p.property
  obtain ⟨y, hy⟩ := T.toBase.surjective (p : X)
  have hyIso : T.toBase y ∈ T.toBase.isoLocus := hy.symm ▸ hpIso
  let q : CodimensionOnePoint Y :=
    ⟨y, (T.toBase.coheight_eq_of_apply_mem_isoLocus hyIso).symm.trans
      ((congrArg coheight hy).trans p.property)⟩
  have : Smooth (T.toBase ≫ f) := (hT.smoothOfRelativeDimension f).smooth 2 _
  have : IsRegular Y := IsRegular.of_smooth (T.toBase ≫ f)
  have := IsNormalScheme.isDiscreteValuationRing_stalk (q : Y) q.property
  have := IsNormalScheme.isDiscreteValuationRing_stalk (p : X) p.property
  have := T.toBase.isIso_stalkMap_of_mem_isoLocus hyIso
  have hpOrder : D.stalkOrder (p : X) = 1 :=
    le_antisymm (hD.stalkOrder_le_one_of_isReduced _) ((D.one_le_stalkOrder_iff _).mpr hp)
  use q
  rw [← WeilDivisor.coeff,
    (hT.isEffectiveCartier_totalTransform f hD).coeff_toWeilDivisor_eq_stalkOrder,
    D.stalkOrder_comap_of_isIso_stalkMap, hy, hpOrder]
  rfl

section Nef

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

/-- Two total transforms identified by an isomorphism of the top models are equal
if their supports agree, the original divisors are reduced, nef and of square zero,
and the first has connected support. -/
theorem totalTransform_eq_of_nef_square_zero {X' W : Scheme.{u}}
    [IsIntegral X'] [X'.Over (Spec (.of k))] [X'.IsProjectiveOver k]
    [SmoothOfRelativeDimension 2 (X' ↘ Spec (.of k))]
    {m : ℕ} {U : BlowupTower X' m W} (hT : IsClosedPointTower X T)
    (hU : IsClosedPointTower X' U) (e : Y ≅ W)
    (hover : T.toBase ≫ (X ↘ Spec (.of k)) = e.hom ≫ U.toBase ≫ (X' ↘ Spec (.of k)))
    {D : X.IdealSheafData} {E : X'.IdealSheafData}
    [IsReduced D.subscheme] [IsReduced E.subscheme]
    (hD : D.IsEffectiveCartier) (hE : E.IsEffectiveCartier)
    (hconn : _root_.IsConnected (D.support : Set X))
    (hsupp : (D.comap T.toBase).support = ((E.comap U.toBase).comap e.hom).support)
    (hnefD : IsNef k (X ↘ Spec (.of k)) (mk hD.toInvertibleSheaf)⁻¹)
    (hnefE : IsNef k (X' ↘ Spec (.of k)) (mk hE.toInvertibleSheaf)⁻¹)
    (hsqD : Chow.classIntersectionNumber k X (mk hD.toInvertibleSheaf)⁻¹
      (mk hD.toInvertibleSheaf)⁻¹ = 0)
    (hsqE : Chow.classIntersectionNumber k X' (mk hE.toInvertibleSheaf)⁻¹
      (mk hE.toInvertibleSheaf)⁻¹ = 0) :
    D.comap T.toBase = (E.comap U.toBase).comap e.hom := by
  let f := X ↘ Spec (.of k)
  let g := X' ↘ Spec (.of k)
  let : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ f⟩
  let : W.Over (Spec (.of k)) := ⟨U.toBase ≫ g⟩
  have : e.hom.IsOver (Spec (.of k)) := ⟨hover.symm⟩
  have : IsNoetherian X := isNoetherian_of_finiteType f
  have : IsNoetherian X' := isNoetherian_of_finiteType g
  have : IsNoetherian Y := T.isNoetherian
  have : IsNoetherian W := U.isNoetherian
  have : IsIntegral Y := hT.isIntegral f
  have : IsIntegral W := hU.isIntegral g
  have : Y.IsProjectiveOver k := T.isProjectiveOver k
  have : W.IsProjectiveOver k := U.isProjectiveOver k
  have : SmoothOfRelativeDimension 2 (T.toBase ≫ f) := hT.smoothOfRelativeDimension f
  have : Smooth (T.toBase ≫ f) := (hT.smoothOfRelativeDimension f).smooth 2 _
  have : Smooth (U.toBase ≫ g) := (hU.smoothOfRelativeDimension g).smooth 2 _
  have : IsRegular Y := IsRegular.of_smooth (T.toBase ≫ f)
  have : IsRegular W := IsRegular.of_smooth (U.toBase ≫ g)
  have : T.toBase.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : U.toBase.IsOver (Spec (.of k)) := ⟨rfl⟩
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension (T.toBase ≫ f) (n := 2)
  have (y : Y) : UniqueFactorizationMonoid (Y.presheaf.stalk y) :=
    (T.toBase ≫ f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two y
  have hDT := hT.isEffectiveCartier_totalTransform f hD
  have hEU := hU.isEffectiveCartier_totalTransform g hE
  have hEU' := hEU.comap_of_isDominant e.hom
  have hconnT : _root_.IsConnected ((D.comap T.toBase).support : Set Y) := by
    rw [support_comap, Closeds.coe_preimage]
    exact hT.isConnected_preimage_of_isClosed f D.support.isClosed hconn
  have hneE : (E.support : Set X').Nonempty := by
    obtain ⟨q, hq⟩ := hconnT.nonempty
    exact ⟨U.toBase (e.hom q),
      by simpa only [hsupp, support_comap, Closeds.coe_preimage, Set.mem_preimage] using hq⟩
  obtain ⟨p, hp⟩ := hT.exists_coeff_totalTransform_eq_one f hD hconn.nonempty
  obtain ⟨q, hq⟩ := hU.exists_coeff_totalTransform_eq_one g hE hneE
  let q' := q.mapOfIsOpenImmersion e.inv
  have hqmap : q'.mapOfIsOpenImmersion e.hom = q := Subtype.ext (by simp [q'])
  have hq' := (hEU.coeff_toWeilDivisor_comap_of_isOpenImmersion e.hom hEU' q').trans
    (hqmap.symm ▸ hq)
  have hclD : pullback T.toBase (mk hD.toInvertibleSheaf)⁻¹ = (mk hDT.toInvertibleSheaf)⁻¹ := by
    rw [pullback_inv, hD.pullback_mk_toInvertibleSheaf hDT]
  have hclE : pullback U.toBase (mk hE.toInvertibleSheaf)⁻¹ = (mk hEU.toInvertibleSheaf)⁻¹ := by
    rw [pullback_inv, hE.pullback_mk_toInvertibleSheaf hEU]
  have hclE' : pullback e.hom (mk hEU.toInvertibleSheaf)⁻¹ = (mk hEU'.toInvertibleSheaf)⁻¹ := by
    rw [pullback_inv, hEU.pullback_mk_toInvertibleSheaf hEU']
  refine Chow.eq_of_nef_square_zero_of_support_eq k hdim hDT hEU' hsupp hconnT.isPreconnected
    (hclD ▸ hnefD.pullback T.toBase) (hclE' ▸ (hclE ▸ hnefE.pullback U.toBase).pullback e.hom)
    ?_ ?_ hp hq'
  · rw [← hclD, hT.classIntersectionNumber_pullback k, hsqD]
  · rw [← hclE', Chow.classIntersectionNumber_pullback_of_isIso k, ← hclE,
      hU.classIntersectionNumber_pullback k, hsqE]

end Nef

end QPainleve.BlowupTower.IsClosedPointTower
