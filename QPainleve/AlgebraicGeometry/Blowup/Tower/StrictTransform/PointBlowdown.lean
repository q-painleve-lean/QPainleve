/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.Basic
public import QPainleve.AlgebraicGeometry.Chow.SurfaceIntersection

import QPainleve.AlgebraicGeometry.Blowup.Intersection

/-!
# Picard classes of primes under point blowdown

In the Picard group upstairs, the pullback of an image prime is the strict
transform plus its intersection with the exceptional curve times the
exceptional class. Equivalently, pullback projects the strict transform class
onto the orthogonal complement of the exceptional curve.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
local notation "S(" k ")" => Spec (CommRingCat.of k)
local notation "g[" k "," X "]" => (X ↘ S(k))
local notation "I[" p "]" => Scheme.Hom.ker (Scheme.fromSpecResidueField _ p)
local notation "P[" q "]" => vanishingIdeal (Closeds.mk (closure {(q : _)}) isClosed_closure)
local notation "B[" k "," X "]" => Chow.intersectionBilinForm k X

variable [X.Over S(k)] [Y.Over S(k)] [IsIntegral X] [IsIntegral Y]
  [Y.IsProjectiveOver k] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 g[k,X]] [SmoothOfRelativeDimension 2 g[k,Y]]

omit [IsIntegral X] [X.IsProjectiveOver k] [SmoothOfRelativeDimension 2 g[k,X]] in
/-- The image of Picard pullback along a point blowdown is the lattice of classes
orthogonal to the exceptional curve. -/
theorem mem_range_pullback_iff_classIntersectionNumber_eq_zero_of_pointBlowdown
    (f : X ⟶ Y) [f.IsOver S(k)] {p : Y} (hp : IsClosed ({p} : Set Y))
    (e : X ≅ (I[p]).blowup) (he : e.hom ≫ (I[p]).blowupToBase = f)
    {E : X.IdealSheafData} (hE : E.IsEffectiveCartier) (hF : (I[p]).comap f = E)
    (L : LineBundleClass X) :
    L ∈ Set.range (pullback f) ↔
      Chow.classIntersectionNumber k X L (LineBundleClass.mk hE.toInvertibleSheaf)⁻¹ = 0 := by
  let c := (LineBundleClass.mk hE.toInvertibleSheaf)⁻¹
  have hpair (a : LineBundleClass Y) (m : ℤ) :
      Chow.classIntersectionNumber k X (pullback f a * c ^ m) c = -m := by
    simpa only [c, zpow_one, pullback_one, one_mul, Chow.classIntersectionNumber_one_right,
      mul_one, zero_sub] using
      f.classIntersectionNumber_pointBlowdown (k := k) hp e he hE hF a 1 m 1
  constructor
  · rintro ⟨a, rfl⟩
    simpa only [zpow_zero, mul_one, neg_zero, c] using hpair a 0
  · intro hL
    let : IsNoetherian Y := isNoetherian_of_finiteType g[k,Y]
    let T := BlowupTower.nil.snoc (I[p])
    let hT : IsClosedPointTower Y T := .snoc .nil p hp rfl
    obtain ⟨⟨a, b⟩, hab⟩ := (hT.bijective_picardHom g[k,Y]).surjective
      (Additive.ofMul (pullback e.inv L))
    have hclass : pullback e.hom (I[p]).blowupExceptionalClass = c :=
      (I[p]).pullback_blowupExceptionalClass_of_comap_eq e.hom hE (by rw [← comap_comp, he, hF])
    have h := congrArg Additive.toMul hab
    dsimp only [T] at h
    rw [picardHom_snoc_apply_toMul, picardHom_nil, toMul_ofMul] at h
    have hcoord : pullback f a.toMul * c ^ b (Fin.last 0) = L := by
      simpa only [pullback_mul, pullback_zpow, pullback_comp, he, hclass, Iso.hom_inv_id,
        pullback_id] using congrArg (pullback e.hom) h
    have hzero := hpair a.toMul (b (Fin.last 0))
    rw [hcoord, hL] at hzero
    refine ⟨a.toMul, ?_⟩
    simpa only [neg_eq_zero.mp hzero.symm, zpow_zero, mul_one] using hcoord

/-- A strict transform and its image prime have Picard classes related by
orthogonal projection away from the prime exceptional curve. -/
theorem pullback_primeDivisorClass_pointBlowdown (f : X ⟶ Y) [f.IsOver S(k)]
    {p : Y} (hp : IsClosed ({p} : Set Y)) (e : X ≅ (I[p]).blowup)
    (he : e.hom ≫ (I[p]).blowupToBase = f)
    (z q : CodimensionOnePoint X) (r : CodimensionOnePoint Y)
    (hz : (I[p]).comap f = P[z.val]) (hqr : f q = r) :
    letI := isNoetherian_of_finiteType g[k,X]
    letI := isNoetherian_of_finiteType g[k,Y]
    letI := g[k,X].uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    letI := g[k,Y].uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let a := Additive.ofMul (primeDivisorClass q)
    let c := Additive.ofMul (primeDivisorClass z)
    Additive.ofMul (pullback f (primeDivisorClass r)) = a + B[k,X] a c • c := by
  let : IsNoetherian X := isNoetherian_of_finiteType g[k,X]
  let : IsNoetherian Y := isNoetherian_of_finiteType g[k,Y]
  let := g[k,X].uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let := g[k,Y].uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let I := I[p]
  let T := BlowupTower.nil.snoc I
  let hT : IsClosedPointTower Y T := .snoc .nil p hp rfl
  let : I.blowup.Over S(k) := ⟨I.blowupToBase ≫ g[k,Y]⟩
  let : IsIntegral I.blowup := hT.isIntegral g[k,Y]
  let : IsLocallyNoetherian I.blowup := LocallyOfFiniteType.isLocallyNoetherian I.blowupToBase
  let : SmoothOfRelativeDimension 2 g[k,I.blowup] := by
    have hg : g[k,I.blowup] = I.blowupToBase ≫ g[k,Y] := rfl
    rw [hg]
    simpa only [T, toBase_snoc, toBase_nil, Category.comp_id] using
      hT.smoothOfRelativeDimension g[k,Y]
  let := g[k,I.blowup].uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let q' := q.mapOfIsOpenImmersion e.hom
  have hq' : I.blowupToBase q' = r := by
    rw [CodimensionOnePoint.coe_mapOfIsOpenImmersion, ← Scheme.Hom.comp_apply, he, hqr]
  have hE : P[z.val].IsEffectiveCartier :=
    isEffectiveCartier_vanishingIdeal_closure_singleton z.property
  have hclass : pullback e.hom (I[p]).blowupExceptionalClass = primeDivisorClass z := by
    rw [primeDivisorClass_def]
    exact I.pullback_blowupExceptionalClass_of_comap_eq e.hom hE (by rw [← comap_comp, he, hz])
  let m : ℤ := -(↑((P[r.val]).stalkOrder p).toNat)
  have h := congrArg Additive.toMul
    (picardHom_primeDivisorClass_pointBlowup g[k,Y] hp r q' hq')
  rw [picardHom_snoc_apply_toMul, picardHom_nil, toMul_ofMul, toMul_ofMul] at h
  have ha : pullback f (primeDivisorClass r) * primeDivisorClass z ^ m = primeDivisorClass q := by
    simpa only [pullback_mul, pullback_zpow, pullback_comp, he, hclass, q', m,
      pullback_primeDivisorClass_mapOfIsOpenImmersion] using congrArg (pullback e.hom) h
  have hpair := f.classIntersectionNumber_pointBlowdown (k := k) hp e he hE hz
    (primeDivisorClass r) 1 m 1
  have hc : (LineBundleClass.mk hE.toInvertibleSheaf)⁻¹ = primeDivisorClass z :=
    (primeDivisorClass_def z).symm
  simp only [hc, zpow_one, pullback_one, one_mul, ha, Chow.classIntersectionNumber_one_right,
    mul_one, zero_sub] at hpair
  dsimp only
  simp only [Chow.intersectionBilinForm_apply, toMul_ofMul, hpair, ← ofMul_zpow, ← ofMul_mul]
  rw [← ha, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]

end AlgebraicGeometry.Scheme.Hom
