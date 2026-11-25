/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import TauCeti.AlgebraicGeometry.Blowup.IdealSheaf
public import QPainleve.AlgebraicGeometry.Chow.Isomorphism
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

import QPainleve.AlgebraicGeometry.Blowup.Intersection
import QPainleve.AlgebraicGeometry.Blowup.Projective.Global
import QPainleve.AlgebraicGeometry.Blowup.Tower.Factorization
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.Blowup.Tower.Intersection
import QPainleve.AlgebraicGeometry.Modules.Differentials.Restriction

/-!
# Surface intersections under birational pullback

A birational morphism of smooth projective surfaces preserves intersections of pulled-back
classes. A pulled-back class also pairs with the source canonical class as the original
class pairs with the target canonical class. The point-blowup Picard marking computes this
mixed intersection because the canonical correction is exceptional.
-/

public section

open AlgebraicGeometry CategoryTheory Scheme.IdealSheafData
open QPainleve
open TauCeti.AlgebraicGeometry LineBundleClass

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
variable [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
variable [X.IsProjectiveOver k] [Y.IsProjectiveOver k] [IsIntegral X] [IsIntegral Y]
variable [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
variable [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]

local notation "S" => Spec (CommRingCat.of k)

/-- Pullback along a birational morphism of smooth projective surfaces preserves
surface intersection numbers. -/
theorem classIntersectionNumber_pullback_of_birational (f : X ⟶ Y)
    [f.IsOver S] (hf : Scheme.BirationalOver f (𝟙 Y)) (a b : LineBundleClass Y) :
    Chow.classIntersectionNumber k X (pullback f a) (pullback f b) =
      Chow.classIntersectionNumber k Y a b := by
  obtain ⟨n, Z, T, e, hT, he⟩ := f.exists_isClosedPointTower_factorization (k := k) hf
  let : Z.Over S := ⟨T.toBase ≫ (Y ↘ S)⟩
  have : e.hom.IsOver S := ⟨(Category.assoc _ _ _).symm.trans (he ▸ comp_over f S)⟩
  rw [← he, ← pullback_comp, ← pullback_comp, Chow.classIntersectionNumber_pullback_of_isIso k]
  exact hT.classIntersectionNumber_pullback k a b

/-- Intersection with the canonical class is preserved on pullbacks along a
birational morphism of smooth projective surfaces. -/
theorem classIntersectionNumber_pullback_canonicalBundle_of_birational (f : X ⟶ Y)
    [f.IsOver S] (hf : Scheme.BirationalOver f (𝟙 Y)) (a : LineBundleClass Y) :
    Chow.classIntersectionNumber k X (pullback f a) (LineBundleClass.mk (canonicalBundle k X 2)) =
      Chow.classIntersectionNumber k Y a (LineBundleClass.mk (canonicalBundle k Y 2)) := by
  obtain ⟨n, Z, T, e, hT, he⟩ := f.exists_isClosedPointTower_factorization (k := k) hf
  let : Z.Over S := ⟨T.toBase ≫ (Y ↘ S)⟩
  have : e.hom.IsOver S := ⟨(Category.assoc _ _ _).symm.trans (he ▸ comp_over f S)⟩
  have : SmoothOfRelativeDimension 2 (Z ↘ S) := hT.smoothOfRelativeDimension (Y ↘ S)
  have hK : pullback e.hom (LineBundleClass.mk (canonicalBundle k Z 2)) =
      LineBundleClass.mk (canonicalBundle k X 2) := by
    rw [pullback_mk, mk_pullback_canonicalBundle]
  rw [← he, ← pullback_comp, ← hK, Chow.classIntersectionNumber_pullback_of_isIso k]
  exact hT.classIntersectionNumber_pullback_canonicalBundle k a

omit [X.IsProjectiveOver k] [IsIntegral X] [IsIntegral Y]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))] in
/-- The intersection formula in pullback and exceptional coordinates, transported
to the source of a specified closed-point blowdown. -/
theorem classIntersectionNumber_pointBlowdown (f : X ⟶ Y) [f.IsOver S]
    {p : Y} (hp : IsClosed ({p} : Set Y)) (e : X ≅ (Y.fromSpecResidueField p).ker.blowup)
    (he : e.hom ≫ (Y.fromSpecResidueField p).ker.blowupToBase = f)
    {E : X.IdealSheafData} (hE : E.IsEffectiveCartier)
    (hF : (Y.fromSpecResidueField p).ker.comap f = E)
    (a b : LineBundleClass Y) (m n : ℤ) :
    let c := (LineBundleClass.mk hE.toInvertibleSheaf)⁻¹
    Chow.classIntersectionNumber k X (pullback f a * c ^ m) (pullback f b * c ^ n) =
      Chow.classIntersectionNumber k Y a b - m * n := by
  let I := (Y.fromSpecResidueField p).ker
  let : I.blowup.Over S := ⟨I.blowupToBase ≫ (Y ↘ S)⟩
  let : e.hom.IsOver S := ⟨by
    -- The blowup carries the structure morphism obtained from its projection.
    change e.hom ≫ I.blowupToBase ≫ (Y ↘ S) = _
    rw [← Category.assoc, he, comp_over]⟩
  let : IsNoetherian Y := isNoetherian_of_finiteType (Y ↘ S)
  have hproj : I.blowup.IsProjectiveOver k := I.isProjectiveOver_blowup_of_isNoetherianRing k
  let hI := I.isEffectiveCartier_comap_blowupToBase
  have hIe : (I.comap I.blowupToBase).comap e.hom = E := by
    rw [← comap_comp, he, hF]
  have hc : pullback e.hom I.blowupExceptionalClass =
      (LineBundleClass.mk hE.toInvertibleSheaf)⁻¹ := by
    rw [blowupExceptionalClass_def, pullback_inv,
      hI.pullback_mk_toInvertibleSheaf (hIe.symm ▸ hE),
      mk_toInvertibleSheaf_congr _ hE hIe]
  have h := Chow.classIntersectionNumber_pointBlowup p k hp a b m n hproj
  rw [← Chow.classIntersectionNumber_pullback_of_isIso k e.hom] at h
  dsimp only [I] at hc
  simpa only [← blowupExceptionalClass_def, pullback_mul, pullback_zpow, hc,
    pullback_comp, he] using h

end AlgebraicGeometry.Scheme.Hom
