/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Basic
public import QPainleve.AlgebraicGeometry.Chow.Nef.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

import QPainleve.AlgebraicGeometry.Blowup.Tower.Contraction
import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Multiplicity
import QPainleve.AlgebraicGeometry.Blowup.Tower.TotalTransform
import QPainleve.AlgebraicGeometry.IdealSheaf.Restriction
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced

/-!
# Uniqueness of nodal contractions to square-zero pairs

On a common nodal blowup model, the support of a connected nef boundary of square
zero determines its total transform. The components of multiplicity at least two
then determine the projection's exceptional locus, so the original pairs are
canonically isomorphic.

The comparison uses `Chow.eq_of_nef_square_zero_of_support_eq` through the
total-transform comparison and `IsClosedPointTower.existsUnique_iso_over_of_eq_exceptional_divisors`
for the descent.
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry
open LineBundleClass Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower.IsNodalBoundaryTower

variable (k : Type u) [Field k] [IsAlgClosed k] {X Y V W : Scheme.{u}}
  [IsIntegral X] [IsIntegral Y] [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X.IsProjectiveOver k] [Y.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]
  {m n : ℕ} {T : BlowupTower X m V} {U : BlowupTower Y n W}
  {D : X.IdealSheafData} {E : Y.IdealSheafData}

local notation "s" => (X ↘ Spec (CommRingCat.of k))
local notation "t" => (Y ↘ Spec (CommRingCat.of k))

/-- Two smooth projective integral surfaces carrying connected nef square-zero nodal
boundaries are uniquely isomorphic as pairs over the field if their nodal blowup
projections from isomorphic models have matching reduced total boundaries. The isomorphism
commutes with the two projections and matches the full boundary ideals. -/
theorem existsUnique_iso_of_nef_square_zero_boundary
    (hT : IsNodalBoundaryTower D s (𝟙 X) T) (hU : IsNodalBoundaryTower E t (𝟙 Y) U)
    (e : V ≅ W) (hover : T.toBase ≫ s = e.hom ≫ U.toBase ≫ t)
    (hD : D.IsEffectiveCartier) (hE : E.IsEffectiveCartier)
    (hnodalD : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ s))
    (hnodalE : AtWorstNodalOfRelativeDimensionOne (E.subschemeι ≫ t))
    (hconn : _root_.IsConnected (D.support : Set X))
    (hsupp : (D.comap T.toBase).support = ((E.comap U.toBase).comap e.hom).support)
    (hnefD : IsNef k s (mk hD.toInvertibleSheaf)⁻¹)
    (hnefE : IsNef k t (mk hE.toInvertibleSheaf)⁻¹)
    (hsqD : Chow.classIntersectionNumber k X (mk hD.toInvertibleSheaf)⁻¹
      (mk hD.toInvertibleSheaf)⁻¹ = 0)
    (hsqE : Chow.classIntersectionNumber k Y (mk hE.toInvertibleSheaf)⁻¹
      (mk hE.toInvertibleSheaf)⁻¹ = 0) :
    ∃! a : X ≅ Y, T.toBase ≫ a.hom = e.hom ≫ U.toBase ∧ a.hom ≫ t = s ∧ E.comap a.hom = D := by
  have : IsReduced D.subscheme := hnodalD.isReduced
  have : IsReduced E.subscheme := hnodalE.isReduced
  have htotal := hT.isClosedPointTower.totalTransform_eq_of_nef_square_zero k
    hU.isClosedPointTower e hover hD hE hconn hsupp hnefD hnefE hsqD hsqE
  have hex := hT.exceptional_divisors_eq_of_totalTransform_eq hU e hD hE hnodalD hnodalE htotal
  obtain ⟨a, ⟨ha, haOver⟩, haUnique⟩ :=
    hT.isClosedPointTower.existsUnique_iso_over_of_eq_exceptional_divisors
      hU.isClosedPointTower e s t hex hover
  refine ⟨a, ⟨ha, haOver, ?_⟩, fun a' h' ↦ haUnique a' ⟨h'.1, h'.2.1⟩⟩
  have hcomap : (E.comap a.hom).comap T.toBase = D.comap T.toBase := by
    rw [← E.comap_comp, ha, E.comap_comp, htotal]
  have hs : (E.comap a.hom).support = D.support := by
    apply SetLike.coe_injective
    have : Surjective T.toBase := hT.isClosedPointTower.surjective s
    apply T.toBase.surjective.preimage_injective
    simpa only [support_comap, TopologicalSpace.Closeds.coe_preimage] using
      congrArg (fun I : V.IdealSheafData ↦ (I.support : Set V)) hcomap
  have hrad : (E.comap a.hom).radical = E.comap a.hom := by
    rw [radical_comap_of_isOpenImmersion,
      E.isReduced_subscheme_iff_radical_eq.mp ‹IsReduced E.subscheme›]
  rw [← hrad, ← vanishingIdeal_support, hs, vanishingIdeal_support,
    D.isReduced_subscheme_iff_radical_eq.mp ‹IsReduced D.subscheme›]

end QPainleve.BlowupTower.IsNodalBoundaryTower
