/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Canonical
public import QPainleve.AlgebraicGeometry.Chow.Nef.Basic
public import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Primes
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Contraction
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Reduced
import QPainleve.AlgebraicGeometry.Blowup.Tower.Contraction
import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.InternalCurve
import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Multiplicity
import QPainleve.AlgebraicGeometry.Blowup.Tower.TotalTransform
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.IdealSheaf.Restriction
import QPainleve.AlgebraicGeometry.Modules.Differentials.Restriction
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.AlgebraicGeometry.Noetherian
import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme

/-!
# Contractions of nodal blowup models

If the reduced anticanonical boundary on a nodal blowup tower identifies with a strict
transform on another point blowup, the corresponding blowdown recovers the divisor
downstairs and contracts a curve omitted by the reduced boundary.

An isomorphism of nodal blowup models that identifies their total boundary supports
descends to the original pairs if it matches the boundary primes that survive the two
contractions.

On a common nodal blowup model, the support of a connected nef boundary of square
zero determines its total transform. The components of multiplicity at least two
then determine the projection's exceptional locus, so the original pairs are
canonically isomorphic.

The comparison uses `Chow.eq_of_nef_square_zero_of_support_eq` through the
total-transform comparison and `IsClosedPointTower.existsUnique_iso_over_of_eq_exceptional_divisors`
for the descent.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open LineBundleClass Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower.IsNodalBoundaryTower

section BoundaryImage

variable {k : Type u} [Field k] [PerfectField k] {X Y W : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [IsIntegral X] [IsIntegral Y] [IsNoetherian X] [IsNoetherian Y]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]
  {n : ℕ} {T : BlowupTower X n W} {D : X.IdealSheafData} {E : Y.IdealSheafData}

local notation "S" => Spec (CommRingCat.of k)
local notation "K(" Z ")" => mk (canonicalBundle k Z 2)
local notation "I(" y ")" => Scheme.Hom.ker (Scheme.fromSpecResidueField _ y)
local notation "J(" y ")" => vanishingIdeal (Closeds.mk (closure ({y} : Set _)) isClosed_closure)

/-- If an isomorphism over the base field identifies the reduced total boundary of an
anticanonical nodal tower with a strict transform on a closed-point blowup, the schematic
image is the original divisor of that strict transform, and the boundary omits the
exceptional curve of the blowdown. -/
theorem map_radical_comap_toBase_of_eq_strictTransform
    (hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T) (hD : D.IsEffectiveCartier)
    (hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S))
    (hK : mk hD.toInvertibleSheaf = K(X))
    {y : Y} (hy : IsClosed ({y} : Set Y)) (hE : E.IsEffectiveCartier) [IsReduced E.subscheme]
    (a : W ≅ (I(y)).blowup) (ha : a.hom ≫ (I(y)).blowupToBase ≫ Y ↘ S = T.toBase ≫ X ↘ S)
    (hstrict : (blowupMap (I(y)) E.subschemeι).ker.comap a.hom = (D.comap T.toBase).radical) :
    (D.comap T.toBase).radical.map (a.hom ≫ (I(y)).blowupToBase) = E ∧
      ¬ ((I(y)).comap (a.hom ≫ (I(y)).blowupToBase)).support ≤
        (D.comap T.toBase).radical.support := by
  let : W.Over S := ⟨T.toBase ≫ X ↘ S⟩
  let : SmoothOfRelativeDimension 2 (W ↘ S) := hT.isClosedPointTower.smoothOfRelativeDimension _
  have hCartier := (hT.radical_comap_toBase hD hN).1
  have hKtotal := (hT.canonicalClass_radical_comap_toBase_iff hD hN).mpr hK
  generalize hI : I(y) = J at a ha hstrict ⊢
  have hJ : J = J(y) := hI.symm.trans (Y.ker_fromSpecResidueField_eq_vanishingIdeal y)
  clear hI
  subst J
  let B := (blowupMap (J(y)) E.subschemeι).ker
  let : (J(y)).blowup.Over S := ⟨(J(y)).blowupToBase ≫ Y ↘ S⟩
  let : SmoothOfRelativeDimension 2 ((J(y)).blowup ↘ S) :=
    smoothOfRelativeDimension_blowup_closed_point (Y ↘ S) hy
  have haOver : a.hom ≫ ((J(y)).blowup ↘ S) = W ↘ S := ha
  have : a.inv.IsOver S := ⟨by rw [← haOver, Iso.inv_hom_id_assoc]⟩
  have hBcomap : (D.comap T.toBase).radical.comap a.inv = B := by
    rw [← hstrict, ← comap_comp, Iso.inv_hom_id, comap_id]
  have hB : B.IsEffectiveCartier := hBcomap ▸ hCartier.comap a.inv
  have : IsReduced B.subscheme := isReduced_subscheme_ker_blowupMap (J(y)) E
  have hKB : mk hB.toInvertibleSheaf = K((J(y)).blowup) := by
    have hclass := (hCartier.pullback_mk_toInvertibleSheaf (hCartier.comap a.inv)).trans
      (mk_toInvertibleSheaf_congr _ hB hBcomap)
    rw [hKtotal, pullback_mk] at hclass
    exact hclass.symm.trans (mk_pullback_canonicalBundle k a.inv 2)
  obtain ⟨hmap, homit⟩ := hB.map_eq_and_not_le_support_of_eq_strictTransform k hy hE rfl hKB
  refine ⟨?_, ?_⟩
  · rw [← hstrict, map_comp, map_comap_of_isClosedImmersion,
      Scheme.Hom.ker_eq_bot_of_isIso a.hom, sup_bot_eq]
    exact hmap
  · rw [← hstrict, comap_comp, support_comap _ a.hom, support_comap _ a.hom]
    exact fun h ↦ homit (SetLike.coe_subset_coe.mp
      (a.hom.surjective.preimage_subset_preimage_iff.mp (SetLike.coe_subset_coe.mpr h)))

end BoundaryImage

section SurvivingPrimes

variable {k : Type u} [Field k] [PerfectField k] {X Y V W : Scheme.{u}}
  [IsIntegral X] [IsIntegral Y] {f : X ⟶ Spec (.of k)} {g : Y ⟶ Spec (.of k)}
  [SmoothOfRelativeDimension 2 f] [SmoothOfRelativeDimension 2 g]
  {m n : ℕ} {T : BlowupTower X m V} {U : BlowupTower Y n W}
  {D : X.IdealSheafData} {E : Y.IdealSheafData}

/-- An isomorphism of two nodal models descends uniquely when the upper boundary
supports match and every surviving boundary prime on either side survives on the
other. The descended isomorphism identifies the reduced boundary ideals. -/
theorem existsUnique_iso_of_eq_surviving_boundaryPrimes
    (hT : IsNodalBoundaryTower D f (𝟙 X) T) (hU : IsNodalBoundaryTower E g (𝟙 Y) U)
    [QuasiCompact f] [QuasiCompact g] [IsReduced D.subscheme] [IsReduced E.subscheme]
    (e : V ≅ W) (hover : T.toBase ≫ f = e.hom ≫ U.toBase ≫ g)
    (hsupp : (D.comap T.toBase).support = ((E.comap U.toBase).comap e.hom).support)
    (hkeep : ∀ x ∈ (D.comap T.toBase).boundaryPrimes,
      T.toBase x ∈ D.boundaryPrimes ↔ U.toBase (e.hom x) ∈ E.boundaryPrimes) :
    ∃! a : X ≅ Y, T.toBase ≫ a.hom = e.hom ≫ U.toBase ∧ a.hom ≫ g = f ∧ E.comap a.hom = D := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  have : Smooth g := SmoothOfRelativeDimension.smooth 2 g
  have : IsNoetherian X := isNoetherian_of_finiteType f
  have : IsNoetherian Y := isNoetherian_of_finiteType g
  have : IsRegular X := IsRegular.of_smooth f
  have : IsRegular Y := IsRegular.of_smooth g
  have : IsIntegral V := hT.isClosedPointTower.isIntegral f
  have : IsIntegral W := hU.isClosedPointTower.isIntegral g
  have := hT.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two f
  have := hU.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two g
  have hs (x : V) : x ∈ (D.comap T.toBase).support ↔ e.hom x ∈ (E.comap U.toBase).support := by
    rw [hsupp, support_comap]
    rfl
  have hnot {S Z : Scheme.{u}} {I : S.IdealSheafData} {p : Z ⟶ S}
      (hπ : I.support.compl ≤ p.isoLocus) {x : Z} (hx : x ∉ (I.comap p).support) :
      p x ∉ p.centre := by
    rw [Scheme.Hom.centre_def, Set.mem_compl_iff, SetLike.mem_coe, not_not]
    exact hπ (by simpa only [← SetLike.mem_coe, TopologicalSpace.Closeds.coe_compl, support_comap,
      TopologicalSpace.Closeds.coe_preimage, Set.mem_preimage, Set.mem_compl_iff] using hx)
  have hex (x : V) (hx : Order.coheight x = 1) :
      T.toBase x ∈ T.toBase.centre ↔ U.toBase (e.hom x) ∈ U.toBase.centre := by
    by_cases hb : x ∈ (D.comap T.toBase).support
    · have hp := mem_boundaryPrimes.mpr ⟨hb, hx⟩
      have hq := mem_boundaryPrimes.mpr
        ⟨(hs x).mp hb, (coheight_eq_of_isOpenImmersion e.hom).trans hx⟩
      rw [D.mem_centre_iff_notMem_boundaryPrimes_of_mem_boundaryPrimes_comap T.toBase hp,
        E.mem_centre_iff_notMem_boundaryPrimes_of_mem_boundaryPrimes_comap U.toBase hq, hkeep x hp]
    · exact iff_of_false (hnot hT.boundaryCompl_le_isoLocus hb)
        (hnot hU.boundaryCompl_le_isoLocus (fun h ↦ hb ((hs x).mpr h)))
  obtain ⟨a, ⟨ha, haOver⟩, hu⟩ :=
    hT.isClosedPointTower.existsUnique_iso_over_of_eq_exceptional_divisors
      hU.isClosedPointTower e f g hex hover
  have : Surjective T.toBase := hT.isClosedPointTower.surjective f
  have hb : ((E.comap a.hom).comap T.toBase).support = (D.comap T.toBase).support := by
    rw [← comap_comp, ha, comap_comp, hsupp]
  have heq := radical_eq_of_support_comap_eq T.toBase hb
  rw [radical_comap_of_isOpenImmersion,
    E.isReduced_subscheme_iff_radical_eq.mp ‹IsReduced E.subscheme›,
    D.isReduced_subscheme_iff_radical_eq.mp ‹IsReduced D.subscheme›] at heq
  exact ⟨a, ⟨ha, haOver, heq⟩, fun a' h ↦ hu a' ⟨h.1, h.2.1⟩⟩

end SurvivingPrimes

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
  have : Surjective T.toBase := hT.isClosedPointTower.surjective s
  have heq := radical_eq_of_support_comap_eq T.toBase (congrArg support hcomap)
  rwa [radical_comap_of_isOpenImmersion,
    E.isReduced_subscheme_iff_radical_eq.mp ‹IsReduced E.subscheme›,
    D.isReduced_subscheme_iff_radical_eq.mp ‹IsReduced D.subscheme›] at heq

end QPainleve.BlowupTower.IsNodalBoundaryTower
