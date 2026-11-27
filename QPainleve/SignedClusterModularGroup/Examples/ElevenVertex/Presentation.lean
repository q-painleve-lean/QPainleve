/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Basic
public import QPainleve.SignedClusterModularGroup.Examples.ElevenVertex.Contraction

import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.InternalIndices
import QPainleve.AlgebraicGeometry.Blowup.Tower.Intersection
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
import QPainleve.AlgebraicGeometry.IdealSheaf.BaseChange
import QPainleve.AlgebraicGeometry.Modules.Differentials.Restriction
import QPainleve.Geometry.Toric.Fan.Boundary.InternalBlowup
import QPainleve.Geometry.Toric.Fan.Boundary.Prestable
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective
import TauCeti.AlgebraicGeometry.IdealSheaf.Extension

/-!
# The ordered toric presentation of the eleven-vertex seed

The two contractions of the strict triangle are the projection of a nodal
blowup tower. The auxiliary surface is the plane blown up in seed-label order.
In its Picard marking the negatives of the total exceptional coefficients of
the pulled-back boundary give the exponent of the boundary Casimir.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module
open QPainleve.BlowupTower Scheme.IdealSheafData TauCeti.AlgebraicGeometry
open TauCeti.Toric TauCeti.Toric.Fan LineBundleClass

namespace QPainleve.ElevenVertex

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]

local notation "b" => Pi.basisFun ℤ (Fin 2)
local notation "hi" => isIntegralLattice_intCast 2
local notation "Φ" => projectiveSpace b hi
local notation "hΦ" => isRegular_projectiveSpace b hi
local notation "hc" => isComplete_projectiveSpace b hi
local notation "Plane" => Fan.finiteFanScheme k₀ Φ
local notation "S" => Spec (CommRingCat.of k₀)
local instance : Nonempty (Φ).cones := Fan.IsComplete.nonempty_cones hc
local instance : SmoothOfRelativeDimension 2 (Plane ↘ S) := by
  rw [finiteFanScheme_over]
  simpa using (Φ).smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΦ

local notation "Y[" c "]" => Sigma.fst (planeBlowup c)
local notation "T[" c "]" => WithBoundary.toTower (Sigma.snd (planeBlowup c))
local notation "B[" c "]" => Scheme.Hom.ker (WithBoundary.boundaryι (Sigma.snd (planeBlowup c)))
local notation "J[" x "]" => Scheme.Hom.ker (Scheme.fromSpecResidueField _ x)
local notation "K[" X "]" => LineBundleClass.mk (canonicalBundle k₀ X 2)
local notation "δ[" h "]" =>
  (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

section Tower

variable [NeZero (2 : k₀)] (c : Fin 11 → k₀ˣ)

/-- The ordered plane blowup has the structure map induced from the plane. -/
local instance planeBlowupOver : (Y[c]).Over S := ⟨(T[c]).toBase ≫ Plane ↘ S⟩

local instance : SmoothOfRelativeDimension 2 (Y[c] ↘ S) :=
  isClosedPointTower_internalBlowupTower k₀ b planeCenterRay c |>.smoothOfRelativeDimension
    (Plane ↘ S)

local instance : IsLocallyNoetherian (Y[c]) := by
  let : Smooth (Y[c] ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  exact LocallyOfFiniteType.isLocallyNoetherian (Y[c] ↘ S)

private theorem exists_nodal_tower_for_triangle {Z W : Scheme} [W.Over S]
    [IsIntegral W] [W.IsProjectiveOver k₀] [SmoothOfRelativeDimension 2 (W ↘ S)]
    [Scheme.IsRationalOver (W ↘ S)]
    {f : Y[c] ⟶ Z} {g : Z ⟶ W} [(f ≫ g).IsOver S] {p : Z} {q : W}
    (hp : IsClosed ({p} : Set Z)) (hq : IsClosed ({q} : Set W))
    (e : Y[c] ≅ (J[p]).blowup) (e' : Z ≅ (J[q]).blowup)
    (he : e.hom ≫ (J[p]).blowupToBase = f) (he' : e'.hom ≫ (J[q]).blowupToBase = g)
    (hB : B[c].IsEffectiveCartier)
    (hpre : PrestableFamily (B[c].subscheme ↘ S))
    (hcard : B[c].boundaryPrimes.ncard = ((B[c]).map (f ≫ g)).boundaryPrimes.ncard + 2) :
    ∃ (U : Scheme) (R : BlowupTower W 2 U) (a : Y[c] ≅ U),
      IsNodalBoundaryTower ((B[c]).map (f ≫ g)) (W ↘ S) (𝟙 _) R ∧
      a.hom ≫ R.toBase = f ≫ g ∧
      ((((B[c]).map (f ≫ g)).comap R.toBase).radical).comap a.hom = B[c] := by
  let T := (BlowupTower.nil (X := W)).snoc (J[q])
  let L := (BlowupTower.nil (X := Z)).snoc (J[p])
  let P := L.transport e'
  let R := T.append P.tower
  let a := e ≪≫ P.iso
  have hT : IsClosedPointTower W T := .snoc .nil q hq rfl
  have hL : IsClosedPointTower Z L := .snoc .nil p hp rfl
  have hR : IsClosedPointTower W R := hT.append (P.isLift.isClosedPointTower hL)
  have ha : a.hom ≫ R.toBase = f ≫ g := by
    have hLbase : L.toBase = (J[p]).blowupToBase := by simp [L]
    have hTbase : T.toBase = (J[q]).blowupToBase := by simp [T]
    simp only [a, R, toBase_append, Iso.trans_hom, Category.assoc, P.isLift.hom_toBase_assoc]
    rw [← Category.assoc e.hom, hLbase, he, hTbase, he']
  let U := P.top
  let : U.Over S := ⟨R.toBase ≫ W ↘ S⟩
  let : SmoothOfRelativeDimension 2 (U ↘ S) := hR.smoothOfRelativeDimension _
  have ha' : a.inv ≫ (Y[c] ↘ S) = U ↘ S := by
    rw [← comp_over (f ≫ g) S, ← ha, ← Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  let : a.inv.IsOver S := ⟨ha'⟩
  let B' := (B[c]).comap a.inv
  have hmap : B'.map R.toBase = B[c].map (f ≫ g) := by
    have h := congrArg (fun D ↦ D.comap a.inv) (B[c].comap_map_of_isOpenImmersion a.hom)
    rw [← comap_comp, Iso.inv_hom_id, comap_id] at h
    rw [← ha, map_comp, h]
  let hB' := hB.comap a.inv
  obtain ⟨v, hv⟩ := B[c].exists_iso_of_comap_eq_ker a.symm B'.subschemeι B'.ker_subschemeι.symm
  have hn := hpre.atWorstNodalOfRelativeDimensionOne.comp_of_etale v.hom
  rw [B[c].over_eq_subschemeι_comp, ← Category.assoc, hv, Category.assoc, Iso.symm_hom, ha'] at hn
  have hcan : mk hB'.toInvertibleSheaf = K[U] := by
    rw [← hB.pullback_mk_toInvertibleSheaf hB', mk_toInvertibleSheaf_planeBlowup_boundary c hB,
      pullback_mk, mk_pullback_canonicalBundle]
  let : Module.Finite ℤ (Additive (LineBundleClass W)) := W.finite_picard_of_isRationalOver k₀
  obtain ⟨hN, hred⟩ := hR.isNodalBoundaryTower_of_ncard_boundaryPrimes_eq_add k₀ hB' hn
    ((ncard_boundaryPrimes_eq_of_iso a.symm (B[c])).trans (hcard.trans (by rw [hmap]))) hcan
  refine ⟨U, R, a, hmap ▸ hN, ha, ?_⟩
  rw [← hmap, hred, ← comap_comp, Iso.hom_inv_id, comap_id]

/-- The two specified blowdowns of the strict triangle are the projection of a
length-two nodal tower. The comparison with its top keeps the ordered plane
centers. The anticanonical boundary downstairs has a single numbered component
of normalization genus zero and two ordered branches at its node. It is the
scheme-theoretic image of the strict line with six centers. Its pullback has the
boundary Casimir exponent in the given seed labels. -/
theorem exists_eleven_vertex_toric_presentation :
    ∃ (W : Scheme) (s : W ⟶ S), letI : W.Over S := ⟨s⟩
      ∃ (_ : SmoothOfRelativeDimension 2 (W ↘ S)) (D : W.IdealSheafData)
        (hD : D.IsEffectiveCartier) (_ : D.subscheme.IsCurveOver k₀)
        (_ : PrestableFamily (D.subscheme ↘ S))
        (_ : PrestableFamily (B[c].subscheme ↘ S))
        (A₀ : Scheme.NodalCycleNumbering
          (PEmpty.elim : PEmpty.{1} → (B[c].subscheme ↘ S).smoothLocus) 3)
        (A₁ : Scheme.NodalCycleNumbering
          (PEmpty.elim : PEmpty.{1} → (D.subscheme ↘ S).smoothLocus) 1)
        (U : Scheme) (R : BlowupTower W 2 U) (a : Y[c] ≅ U) (β : (B[c]).subscheme ⟶ D.subscheme),
        IsIntegral W ∧ W.IsProjectiveOver k₀ ∧ Scheme.IsRationalOver s ∧ IsIntegral D.subscheme ∧
        D.subscheme.normalizationGenus k₀ = 0 ∧
        mk hD.toInvertibleSheaf = K[W] ∧
        TauCeti.IsPrimitive (Additive.ofMul δ[hD]) ∧ δ[hD].IsNef k₀ s ∧
        Chow.classIntersectionNumber k₀ W δ[hD] δ[hD] = 0 ∧
        IsNodalBoundaryTower D (W ↘ S) (𝟙 _) R ∧
        a.hom ≫ R.toBase ≫ s = (T[c]).toBase ≫ Fan.finiteFanSchemeToSpec k₀ Φ ∧
        ((D.comap R.toBase).radical).comap a.hom = B[c] ∧
        D = (strictTransform (Fan.rayDivisorIdeal k₀ Φ hΦ (planeBoundaryRay 2)) (T[c])).map
          (a.hom ≫ R.toBase) ∧
        β ≫ D.subschemeι = (B[c]).subschemeι ≫ a.hom ≫ R.toBase ∧
        β.IsOrientedCycleSubdivision A₀ A₁ ∧
        ((internalBlowupPicardMarking k₀ b planeCenterRay c hΦ).symm
          (Additive.ofMul (pullback (a.hom ≫ R.toBase) δ[hD]))).2 = -boundaryExponent := by
  obtain ⟨Z, W, t, s, f, g, p, q, hWsm, hW, hproj, hrat, hf, hg, _, _, hp, hq, _, _,
    e, e', he, he', hline, hDint, hD, hpre, hpreB, hcurve, hgenus, hcan, hclass, hprim, hnef, hsq,
    A, A', β, hβ, hsub⟩ := exists_eleven_vertex_nodal_boundary c
  let : Z.Over S := ⟨t⟩
  let : W.Over S := ⟨s⟩
  let : SmoothOfRelativeDimension 2 (W ↘ S) := hWsm
  let : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (W ↘ S)
  let : IsIntegral W := hW
  let : W.IsProjectiveOver k₀ := hproj
  let : Scheme.IsRationalOver (W ↘ S) := hrat
  let : f.IsOver S := hf
  let : g.IsOver S := hg
  let : PrestableFamily (B[c].subscheme ↘ S) := hpreB
  let : PrestableFamily ((((B[c]).map f).map g).subscheme ↘ S) := hpre
  have hB : B[c].IsEffectiveCartier :=
    isEffectiveCartier_internalBlowupBoundary k₀ b planeCenterRay hΦ c
      ((Φ).isEffectiveCartier_boundaryIdeal k₀ hΦ hc (by simp))
  have hcard := (Nat.card_congr (A.boundaryPrimeEquiv hB)).symm.trans (Nat.card_zmod 3)
  have hcard' := (Nat.card_congr (A'.boundaryPrimeEquiv hD)).symm.trans (Nat.card_zmod 1)
  rw [Nat.card_coe_set_eq] at hcard hcard'
  obtain ⟨U, R, a, hR, ha, hBred⟩ := exists_nodal_tower_for_triangle c hp hq e e' he he' hB hpreB
    (by rw [← map_comp] at hcard'; rw [hcard, hcard'])
  refine ⟨W, s, hWsm, _, hD, hcurve, hpre, hpreB, A, A', U, R, a, β, hW, hproj, hrat, hDint,
    hgenus, hcan, hprim, hnef, hsq, ?_, ?_, ?_, ha.symm ▸ hline, ?_, hsub, ?_⟩
  · simpa only [← map_comp] using hR
  · have hbase : (f ≫ g) ≫ s = Y[c] ↘ S := comp_over (f ≫ g) S
    have hplane : Y[c] ↘ S = (T[c]).toBase ≫ (Plane ↘ S) := rfl
    rw [← Category.assoc, ha, hbase, hplane, finiteFanScheme_over]
  · simpa only [← map_comp] using hBred
  · rw [ha]
    exact hβ
  · rw [ha, hclass, internalBlowupPicardMarking_symm_weightedBoundaryClass_snd]

end Tower

end QPainleve.ElevenVertex
