/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Basic
public import QPainleve.AlgebraicGeometry.Modules.Differentials.Canonical
public import QPainleve.Geometry.Toric.Fan.InternalBlowup
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Branches.NodalContraction
import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.AlgebraicGeometry.Curves.Node.Comap
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import QPainleve.AlgebraicGeometry.Modules.Differentials.Restriction
import QPainleve.Geometry.Toric.Fan.Presentation.InternalBlowup
import QPainleve.Geometry.Toric.Fan.Presentation.NodalBlowup
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import TauCeti.AlgebraicGeometry.IdealSheaf.Extension
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced
import TauCeti.AlgebraicGeometry.Noetherian

/-!
# Toric presentations along closed-point towers

A toric presentation of the schematic image of a nodal anticanonical boundary
extends to the original pair along a specified closed-point blowup tower.
Boundary descent detects the nodal and smooth centers at each stage.
This is the reduction to a minimal surface in
[Gross, Hacking and Keel, *Mirror symmetry for log Calabi–Yau surfaces I*,
Proposition 1.3][GHK].

[GHK]: https://arxiv.org/html/1106.4977v3#S1.Thmproposition3
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.Toric
open QPainleve QPainleve.BlowupTower TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData LineBundleClass

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {X Y : Scheme} (b : Module.Basis (Fin 2) ℤ N)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "K(" W ")" => LineBundleClass.mk (QPainleve.canonicalBundle ℂ W 2)

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- A pair has a toric presentation if a nodal blowup tower over the pair is
isomorphic over the ground field to an ordered internal blowup model of a regular
complete fan. The isomorphism identifies the reduced total boundary with the
strict toric boundary. The center parameters may repeat. -/
def HasToricPresentation (D : X.IdealSheafData) (s : X ⟶ S)
    (b : Module.Basis (Fin 2) ℤ N) (i : N →+ V) : Prop :=
  ∃ (Φ : Fan i) (_ : Φ.IsRegular) (hc : Φ.IsComplete)
    (m : ℕ) (rays : Fin m → Φ.Ray) (c : Fin m → ℂˣ)
    (n : ℕ) (Y : Scheme) (T : BlowupTower X n Y),
    IsNodalBoundaryTower D s (𝟙 X) T ∧
    let A := Fan.internalBlowupTower (h₀ := hc.nonempty_cones) b rays c
    ∃ e : A.1 ≅ Y,
      e.hom ≫ T.toBase ≫ s = A.2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap ∧
      ((D.comap T.toBase).radical).comap e.hom = A.2.boundaryι.ker

/-- The existence of a toric presentation is witnessed by the fan, the ordered
internal centers, the nodal tower, and the boundary-preserving comparison. -/
theorem hasToricPresentation_iff (D : X.IdealSheafData) (s : X ⟶ S)
    (b : Module.Basis (Fin 2) ℤ N) (i : N →+ V) :
    D.HasToricPresentation s b i ↔
      ∃ (Φ : Fan i) (_ : Φ.IsRegular) (hc : Φ.IsComplete)
        (m : ℕ) (rays : Fin m → Φ.Ray) (c : Fin m → ℂˣ)
        (n : ℕ) (Y : Scheme) (T : BlowupTower X n Y),
        IsNodalBoundaryTower D s (𝟙 X) T ∧
        let A := Fan.internalBlowupTower (h₀ := hc.nonempty_cones) b rays c
        ∃ e : A.1 ≅ Y,
          e.hom ≫ T.toBase ≫ s = A.2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap ∧
          ((D.comap T.toBase).radical).comap e.hom = A.2.boundaryι.ker :=
  Iff.rfl

variable {b}

/-- A toric presentation transports along an isomorphism over the ground field. -/
theorem HasToricPresentation.of_comap_iso {D : X.IdealSheafData} {s : X ⟶ S} {t : Y ⟶ S}
    {e : X ≅ Y} (h : (D.comap e.inv).HasToricPresentation t b i) (he : e.hom ≫ t = s) :
    D.HasToricPresentation s b i := by
  obtain ⟨Φ, hΦ, hc, m, r, c, n, Z, U, hU, a, ha, hD⟩ := (hasToricPresentation_iff ..).mp h
  obtain ⟨W, T, f, hT, hf, hB⟩ := hU.exists_transport_of_iso he
  have he' : e.inv ≫ s = t := by rw [← he, Iso.inv_hom_id_assoc]
  refine (hasToricPresentation_iff ..).mpr ⟨Φ, hΦ, hc, m, r, c, n, W, T, hT,
    a ≪≫ f.symm, ?_, ?_⟩
  · simpa only [Iso.trans_hom, Iso.symm_hom, hf, Category.assoc, Iso.inv_hom_id_assoc, he']
      using ha
  · simpa only [hB, Iso.trans_hom, Iso.symm_hom, ← comap_comp, Category.assoc,
      Iso.inv_hom_id, Category.comp_id] using hD

variable {D : X.IdealSheafData} {s : X ⟶ S} {p : X}
local notation "I" => vanishingIdeal (Closeds.mk (closure (Singleton.singleton p)) isClosed_closure)
local notation "π" => blowupToBase I

private theorem HasToricPresentation.nodalBlowup
    (h : D.HasToricPresentation s b i) (hp : IsClosed ({p} : Set X))
    (hn : D.IsNodeOfReducedBoundary s p) :
    (D.comap π).radical.HasToricPresentation (π ≫ s) b i := by
  obtain ⟨Φ, hΦ, hc, m, r, c, n, Z, T, hT, e, he, hD⟩ := (hasToricPresentation_iff ..).mp h
  obtain ⟨Ψ, hΨ, H, l, W, U, -, hU, a, _, _, _, ha, hB⟩ :=
    Fan.exists_toric_presentation_of_nodal_boundary_tower b r c hΦ hc hT
      (IsNodalBoundaryTower.of_node hp hn) e he hD
  refine (hasToricPresentation_iff ..).mpr ⟨Ψ, hΨ, H.isComplete_iff.mpr hc, m, H.liftRay ∘ r, c,
    l, W, U, ?_, a, ?_, ?_⟩
  · simpa only [toBase_snoc, toBase_nil, Category.comp_id] using hU
  · simpa only [toBase_snoc, toBase_nil, Category.comp_id, Category.assoc] using ha
  · simpa only [toBase_snoc, toBase_nil, Category.comp_id] using hB

private theorem HasToricPresentation.internalBlowup [IsLocallyNoetherian X]
    (h : D.HasToricPresentation s b i) (hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ s))
    (hp : IsClosed ({p} : Set X)) {q : D.subscheme} (hq : D.subschemeι q = p)
    (hs : ((D.subschemeι ≫ s).stalkMap q).hom.FormallySmooth) :
    ((I).blowupMap D.subschemeι).ker.HasToricPresentation (π ≫ s) b i := by
  have hqclosed : IsClosed ({q} : Set D.subscheme) :=
    D.subschemeι.isClosedEmbedding.isClosed_iff_image_isClosed.mpr (by
      rw [Set.image_singleton, hq]
      exact hp)
  have hI : ((D.subscheme.fromSpecResidueField q).ker).map D.subschemeι = I := by
    rw [D.subschemeι.map_ker_fromSpecResidueField, hq,
      Scheme.ker_fromSpecResidueField_eq_vanishingIdeal]
  obtain ⟨Φ, hΦ, hc, m, r, c, n, Z, T, hT, e, he, hD⟩ := (hasToricPresentation_iff ..).mp h
  let := hc.nonempty_cones
  obtain ⟨r', a, W, U, _, hU, _, d, _, hd, hB⟩ :=
    Fan.exists_toric_presentation_of_internal_blowup b hΦ hc r c hT e he
      ((radical_comap_of_isOpenImmersion _ _).trans hD) hN hqclosed hs
  rw [← hI]
  exact (hasToricPresentation_iff ..).mpr
    ⟨Φ, hΦ, hc, m + 1, Fin.snoc r r', Fin.snoc c a, n, W, U, hU, d, hd, hB⟩

end AlgebraicGeometry.Scheme.IdealSheafData

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {b} [X.Over S] [X.IsProjectiveOver ℂ] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ S)] {n : ℕ} {T : BlowupTower X n Y}

local notation "s" => (X ↘ S)

/-- If the schematic image of a nodal anticanonical boundary along a
closed-point blowup tower admits a toric presentation, then the original pair
does as well. The tower may mix nodal and internal stages, including infinitely
near centers. -/
theorem hasToricPresentation_of_closedPointTower (hT : IsClosedPointTower X T)
    {B : Y.IdealSheafData} (hB : B.IsEffectiveCartier)
    (hN : AtWorstNodalOfRelativeDimensionOne (B.subschemeι ≫ T.toBase ≫ s)) :
    let : Y.Over S := ⟨T.toBase ≫ s⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension s
    LineBundleClass.mk hB.toInvertibleSheaf = K(Y) →
    (B.map T.toBase).HasToricPresentation s b i →
    B.HasToricPresentation (T.toBase ≫ s) b i := by
  have : Smooth s := SmoothOfRelativeDimension.smooth 2 _
  have : IsNoetherian X := isNoetherian_of_finiteType s
  induction hT with
  | nil =>
    simpa only [toBase_nil, map_id, Category.id_comp] using fun _ h ↦ h
  | @snoc m W U J hU p hp hJ ih =>
    have hcenter := hJ.trans (W.ker_fromSpecResidueField_eq_vanishingIdeal p)
    subst hcenter
    let I := vanishingIdeal (Closeds.mk (closure ({p} : Set W)) isClosed_closure)
    let π := I.blowupToBase
    let : W.Over S := ⟨U.toBase ≫ s⟩
    let : SmoothOfRelativeDimension 2 (W ↘ S) := hU.smoothOfRelativeDimension s
    have : IsIntegral W := hU.isIntegral s
    have : W.IsProjectiveOver ℂ := U.isProjectiveOver ℂ
    have : IsNoetherian W := U.isNoetherian
    intro _ _ hcan h
    have hbase : (U.snoc I).toBase ≫ s = π ≫ (W ↘ S) := by
      rw [toBase_snoc, Category.assoc]
      rfl
    -- Pointwise descent uses the last blowup followed by the intermediate structure map.
    have hclass (f : I.blowup ⟶ S) (hf : f = π ≫ (W ↘ S))
        (hs : SmoothOfRelativeDimension 2 f) :
        @QPainleve.canonicalBundle ℂ _ I.blowup ⟨f⟩ 2 hs =
          @QPainleve.canonicalBundle ℂ _ I.blowup ⟨π ≫ (W ↘ S)⟩ 2
            (smoothOfRelativeDimension_blowup_closed_point (W ↘ S) hp) := by
      subst f
      rfl
    rw [hclass _ hbase _] at hcan
    have hnodal : AtWorstNodalOfRelativeDimensionOne (B.subschemeι ≫ π ≫ (W ↘ S)) :=
      hbase ▸ hN
    let D := B.map π
    have hDpres : (D.map U.toBase).HasToricPresentation s b i := by
      simpa only [toBase_snoc, map_comp] using h
    rw [hbase]
    by_cases hE : (I.comap π).support ≤ B.support
    · obtain ⟨hD, hcanD, hN', htotal, hnode⟩ :=
        hB.anticanonical_nodal_boundary_point_blowdown ℂ hp hnodal hcan
      have hBD : (D.comap π).radical = B := by
        rw [← vanishingIdeal_support, htotal, support_mul, sup_eq_left.mpr hE,
          vanishingIdeal_support, B.isReduced_subscheme_iff_radical_eq.mp hnodal.isReduced]
      rw [← hBD]
      exact (ih hD hN' hcanD hDpres).nodalBlowup hp (hnode.mp hE)
    · obtain ⟨hD, hcanD, hN', _, _, hstrict, _, ⟨q, hq, hs⟩, -⟩ :=
        hB.internalBlowdown_of_anticanonical ℂ hp hE hnodal hcan
      have : Smooth (W ↘ S) := SmoothOfRelativeDimension.smooth 2 _
      have hfp : LocallyOfFinitePresentation (D.subschemeι ≫ (W ↘ S)) :=
        TauCeti.locallyOfFinitePresentation_subschemeι_comp_of_isEffectiveCartier hD
      exact hstrict ▸
        (ih hD hN' hcanD hDpres).internalBlowup hN' hp hq
          ((@Scheme.Hom.mem_smoothLocus _ _ _ hfp q).mp hs)

/-- The closed-point tower comparison also applies when the original surface is
identified with the top by an isomorphism over the ground field, as in the
minimal-model theorem. The boundary on the base is the schematic image along
the specified projection. -/
theorem hasToricPresentation_of_closedPointTower_of_iso (hT : IsClosedPointTower X T)
    {Z : Scheme} [Z.Over S] [SmoothOfRelativeDimension 2 (Z ↘ S)]
    (a : Z ≅ Y) (ha : a.hom ≫ T.toBase ≫ s = Z ↘ S)
    {B : Z.IdealSheafData} (hB : B.IsEffectiveCartier)
    (hN : AtWorstNodalOfRelativeDimensionOne (B.subschemeι ≫ (Z ↘ S)))
    (hcan : LineBundleClass.mk hB.toInvertibleSheaf = K(Z))
    (h : (B.map (a.hom ≫ T.toBase)).HasToricPresentation s b i) :
    B.HasToricPresentation (Z ↘ S) b i := by
  let : Y.Over S := ⟨T.toBase ≫ s⟩
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension s
  have hover : a.inv ≫ (Z ↘ S) = T.toBase ≫ s := by
    rw [← ha, Iso.inv_hom_id_assoc]
  have : a.inv.IsOver S := ⟨hover⟩
  let B' := B.comap a.inv
  have hB' : B'.IsEffectiveCartier := hB.comap a.inv
  have hN' := hN.comap_of_etale a.inv
  rw [hover] at hN'
  have hcan' : LineBundleClass.mk hB'.toInvertibleSheaf = K(Y) := by
    rw [← hB.pullback_mk_toInvertibleSheaf hB', hcan, pullback_mk,
      mk_pullback_canonicalBundle]
  have hmap : B' = B.map a.hom := by
    have hcomap := congrArg (fun J : Z.IdealSheafData ↦ J.comap a.inv)
      (B.comap_map_of_isOpenImmersion a.hom)
    rw [← comap_comp, Iso.inv_hom_id, comap_id] at hcomap
    exact hcomap.symm
  have h' : (B'.map T.toBase).HasToricPresentation s b i := by rwa [hmap, ← map_comp]
  exact (hT.hasToricPresentation_of_closedPointTower hB' hN' hcan' h').of_comap_iso ha

end QPainleve.BlowupTower.IsClosedPointTower
