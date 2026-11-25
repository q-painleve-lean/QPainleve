/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Presentation.InternalBlowup
public import QPainleve.AlgebraicGeometry.Modules.Differentials.Canonical
public import TauCeti.AlgebraicGeometry.Curves.Prestable
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Contraction
import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Canonical
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.IdealSheaf.Restriction
import TauCeti.AlgebraicGeometry.Noetherian

/-!
# Toric presentations under nodal reductions

A nodal blowup followed by an internal contraction is the link used to reduce a
ruled anticanonical pair in [Gross, Hacking and Keel, Proposition 1.3][GHK].
A toric presentation of the contracted pair pulls back through the link by
appending the contraction center to its ordered list of internal blowups.

[GHK]: https://arxiv.org/html/1106.4977v3#S1.Thmproposition3
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open QPainleve QPainleve.BlowupTower TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]
  (b : Module.Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  {m : ℕ} (ρ : Fin m → Φ.Ray) (c : Fin m → ℂˣ)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "K[" Y "]" => LineBundleClass.mk (canonicalBundle ℂ Y 2)
local notation "P" => internalBlowupTower b ρ c
local notation "J[" q "]" => Scheme.Hom.ker (Scheme.fromSpecResidueField _ q)

variable {X Y Z : Scheme} [X.Over S] [Y.Over S]
  [IsIntegral X] [IsIntegral Y] [IsNoetherian X] [IsNoetherian Y]
  [SmoothOfRelativeDimension 2 (X ↘ S)] [SmoothOfRelativeDimension 2 (Y ↘ S)]
  {D : X.IdealSheafData}

include hΦ hc in
/-- A specified toric presentation of the schematic image of the reduced boundary
under an internal contraction gives a presentation before the nodal blowups.
The new presentation keeps the fan, appends the contraction center to the ordered
internal centers, and appends the lifted nodal tower to the original nodal tower. -/
theorem exists_toric_presentation_of_internal_contraction_after_nodal_tower
    (hD : D.IsEffectiveCartier)
    (hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S))
    (hK : LineBundleClass.mk hD.toInvertibleSheaf = K[X])
    {k : ℕ} {U : BlowupTower X k Z}
    (hU : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) U)
    (g : Z ⟶ Y) (hg : g ≫ Y ↘ S = U.toBase ≫ X ↘ S)
    {q : Y} (hq : IsClosed ({q} : Set Y))
    (u : Z ≅ (J[q]).blowup) (hu : u.hom ≫ (J[q]).blowupToBase = g)
    (homit : ¬ ((J[q]).comap g).support ≤ (D.comap U.toBase).support)
    {n : ℕ} {W : Scheme} {T : BlowupTower Y n W}
    (hT : IsNodalBoundaryTower ((D.comap U.toBase).radical.map g) (Y ↘ S) (𝟙 Y) T)
    (e : (P).1 ≅ W)
    (he : e.hom ≫ T.toBase ≫ Y ↘ S = (P).2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap)
    (hB : ((((D.comap U.toBase).radical.map g).comap T.toBase).comap e.hom).radical =
        (P).2.boundaryι.ker) :
    ∃ (r : Φ.Ray) (a : ℂˣ) (W' : Scheme) (T' : BlowupTower X (k + n) W'),
      IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T' ∧
      let P' := internalBlowupTower b (Fin.snoc ρ r) (Fin.snoc c a)
      ∃ d : P'.1 ≅ W',
        d.hom ≫ T'.toBase ≫ X ↘ S = P'.2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap ∧
        ((D.comap T'.toBase).comap d.hom).radical = P'.2.boundaryι.ker := by
  let R := (D.comap U.toBase).radical
  let D' := R.map g
  let : Z.Over S := ⟨U.toBase ≫ X ↘ S⟩
  let : g.IsOver S := ⟨hg⟩
  let : SmoothOfRelativeDimension 2 (Z ↘ S) := hU.isClosedPointTower.smoothOfRelativeDimension _
  obtain ⟨hR, hRN⟩ := hU.radical_comap_toBase hD hN
  have hRK := (hU.canonicalClass_radical_comap_toBase_iff hD hN).mpr hK
  let I := vanishingIdeal (Closeds.mk (closure ({q} : Set Y)) isClosed_closure)
  have hI : J[q] = I := Y.ker_fromSpecResidueField_eq_vanishingIdeal q
  let v : Z ≅ I.blowup := u ≪≫ blowupIso (Iso.refl Y) (hI.trans (comap_id I).symm)
  have hv : v.hom ≫ I.blowupToBase = g := by simp [v, hu]
  have hv' : v.inv ≫ g = I.blowupToBase := by rw [← hv, Iso.inv_hom_id_assoc]
  have hOmit : ¬ (I.comap g).support ≤ R.support := by
    simpa only [← hI, R, support_radical] using homit
  obtain ⟨hD', -, hN', -, -, hCartier, hPoint, d, hd⟩ :=
    hR.internalBlowdown_of_anticanonical_of_blowupIso ℂ hq g v.symm hv'
      hOmit hRN hRK
  let := hN'.syntomic.locallyOfFinitePresentation
  obtain ⟨p, hpq, hs⟩ := hPoint
  have hp : IsClosed ({p} : Set D'.subscheme) := by
    rw [D'.subschemeι.isClosedEmbedding.isClosed_iff_image_isClosed, Set.image_singleton, hpq]
    exact hq
  have hI' : (J[p]).map D'.subschemeι = J[q] := by
    rw [D'.subschemeι.map_ker_fromSpecResidueField, hpq]
  let J := (J[p]).map D'.subschemeι
  let hLift : Z ≅ J.blowup :=
    u ≪≫ blowupIso (Iso.refl Y) (hI'.symm.trans (comap_id J).symm)
  have hLiftBase : hLift.hom ≫ J.blowupToBase = g := by simp [hLift, hu]
  -- The strict transform and the given boundary are two lifts of the same immersion.
  have hStrict : (J.blowupMap D'.subschemeι).ker.comap hLift.hom = R := by
    have hJI : J = I := hI'.trans hI
    have hJ : (J.comap D'.subschemeι).IsEffectiveCartier := hJI.symm ▸ hCartier
    have : IsIso ((J.comap D'.subschemeι).blowupToBase) :=
      (isIso_blowupToBase_iff _).mpr hJ
    let a := asIso ((J.comap D'.subschemeι).blowupToBase) ≪≫ d.symm
    have ha : a.hom ≫ R.subschemeι ≫ hLift.hom = J.blowupMap D'.subschemeι := by
      apply J.eq_blowupMap
      simp only [Category.assoc, hLiftBase, a, Iso.trans_hom, asIso_hom,
        Iso.symm_hom]
      rw [← hd, Iso.inv_hom_id_assoc]
    rw [← ha, Scheme.Hom.ker_comp_of_isIso a.hom,
      Scheme.Hom.comap_ker_comp_of_isClosedImmersion R.subschemeι hLift.hom, ker_subschemeι]
  exact exists_toric_presentation_of_nodalTower_and_internal_blowdown b hΦ hc ρ c
    hT e he hB hN' hp (Scheme.Hom.mem_smoothLocus.mp hs) hU hLift
    (by rw [reassoc_of% hLiftBase, hg])
    (by rw [hStrict, support_radical])

local notation "I[" p "]" =>
  vanishingIdeal (TopologicalSpace.Closeds.closure ({p} : Set X))
local notation "π[" p "]" => blowupToBase (I[p])
local notation "R[" p "]" => radical (comap D (π[p]))

include hΦ hc in
/-- A toric presentation pulls back through the blowup of a boundary node followed
by the contraction of the strict transform of a closed subscheme omitted by the
boundary. In a ruled elementary transformation the closed subscheme is the ruling
fiber. The original node contributes one nodal blowup, and the image of the
contracted strict transform contributes the last internal center. -/
theorem exists_toric_presentation_of_nodal_blowup_and_strict_transform_contraction
    (hD : D.IsEffectiveCartier)
    (hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S))
    (hK : LineBundleClass.mk hD.toInvertibleSheaf = K[X])
    {p : X} (hp : IsClosed ({p} : Set X)) (hn : D.IsNodeOfReducedBoundary (X ↘ S) p)
    (F : X.IdealSheafData) (hF : ¬ F.support ≤ D.support)
    (g : (I[p]).blowup ⟶ Y) (hg : g ≫ Y ↘ S = π[p] ≫ X ↘ S)
    {q : Y} (hq : IsClosed ({q} : Set Y))
    (u : (I[p]).blowup ≅ (J[q]).blowup) (hu : u.hom ≫ (J[q]).blowupToBase = g)
    (hqF : (J[q]).comap g = ((I[p]).blowupMap F.subschemeι).ker)
    {n : ℕ} {W : Scheme} {T : BlowupTower Y n W}
    (hT : IsNodalBoundaryTower ((R[p]).map g) (Y ↘ S) (𝟙 Y) T)
    (e : (P).1 ≅ W)
    (he : e.hom ≫ T.toBase ≫ Y ↘ S = (P).2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap)
    (hB : ((((R[p]).map g).comap T.toBase).comap e.hom).radical = (P).2.boundaryι.ker) :
    ∃ (r : Φ.Ray) (a : ℂˣ) (W' : Scheme) (T' : BlowupTower X (1 + n) W'),
      IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T' ∧
      let P' := internalBlowupTower b (Fin.snoc ρ r) (Fin.snoc c a)
      ∃ d : P'.1 ≅ W',
        d.hom ≫ T'.toBase ≫ X ↘ S = P'.2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap ∧
        ((D.comap T'.toBase).comap d.hom).radical = P'.2.boundaryι.ker := by
  let U : BlowupTower X 1 (I[p]).blowup := .snoc .nil (I[p])
  have hU : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) U :=
    .snoc .nil p hp (X.ker_fromSpecResidueField_eq_vanishingIdeal p).symm
      (by simpa only [toBase_nil, Category.id_comp, comap_id] using hn)
  have hπ : U.toBase = π[p] := by simp [U]
  have hI : (I[p]).support ≤ D.support :=
    support_antitone (((D.le_ker_fromSpecResidueField_iff_mem_support hp).mpr
      (mem_support_of_isNodeOfReducedBoundary hn)).trans_eq
        (X.ker_fromSpecResidueField_eq_vanishingIdeal p))
  have hG : ¬ ((J[q]).comap g).support ≤ (D.comap U.toBase).support := by
    simpa only [hπ, hqF, support_ker_blowupMap_subschemeι_le_comap_iff, Set.sdiff_subset_iff,
      Set.union_eq_right.mpr (SetLike.coe_subset_coe.mpr hI), SetLike.coe_subset_coe] using hF
  exact exists_toric_presentation_of_internal_contraction_after_nodal_tower b hΦ hc ρ c
    hD hN hK hU g (hπ.symm ▸ hg) hq u hu hG (by rwa [hπ]) e he (by rwa [hπ])

end TauCeti.Toric.Fan

open TauCeti.Toric

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  (b : Module.Basis (Fin 2) ℤ N)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "K[" X "]" => LineBundleClass.mk (canonicalBundle ℂ X 2)
local notation "J[" x "]" => Scheme.Hom.ker (Scheme.fromSpecResidueField _ x)
local notation "T[" x "]" => BlowupTower.nil.snoc J[x]

/-- If a nodal blowup is followed by an internal contraction, a toric
presentation of the schematic image of the reduced total boundary gives
a toric presentation of the original pair. -/
theorem hasToricPresentation_of_nodal_blowup_and_internal_contraction
    {X Y : Scheme} [X.Over S] [Y.Over S] [IsIntegral X] [IsIntegral Y]
    [X.IsProjectiveOver ℂ] [Y.IsProjectiveOver ℂ]
    [SmoothOfRelativeDimension 2 (X ↘ S)] [SmoothOfRelativeDimension 2 (Y ↘ S)]
    {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ S)] (hD : D.IsEffectiveCartier)
    (hK : LineBundleClass.mk hD.toInvertibleSheaf = K[X])
    {x : X} (hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T[x])
    {y : Y} (hy : IsClosed ({y} : Set Y)) (u : J[x].blowup ≅ J[y].blowup) :
    let g := u.hom ≫ J[y].blowupToBase
    let R := (D.comap J[x].blowupToBase).radical
    g ≫ Y ↘ S = J[x].blowupToBase ≫ X ↘ S →
    ¬ (J[y].comap g).support ≤ R.support →
    (R.map g).HasToricPresentation (Y ↘ S) b i →
    D.HasToricPresentation (X ↘ S) b i := by
  intro g R hg hOmit h
  have hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S) := by
    rw [← D.over_eq_subschemeι_comp]
    exact PrestableFamily.atWorstNodalOfRelativeDimensionOne
  let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  let : IsNoetherian Y := isNoetherian_of_finiteType (Y ↘ S)
  have hπ : T[x].toBase = J[x].blowupToBase := by simp
  obtain ⟨n, ⟨Φ, hΦ, hc, r, c, l, W, U, hU, e, he, hB⟩⟩ := (hasToricPresentation_iff ..).mp h
  let : Nonempty Φ.cones := hc.nonempty_cones
  obtain ⟨r', c', Z', T', hT', d, hd, hD'⟩ :=
    Fan.exists_toric_presentation_of_internal_contraction_after_nodal_tower b hΦ hc r c hD hN hK
      hT g (by rwa [hπ]) hy u rfl (by simpa only [hπ, R, support_radical] using hOmit)
      (by rwa [hπ]) e he (by rwa [hπ, radical_comap_of_isOpenImmersion])
  exact ToricPresentation.hasToricPresentation (r := n + 1)
    ⟨Φ, hΦ, hc, Fin.snoc r r', Fin.snoc c c', 1 + l, Z', T', hT', d, hd,
      by rwa [← radical_comap_of_isOpenImmersion]⟩

end AlgebraicGeometry.Scheme.IdealSheafData
