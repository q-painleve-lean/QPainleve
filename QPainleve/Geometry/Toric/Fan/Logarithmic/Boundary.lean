/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Presentation
public import QPainleve.Geometry.Toric.Fan.Boundary.CycleAction

import QPainleve.AlgebraicGeometry.IdealSheaf.BaseChange
import QPainleve.Geometry.Toric.Fan.Boundary.DualGraph
import QPainleve.Geometry.Toric.Fan.Boundary.Prestable
import QPainleve.Geometry.Toric.Fan.Boundary.PositiveRefinement
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective
import QPainleve.Geometry.Toric.Fan.TorusAction.Branches

/-!
# Boundary orientation in ordered toric models

The strict boundary of an ordered internal tower inherits the orientation of the
rays in the toric frame. The same resolving surface can carry several such models.
The comparison on its numbered branches records the sign of a frame change and
is multiplicative through intermediate numberings. The link comparisons use
the branch actions of fan equivalences, translations, and the elementary
transformation of [Gross, Hacking and Keel, §3.1][GHK].

[GHK]: https://arxiv.org/html/1309.2573v2#S3.SS1
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory DihedralGroup Module Multiplicative QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan.LogarithmicProjection.OrderedToricModel

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Z : Scheme}
local notation "S" => Spec (CommRingCat.of k₀)

variable [Z.Over (Spec (.of k₀))] [SmoothOfRelativeDimension 2 (Z ↘ Spec (.of k₀))]
  {D : Z.IdealSheafData} {A B : LogarithmicProjection k₀ i D} {m l : ℕ}

local notation "C[" U "]" => Scheme.IdealSheafData.subscheme
  (Fan.toricBoundaryIdeal k₀ (OrderedToricModel.fan U) inferInstance)

/-- The strict boundary of an ordered model is identified with the pole boundary
on the resolving surface. -/
def boundaryIso (U : OrderedToricModel A m) : C[U] ≅ D.subscheme :=
  (D.exists_iso_of_comap_eq_ker U.iso U.tower.2.boundaryι U.pole_eq).choose

omit [IsAlgClosed k₀] in
/-- The strict boundary identification commutes with the embedding into the resolving surface. -/
@[reassoc]
theorem boundaryIso_hom_subschemeι (U : OrderedToricModel A m) :
    U.boundaryIso.hom ≫ D.subschemeι = U.tower.2.boundaryι ≫ U.iso.hom :=
  (D.exists_iso_of_comap_eq_ker U.iso U.tower.2.boundaryι U.pole_eq).choose_spec

omit [IsAlgClosed k₀] in
/-- The strict boundary identification is inverse to the refined projection on the boundary. -/
@[reassoc]
theorem boundaryIso_hom_subschemeι_comp_hom (U : OrderedToricModel A m) :
    U.boundaryIso.hom ≫ D.subschemeι ≫ U.hom =
      (U.fan.toricBoundaryIdeal k₀ inferInstance).subschemeι := by
  rw [U.boundaryIso_hom_subschemeι_assoc, U.hom_def, Iso.hom_inv_id_assoc,
    WithBoundary.boundaryι_toBase]

/-- The strict boundary identification respects the ground field. -/
instance (U : OrderedToricModel A m) : U.boundaryIso.hom.IsOver S := ⟨by
  rw [D.over_eq_subschemeι_comp, ← comp_over U.hom S, U.boundaryIso_hom_subschemeι_comp_hom_assoc,
    ← Scheme.IdealSheafData.over_eq_subschemeι_comp]⟩

omit [IsAlgClosed k₀] in
/-- A comparison of the refined projections gives the same comparison on the strict boundaries. -/
theorem boundaryIso_trans_of_hom_comp (U : OrderedToricModel A m) (W : OrderedToricModel B l)
    (e : C[U] ≅ C[W]) {f : (U.fan.finiteFanScheme k₀) ⟶ (W.fan.finiteFanScheme k₀)}
    (hf : U.hom ≫ f = W.hom)
    (he : e.hom ≫ (W.fan.toricBoundaryIdeal k₀ inferInstance).subschemeι =
      (U.fan.toricBoundaryIdeal k₀ inferInstance).subschemeι ≫ f) :
    e ≪≫ W.boundaryIso = U.boundaryIso := by
  have heq : U.boundaryIso.hom ≫ D.subschemeι ≫ W.hom =
      e.hom ≫ (W.fan.toricBoundaryIdeal k₀ inferInstance).subschemeι := by
    rw [he, ← hf, U.boundaryIso_hom_subschemeι_comp_hom_assoc]
  have hh : e.hom = U.boundaryIso.hom ≫ W.boundaryIso.inv := by
    apply (cancel_mono (W.fan.toricBoundaryIdeal k₀ inferInstance).subschemeι).mp
    rw [heq.symm, Category.assoc, ← W.boundaryIso_hom_subschemeι_comp_hom,
      Iso.inv_hom_id_assoc]
  ext
  simp [hh]

/-- The resolving boundary in an ordered toric model is a prestable curve. -/
theorem prestableFamily_resolvingBoundary (U : OrderedToricModel A m) :
    PrestableFamily (D.subscheme ↘ S) := by
  have hc := U.subdivision.isComplete_iff.mpr A.isComplete
  let : (U.fan.finiteFanScheme k₀).IsProjectiveOver k₀ :=
    U.fan.isProjectiveOver_finiteFanScheme_of_isComplete k₀ U.regular hc U.basis
  have hproper : IsProper (U.fan.finiteFanSchemeToSpec k₀) := by
    rw [← U.fan.finiteFanScheme_over k₀]
    infer_instance
  have hpre := U.fan.prestableFamily_boundary k₀ U.regular hc
    ((Module.finrank_eq_card_basis U.basis).trans (Fintype.card_fin 2))
  refine (MorphismProperty.cancel_left_of_respectsIso (P := @PrestableFamily)
    U.boundaryIso.hom _).mp ?_
  rw [comp_over]
  exact hpre

variable [PrestableFamily (D.subscheme ↘ Spec (.of k₀))]

omit [IsAlgClosed k₀] in
/-- The toric boundary is prestable because it is isomorphic to the resolving boundary. -/
theorem prestableFamily_boundary (U : OrderedToricModel A m) :
    PrestableFamily (C[U] ↘ S) := by
  rw [← comp_over U.boundaryIso.hom S]
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @PrestableFamily)
    U.boundaryIso.hom _).mpr inferInstance

local notation "Cycle[" k "," X "," n "]" => Scheme.NodalCycleNumbering
  (@Empty.elim (Scheme.Hom.smoothLocus (X ↘ Spec (CommRingCat.of k)))) n

/-- A numbering on the resolving boundary is positive in an ordered model when
it is induced by a positive cyclic numbering of the toric rays in the model's frame. -/
def IsPositiveBoundaryNumbering (U : OrderedToricModel A m) {n : ℕ} [NeZero n]
    (T : Cycle[k₀,D.subscheme,n]) : Prop :=
  let := U.prestableFamily_boundary
  ∃ (P : Cycle[k₀,C[U],n]) (u : ZMod n ≃ U.fan.Ray),
    T = U.boundaryIso.mapNodalCycleNumbering P ∧
      (∀ j, P.component j = U.fan.boundaryNormalizationComponentEquiv k₀ U.regular (u j)) ∧
      ∀ j, U.basis.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1 ∧
        ∃ σ : U.fan.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ

/-- A numbered toric cycle with positively ordered adjacent rays induces a
positive numbering of the resolving boundary. -/
theorem isPositiveBoundaryNumbering_map_boundaryIso (U : OrderedToricModel A m)
    {n : ℕ} [NeZero n] :
    let := U.prestableFamily_boundary
    ∀ (P : Cycle[k₀,C[U],n]) (u : ZMod n ≃ U.fan.Ray),
      (∀ j, P.component j = U.fan.boundaryNormalizationComponentEquiv k₀ U.regular (u j)) →
      (∀ j, U.basis.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1 ∧
        ∃ σ : U.fan.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ) →
      U.IsPositiveBoundaryNumbering (U.boundaryIso.mapNodalCycleNumbering P) :=
  fun P u hP hu ↦ ⟨P, u, rfl, hP, hu⟩

/-- The resolving boundary admits a positive numbering in the model's lattice frame. -/
theorem exists_isPositiveBoundaryNumbering (U : OrderedToricModel A m) :
    ∃ (n : ℕ) (_ : NeZero n) (T : Cycle[k₀,D.subscheme,n]),
      U.IsPositiveBoundaryNumbering T := by
  let := U.prestableFamily_boundary
  have hc := U.subdivision.isComplete_iff.mpr A.isComplete
  have : Nontrivial N := U.basis.equivFun.toEquiv.nontrivial
  obtain ⟨ρ⟩ := U.fan.nonempty_ray_of_isComplete hc
  let : Nonempty U.fan.Ray := ⟨ρ⟩
  let : NeZero (Nat.card U.fan.Ray) := ⟨Nat.card_pos.ne'⟩
  obtain ⟨u, ⟨-, hu⟩, -⟩ := U.fan.existsUnique_cyclicRayNumbering U.basis U.regular hc ρ
  obtain ⟨edge, order, vertex, hend, hcomp, -⟩ :=
    U.fan.exists_toric_boundary_dualGraph_cycle k₀ U.regular hc Empty.elim U.basis u hu
  let P : Cycle[k₀,C[U],Nat.card U.fan.Ray] := ⟨vertex, edge, order, hend⟩
  have hP (j : ZMod (Nat.card U.fan.Ray)) :
      P.component j = U.fan.boundaryNormalizationComponentEquiv k₀ U.regular (u j) := by
    rw [P.component_apply]
    exact hcomp j
  exact ⟨_, inferInstance, _, U.isPositiveBoundaryNumbering_map_boundaryIso P u hP hu⟩

section Subdivision

variable {Y : Scheme} [Y.Over (Spec (.of k₀))] [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k₀))]
  {E : Y.IdealSheafData} {B' : LogarithmicProjection k₀ i E}

/-- A fan subdivision in the same frame lifts a positive boundary numbering
to a positive numbering on the finer model. Its map on the resolving
boundaries is an oriented subdivision. -/
theorem exists_positiveBoundaryNumbering_of_subdivision
    [PrestableFamily (E.subscheme ↘ S)]
    (U : OrderedToricModel A m) (V : OrderedToricModel B' l)
    (H : V.fan.IsSubdivision U.fan) (hb : V.basis = U.basis)
    {f : Y ⟶ Z} {g : E.subscheme ⟶ D.subscheme}
    (hf : f ≫ U.hom = V.hom ≫ (H.toFanHom.finiteFanSchemeHom k₀))
    (hg : g ≫ D.subschemeι = E.subschemeι ≫ f)
    {k : ℕ} [NeZero k] {P : Cycle[k₀,D.subscheme,k]} (hP : U.IsPositiveBoundaryNumbering P) :
    ∃ (j : ℕ) (_ : NeZero j) (Q : Cycle[k₀,E.subscheme,j]),
      V.IsPositiveBoundaryNumbering Q ∧ g.IsOrientedCycleSubdivision Q P := by
  obtain ⟨P₀, u, rfl, hu, hpos⟩ := hP
  let : PrestableFamily ((U.fan.toricBoundaryIdeal k₀ inferInstance).subscheme ↘ S) :=
    U.prestableFamily_boundary
  obtain ⟨_, j, hj, hLift⟩ := H.exists_positive_boundary_subdivision_numbering k₀
    (δ := Empty) U.basis U.regular V.regular (U.subdivision.isComplete_iff.mpr A.isComplete)
    P₀ u hu hpos (u 0)
  let : PrestableFamily ((V.fan.toricBoundaryIdeal k₀ inferInstance).subscheme ↘ S) :=
    V.prestableFamily_boundary
  let : NeZero j := hj
  obtain ⟨Q₀, v, hQ₀, -, hv, hpos'⟩ := hLift Empty.elim
  let Q : Cycle[k₀,E.subscheme,j] := V.boundaryIso.mapNodalCycleNumbering Q₀
  have hQ : V.IsPositiveBoundaryNumbering Q :=
    V.isPositiveBoundaryNumbering_map_boundaryIso Q₀ v hv (by rwa [hb])
  let : V.boundaryIso.symm.hom.IsOver S := inferInstanceAs (V.boundaryIso.inv.IsOver S)
  have hact : V.boundaryIso.boundaryCycleAction Q₀ Q = 1 :=
    V.boundaryIso.boundaryCycleAction_mapNodalCycleNumbering (q := Empty.elim) Q₀
  have hleft := V.boundaryIso.symm.isOrientedCycleSubdivision_of_cycleOrientationSign_eq_one
    Q Q₀ (by rw [V.boundaryIso.boundaryCycleAction_symm Q₀ Q, hact, inv_one, map_one])
  have hp : U.boundaryIso.boundaryCycleAction P₀
      (U.boundaryIso.mapNodalCycleNumbering P₀ (q := Empty.elim)) = 1 :=
    U.boundaryIso.boundaryCycleAction_mapNodalCycleNumbering (q := Empty.elim) P₀
  have hright := U.boundaryIso.isOrientedCycleSubdivision_of_cycleOrientationSign_eq_one
    P₀ (U.boundaryIso.mapNodalCycleNumbering P₀ (q := Empty.elim)) (by
      rw [hp, map_one])
  have hg' :
      V.boundaryIso.hom ≫ g = H.boundaryMap k₀ inferInstance inferInstance ≫ U.boundaryIso.hom := by
    rw [← cancel_mono U.boundaryIso.inv,
      ← cancel_mono (U.fan.toricBoundaryIdeal k₀ inferInstance).subschemeι]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, IsSubdivision.boundaryMap_comp_subschemeι]
    rw [← U.boundaryIso_hom_subschemeι_comp_hom, Iso.inv_hom_id_assoc, reassoc_of% hg, hf,
      V.boundaryIso_hom_subschemeι_comp_hom_assoc]
  refine ⟨j, hj, Q, hQ, ?_⟩
  rw [← V.boundaryIso.inv_hom_id_assoc g, hg']
  exact hleft.comp (hQ₀.comp hright)

end Subdivision

variable {n : ℕ} [NeZero n] {U : OrderedToricModel A m} {W : OrderedToricModel B l}
  {T T' : Cycle[k₀,D.subscheme,n]}

local instance (X : Scheme) [X.Over S] : (Iso.refl X).hom.IsOver S := by
  rw [Iso.refl_hom]
  infer_instance

local instance {X Y W : Scheme} [X.Over S] [Y.Over S] [W.Over S] (e : X ≅ Y) (f : Y ≅ W)
    [e.hom.IsOver S] [f.hom.IsOver S] : (e ≪≫ f).hom.IsOver S := by
  rw [Iso.trans_hom]
  infer_instance

/-- Compute the action on the resolving boundary in the two toric numberings. -/
theorem boundaryCycleAction_map_boundaryIso (U : OrderedToricModel A m)
    (W : OrderedToricModel B l) (e : C[U] ≅ C[W]) [e.hom.IsOver S]
    (he : e ≪≫ W.boundaryIso = U.boundaryIso) :
    let := U.prestableFamily_boundary
    let := W.prestableFamily_boundary
    ∀ (P : Cycle[k₀,C[U],n]) (Q : Cycle[k₀,C[W],n]),
      (Iso.refl D.subscheme).boundaryCycleAction
        (U.boundaryIso.mapNodalCycleNumbering P (q := Empty.elim))
        (W.boundaryIso.mapNodalCycleNumbering Q (q := Empty.elim)) =
      e.boundaryCycleAction P Q := by
  intro _ _ P Q
  have h := Iso.boundaryCycleAction_trans e P Q W.boundaryIso
    (W.boundaryIso.mapNodalCycleNumbering Q (q := Empty.elim))
  have hW := W.boundaryIso.boundaryCycleAction_mapNodalCycleNumbering (q := Empty.elim) Q
  rw [hW, one_mul] at h
  have h' := Iso.boundaryCycleAction_trans U.boundaryIso P
    (U.boundaryIso.mapNodalCycleNumbering P (q := Empty.elim)) (Iso.refl D.subscheme)
    (W.boundaryIso.mapNodalCycleNumbering Q (q := Empty.elim))
  have hU := U.boundaryIso.boundaryCycleAction_mapNodalCycleNumbering (q := Empty.elim) P
  rw [hU, mul_one] at h'
  exact h'.symm.trans ((Iso.boundaryCycleAction_congr (k := k₀) _ _ _ _ (Iso.trans_refl _)).trans
    ((Iso.boundaryCycleAction_congr (k := k₀) _ _ _ _ he.symm).trans h))

/-- A positive numbering of the same resolving boundary can be chosen with the
length of any given numbering of that boundary. -/
theorem exists_isPositiveBoundaryNumbering_of_numbering (U : OrderedToricModel A m)
    (T : Cycle[k₀,D.subscheme,n]) :
    ∃ T' : Cycle[k₀,D.subscheme,n], U.IsPositiveBoundaryNumbering T' := by
  obtain ⟨n', h, T', hT'⟩ := U.exists_isPositiveBoundaryNumbering
  obtain rfl := (Iso.refl D.subscheme).nodalCycleNumbering_length_eq T T'
  exact ⟨T', hT'⟩

/-- For two ordered models related by a translated fan isomorphism, the sign
on the actual numbered branches is the determinant in the two specified frames. -/
private theorem IsPositiveBoundaryNumbering.cycleOrientationSign_of_toricIso
    (hT : U.IsPositiveBoundaryNumbering T) (hT' : W.IsPositiveBoundaryNumbering T')
    (f : FanEquiv U.fan W.fan) (χ : Multiplicative (N →+ ℤ) →* k₀ˣ)
    (hf : U.hom ≫ (f.toFanHom.finiteFanSchemeHom k₀) ≫ (W.fan.torusTranslationIso k₀ χ).hom = W.hom)
    (η : ℤˣ)
    (hdet : ∀ x y, W.basis.detDualEquiv (f.latticeEquiv x) (f.latticeEquiv y) =
      (η : ℤ) * U.basis.detDualEquiv x y) :
    cycleOrientationSign ((Iso.refl D.subscheme).boundaryCycleAction T T') = η := by
  let _ := U.prestableFamily_boundary
  let _ := W.prestableFamily_boundary
  obtain ⟨P, u, rfl, hP, hu⟩ := hT
  obtain ⟨Q, v, rfl, hQ, hv⟩ := hT'
  let g := f.boundaryIso k₀ inferInstance inferInstance
  let t := W.fan.boundaryTranslation k₀ χ
  have he : (g ≪≫ t) ≪≫ W.boundaryIso = U.boundaryIso := by
    apply U.boundaryIso_trans_of_hom_comp W (g ≪≫ t) hf
    simp only [g, t, Iso.trans_hom, Category.assoc, Fan.boundaryTranslation_hom_subschemeι,
      FanEquiv.boundaryIso_hom_subschemeι_assoc]
  have ht : t.boundaryCycleAction Q Q = 1 :=
    W.fan.boundaryCycleAction_boundaryTranslation k₀ W.regular
      (W.subdivision.isComplete_iff.mpr B.isComplete)
      ((Module.finrank_eq_card_basis W.basis).trans (Fintype.card_fin 2)) Q χ
  have hgt := g.boundaryCycleAction_trans P Q t Q
  refine (congrArg cycleOrientationSign (U.boundaryCycleAction_map_boundaryIso W
    (g ≪≫ t) he P Q)).trans ?_
  rw [hgt, ht, one_mul]
  have hs := f.cycleOrientationSign_boundaryIso k₀ U.regular W.regular P Q hP hQ U.basis W.basis
    (fun j ↦ (hu j).1) (fun j ↦ (hv j).1)
  rcases Int.units_eq_one_or η with rfl | rfl
  · exact hs false (by simpa only [Units.val_one, one_mul, Bool.false_eq_true, ↓reduceIte]
      using hdet)
  · exact hs true (by simpa only [Units.val_neg, Units.val_one, neg_one_mul, ↓reduceIte]
      using hdet)

omit [PrestableFamily (D.subscheme ↘ Spec (.of k₀))] in
/-- The sign comparing the ordered branches in the lattice frames of two models
of the same resolving boundary. -/
def HasBoundarySign (U : OrderedToricModel A m) (W : OrderedToricModel B l) (η : ℤˣ) : Prop :=
  let := U.prestableFamily_resolvingBoundary
  ∀ {n : ℕ} [NeZero n] {T T' : Cycle[k₀,D.subscheme,n]},
    U.IsPositiveBoundaryNumbering T → W.IsPositiveBoundaryNumbering T' →
    cycleOrientationSign ((Iso.refl D.subscheme).boundaryCycleAction T T') = η

/-- A comparison of frames computes the sign on any induced positive numberings. -/
theorem HasBoundarySign.cycleOrientationSign_eq {η : ℤˣ} (h : U.HasBoundarySign W η)
    (hT : U.IsPositiveBoundaryNumbering T) (hT' : W.IsPositiveBoundaryNumbering T') :
    cycleOrientationSign ((Iso.refl D.subscheme).boundaryCycleAction T T') = η :=
  h hT hT'

section CommonSubdivision

variable {Y : Scheme} [Y.Over (Spec (.of k₀))] [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k₀))]
  {E : Y.IdealSheafData} {A' B' : LogarithmicProjection k₀ i E}

omit [PrestableFamily (D.subscheme ↘ Spec (.of k₀))] in
/-- When both models are subdivided above the same map of resolving surfaces,
the sign comparing the fine models is the sign comparing the original models. -/
theorem HasBoundarySign.of_common_subdivision
    {U : OrderedToricModel A m} {T : OrderedToricModel B l}
    {m' l' : ℕ} {U' : OrderedToricModel A' m'} {T' : OrderedToricModel B' l'}
    {η : ℤˣ} (hη : U'.HasBoundarySign T' η)
    (H : U'.fan.IsSubdivision U.fan) (K : T'.fan.IsSubdivision T.fan)
    (hU : U'.basis = U.basis) (hT : T'.basis = T.basis)
    {f : Y ⟶ Z} [f.IsOver S] (hle : D.comap f ≤ E)
    (hfU : f ≫ U.hom = U'.hom ≫ (H.toFanHom.finiteFanSchemeHom k₀))
    (hfT : f ≫ T.hom = T'.hom ≫ (K.toFanHom.finiteFanSchemeHom k₀)) : U.HasBoundarySign T η := by
  let : PrestableFamily (D.subscheme ↘ S) := U.prestableFamily_resolvingBoundary
  let : PrestableFamily (E.subscheme ↘ S) := U'.prestableFamily_resolvingBoundary
  intro k hk P Q hP hQ
  let g := subschemeMap E D f (le_map_iff_comap_le.mpr hle)
  have hg := subschemeMap_subschemeι E D f (le_map_iff_comap_le.mpr hle)
  have : g.IsOver S := ⟨by
    rw [D.over_eq_subschemeι_comp, ← Category.assoc, hg, Category.assoc, comp_over f S,
      ← E.over_eq_subschemeι_comp]⟩
  obtain ⟨r, hr, P', hP', hgP⟩ :=
    U.exists_positiveBoundaryNumbering_of_subdivision U' H hU hfU hg hP
  obtain ⟨r', hr', Q', hQ', hgQ⟩ :=
    T.exists_positiveBoundaryNumbering_of_subdivision T' K hT hfT hg hQ
  let : (Iso.refl D.subscheme).hom.IsOver S := ⟨Category.id_comp _⟩
  let : (Iso.refl E.subscheme).hom.IsOver S := ⟨Category.id_comp _⟩
  obtain rfl := (Iso.refl E.subscheme).nodalCycleNumbering_length_eq P' Q'
  have hsq : CommSq (Iso.refl E.subscheme).hom g g (Iso.refl D.subscheme).hom := by
    constructor
    simp
  exact ((Iso.refl D.subscheme).cycleOrientationSign_eq_of_orientedCycleSubdivisions P Q P' Q'
    (Iso.refl E.subscheme) hgP hgQ hsq).trans (hη.cycleOrientationSign_eq hP' hQ')

end CommonSubdivision

omit [PrestableFamily (D.subscheme ↘ Spec (.of k₀))] in
/-- A sign comparison on the toric boundaries gives the same sign on the
resolving boundary when their embeddings commute. -/
theorem hasBoundarySign_of_boundaryIso (U : OrderedToricModel A m) (W : OrderedToricModel B l)
    (e : C[U] ≅ C[W]) [e.hom.IsOver S]
    (he : e.hom ≫ W.tower.2.boundaryι ≫ W.iso.hom = U.tower.2.boundaryι ≫ U.iso.hom)
    (η : ℤˣ)
    (hs : let := U.prestableFamily_resolvingBoundary
      let := U.prestableFamily_boundary
      let := W.prestableFamily_boundary
      ∀ {n : ℕ} [NeZero n] (P : Cycle[k₀,C[U],n]) (Q : Cycle[k₀,C[W],n])
        (u : ZMod n ≃ U.fan.Ray) (v : ZMod n ≃ W.fan.Ray),
        (∀ j, P.component j = U.fan.boundaryNormalizationComponentEquiv k₀ U.regular (u j)) →
        (∀ j, Q.component j = W.fan.boundaryNormalizationComponentEquiv k₀ W.regular (v j)) →
        (∀ j, U.basis.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1 ∧
          ∃ σ : U.fan.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ) →
        (∀ j, W.basis.detDualEquiv (v j).primitiveGenerator (v (j + 1)).primitiveGenerator = 1) →
        cycleOrientationSign (e.boundaryCycleAction P Q) = η) :
    U.HasBoundarySign W η := by
  let := U.prestableFamily_resolvingBoundary
  let := U.prestableFamily_boundary
  let := W.prestableFamily_boundary
  intro n hn T T' hT hT'
  obtain ⟨P, u, rfl, hP, hu⟩ := hT
  obtain ⟨Q, v, rfl, hQ, hv⟩ := hT'
  have h : e ≪≫ W.boundaryIso = U.boundaryIso := by
    apply Iso.ext
    apply (cancel_mono D.subschemeι).mp
    simpa only [Iso.trans_hom, Category.assoc, boundaryIso_hom_subschemeι] using he
  exact (congrArg cycleOrientationSign (U.boundaryCycleAction_map_boundaryIso W e h P Q)).trans
    (hs P Q u v hP hQ hu (fun j ↦ (hv j).1))

omit [PrestableFamily (D.subscheme ↘ Spec (.of k₀))] in
/-- A translated fan equivalence gives the sign of the determinant in the two frames. -/
theorem hasBoundarySign_of_toricIso (U : OrderedToricModel A m) (W : OrderedToricModel B l)
    (f : FanEquiv U.fan W.fan) (χ : Multiplicative (N →+ ℤ) →* k₀ˣ)
    (hf : U.hom ≫ (f.toFanHom.finiteFanSchemeHom k₀) ≫ (W.fan.torusTranslationIso k₀ χ).hom = W.hom)
    (η : ℤˣ)
    (hdet : ∀ x y, W.basis.detDualEquiv (f.latticeEquiv x) (f.latticeEquiv y) =
      (η : ℤ) * U.basis.detDualEquiv x y) : U.HasBoundarySign W η := by
  let := U.prestableFamily_resolvingBoundary
  intro n hn T T' hT hT'
  exact hT.cycleOrientationSign_of_toricIso hT' f χ hf η hdet

omit [PrestableFamily (D.subscheme ↘ Spec (.of k₀))] in
/-- Reading the resolving boundary twice in the same frame preserves its orientation. -/
theorem HasBoundarySign.refl (U : OrderedToricModel A m) : U.HasBoundarySign U 1 := by
  apply U.hasBoundarySign_of_toricIso U (FanEquiv.refl U.fan) 1
  · simp only [FanEquiv.toFanHom_refl, FanHom.finiteFanSchemeHom_id, Fan.torusTranslationIso_one,
      Iso.refl_hom, Category.comp_id]
  · simp

omit [PrestableFamily (D.subscheme ↘ Spec (.of k₀))] in
/-- The signs of successive comparisons of the resolving boundary multiply. -/
theorem HasBoundarySign.trans {C : LogarithmicProjection k₀ i D} {k : ℕ}
    {M : OrderedToricModel C k}
    {η θ : ℤˣ} (h : U.HasBoundarySign M η) (h' : M.HasBoundarySign W θ) :
    U.HasBoundarySign W (η * θ) := by
  let := U.prestableFamily_resolvingBoundary
  intro n hn T T' hT hT'
  obtain ⟨T₀, hT₀⟩ := M.exists_isPositiveBoundaryNumbering_of_numbering T
  let e := Iso.refl D.subscheme
  have he := e.boundaryCycleAction_trans T T₀ e T'
  have he' := (e ≪≫ e).boundaryCycleAction_congr T T' e (Iso.trans_refl _)
  rw [he'] at he
  apply (congrArg cycleOrientationSign he).trans
  rw [map_mul, h.cycleOrientationSign_eq hT hT₀, h'.cycleOrientationSign_eq hT₀ hT', mul_comm]

omit [PrestableFamily (D.subscheme ↘ Spec (.of k₀))] in
/-- Two models determine at most one comparison sign. -/
theorem HasBoundarySign.unique {η θ : ℤˣ} (h : U.HasBoundarySign W η)
    (h' : U.HasBoundarySign W θ) : η = θ := by
  let := U.prestableFamily_resolvingBoundary
  obtain ⟨n, hn, T, hT⟩ := U.exists_isPositiveBoundaryNumbering
  obtain ⟨T', hT'⟩ := W.exists_isPositiveBoundaryNumbering_of_numbering T
  exact (h.cycleOrientationSign_eq hT hT').symm.trans (h'.cycleOrientationSign_eq hT hT')

end TauCeti.Toric.Fan.LogarithmicProjection.OrderedToricModel
