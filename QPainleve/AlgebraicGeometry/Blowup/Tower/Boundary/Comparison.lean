/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Split
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension

import Mathlib.Logic.Equiv.Fin.Basic
import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Recovery
import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Reorder
import QPainleve.AlgebraicGeometry.Blowup.Tower.IsoLocus
import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.Morphisms.Modification.IsoLocus
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyReduced

/-!
# Recovering ordered boundary centers from a projection

Two boundary blowup towers with isomorphic surfaces over the same smooth surface
have the same centers on the boundary, with multiplicity. The matching preserves
the order within each chain over a repeated center. It is obtained by removing
the first occurrence of a common center and comparing over its blowup.
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry TopologicalSpace
open Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower

variable {D X : Scheme.{u}} {i : D ⟶ X} [IsClosedImmersion i] {n m : ℕ}

local notation "I[" p "]" => Scheme.Hom.ker (Scheme.fromSpecResidueField D p)
local notation "C[" p "," h "]" => (fun j ↦ (Subtype.mk I[p j] (h j) :
  {J : D.IdealSheafData // J.IsEffectiveCartier}))
local notation "A[" i "," p "," h "]" => alongBoundary i C[p,h]
local notation "π[" A "]" => toBase (WithBoundary.toTower (Sigma.snd A))

variable {k : Type u} [Field k] [PerfectField k]
  (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 f] [IrreducibleSpace X]

omit [IrreducibleSpace X] in
include f in
private theorem range_eq_of_alongBoundary_iso
    (p : Fin n → D) (q : Fin m → D)
    (hp : ∀ j, IsClosed ({p j} : Set D)) (hq : ∀ j, IsClosed ({q j} : Set D))
    (hP : ∀ j, I[p j].IsEffectiveCartier) (hQ : ∀ j, I[q j].IsEffectiveCartier)
    (e : A[i,p,hP].1 ≅ A[i,q,hQ].1) (he : e.hom ≫ π[A[i,q,hQ]] = π[A[i,p,hP]]) :
    Set.range p = Set.range q := by
  let T := A[i,p,hP].2.toTower
  let U := A[i,q,hQ].2.toTower
  have hT : IsClosedPointTower X T :=
    isClosedPointTower_alongBoundary i C[p,hP] (fun j ↦ ⟨p j, hp j, rfl⟩)
  have hU : IsClosedPointTower X U :=
    isClosedPointTower_alongBoundary i C[q,hQ] (fun j ↦ ⟨q j, hq j, rfl⟩)
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : Smooth (U.toBase ≫ f) := (hU.smoothOfRelativeDimension f).smooth
  have : IsReduced A[i,q,hQ].1 := (U.toBase ≫ f).isReduced_of_smooth
  have := U.isProper_toBase
  have hc := e.hom.centre_comp U.toBase
  rw [(e.hom.centre_eq_empty_iff).mpr inferInstance, Set.image_empty, Set.union_empty, he,
    hT.centre_toBase_eq_range_baseCenter f, hU.centre_toBase_eq_range_baseCenter f] at hc
  have htp : hT.baseCenter = i ∘ p := funext (hT.baseCenter_alongBoundary p (fun _ ↦ rfl))
  have huq : hU.baseCenter = i ∘ q := funext (hU.baseCenter_alongBoundary q (fun _ ↦ rfl))
  rw [htp, huq, Set.range_comp, Set.range_comp] at hc
  exact i.injective.image_injective hc

omit [IrreducibleSpace X] in
private theorem exists_iso_alongBoundary_removeNth
    (p : Fin (n + 1) → D) (hp : ∀ j, IsClosed ({p j} : Set D))
    (hP : ∀ j, I[p j].IsEffectiveCartier) (l : Fin (n + 1))
    (hl : ∀ j < l, p j ≠ p l)
    (j : D ⟶ (I[p l].map i).blowup) [IsClosedImmersion j]
    (hj : j ≫ (I[p l].map i).blowupToBase = i) :
    let B := A[j, p ∘ l.succAbove, fun a ↦ hP (l.succAbove a)]
    ∃ e : A[i,p,hP].1 ≅ B.1,
      e.hom ≫ π[B] ≫ (I[p l].map i).blowupToBase = π[A[i,p,hP]] := by
  have hd (a : Fin (n + 1)) (ha : a < l) :
      Disjoint (I[p a].support : Set D) (I[p l].support : Set D) := by
    rw [D.support_ker_fromSpecResidueField_of_isClosed (hp a),
      D.support_ker_fromSpecResidueField_of_isClosed (hp l)]
    exact Set.disjoint_singleton.mpr (hl a ha)
  have hm := exists_iso_alongBoundary_move_to_front (i := i) C[p,hP] l hd
  dsimp only at hm
  rw [Fin.comp_cons] at hm
  obtain ⟨e, he, -, -⟩ := hm
  obtain ⟨a, ha, -, -⟩ :=
    exists_iso_alongBoundary_cons (i := i) (C[p,hP] l) rfl j hj (C[p,hP] ∘ l.succAbove)
  refine ⟨e ≪≫ a, ?_⟩
  rw [Iso.trans_hom, Category.assoc]
  exact (congrArg (e.hom ≫ ·) ha).trans he

include f in
private theorem exists_iso_between_alongBoundary_tails
    (p : Fin (n + 1) → D) (q : Fin (m + 1) → D)
    (hp : ∀ j, IsClosed ({p j} : Set D)) (hq : ∀ j, IsClosed ({q j} : Set D))
    (hP : ∀ j, I[p j].IsEffectiveCartier) (hQ : ∀ j, I[q j].IsEffectiveCartier)
    (e : A[i,p,hP].1 ≅ A[i,q,hQ].1) (he : e.hom ≫ π[A[i,q,hQ]] = π[A[i,p,hP]])
    (l : Fin (m + 1)) (hl : q l = p 0) (hfirst : ∀ a < l, q a ≠ q l) :
    let I := I[p 0].map i
    ∃ (j : D ⟶ I.blowup) (hj : IsClosedImmersion j)
      (_ : SmoothOfRelativeDimension 2 (I.blowupToBase ≫ f)) (_ : IrreducibleSpace I.blowup),
      letI := hj
      let A := alongBoundary j (C[p,hP] ∘ Fin.succ (n := n))
      let B := alongBoundary j (C[q,hQ] ∘ l.succAbove)
      ∃ a : A.1 ≅ B.1, a.hom ≫ π[B] = π[A] := by
  intro I
  have hC : (I.comap i).IsEffectiveCartier := by
    simpa only [I, comap_map_of_isClosedImmersion] using hP 0
  let j := I.blowupLift i hC
  have hj : IsClosedImmersion j := I.isClosedImmersion_blowupLift i hC
  have hji := I.blowupLift_blowupToBase i hC
  let g := I.blowupToBase
  have hclosed : IsClosed ({i (p 0)} : Set X) := by
    simpa only [Set.image_singleton] using i.isClosedEmbedding.isClosedMap _ (hp 0)
  have hpoint : IsClosedPointTower X (BlowupTower.nil.snoc I) :=
    .snoc .nil _ hclosed (i.map_ker_fromSpecResidueField (p 0))
  have hsm : SmoothOfRelativeDimension 2 (g ≫ f) := by
    simpa only [g, toBase_snoc, toBase_nil, Category.comp_id] using
      hpoint.smoothOfRelativeDimension f
  have : IsModification g := by
    simpa only [g, toBase_snoc, toBase_nil, Category.comp_id] using
      hpoint.isModification_of_smoothOfRelativeDimension_two f
  have hirr : IrreducibleSpace I.blowup := (IsModification.birational g).irreducibleSpace
  let A := alongBoundary j (C[p,hP] ∘ Fin.succ (n := n))
  let B := alongBoundary j (C[q,hQ] ∘ l.succAbove)
  obtain ⟨a, ha⟩ : ∃ a : A[i,p,hP].1 ≅ A.1, a.hom ≫ π[A] ≫ g = π[A[i,p,hP]] :=
    exists_iso_alongBoundary_removeNth (i := i) p hp hP 0
      (fun _ h ↦ (Fin.not_lt_zero _ h).elim) j hji
  have hb := exists_iso_alongBoundary_removeNth (i := i) q hq hQ l hfirst
  rw [hl] at hb
  obtain ⟨b, hb⟩ : ∃ b : A[i,q,hQ].1 ≅ B.1, b.hom ≫ π[B] ≫ g = π[A[i,q,hQ]] := hb j hji
  have hA := isClosedPointTower_alongBoundary j (C[p,hP] ∘ Fin.succ)
    (fun a ↦ ⟨p a.succ, hp a.succ, rfl⟩)
  have hB := isClosedPointTower_alongBoundary j (C[q,hQ] ∘ l.succAbove)
    (fun b ↦ ⟨q (l.succAbove b), hq (l.succAbove b), rfl⟩)
  have : IsModification π[A] := hA.isModification_of_smoothOfRelativeDimension_two (g ≫ f)
  have : IsModification π[B] := hB.isModification_of_smoothOfRelativeDimension_two (g ≫ f)
  have : IrreducibleSpace A.1 := (IsModification.birational π[A]).irreducibleSpace
  have : Smooth (π[A] ≫ g ≫ f) := (hA.smoothOfRelativeDimension (g ≫ f)).smooth
  have : IsReduced A.1 := (π[A] ≫ g ≫ f).isReduced_of_smooth
  have hab : (a.symm ≪≫ e ≪≫ b).hom ≫ π[B] ≫ g = π[A] ≫ g := by
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hb, he, ← ha, Iso.inv_hom_id_assoc]
  exact ⟨j, hj, hsm, hirr, a.symm ≪≫ e ≪≫ b, g.eq_of_comp_eq_of_isModification hab⟩

include f in
/-- An isomorphism of boundary blowup towers over a smooth irreducible surface matches
the lists of projected centers and preserves the order over each repeated point.
The lists may initially have different lengths. -/
theorem exists_reindex_alongBoundary_of_iso
    (p : Fin n → D) (q : Fin m → D)
    (hp : ∀ j, IsClosed ({p j} : Set D)) (hq : ∀ j, IsClosed ({q j} : Set D))
    (hP : ∀ j, I[p j].IsEffectiveCartier) (hQ : ∀ j, I[q j].IsEffectiveCartier)
    (e : A[i,p,hP].1 ≅ A[i,q,hQ].1) (he : e.hom ≫ π[A[i,q,hQ]] = π[A[i,p,hP]]) :
    ∃ σ : Fin n ≃ Fin m, q ∘ σ = p ∧
      ∀ a b, a < b → p a = p b → σ a < σ b := by
  induction n generalizing X m with
  | zero =>
    have hr := range_eq_of_alongBoundary_iso f p q hp hq hP hQ e he
    cases m with
    | zero => exact ⟨Equiv.refl _, funext fun a ↦ a.elim0, fun a ↦ a.elim0⟩
    | succ m =>
      have h : q 0 ∈ Set.range p := hr.symm ▸ Set.mem_range_self 0
      obtain ⟨j, -⟩ := h
      exact j.elim0
  | succ n ih =>
    have hr := range_eq_of_alongBoundary_iso f p q hp hq hP hQ e he
    have hmem : p 0 ∈ Set.range q := hr ▸ Set.mem_range_self 0
    cases m with
    | zero => simp at hmem
    | succ m =>
      obtain ⟨l, hl, hmin⟩ := (wellFounded_lt (α := Fin (m + 1))).has_min
        {a | q a = p 0} hmem
      have hlq : q l = p 0 := hl
      have hfirst (a : Fin (m + 1)) (ha : a < l) (h : q a = q l) : False :=
        hmin a (h.trans hlq) ha
      -- Work on the common blowup of the first center before matching the remaining labels.
      obtain ⟨j, _, _, _, a, ha⟩ :=
        exists_iso_between_alongBoundary_tails f p q hp hq hP hQ e he l hlq hfirst
      obtain ⟨τ, hτ, hord⟩ := ih ((I[p 0].map i).blowupToBase ≫ f)
        (i := j) (p ∘ Fin.succ) (q ∘ l.succAbove)
        (fun a ↦ hp a.succ) (fun b ↦ hq (l.succAbove b)) _ _ a ha
      -- Restore the matched first occurrence and retain the order in the remaining fibers.
      let σ := (finSuccEquiv n).trans ((Equiv.optionCongr τ).trans (finSuccEquiv' l).symm)
      have hσ₀ : σ 0 = l := by simp [σ]
      have hσ₁ (a : Fin n) : σ a.succ = l.succAbove (τ a) := by simp [σ]
      refine ⟨σ, ?_, ?_⟩
      · funext a
        cases a using Fin.cases with
        | zero => simpa only [Function.comp_apply, hσ₀] using hlq
        | succ a => simpa only [Function.comp_apply, hσ₁] using congrFun hτ a
      · intro a b hab heq
        cases b using Fin.cases with
        | zero => exact (Fin.not_lt_zero _ hab).elim
        | succ b =>
          cases a using Fin.cases with
          | zero =>
            rw [hσ₀, hσ₁]
            have hne := Fin.succAbove_ne l (τ b)
            have hqeq : q (l.succAbove (τ b)) = q l :=
              (congrFun hτ b).trans (heq.symm.trans hlq.symm)
            exact lt_of_le_of_ne (le_of_not_gt (fun h ↦ hfirst _ h hqeq)) hne.symm
          | succ a =>
            rw [hσ₁, hσ₁]
            exact Fin.strictMono_succAbove l (hord a b (Fin.succ_lt_succ_iff.mp hab) heq)

end QPainleve.BlowupTower
