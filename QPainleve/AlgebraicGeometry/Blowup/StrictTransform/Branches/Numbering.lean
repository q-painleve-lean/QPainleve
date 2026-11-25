/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Branches.Subdivision
public import TauCeti.AlgebraicGeometry.Curves.Node.Reduced

import Mathlib.SetTheory.Cardinal.NatCard
import TauCeti.Data.ZMod.FinEquiv
import TauCeti.Logic.Equiv.Fin.Basic

/-!
# Descending cycle numberings through a nodal blowdown

Deleting the exceptional component splices together the two attachment nodes.
The ordered branches of the resulting node come from the strict branches of
the two attachments, including when those strict branches lie on the same
normalized component. This is the inverse of the boundary subdivision used
in [Gross, Hacking and Keel, *Mirror symmetry for log Calabi–Yau surfaces I*, §1][GHK].

[GHK]: https://arxiv.org/html/1106.4977v3#S1
-/

public noncomputable section

open CategoryTheory TopologicalSpace TauCeti TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [IsIntegral X] [QuasiCompact (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  {D : X.IdealSheafData} [D.subscheme.Over (Spec (.of k))]
  [PrestableFamily (D.subscheme ↘ Spec (.of k))]
  {p : D.subscheme} (hc : IsClosed ({D.subschemeι p} : Set X))

local notation "S" => Spec (CommRingCat.of k)
local notation "C" => IdealSheafData.subscheme D
local notation "I" =>
  vanishingIdeal (Closeds.mk (closure ({D.subschemeι p} : Set X)) isClosed_closure)
local notation "π" => blowupToBase (I)
local notation "R" => radical (D.comap (π))
local notation "B" => subscheme (R)
local notation "β" => subschemeMap (R) D (π) (le_map_iff_comap_le.mpr (le_radical _))
local notation "J[" T "]" => Scheme.singularLocus k T
local notation "N[" T "]" => blowup J[T]
local notation "b[" T "]" => Scheme.branchSchemeToBlowup k T
local notation "α[" T "]" => Scheme.branchSchemeToSingularLocus k T
local notation "nodal[" T "]" =>
  PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := T ↘ S)

variable [(D.comap (vanishingIdeal
  ⟨closure ({D.subschemeι p} : Set X), isClosed_closure⟩).blowupToBase).radical.subscheme.Over
    (Spec (.of k))]
  [PrestableFamily ((D.comap (vanishingIdeal
    ⟨closure ({D.subschemeι p} : Set X), isClosed_closure⟩).blowupToBase).radical.subscheme ↘
      Spec (.of k))]
  (hp : p ∈ (D.subscheme.singularLocus k).support)
  (hCOver : D.subscheme ↘ Spec (.of k) = D.subschemeι ≫ X ↘ Spec (.of k))
  (hBOver :
    (D.comap (vanishingIdeal
      ⟨closure ({D.subschemeι p} : Set X), isClosed_closure⟩).blowupToBase).radical.subscheme ↘
        Spec (.of k) =
      (D.comap (vanishingIdeal
        ⟨closure ({D.subschemeι p} : Set X), isClosed_closure⟩).blowupToBase).radical.subschemeι ≫
        (vanishingIdeal ⟨closure ({D.subschemeι p} : Set X), isClosed_closure⟩).blowupToBase ≫
        X ↘ Spec (.of k))
  (hD : D.IsEffectiveCartier)

local notation "exc" => hD.exceptionalNormalizationComponent (k := k) hc
local notation "s" => D.normalizationToNodalBlowup hc hp hCOver hBOver
local notation "strict" => D.strictNormalizationBranch hc hp hCOver hBOver hD
local notation "exceptional" => D.exceptionalSideBranch hc hp hCOver hBOver hD
local notation "components" => D.strictNormalizationComponentEquiv hc hp hCOver hBOver hD
local notation "branches" => D.normalizationBranchEquiv hc hp hCOver hBOver hD

-- Indices start immediately after the exceptional component and stop just before it.
private def survivingIndices {n : ℕ} [NeZero n] (t : ZMod (n + 1)) :
    ZMod n ≃ {j : ZMod (n + 1) // j ≠ t} :=
  (ZMod.finEquiv n).symm.toEquiv.trans <|
    (finSuccAboveEquiv (Fin.last n)).trans <|
      ((ZMod.finEquiv (n + 1)).toEquiv.trans (Equiv.addRight (t + 1))).subtypeEquiv (by
        intro j
        have hsum : (n : ZMod (n + 1)) + 1 = 0 := by
          exact_mod_cast ZMod.natCast_self (n + 1)
        have hlast : (ZMod.finEquiv (n + 1)) (Fin.last n) + (t + 1) = t := by
          rw [ZMod.finEquiv_apply, Fin.val_last, add_left_comm, hsum, add_zero]
        let e := (ZMod.finEquiv (n + 1)).toEquiv.trans (Equiv.addRight (t + 1))
        have he : e (Fin.last n) = t := hlast
        exact not_congr (e.injective.eq_iff.symm.trans (by rw [he])))

private theorem survivingIndices_val {n : ℕ} [NeZero n] (t : ZMod (n + 1)) (j : ZMod n) :
    (survivingIndices t j).val = (j.val : ZMod (n + 1)) + (t + 1) := by
  simp [survivingIndices, add_assoc]

private theorem survivingIndices_succ_sub_one {n : ℕ} [NeZero n]
    (t : ZMod (n + 1)) (j : ZMod n) :
    (survivingIndices t (j + 1)).val - 1 =
      if j.val + 1 = n then t else (survivingIndices t j).val := by
  have hj := ZMod.val_lt j
  have hcast : j + 1 = ((j.val + 1 : ℕ) : ZMod n) := by
    rw [Nat.cast_add, ZMod.natCast_zmod_val, Nat.cast_one]
  rw [hcast]
  by_cases h : j.val + 1 = n
  · rw [ite_eq_left h, survivingIndices_val, h, ZMod.natCast_self, ZMod.val_zero, Nat.cast_zero,
      zero_add, add_sub_cancel_right]
  · rw [ite_eq_right h, survivingIndices_val, ZMod.val_natCast_of_lt (by omega),
      survivingIndices_val, Nat.cast_succ]
    ring

section Branches

variable [IsReduced D.subscheme]

private theorem exceptional_branch_mem_component
    (q : {q : (C).branchScheme k // (J[C]).subschemeι ((α[C]) q) = p}) :
    (b[B]) ((exceptional) q) ∈ ((exc) : Set N[B]) := by
  rw [D.branchSchemeToBlowup_exceptionalSideBranch, ← (B).coe_blowupComponent]
  exact (hD.exceptionalNormalizationBranchEquiv hc hCOver hBOver hp q).property.1

private theorem exceptional_branch_projection
    (q : {q : (C).branchScheme k // (J[C]).subschemeι ((α[C]) q) = p}) :
    (β) ((J[B]).subschemeι ((α[B]) ((exceptional) q))) = p := by
  rw [D.branchSchemeToSingularLocus_exceptionalSideBranch, D.boundaryMap_strictBranch_node]
  exact q.property

private theorem existsUnique_strictBranch (q : (B).branchScheme k)
    (hq : (b[B]) q ∉ ((exc) : Set N[B])) :
    ∃! a, (strict) a = q := by
  obtain ⟨a, ha⟩ := (branches).surjective q
  cases a with
  | inl a =>
    rw [D.normalizationBranchEquiv_inl] at ha
    exact ⟨a, ha, fun z hz ↦ Sum.inl_injective
      ((branches).injective (by simpa only [D.normalizationBranchEquiv_inl, ha] using hz))⟩
  | inr a =>
    rw [D.normalizationBranchEquiv_inr] at ha
    exact (hq (ha ▸ exceptional_branch_mem_component hc hp hCOver hBOver hD a)).elim

end Branches

-- The second flag is the incoming flag on the next surviving component.
private def survivingFlag {n : ℕ} [NeZero n] (t : ZMod (n + 1))
    (j : ZMod n) (b : Fin 2) : ZMod (n + 1) × Fin 2 :=
  (if b = 0 then (survivingIndices t j).val else (survivingIndices t (j + 1)).val - 1, b)

private theorem survivingFlag_zero {n : ℕ} [NeZero n] (t : ZMod (n + 1))
    (j : ZMod n) : survivingFlag t j 0 = ((survivingIndices t j).val, 0) := by
  simp [survivingFlag]

private theorem survivingFlag_one {n : ℕ} [NeZero n] (t : ZMod (n + 1))
    (j : ZMod n) : survivingFlag t j 1 =
      (if j.val + 1 = n then t else (survivingIndices t j).val, 1) := by
  have h : (1 : Fin 2) ≠ 0 := by decide
  simp only [survivingFlag, h, ite_false, survivingIndices_succ_sub_one]

private theorem endpoint_survivingFlag {n : ℕ} [NeZero n] (t : ZMod (n + 1))
    (j : ZMod n) (b : Fin 2) :
    (DualGraph.cycle (n + 1)).endpoint (survivingFlag t j b).1 b =
      (survivingIndices t ((DualGraph.cycle n).endpoint j b)).val := by
  fin_cases b <;> simp [survivingFlag, DualGraph.cycle]

private theorem survivingFlag_injective {n : ℕ} [NeZero n] (t : ZMod (n + 1)) :
    Function.Injective (fun x : ZMod n × Fin 2 ↦ survivingFlag t x.1 x.2) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  have hab : a = b := congrArg Prod.snd h
  subst b
  have h' : (DualGraph.cycle (n + 1)).endpoint (survivingFlag t i a).1 a =
      (DualGraph.cycle (n + 1)).endpoint (survivingFlag t j a).1 a :=
    congrArg (fun z : ZMod (n + 1) × Fin 2 ↦ (DualGraph.cycle (n + 1)).endpoint z.1 a) h
  rw [endpoint_survivingFlag, endpoint_survivingFlag] at h'
  have he := (survivingIndices t).injective (Subtype.ext h')
  congr 1
  fin_cases a <;> simpa [DualGraph.cycle] using he

private theorem exists_survivingFlag {n : ℕ} [NeZero n] {t i : ZMod (n + 1)} {a : Fin 2}
    (h : (DualGraph.cycle (n + 1)).endpoint i a ≠ t) :
    ∃ j : ZMod n, survivingFlag t j a = (i, a) := by
  obtain ⟨j, hj⟩ := (survivingIndices t).surjective ⟨_, h⟩
  have hv := congrArg Subtype.val hj
  fin_cases a
  · exact ⟨j, by simpa [survivingFlag, DualGraph.cycle] using hv⟩
  · have hs : (survivingIndices t j).val = i + 1 := by simpa [DualGraph.cycle] using hv
    exact ⟨j - 1, by simp [survivingFlag, hs]⟩

section Numbering

variable {n : ℕ} [NeZero n] {ι : Type*}
  {pB : ι → ((D.comap (vanishingIdeal
    ⟨closure ({D.subschemeι p} : Set X), isClosed_closure⟩).blowupToBase).radical.subscheme ↘
      Spec (.of k)).smoothLocus}
  (A : Scheme.NodalCycleNumbering pB (n + 1)) (t : ZMod (n + 1))

section Reduced

variable [IsReduced D.subscheme]
  (ht : A.component t = hD.exceptionalNormalizationComponent (k := k) hc)

omit [D.subscheme.Over (Spec (.of k))] [PrestableFamily (D.subscheme ↘ Spec (.of k))]
  [NeZero n] in
include ht in
private theorem branch_notMem_exceptional (i : ZMod (n + 1)) (a : Fin 2) :
    (b[B]) (A.branch (i, a)) ∉ ((exc) : Set N[B]) ↔
      (DualGraph.cycle (n + 1)).endpoint i a ≠ t := by
  rw [← ht, A.branchSchemeToBlowup_branch_mem_component_iff, A.component.injective.eq_iff]

private def descendedBranchWithProof (j : ZMod n) (a : Fin 2) :
    {q : (C).branchScheme k // (strict) q = A.branch (survivingFlag t j a)} := by
  apply Classical.indefiniteDescription
  apply (existsUnique_strictBranch hc hp hCOver hBOver hD _ ?_).exists
  apply (branch_notMem_exceptional hc hD A t ht _ _).mpr
  exact (endpoint_survivingFlag t j a).symm ▸ (survivingIndices t _).property

private abbrev descendedBranch (j : ZMod n) (a : Fin 2) : (C).branchScheme k :=
  (descendedBranchWithProof hc hp hCOver hBOver hD A t ht j a).val

private theorem strictNormalizationBranch_descendedBranch (j : ZMod n) (a : Fin 2) :
    (strict) (descendedBranch hc hp hCOver hBOver hD A t ht j a) =
      A.branch (survivingFlag t j a) :=
  (descendedBranchWithProof hc hp hCOver hBOver hD A t ht j a).property

private theorem descendedBranch_injective :
    Function.Injective (fun x : ZMod n × Fin 2 ↦
      descendedBranch hc hp hCOver hBOver hD A t ht x.1 x.2) := by
  intro x y h
  apply survivingFlag_injective t
  apply A.branch.injective
  simpa only [strictNormalizationBranch_descendedBranch] using congrArg (strict) h

private theorem descendedBranch_surjective :
    Function.Surjective (fun x : ZMod n × Fin 2 ↦
      descendedBranch hc hp hCOver hBOver hD A t ht x.1 x.2) := by
  intro q
  obtain ⟨⟨i, a⟩, hq⟩ := A.branch.surjective ((strict) q)
  have hne : (b[B]) ((strict) q) ∉ ((exc) : Set N[B]) := by
    rw [D.branchSchemeToBlowup_strictNormalizationBranch]
    exact (D.range_normalizationToNodalBlowup hc hp hCOver hBOver hD).le ⟨_, rfl⟩
  have h := (branch_notMem_exceptional hc hD A t ht i a).mp (hq ▸ hne)
  obtain ⟨j, hj⟩ := exists_survivingFlag h
  refine ⟨(j, a), ?_⟩
  exact (existsUnique_strictBranch hc hp hCOver hBOver hD _ hne).unique
    ((strictNormalizationBranch_descendedBranch hc hp hCOver hBOver hD A t ht j a).trans
      (congrArg A.branch hj |>.trans hq)) rfl

omit [NeZero n] in
include hp hCOver hBOver ht in
private theorem exists_exceptionalSideBranch (i : ZMod (n + 1)) (a : Fin 2)
    (ha : (DualGraph.cycle (n + 1)).endpoint i a = t) :
    ∃ q, (exceptional) q = A.branch (i, a) := by
  obtain ⟨q, hq⟩ := (branches).surjective (A.branch (i, a))
  cases q with
  | inl q =>
    rw [D.normalizationBranchEquiv_inl] at hq
    have hn : ¬ (b[B]) (A.branch (i, a)) ∉ ((exc) : Set N[B]) :=
      fun hm ↦ (branch_notMem_exceptional hc hD A t ht i a).mp hm ha
    rw [← hq, D.branchSchemeToBlowup_strictNormalizationBranch] at hn
    exact absurd ((D.range_normalizationToNodalBlowup hc hp hCOver hBOver hD).le ⟨_, rfl⟩) hn
  | inr q => exact ⟨q, by simpa only [D.normalizationBranchEquiv_inr] using hq⟩

omit [NeZero n] in
include hp hCOver hBOver ht in
private theorem image_node_of_exceptional_endpoint (i : ZMod (n + 1)) (a : Fin 2)
    (ha : (DualGraph.cycle (n + 1)).endpoint i a = t) :
    (β) ((J[B]).subschemeι (A.node i)) = p := by
  obtain ⟨q, hq⟩ := exists_exceptionalSideBranch hc hp hCOver hBOver hD A t ht i a ha
  simpa only [hq, A.branchSchemeToSingularLocus_branch] using
    exceptional_branch_projection hc hp hCOver hBOver hD q

private theorem descendedBranch_projection (j : ZMod n) (a : Fin 2) :
    (J[C]).subschemeι ((α[C]) (descendedBranch hc hp hCOver hBOver hD A t ht j a)) =
      (β) ((J[B]).subschemeι (A.node (survivingFlag t j a).1)) := by
  rw [← D.boundaryMap_strictBranch_node hc hp hCOver hBOver hD,
    strictNormalizationBranch_descendedBranch, A.branchSchemeToSingularLocus_branch]

private theorem survivingIndices_eq_pred_of_last (j : ZMod n) (hj : j.val + 1 = n) :
    (survivingIndices t j).val = t - 1 := by
  have h : (j.val : ZMod (n + 1)) + 1 + 1 = 0 := by
    have hh : j.val + 1 + 1 = n + 1 := by omega
    have hh' : ((j.val + 1 + 1 : ℕ) : ZMod (n + 1)) = 0 := by rw [hh, ZMod.natCast_self]
    simpa only [Nat.cast_add, Nat.cast_one] using hh'
  rw [survivingIndices_val]
  linear_combination h

private theorem descendedBranch_same_node (j : ZMod n) (a : Fin 2) :
    (α[C]) (descendedBranch hc hp hCOver hBOver hD A t ht j a) =
      (α[C]) (descendedBranch hc hp hCOver hBOver hD A t ht j 0) := by
  have ha : a = 0 ∨ a = 1 := by fin_cases a <;> decide
  rcases ha with rfl | rfl
  · rfl
  · apply (J[C]).subschemeι.injective
    rw [descendedBranch_projection, descendedBranch_projection]
    rw [survivingFlag_one, survivingFlag_zero]
    split_ifs with hj
    · rw [survivingIndices_eq_pred_of_last t j hj]
      exact (image_node_of_exceptional_endpoint hc hp hCOver hBOver hD A t ht t 0
        (by simp [DualGraph.cycle])).trans
        (image_node_of_exceptional_endpoint hc hp hCOver hBOver hD A t ht (t - 1) 1
          (by simp [DualGraph.cycle])).symm
    · rfl

local notation "branchAt" => descendedBranch hc hp hCOver hBOver hD A t ht
local notation "nodeAt" => fun j : ZMod n ↦ (α[C]) ((branchAt) j 0)

private def descendedBranchOrder {q : Type*} (pC : q → (C ↘ S).smoothLocus) (j : ZMod n) :
    Fin 2 ≃ {a : (C).branchScheme k // (α[C]) a = (nodeAt) j} := by
  let f (a : Fin 2) : {a : (C).branchScheme k // (α[C]) a = (nodeAt) j} :=
    ⟨(branchAt) j a, descendedBranch_same_node hc hp hCOver hBOver hD A t ht j a⟩
  have hf : Function.Injective f := fun a b hab ↦ congrArg Prod.snd
    (descendedBranch_injective hc hp hCOver hBOver hD A t ht
      (a₁ := (j, a)) (a₂ := (j, b)) (congrArg Subtype.val hab))
  let e := (C).branchOrderOfDualGraph pC (fun _ ↦ Equiv.refl _) ((nodeAt) j)
  exact (Equiv.ofBijective (e.symm ∘ f) (e.symm.injective.comp hf).bijective_of_finite).trans e

private theorem descendedBranchOrder_apply {q : Type*} (pC : q → (C ↘ S).smoothLocus)
    (j : ZMod n) (a : Fin 2) :
    (descendedBranchOrder hc hp hCOver hBOver hD A t ht pC j a).val = (branchAt) j a := by
  simp [descendedBranchOrder]

private def descendedNodes {q : Type*} (pC : q → (C ↘ S).smoothLocus) :
    ZMod n ≃ (J[C]).subscheme := by
  refine Equiv.ofBijective (nodeAt) ⟨?_, ?_⟩
  · intro i j h
    let a := descendedBranchOrder hc hp hCOver hBOver hD A t ht pC i
    obtain ⟨b, hb⟩ := a.surjective ⟨(branchAt) j 0, h.symm⟩
    have hb' := congrArg Subtype.val hb
    rw [descendedBranchOrder_apply] at hb'
    exact congrArg Prod.fst (descendedBranch_injective hc hp hCOver hBOver hD A t ht
      (a₁ := (i, b)) (a₂ := (j, 0)) hb')
  · intro z
    let e := (C).branchOrderOfDualGraph pC (fun _ ↦ Equiv.refl _) z
    obtain ⟨⟨j, b⟩, h⟩ := descendedBranch_surjective hc hp hCOver hBOver hD A t ht (e 0).val
    exact ⟨j, (descendedBranch_same_node hc hp hCOver hBOver hD A t ht j b).symm.trans
      ((congrArg (α[C]) h).trans (e 0).property)⟩

private def descendedComponents : ZMod n ≃ irreducibleComponents N[C] :=
  (survivingIndices t).trans
    ((A.component.subtypeEquiv (fun j ↦ not_congr (by rw [← ht, A.component.injective.eq_iff])))
      |>.trans (components).symm)

private theorem descendedComponent_strict (j : ZMod n) :
    ((components) (descendedComponents hc hp hCOver hBOver hD A t ht j)).val =
      A.component (survivingIndices t j).val := by
  simp [descendedComponents]

private theorem descendedBranch_mem_component (j : ZMod n) (a : Fin 2) :
    (b[C]) ((branchAt) j a) ∈ ((descendedComponents hc hp hCOver hBOver hD A t ht
      ((DualGraph.cycle n).endpoint j a)) : Set N[C]) := by
  let y := (b[C]) ((branchAt) j a)
  have h : (s) y ∈ (A.component (survivingIndices t ((DualGraph.cycle n).endpoint j a)).val :
      Set N[B]) := by
    dsimp only [y]
    rw [← D.branchSchemeToBlowup_strictNormalizationBranch hc hp hCOver hBOver hD,
      strictNormalizationBranch_descendedBranch]
    exact (A.branchSchemeToBlowup_branch_mem_component_iff _ _ _).mpr
      (congrArg A.component (endpoint_survivingFlag t j a))
  let v := irreducibleComponentOf y
  have hv := D.normalizationToNodalBlowup_mem_strictNormalizationComponentEquiv
    hc hp hCOver hBOver hD v (mem_irreducibleComponentOf y)
  have : IsRegular N[B] := (B).isRegular_blowup_singularLocus nodal[B]
  have he := (irreducibleComponentOf_eq_iff.mpr hv).symm.trans (irreducibleComponentOf_eq_iff.mpr h)
  rw [← descendedComponent_strict hc hp hCOver hBOver hD A t ht] at he
  have hv' := (components).injective (Subtype.ext he)
  exact hv' ▸ mem_irreducibleComponentOf y

variable {q : Type*} (pC : q → (D.subscheme ↘ (Spec (.of k))).smoothLocus)

local notation "nodes" => descendedNodes hc hp hCOver hBOver hD A t ht pC
local notation "vertices" => descendedComponents hc hp hCOver hBOver hD A t ht
private def descendedEdges : ZMod n ≃ ((C).dualGraph pC).Edge :=
  (nodes).trans ((C).dualGraphNodeEquiv pC).symm

local notation "edges" => descendedEdges hc hp hCOver hBOver hD A t ht pC

private def descendedOrder (e : ((C).dualGraph pC).Edge) : Equiv.Perm (Fin 2) :=
  let j := (edges).symm e
  (descendedBranchOrder hc hp hCOver hBOver hD A t ht pC j).trans
    ((C).branchOrderOfDualGraph pC (fun _ ↦ Equiv.refl _) ((nodeAt) j)).symm

private theorem dualGraphBranchEquiv_descendedOrder (j : ZMod n) (a : Fin 2) :
    (C).dualGraphBranchEquiv pC ((edges) j, descendedOrder hc hp hCOver hBOver hD A t ht
      pC ((edges) j) a) = (branchAt) j a := by
  have hn : (C).dualGraphNodeEquiv pC ((edges) j) = (nodeAt) j := by
    simp only [descendedEdges, Equiv.trans_apply, Equiv.apply_symm_apply, descendedNodes]
    rfl
  have hflag := (C).branchOrderOfDualGraph_apply_val pC (fun _ ↦ Equiv.refl _) ((edges) j)
    (descendedOrder hc hp hCOver hBOver hD A t ht pC ((edges) j) a)
  rw [hn, Equiv.refl_apply] at hflag
  rw [← hflag]
  have hi := (edges).symm_apply_apply j
  rw [descendedOrder, hi, Equiv.trans_apply, Equiv.apply_symm_apply, descendedBranchOrder_apply]

private def descendedNumbering : Scheme.NodalCycleNumbering pC n where
  vertex := (vertices).trans ((C).dualGraphVertexEquiv pC).symm
  edge := edges
  order := descendedOrder hc hp hCOver hBOver hD A t ht pC
  endpoint_eq j a := by
    apply ((C).dualGraphVertexEquiv pC).injective
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    apply ((C).dualGraphVertexEquiv_endpoint_eq_iff pC _ _ _).mpr
    rw [← (C).branchSchemeToBlowup_dualGraphBranchEquiv, dualGraphBranchEquiv_descendedOrder]
    exact descendedBranch_mem_component hc hp hCOver hBOver hD A t ht j a

local notation "numbering" => descendedNumbering hc hp hCOver hBOver hD A t ht pC

private theorem descendedNumbering_node (j : ZMod n) : (numbering).node j = (nodes) j := by
  rw [Scheme.NodalCycleNumbering.node_apply]
  simp [descendedNumbering, descendedEdges]

private theorem descendedNumbering_component (j : ZMod n) :
    (numbering).component j = (vertices) j := by
  rw [Scheme.NodalCycleNumbering.component_apply]
  simp [descendedNumbering]

private theorem descendedNumbering_branch (j : ZMod n) (a : Fin 2) :
    (numbering).branch (j, a) = (branchAt) j a := by
  rw [Scheme.NodalCycleNumbering.branch_eq_branchOrderOfDualGraph,
    Scheme.NodalCycleNumbering.node_apply, (C).branchOrderOfDualGraph_apply_val]
  exact dualGraphBranchEquiv_descendedOrder hc hp hCOver hBOver hD A t ht pC j a

private def precedingIndex (n : ℕ) : ZMod n := ((n - 1 : ℕ) : ZMod n)

private theorem precedingIndex_is_last : (precedingIndex n).val + 1 = n := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  rw [precedingIndex, ZMod.val_natCast_of_lt (by omega)]
  omega

private theorem eq_precedingIndex_of_last {j : ZMod n} (hj : j.val + 1 = n) :
    j = precedingIndex n :=
  ZMod.val_injective n (by have := precedingIndex_is_last (n := n); omega)

private theorem descendedNumbering_isOrientedCycleSubdivision :
    (β).IsOrientedCycleSubdivision A (numbering) := by
  let j₀ := precedingIndex n
  have hj₀ : j₀.val + 1 = n := precedingIndex_is_last (n := n)
  let q₀ : {q : (C).branchScheme k // (J[C]).subschemeι ((α[C]) q) = p} :=
    ⟨(branchAt) j₀ 1, by
      rw [descendedBranch_projection, survivingFlag_one, ite_eq_left hj₀]
      exact image_node_of_exceptional_endpoint hc hp hCOver hBOver hD A t ht t 0
        (by simp [DualGraph.cycle])⟩
  obtain ⟨g, hg, hstr, hexc⟩ := D.exists_nodalBlowupNormalizationLift hc hp hCOver hBOver hD q₀
  let keep : (J[C]).subscheme ↪ (J[B]).subscheme :=
    ((numbering).node.symm.toEmbedding.trans ((survivingIndices t).toEmbedding.trans
      (Function.Embedding.subtype _))).trans A.node.toEmbedding
  have hstrict (j : ZMod n) (a : Fin 2) :
      g ((b[B]) (A.branch (survivingFlag t j a))) = (b[C]) ((branchAt) j a) := by
    rw [← strictNormalizationBranch_descendedBranch hc hp hCOver hBOver hD A t ht, hstr]
  refine ⟨g, hg, D.mapsTo_support_singularLocus_nodalBlowup nodal[C] hc hCOver hBOver hp nodal[B],
    keep, ?_, ?_⟩
  · intro z a
    obtain ⟨j, rfl⟩ := (numbering).node.surjective z
    have hk : keep ((numbering).node j) = A.node (survivingIndices t j).val := by simp [keep]
    rw [hk, ← A.branch_eq_branchOrderOfDualGraph,
      ← (numbering).branch_eq_branchOrderOfDualGraph, descendedNumbering_branch]
    have hcases : a = 0 ∨ a = 1 := by fin_cases a <;> decide
    rcases hcases with rfl | rfl
    · simpa only [survivingFlag_zero] using hstrict j 0
    · by_cases hj : j.val + 1 = n
      · rw [eq_precedingIndex_of_last hj, survivingIndices_eq_pred_of_last t j₀ hj₀]
        obtain ⟨q, hq⟩ := exists_exceptionalSideBranch hc hp hCOver hBOver hD A t ht (t - 1) 1
          (by simp [DualGraph.cycle])
        rw [← hq, hexc q]
      · simpa only [survivingFlag_one, ite_eq_right hj] using hstrict j 1
  · intro z hz
    obtain ⟨j, rfl⟩ := A.node.surjective z
    have hj : j = t := by
      by_contra! hn
      obtain ⟨l, hl⟩ := (survivingIndices t).surjective ⟨j, hn⟩
      refine hz ⟨(numbering).node l, ?_⟩
      simpa [keep] using congrArg A.node (congrArg Subtype.val hl)
    subst j
    rw [← A.branch_eq_branchOrderOfDualGraph, ← A.branch_eq_branchOrderOfDualGraph]
    obtain ⟨q, hq⟩ := exists_exceptionalSideBranch hc hp hCOver hBOver hD A t ht t 0
      (by simp [DualGraph.cycle])
    rw [← hq, hexc q]
    simpa only [survivingFlag_one, ite_eq_left hj₀] using hstrict j₀ 1

end Reduced

variable {q : Type*} (pC : q → (D.subscheme ↘ (Spec (.of k))).smoothLocus)

/-- Descend the numbering through the contraction of component `t`.
The target starts at the first surviving component after `t`. At the new node
the first branch comes from the incoming attachment and the second from the
outgoing attachment, including when the target has one component. -/
theorem exists_numbering_of_nodal_boundary_blowdown_at :
    let : IsReduced (C) := nodal[C].isReduced
    A.component t = (exc) →
    ∃ L : Scheme.NodalCycleNumbering pC n, (β).IsOrientedCycleSubdivision A L ∧
      (∀ j, ((components) (L.component j)).val =
        A.component ((j.val : ZMod (n + 1)) + (t + 1))) ∧
      (∀ (j : ZMod n) (a : Fin 2), (strict) (L.branch (j, a)) = A.branch
        (if j.val + 1 = n ∧ a = 1 then t else (j.val : ZMod (n + 1)) + (t + 1), a)) := by
  intro hred ht
  let : IsReduced (C) := hred
  refine ⟨descendedNumbering hc hp hCOver hBOver hD A t ht pC, ?_, ?_, ?_⟩
  · exact descendedNumbering_isOrientedCycleSubdivision hc hp hCOver hBOver hD A t ht pC
  · intro j
    rw [descendedNumbering_component, descendedComponent_strict, survivingIndices_val]
  · intro j a
    rw [descendedNumbering_branch, strictNormalizationBranch_descendedBranch]
    have hcases : a = 0 ∨ a = 1 := by fin_cases a <;> decide
    rcases hcases with rfl | rfl
    · simp [survivingFlag_zero, survivingIndices_val]
    · simp [survivingFlag_one, survivingIndices_val]

end Numbering

section ArbitraryLength

variable {m : ℕ} [NeZero m] {ι : Type*}
  {pB : ι → ((D.comap (vanishingIdeal
    ⟨closure ({D.subschemeι p} : Set X), isClosed_closure⟩).blowupToBase).radical.subscheme ↘
      Spec (.of k)).smoothLocus}
  (A : Scheme.NodalCycleNumbering pB m)
  {q : Type*} (pC : q → (D.subscheme ↘ (Spec (.of k))).smoothLocus)

variable [IsReduced D.subscheme] in
include hc hp hCOver hBOver hD A in
private theorem cycleLength_eq_succ_card_strict :
    NeZero (Nat.card (irreducibleComponents N[C])) ∧
      m = Nat.card (irreducibleComponents N[C]) + 1 := by
  classical
  let e := (Equiv.optionCongr (components)).trans (Equiv.optionSubtypeNe (exc))
  let e' := e.trans A.component.symm
  have : Finite (irreducibleComponents N[C]) :=
    Finite.of_injective (fun v ↦ e' (some v)) (e'.injective.comp (Option.some_injective _))
  -- The original normalization surjects onto the center, so some component survives.
  obtain ⟨x, -⟩ := ((C).surjective_blowupToBase_singularLocus nodal[C]).surj p
  let : Nonempty (irreducibleComponents N[C]) := ⟨irreducibleComponentOf x⟩
  refine ⟨⟨Nat.card_pos.ne'⟩, ?_⟩
  simpa only [Nat.card_zmod, Finite.card_option] using (Nat.card_congr e').symm

include hc hp hCOver hBOver hD in
/-- If the reduced total boundary over a node is a numbered cycle, the original
boundary is also a numbered cycle with one fewer component. The blowdown is
an oriented subdivision, so the ordered branches still determine the orientation
when the descended cycle has one or two components. -/
theorem exists_numbering_of_nodal_boundary_blowdown :
    ∃ n : ℕ, ∃ _ : NeZero n, m = n + 1 ∧
      ∃ L : Scheme.NodalCycleNumbering pC n, (β).IsOrientedCycleSubdivision A L := by
  have : IsReduced (C) := nodal[C].isReduced
  obtain ⟨hn, hm⟩ := cycleLength_eq_succ_card_strict hc hp hCOver hBOver hD A
  let n := Nat.card (irreducibleComponents N[C])
  have hm' : m = n + 1 := hm
  cases hm'
  obtain ⟨t, ht⟩ := A.component.surjective (exc)
  obtain ⟨L, hL, -, -⟩ := exists_numbering_of_nodal_boundary_blowdown_at
    hc hp hCOver hBOver hD A t pC ht
  exact ⟨n, hn, rfl, L, hL⟩

end ArbitraryLength

end AlgebraicGeometry.Scheme.IdealSheafData
