/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.GenericPoint
public import QPainleve.AlgebraicGeometry.Curves.Node.Locus
public import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Primes
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic

import QPainleve.AlgebraicGeometry.Curves.Node.BoundaryRestriction
import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Map
import QPainleve.AlgebraicGeometry.Curves.Node.PointBlowup
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Dimension
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced

/-!
# Ambient primes of numbered nodal cycles

The component numbering of a nodal Cartier boundary numbers its ambient prime
divisors. The incidence of each numbered node is read from its two ordered
branches, including when both branches lie on the same component.
-/

public noncomputable section

open CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.IdealSheafData

universe u v

namespace AlgebraicGeometry.Scheme.NodalCycleNumbering

variable {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}} {D : X.IdealSheafData}
  [D.subscheme.Over (Spec (.of k))] [PrestableFamily (D.subscheme ↘ Spec (.of k))]
  {ι : Type v} {p : ι → (D.subscheme ↘ Spec (.of k)).smoothLocus} {n : ℕ} [NeZero n]

local notation "C" => D.subscheme
local notation "J" => Scheme.singularLocus k C
local notation "ν" => blowupToBase J

variable (A : NodalCycleNumbering p n)

/-- The point of the ambient scheme at the specified node of the boundary cycle. -/
def ambientNode (j : ZMod n) : X := D.subschemeι ((J).subschemeι (A.node j))

/-- The ambient image of the corresponding point of the singular subscheme. -/
theorem ambientNode_def (j : ZMod n) :
    A.ambientNode j = D.subschemeι ((J).subschemeι (A.node j)) := (rfl)

/-- Distinct numbered nodes give distinct points of the ambient scheme. -/
theorem ambientNode_injective : Function.Injective A.ambientNode :=
  D.subschemeι.injective.comp (J).subschemeι.injective |>.comp A.node.injective

/-- A numbered node is a closed point of the ambient scheme. -/
theorem isClosed_ambientNode (j : ZMod n) : IsClosed ({A.ambientNode j} : Set X) := by
  rw [ambientNode_def, ← Set.image_singleton]
  exact (D.subschemeι).isClosedMap _ ((C).isClosed_singleton_of_mem_singularLocus
    PrestableFamily.atWorstNodalOfRelativeDimensionOne ((J).range_subschemeι.le ⟨_, rfl⟩))

/-- The numbered point is a node of the reduced boundary in the ambient scheme. -/
theorem isNodeOfReducedBoundary_ambientNode [X.Over (Spec (.of k))] (j : ZMod n)
    (hOver : C ↘ Spec (.of k) = D.subschemeι ≫ X ↘ Spec (.of k)) :
    D.IsNodeOfReducedBoundary (X ↘ Spec (.of k)) (A.ambientNode j) := by
  have hn : AtWorstNodalOfRelativeDimensionOne (C ↘ Spec (.of k)) :=
    PrestableFamily.atWorstNodalOfRelativeDimensionOne
  have := hn.isReduced
  have := hn.syntomic
  apply (D.isNodeOfReducedBoundary_iff_of_isReduced _ _).mpr
  refine ⟨(J).subschemeι (A.node j), A.ambientNode_def j |>.symm, ?_⟩
  rw [← hOver]
  exact ((C ↘ Spec (.of k)).isNodeAt_iff_notMem_smoothLocus hn _).mpr
    (((C).mem_support_singularLocus_iff_notMem_smoothLocus _).mp
      ((J).range_subschemeι.le ⟨_, rfl⟩))

/-- Every node of the reduced boundary occurs in its cycle numbering. -/
theorem exists_ambientNode_eq [X.Over (Spec (.of k))] {x : X}
    (hx : D.IsNodeOfReducedBoundary (X ↘ Spec (.of k)) x)
    (hOver : C ↘ Spec (.of k) = D.subschemeι ≫ X ↘ Spec (.of k)) :
    ∃ j, A.ambientNode j = x := by
  have hn : AtWorstNodalOfRelativeDimensionOne (C ↘ Spec (.of k)) :=
    PrestableFamily.atWorstNodalOfRelativeDimensionOne
  have := hn.isReduced
  have := hn.syntomic
  obtain ⟨z, rfl, hz⟩ := (D.isNodeOfReducedBoundary_iff_of_isReduced _ _).mp hx
  rw [← hOver] at hz
  have hs := ((C).mem_support_singularLocus_iff_notMem_smoothLocus z).mpr
    (((C ↘ Spec (.of k)).isNodeAt_iff_notMem_smoothLocus hn z).mp hz)
  obtain ⟨q, rfl⟩ := (J).range_subschemeι.ge hs
  obtain ⟨j, rfl⟩ := A.node.surjective q
  exact ⟨j, A.ambientNode_def j⟩

variable [IsLocallyNoetherian X]

/-- The numbered normalized components give exactly the prime divisors of a Cartier boundary. -/
def boundaryPrimeEquiv (hD : D.IsEffectiveCartier) : ZMod n ≃ D.boundaryPrimes := by
  let f : ZMod n → D.boundaryPrimes := fun j ↦
    ⟨D.subschemeι (A.componentGenericPoint j), mem_boundaryPrimes.mpr
      ⟨D.range_subschemeι.le ⟨_, rfl⟩, hD.coheight_subschemeι_of_coheight_eq_zero
        (by rw [componentGenericPoint_def]; exact
          (C).coheight_blowupComponentGeneric (A.component j))⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b h
    exact A.componentGenericPoint_injective
      ((D.subschemeι).injective (congrArg (fun q : D.boundaryPrimes ↦ q.val) h))
  · intro q
    obtain ⟨v, hv⟩ := hD.exists_subschemeι_blowupComponentGeneric_eq (k := k)
      (p := D.boundaryPrimeEmbedding q) (by
        simpa only [coe_boundaryPrimeEmbedding] using (mem_boundaryPrimes.mp q.property).1)
    obtain ⟨j, rfl⟩ := A.component.surjective v
    exact ⟨j, Subtype.ext (by
      simpa only [f, componentGenericPoint_def, coe_boundaryPrimeEmbedding] using hv)⟩

/-- The ambient prime is the image of the numbered component's generic point. -/
@[simp]
theorem boundaryPrimeEquiv_apply_val (hD : D.IsEffectiveCartier) (j : ZMod n) :
    (A.boundaryPrimeEquiv hD j).val = D.subschemeι (A.componentGenericPoint j) := (rfl)

/-- The components through node `j` are the endpoints of its two ordered branches. -/
theorem ambientNode_mem_closure_boundaryPrime_iff (hD : D.IsEffectiveCartier) (j l : ZMod n) :
    A.ambientNode j ∈ closure {(A.boundaryPrimeEquiv hD l).val} ↔
      ∃ b : Fin 2, (TauCeti.DualGraph.cycle n).endpoint j b = l := by
  rw [boundaryPrimeEquiv_apply_val, componentGenericPoint_def,
    ← (C).range_blowupComponent_comp (A.component l) D.subschemeι (D.subschemeι).isClosedMap]
  have hnodal : AtWorstNodalOfRelativeDimensionOne (C ↘ Spec (.of k)) :=
    PrestableFamily.atWorstNodalOfRelativeDimensionOne
  have := hnodal.syntomic
  have hbranch (b : (C).branchScheme k) :
      ν ((C).branchSchemeToBlowup k b) = (J).subschemeι ((C).branchSchemeToSingularLocus k b) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      (C).branchSchemeToSingularLocus_subschemeι k]
  constructor
  · rintro ⟨x, hx⟩
    have hx' : ν x.val = (J).subschemeι (A.node j) := by
      apply (D.subschemeι).injective
      have hι : ((C).blowupComponent (A.component l)).ι x = x.val := (rfl)
      simpa only [Scheme.Hom.comp_apply, hι, ambientNode_def] using hx
    have hsing : ν x.val ∈ (J).support := hx'.symm ▸ (J).range_subschemeι.le ⟨_, rfl⟩
    obtain ⟨b, hb⟩ := ((C).range_branchSchemeToBlowup (k := k)).ge hsing
    obtain ⟨⟨a, i⟩, rfl⟩ := A.branch.surjective b
    rw [← hb, hbranch, A.branchSchemeToSingularLocus_branch] at hx'
    have h : a = j := A.node.injective ((J).subschemeι.injective hx')
    subst a
    have hm : (C).branchSchemeToBlowup k (A.branch (j, i)) ∈ (A.component l).val := by
      rw [hb, ← (C).coe_blowupComponent]
      exact x.property
    exact ⟨i, A.component.injective
      ((A.branchSchemeToBlowup_branch_mem_component_iff j i (A.component l)).mp hm)⟩
  · rintro ⟨b, rfl⟩
    let y := (C).branchSchemeToBlowup k (A.branch (j, b))
    have hy : y ∈ ((C).blowupComponent (A.component ((TauCeti.DualGraph.cycle n).endpoint j b)) :
        Set (J).blowup) := by
      rw [(C).coe_blowupComponent]
      exact (A.branchSchemeToBlowup_branch_mem_component_iff j b _).mpr rfl
    let U := (C).blowupComponent (A.component ((TauCeti.DualGraph.cycle n).endpoint j b))
    let x : U.toScheme := ⟨y, hy⟩
    have hι : U.ι x = y := (rfl)
    exact ⟨x, by
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hι, hbranch,
        A.branchSchemeToSingularLocus_branch, ambientNode_def]⟩

private theorem exists_ambientNode_of_mem_closure_boundaryPrimes (hD : D.IsEffectiveCartier)
    {i j : ZMod n} (hij : i ≠ j) {x : X}
    (hi : x ∈ closure {(A.boundaryPrimeEquiv hD i).val})
    (hj : x ∈ closure {(A.boundaryPrimeEquiv hD j).val}) :
    ∃ a, A.ambientNode a = x := by
  have hnodal : AtWorstNodalOfRelativeDimensionOne (C ↘ Spec (.of k)) :=
    PrestableFamily.atWorstNodalOfRelativeDimensionOne
  let := hnodal.syntomic
  have hclosure (l : ZMod n) := (C).range_blowupComponent_comp
    (A.component l) D.subschemeι D.subschemeι.isClosedMap
  simp only [← componentGenericPoint_def] at hclosure
  obtain ⟨y, hy⟩ := (hclosure i).symm ▸ hi
  obtain ⟨z, hz⟩ := (hclosure j).symm ▸ hj
  simp only [Scheme.Hom.comp_apply] at hy hz
  have he := D.subschemeι.injective (hy.trans hz.symm)
  have hs : ν (((C).blowupComponent (A.component i)).ι y) ∈ (J).support := by
    apply ((C).mem_support_singularLocus_iff_notMem_smoothLocus _).mpr
    intro hm
    have h := (C).eq_of_blowupToBase_singularLocus_eq_of_mem_smoothLocus he hm
    have hd := (C).pairwise_disjoint_blowupComponent (A.component.injective.ne hij)
    have hz' : ((C).blowupComponent (A.component j)).ι z ∈
        (C).blowupComponent (A.component j) := z.property
    have hy' : ((C).blowupComponent (A.component i)).ι y ∈
        (C).blowupComponent (A.component j) := h.symm ▸ hz'
    exact Set.disjoint_left.mp (TopologicalSpace.Opens.coe_disjoint.mpr hd) y.property hy'
  obtain ⟨a, ha⟩ := (J).range_subschemeι.ge hs
  obtain ⟨l, rfl⟩ := A.node.surjective a
  exact ⟨l, (congrArg D.subschemeι ha).trans hy⟩

/-- Distinct components of a numbered nodal Cartier cycle meet exactly at the
numbered nodes incident to both. For a two-component cycle, both joining nodes
occur in the intersection. -/
theorem closure_boundaryPrime_inter_of_ne (hD : D.IsEffectiveCartier) {i j : ZMod n}
    (hij : i ≠ j) :
    closure {(A.boundaryPrimeEquiv hD i).val} ∩ closure {(A.boundaryPrimeEquiv hD j).val} =
      A.ambientNode '' {a | (a = i ∧ j = i + 1) ∨ (a = j ∧ i = j + 1)} := by
  have hnode (a : ZMod n) : A.ambientNode a ∈
      closure {(A.boundaryPrimeEquiv hD i).val} ∩ closure {(A.boundaryPrimeEquiv hD j).val} ↔
      (a = i ∧ j = i + 1) ∨ (a = j ∧ i = j + 1) := by
    simp only [Set.mem_inter_iff, A.ambientNode_mem_closure_boundaryPrime_iff, Fin.exists_fin_two]
    simp
    grind
  ext x
  constructor
  · rintro ⟨hi, hj⟩
    obtain ⟨a, rfl⟩ := A.exists_ambientNode_of_mem_closure_boundaryPrimes hD hij hi hj
    exact ⟨a, (hnode a).mp ⟨hi, hj⟩, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact (hnode a).mpr ha

end AlgebraicGeometry.Scheme.NodalCycleNumbering
