/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Coordinates
public import QPainleve.Geometry.Toric.Fan.Boundary.Normalization
public import QPainleve.Geometry.Toric.Fan.CyclicOrder
public import TauCeti.AlgebraicGeometry.Curves.DualGraph.Cycle

import QPainleve.Geometry.Toric.Fan.Boundary.Intersection
import QPainleve.Geometry.Toric.Fan.Boundary.Node

/-!
# The oriented dual graph of a toric boundary

In a complete regular rank-two fan, the cone between consecutive rays gives a node
of the reduced toric boundary. Ordering its two branches by their normalized
ray components gives the orientation used by
`AlgebraicGeometry.Scheme.nodalPicardCycleMulEquiv` to multiply branch gluing ratios.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti
open AlgebraicGeometry.Scheme.IdealSheafData TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]

local notation "X" => Φ.algebraicRealization
local notation "D" => Φ.boundaryIdeal inferInstance
local notation "C" => Scheme.IdealSheafData.subscheme D
local notation "ν" => Scheme.IdealSheafData.blowupToBase (Scheme.singularLocus ℂ C)
local notation "base" => Spec (CommRingCat.of ℂ)
local notation "point" => IsLocalRing.closedPoint ℂ
local notation "G(" p ")" => Scheme.dualGraph (K := ℂ) C p

variable [PrestableFamily ((Φ.boundaryIdeal inferInstance).subscheme ↘ Spec (.of ℂ))]
variable {ι : Type*} (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (hdim : Module.finrank ℤ N = 2)

include hΦ hc hdim in
/-- The two-ray cones of a complete regular rank-two fan index the edges of the
native dual graph via their distinguished points. -/
theorem exists_boundaryDualGraphEdgeEquiv (p : ι → (C ↘ base).smoothLocus) :
    ∃ e : {σ : Φ.cones // Nat.card (ToricRay σ.val) = 2} ≃ (G(p)).Edge,
      ∀ σ, (D).subschemeι ((C).dualGraphEdgeEquiv p (e σ)).val =
        Φ.distinguishedPointHom σ.val point := by
  have : IsReduced C := by
    rw [Φ.boundaryIdeal_def]
    infer_instance
  let f (a : (G(p)).Edge) := (D).subschemeι ((C).dualGraphEdgeEquiv p a).val
  have hn (z : C) : (C ↘ base).IsNodeAt z ↔ z ∉ (C ↘ base).smoothLocus :=
    (C ↘ base).isNodeAt_iff_notMem_smoothLocus
      PrestableFamily.atWorstNodalOfRelativeDimensionOne z
  have hnode (x : X) : (D).IsNodeOfReducedBoundary Φ.algebraicRealizationStructureMap x ↔
      ∃ a, f a = x := by
    rw [(D).isNodeOfReducedBoundary_iff_of_isReduced, ← Φ.algebraicRealization_over,
      ← over_eq_subschemeι_comp]
    constructor
    · rintro ⟨z, hz, hz'⟩
      refine ⟨((C).dualGraphEdgeEquiv p).symm ⟨z, (hn z).mp hz'⟩, ?_⟩
      simpa only [f, Equiv.apply_symm_apply] using hz
    · rintro ⟨a, rfl⟩
      exact ⟨_, rfl, (hn _).mpr ((C).dualGraphEdgeEquiv p a).property⟩
  choose g hg using fun (σ : {σ : Φ.cones // Nat.card (ToricRay σ.val) = 2}) ↦
    (hnode _).mp (Φ.isNodeOfReducedBoundary_distinguishedPointHom hΦ σ.val hdim σ.property)
  have hcone (x : X) (hx : (D).IsNodeOfReducedBoundary Φ.algebraicRealizationStructureMap x) :=
    (Φ.isNodeOfReducedBoundary_iff_existsUnique_twoRayCone hΦ hc hdim).mp hx
  refine ⟨Equiv.ofBijective g ⟨?_, ?_⟩, hg⟩
  · intro σ τ h
    have he : Φ.distinguishedPointHom τ.val point = Φ.distinguishedPointHom σ.val point :=
      (hg τ).symm.trans ((congrArg f h).symm.trans (hg σ))
    obtain ⟨s, _, hs⟩ := hcone _ (Φ.isNodeOfReducedBoundary_distinguishedPointHom hΦ
      σ.val hdim σ.property)
    exact Subtype.ext ((hs σ.val ⟨σ.property, rfl⟩).trans (hs τ.val ⟨τ.property, he⟩).symm)
  · intro a
    obtain ⟨σ, ⟨hσ, he⟩, -⟩ := hcone _ ((hnode (f a)).mpr ⟨a, rfl⟩)
    refine ⟨⟨σ, hσ⟩, ((C).dualGraphEdgeEquiv p).injective (Subtype.ext ?_)⟩
    exact (D).subschemeι.isClosedEmbedding.injective ((hg ⟨σ, hσ⟩).trans he)

include hdim in
private theorem exists_endpoint_of_distinguishedPoint (p : ι → (C ↘ base).smoothLocus)
    {σ : Φ.cones} {ρ τ : Φ.Ray}
    (hne : ρ ≠ τ) (hρ : ρ.toCone ≤ σ) (hτ : τ.toCone ≤ σ)
    (e : (G(p)).Edge)
    (he : (D).subschemeι ((C).dualGraphEdgeEquiv p e).val = Φ.distinguishedPointHom σ point) :
    ∃ b, (C).dualGraphVertexEquiv p ((G(p)).endpoint e b) =
      Φ.boundaryNormalizationComponentEquiv hΦ ρ := by
  let z := ((C).dualGraphEdgeEquiv p e).val
  let v := Φ.boundaryNormalizationComponentEquiv hΦ ρ
  let U := (C).blowupComponent (K := ℂ) v
  have hp : Φ.distinguishedPointHom σ point ∈
      ((Φ.rayBoundaryIdeal hΦ ρ ⊔ Φ.rayBoundaryIdeal hΦ τ).support : Set X) := by
    rw [Φ.sup_rayBoundaryIdeal_eq_ker_distinguishedPoint hΦ hdim hne σ hρ hτ,
      ← Φ.distinguishedPointHom_def, Scheme.Hom.support_ker]
    exact subset_closure (Set.mem_range_self _)
  rw [support_sup, Closeds.coe_inf] at hp
  have hz : z ∈ Set.range (ρ.boundaryComponentι hΦ) := by
    obtain ⟨x, hx⟩ := (range_subschemeι (Φ.rayBoundaryIdeal hΦ ρ)).symm ▸ hp.1
    refine ⟨x, (D).subschemeι.isClosedEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, ρ.boundaryComponentι_subschemeι, he]
    exact hx
  have hz' : z ∈ Set.range (U.ι ≫ ν) :=
    (Φ.range_boundaryNormalizationComponentEquiv hΦ ρ).symm ▸ hz
  obtain ⟨x, hx⟩ := hz'
  obtain ⟨b, hb⟩ := ((C).branchPointEquiv ((C).dualGraphEdgeEquiv p e)).surjective
    ⟨U.ι x, (Scheme.Hom.comp_apply U.ι ν x).symm.trans hx⟩
  refine ⟨b, ((C).dualGraphVertexEquiv_endpoint_eq_iff p e b v).mpr ?_⟩
  rw [congrArg Subtype.val hb, ← (C).coe_blowupComponent v]
  exact x.property

include hc in
/-- A positive cyclic numbering of the rays gives the oriented cycle on the actual
dual graph of the reduced toric boundary. Each vertex is the normalized ray component,
and edge `j` is the distinguished point of the cone containing rays `j` and `j + 1`. -/
theorem exists_toric_boundary_dualGraph_cycle (p : ι → (C ↘ base).smoothLocus)
    (b : Module.Basis (Fin 2) ℤ N)
    {n : ℕ} [NeZero n] (u : ZMod n ≃ Φ.Ray)
    (hu : ∀ j, b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ) :
    ∃ (e : ZMod n ≃ (G(p)).Edge) (o : (G(p)).Edge → Equiv.Perm (Fin 2))
      (w : ZMod n ≃ (G(p)).Vertex),
      (∀ j k, (G(p)).endpoint (e j) (o (e j) k) =
        w ((DualGraph.cycle n).endpoint j k)) ∧
      (∀ j, (C).dualGraphVertexEquiv p (w j) = Φ.boundaryNormalizationComponentEquiv hΦ (u j)) ∧
      ∀ j, ∃ σ : {σ : Φ.cones // Nat.card (ToricRay σ.val) = 2},
        (u j).toCone ≤ σ.val ∧ (u (j + 1)).toCone ≤ σ.val ∧
        (D).subschemeι ((C).dualGraphEdgeEquiv p (e j)).val =
          Φ.distinguishedPointHom σ.val point := by
  obtain ⟨c, hcone⟩ := exists_cyclicConeNumbering b hΦ hc u hu
  have hdim : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  obtain ⟨g, hg⟩ := exists_boundaryDualGraphEdgeEquiv hΦ hc hdim p
  let e := c.trans g
  let w := u.trans ((Φ.boundaryNormalizationComponentEquiv hΦ).trans
    ((C).dualGraphVertexEquiv p).symm)
  have hw (j) : (C).dualGraphVertexEquiv p (w j) =
      Φ.boundaryNormalizationComponentEquiv hΦ (u j) := by simp only [w, Equiv.trans_apply,
        Equiv.apply_symm_apply]
  have hne (j) : u j ≠ u (j + 1) := by
    intro h
    have hdet := (hu j).1
    rw [← h, b.detDualEquiv_self] at hdet
    exact zero_ne_one hdet
  choose l hl using fun j ↦ exists_endpoint_of_distinguishedPoint hΦ hdim p
    (hne j) (hcone j).1 (hcone j).2 (e j) (hg (c j))
  choose r hr using fun j ↦ exists_endpoint_of_distinguishedPoint hΦ hdim p
    (hne j).symm (hcone j).2 (hcone j).1 (e j) (hg (c j))
  let f (j : ZMod n) : Fin 2 → Fin 2 := ![l j, r j]
  have hf (j) : Function.Injective (f j) := Matrix.injective_pair_iff_ne.mpr fun h ↦
    hne j ((Φ.boundaryNormalizationComponentEquiv hΦ).injective
      ((hl j).symm.trans (h ▸ hr j)))
  let o (a : (G(p)).Edge) : Equiv.Perm (Fin 2) :=
    Equiv.ofBijective (f (e.symm a)) (Finite.injective_iff_bijective.mp (hf (e.symm a)))
  refine ⟨e, o, w, ?_, hw, fun j ↦ ⟨c j, (hcone j).1, (hcone j).2, hg (c j)⟩⟩
  intro j k
  apply ((C).dualGraphVertexEquiv p).injective
  have ho : o (e j) k = f j k := by simp [o]
  rw [ho, hw]
  fin_cases k
  · simpa [f, DualGraph.cycle] using hl j
  · simpa [f, DualGraph.cycle] using hr j

end TauCeti.Toric.Fan

namespace TauCeti.Toric.FanEquiv

variable {N N' V V' : Type} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'} (e : FanEquiv Φ Ψ)

variable [hΦ₀ : Nonempty Φ.cones] [hΨ₀ : Nonempty Ψ.cones]

local notation "base" => Spec (CommRingCat.of ℂ)
local notation "D[" Φ "]" => Fan.boundaryIdeal Φ inferInstance
local notation "C[" Φ "]" => Scheme.IdealSheafData.subscheme (D[Φ])
local notation "g" => e.boundaryIso hΦ₀ hΨ₀

variable [PrestableFamily (C[Φ] ↘ base)] [PrestableFamily (C[Ψ] ↘ base)]

variable {α β : Type*} {p : α → (C[Φ] ↘ base).smoothLocus}
  {p' : β → (C[Ψ] ↘ base).smoothLocus}

local notation "G[" p "]" => Scheme.dualGraph (K := ℂ) _ p

/-- The induced isomorphism of singular loci sends the node of a cone to the
node of its image cone. The edge labels can come from independent numberings. -/
theorem singularLocusIso_dualGraphNodeEquiv_of_distinguishedPoint
    {σ : Φ.cones} {x : (G[p]).Edge} {y : (G[p']).Edge}
    (hx : (D[Φ]).subschemeι ((C[Φ]).dualGraphEdgeEquiv p x).val =
      Φ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ))
    (hy : (D[Ψ]).subschemeι ((C[Ψ]).dualGraphEdgeEquiv p' y).val =
      Ψ.distinguishedPointHom (e.coneEquiv σ) (IsLocalRing.closedPoint ℂ)) :
    (Iso.singularLocusIso (R := ℂ) g).hom ((C[Φ]).dualGraphNodeEquiv p x) =
      (C[Ψ]).dualGraphNodeEquiv p' y := by
  let I := Scheme.singularLocus ℂ (C[Φ])
  let J := Scheme.singularLocus ℂ (C[Ψ])
  let f := (Iso.singularLocusIso (R := ℂ) g).hom
  have h : f ≫ J.subschemeι ≫ (D[Ψ]).subschemeι =
      I.subschemeι ≫ (D[Φ]).subschemeι ≫ e.toFanHom.algebraicMap := by
    simp only [f, I, J, Iso.singularLocusIso_hom_subschemeι_assoc, boundaryIso_hom_subschemeι]
  have hp := congrArg (fun k : I.subscheme ⟶ Ψ.algebraicRealization ↦
    k ((C[Φ]).dualGraphNodeEquiv p x)) h
  let z := IsLocalRing.closedPoint ℂ
  have hσ : e.toFanHom.algebraicMap (Φ.distinguishedPointHom σ z) =
      Ψ.distinguishedPointHom (e.coneEquiv σ) z := by
    calc
      _ = (Φ.distinguishedPointHom σ ≫ e.toFanHom.algebraicMap) z :=
        (Scheme.Hom.comp_apply (Φ.distinguishedPointHom σ) e.toFanHom.algebraicMap z).symm
      _ = _ := by rw [e.distinguishedPointHom_comp_algebraicMap]
  simp only [I, Scheme.Hom.comp_apply, Scheme.subschemeι_dualGraphNodeEquiv, hx] at hp
  apply J.subschemeι.isClosedEmbedding.injective
  apply (D[Ψ]).subschemeι.isClosedEmbedding.injective
  simpa only [J, Scheme.subschemeι_dualGraphNodeEquiv, hy, z] using hp.trans hσ

end TauCeti.Toric.FanEquiv
