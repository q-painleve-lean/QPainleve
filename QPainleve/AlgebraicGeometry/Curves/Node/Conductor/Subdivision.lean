/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.CycleAction

import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Etale

/-!
# Oriented subdivisions of nodal cycles

The conductor condition for a contraction records a normalization lift and one
ordered pair of branches over each target node. Every other pair coalesces.
This condition composes, so successive contractions of boundary components
give a single subdivision to which the gluing-period formula applies.
-/

public section

open AlgebraicGeometry CategoryTheory DihedralGroup TauCeti.AlgebraicGeometry
open Scheme (NodalCycleNumbering)

universe u v₀ v₁ v₂

variable {k : Type u} [Field k] [IsSepClosed k] {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
  [PrestableFamily (X ↘ Spec (.of k))] [PrestableFamily (Y ↘ Spec (.of k))]
  [PrestableFamily (Z ↘ Spec (.of k))]
  {ι₀ : Type v₀} {ι₁ : Type v₁} {ι₂ : Type v₂}
  {pX : ι₀ → (X ↘ Spec (.of k)).smoothLocus} {pY : ι₁ → (Y ↘ Spec (.of k)).smoothLocus}
  {pZ : ι₂ → (Z ↘ Spec (.of k)).smoothLocus}
  {n m l : ℕ} [NeZero n] [NeZero m] [NeZero l]

local notation "N[" T "]" => Scheme.IdealSheafData.subscheme (Scheme.singularLocus k T)
local notation "ν[" T "]" => Scheme.IdealSheafData.blowupToBase (Scheme.singularLocus k T)
local notation "j[" T "]" => Scheme.branchSchemeToBlowup k T

namespace AlgebraicGeometry.Scheme.Hom

/-- The oriented conductor condition for a subdivision of numbered nodal cycles.
A lift to the normalizations sends the two branches of one selected node over each
target node to the two branches in order. At the other nodes the two branches have
the same image under the lift. -/
inductive IsOrientedCycleSubdivision (f : Z ⟶ X)
    (C : NodalCycleNumbering pZ m) (A : NodalCycleNumbering pX n) : Prop where
  /-- Choose a lift to the normalizations and the node at which each ordered branch
  pair survives. -/
  | intro (fν : (Z.singularLocus k).blowup ⟶ (X.singularLocus k).blowup)
      (hν : CommSq ν[Z] fν f ν[X])
      (hnodes : Set.MapsTo f (Z.singularLocus k).support (X.singularLocus k).support)
      (keep : N[X] ↪ N[Z])
      (hkeep : ∀ z b, fν (j[Z] (Z.branchOrderOfDualGraph pZ C.order (keep z) b).val) =
        j[X] (X.branchOrderOfDualGraph pX A.order z b).val)
      (hcollapse : ∀ z ∉ Set.range keep,
        fν (j[Z] (Z.branchOrderOfDualGraph pZ C.order z 1).val) =
        fν (j[Z] (Z.branchOrderOfDualGraph pZ C.order z 0).val)) :
      IsOrientedCycleSubdivision f C A

/-- Composing two oriented subdivisions retains the node selected successively by
the two node embeddings. Every other source node has coalescing branches. -/
theorem IsOrientedCycleSubdivision.comp {f : Z ⟶ Y} {g : Y ⟶ X}
    {A : NodalCycleNumbering pX n} {B : NodalCycleNumbering pY m}
    {C : NodalCycleNumbering pZ l}
    (hf : f.IsOrientedCycleSubdivision C B) (hg : g.IsOrientedCycleSubdivision B A) :
    (f ≫ g).IsOrientedCycleSubdivision C A := by
  obtain ⟨fν, hfν, hfNodes, retainF, hfKeep, hfCollapse⟩ := hf
  obtain ⟨gν, hgν, hgNodes, retainG, hgKeep, hgCollapse⟩ := hg
  refine ⟨fν ≫ gν, hfν.vert_comp hgν, ?_, retainG.trans retainF, ?_, ?_⟩
  · intro z hz
    rw [Scheme.Hom.comp_apply]
    exact hgNodes (hfNodes hz)
  · intro x b
    rw [Scheme.Hom.comp_apply, Function.Embedding.trans_apply, hfKeep, hgKeep]
  · intro z hz
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    by_cases h : z ∈ Set.range retainF
    · obtain ⟨y, rfl⟩ := h
      have hy : y ∉ Set.range retainG := by
        rintro ⟨x, rfl⟩
        exact hz ⟨x, rfl⟩
      rw [hfKeep, hfKeep]
      exact hgCollapse y hy
    · rw [hfCollapse z h]

/-- Reversing both cycle numberings preserves an oriented subdivision. The same
normalization lift retains the same nodes and exchanges the two branches on both sides. -/
theorem IsOrientedCycleSubdivision.reverse {f : Z ⟶ X}
    {C : NodalCycleNumbering pZ m} {A : NodalCycleNumbering pX n}
    (hf : f.IsOrientedCycleSubdivision C A) :
    f.IsOrientedCycleSubdivision C.reverse A.reverse := by
  obtain ⟨fν, hν, hnodes, keep, hkeep, hcollapse⟩ := hf
  refine ⟨fν, hν, hnodes, keep, fun z b ↦ ?_, fun z hz ↦ ?_⟩
  · simpa only [NodalCycleNumbering.reverse_branchOrderOfDualGraph] using hkeep z b.rev
  · simpa only [NodalCycleNumbering.reverse_branchOrderOfDualGraph,
      show (1 : Fin 2).rev = 0 from rfl, show (0 : Fin 2).rev = 1 from rfl] using
      (hcollapse z hz).symm

end AlgebraicGeometry.Scheme.Hom

namespace CategoryTheory.Iso

/-- An orientation-preserving boundary isomorphism is an oriented subdivision
with a retained node over every node of the target. -/
theorem isOrientedCycleSubdivision_of_cycleOrientationSign_eq_one
    (e : X ≅ Y) [e.hom.IsOver (Spec (.of k))]
    (A : NodalCycleNumbering pX n) (B : NodalCycleNumbering pY n)
    (h : cycleOrientationSign (e.boundaryCycleAction A B) = 1) :
    e.hom.IsOrientedCycleSubdivision A B := by
  let nodeIso := e.singularLocusIso (R := k)
  let retain := (Scheme.homeoOfIso nodeIso.symm).toEquiv
  refine ⟨(e.singularLocusBlowupIso (R := k)).hom,
    ⟨(e.singularLocusBlowupIso_hom_blowupToBase (R := k)).symm⟩, ?_,
    retain.toEmbedding, ?_, ?_⟩
  · exact fun {x} hx ↦ (e.hom.mem_support_singularLocus_image_iff x).mpr hx
  · intro z b
    rw [← Scheme.Hom.comp_apply, ← e.branchSchemeIso_hom_branchSchemeToBlowup,
      Scheme.Hom.comp_apply, e.branchOrder_boundaryCycleAction A B, h]
    rw [ite_eq_right (by decide : (1 : ℤˣ) ≠ -1)]
    -- Evaluate the node identity before applying the dependent branch order.
    have hz : (e.singularLocusIso (R := k)).hom (retain.toEmbedding z) = z := by
      simp only [Equiv.toEmbedding_apply, retain, Homeomorph.coe_toEquiv,
        Scheme.coe_homeoOfIso_symm, nodeIso, Scheme.inv_hom_apply]
    exact congrArg (fun x : N[Y] ↦ j[Y] (Y.branchOrderOfDualGraph pY B.order x b).val) hz
  · intro z hz
    exact (hz (retain.surjective z)).elim

end CategoryTheory.Iso

namespace AlgebraicGeometry.Scheme.Hom

/-- The identity leaves every node and its branch order intact. -/
@[simp]
theorem IsOrientedCycleSubdivision.id (A : NodalCycleNumbering pX n) :
    IsOrientedCycleSubdivision (𝟙 X) A A := by
  have : (Iso.refl X).hom.IsOver (Spec (.of k)) := by
    rw [Iso.refl_hom]
    infer_instance
  simpa only [Iso.refl_hom] using
    (Iso.refl X).isOrientedCycleSubdivision_of_cycleOrientationSign_eq_one A A (by simp)

end AlgebraicGeometry.Scheme.Hom
