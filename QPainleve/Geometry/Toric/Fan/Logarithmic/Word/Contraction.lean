/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Word.Endpoint

/-!
# Boundary action of Sarkisov words after contraction

The two prescribed toric frames number the branches of the common resolving
boundary. When both maps to the original boundaries are oriented subdivisions,
the inversion sign of the word measures the orientation of the specified
isomorphism on the original boundaries. Together with the image of a surviving
component, this determines the action on the numbered branches.

The resolved paths here are those of
[Lutz, Theorem 8.4](https://arxiv.org/pdf/2005.05010v3#page=68).
-/

public section

open AlgebraicGeometry CategoryTheory DihedralGroup QPainleve.Cluster TauCeti.AlgebraicGeometry
open Scheme (NodalCycleNumbering)
open scoped Sarkisov

namespace TauCeti.Toric.Fan.LogarithmicProjection

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

local notation "S" => Spec (CommRingCat.of k₀)

variable {Z X Y : Scheme} [Z.Over (Spec (.of k₀))] [SmoothOfRelativeDimension 2 (Z ↘ Spec (.of k₀))]
  [IsIntegral Z] [Z.IsProjectiveOver k₀] [X.Over (Spec (.of k₀))] [Y.Over (Spec (.of k₀))]
  [PrestableFamily (X ↘ Spec (.of k₀))] [PrestableFamily (Y ↘ Spec (.of k₀))]
  {D : Z.IdealSheafData} {A B : LogarithmicProjection k₀ i D} {m : ℕ}
  {ι₀ ι₁ : Type*} {pX : ι₀ → (X ↘ Spec (.of k₀)).smoothLocus} {pY : ι₁ →
    (Y ↘ Spec (.of k₀)).smoothLocus}

/-- Read a resolved Sarkisov path in the prescribed endpoint frames and labels.
If the two oriented subdivision maps from the resolving boundary commute with
the specified boundary isomorphism, the word has the sign of that isomorphism.
The image of source component zero and this sign give the permutation of all
surviving components. The sign still records the branch action for one- and
two-component cycles. -/
theorem exists_word_of_resolved_sarkisov_path_to_model_of_orientedCycleSubdivisions
    (p : SarkisovPath A B) (U : OrderedToricModel A m) (T : OrderedToricModel B m)
    {n l : ℕ} [NeZero n] [NeZero l]
    (C₀ : NodalCycleNumbering pX n) (C₁ : NodalCycleNumbering pY n)
    (e : X ≅ Y) [e.hom.IsOver S] {f : D.subscheme ⟶ X} {g : D.subscheme ⟶ Y}
    [f.IsOver S] [g.IsOver S] (h : f ≫ e.hom = g) :
    letI := U.prestableFamily_resolvingBoundary
    ∀ {R₀ R₁ : NodalCycleNumbering
        (@Empty.elim (Scheme.Hom.smoothLocus (D.subscheme ↘ S))) l},
      U.IsPositiveBoundaryNumbering R₀ → T.IsPositiveBoundaryNumbering R₁ →
      f.IsOrientedCycleSubdivision R₀ C₀ → g.IsOrientedCycleSubdivision R₁ C₁ →
      ∃ w : Word U.exchangeMatrix T.exchangeMatrix,
        (∃ hd, U.xEvaluation.compOfDefined (w.xRationalMap k₀) hd = T.xEvaluation) ∧
        cycleOrientationSign (e.boundaryCycleAction C₀ C₁) = (-1 : ℤˣ) ^ w.inversionCount ∧
        ∀ {x₀ x : D.subscheme} {j j₀ : ZMod n},
          f x₀ = C₀.componentGenericPoint 0 → g x₀ = C₁.componentGenericPoint j₀ →
          f x = C₀.componentGenericPoint j →
          g x = C₁.componentGenericPoint ((((-1 : ℤˣ) ^ w.inversionCount : ℤˣ) : ℤ) • j + j₀) := by
  intro R₀ R₁ h₀ h₁ hf hg
  let := U.prestableFamily_resolvingBoundary
  obtain ⟨_, _, _, w, _, _, -, -, -, -, -, -, -, -, -, hw, -, hEval⟩ :=
    exists_word_of_resolved_sarkisov_path_to_model p U T
  let t := Iso.refl D.subscheme
  let : t.hom.IsOver S := ⟨Category.id_comp _⟩
  have hsq : CommSq t.hom f g e.hom :=
    ⟨by simpa only [t, Iso.refl_hom, Category.id_comp] using h.symm⟩
  have hsign := (e.cycleOrientationSign_eq_of_orientedCycleSubdivisions C₀ C₁ R₀ R₁
    t hf hg hsq).trans (hw.cycleOrientationSign_eq h₀ h₁)
  have hpoint {x : D.subscheme} {j : ZMod n} (hx : f x = C₀.componentGenericPoint j) :
      g x = C₁.componentGenericPoint (cycleVertexPerm (e.boundaryCycleAction C₀ C₁) j) := by
    rw [← h, Scheme.Hom.comp_apply, hx, e.apply_componentGenericPoint]
  refine ⟨w, hEval, hsign, fun hx₀ hg₀ hx ↦ ?_⟩
  have hj₀ := C₁.componentGenericPoint_injective ((hpoint hx₀).symm.trans hg₀)
  rw [hpoint hx, cycleVertexPerm_apply, hsign, hj₀]

end TauCeti.Toric.Fan.LogarithmicProjection
