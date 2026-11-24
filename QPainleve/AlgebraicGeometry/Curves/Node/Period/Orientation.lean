/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Period.CycleAction
public import QPainleve.AlgebraicGeometry.Curves.Node.Period.Subdivision

/-!
# Orientation in a square of nodal cycles

A commuting square with oriented conductor subdivisions as its vertical maps
has the same orientation sign on the two horizontal isomorphisms. The
subdivision formula preserves the gluing period on each vertical map. The
period isomorphism detects inversion on the horizontal maps, including on
cycles with one or two components.
-/

public section

open AlgebraicGeometry CategoryTheory DihedralGroup TauCeti.AlgebraicGeometry
open Scheme (NodalCycleNumbering)

universe u v₀ v₁ v₂ v₃

variable {k : Type u} [Field k] {X Y Z W : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [Z.Over (Spec (.of k))] [W.Over (Spec (.of k))]
  [PrestableFamily (X ↘ Spec (.of k))] [PrestableFamily (Y ↘ Spec (.of k))]
  [PrestableFamily (Z ↘ Spec (.of k))] [PrestableFamily (W ↘ Spec (.of k))]
  {ι₀ : Type v₀} {ι₁ : Type v₁} {ι₂ : Type v₂} {ι₃ : Type v₃}
  {pX : ι₀ → (X ↘ Spec (.of k)).smoothLocus} {pY : ι₁ → (Y ↘ Spec (.of k)).smoothLocus}
  {pZ : ι₂ → (Z ↘ Spec (.of k)).smoothLocus} {pW : ι₃ → (W ↘ Spec (.of k)).smoothLocus}
  {n m : ℕ} [NeZero n] [NeZero m]

local notation "N[" T "]" => Scheme.IdealSheafData.subscheme (Scheme.singularLocus k T)
local notation "ν[" T "]" => Scheme.IdealSheafData.blowupToBase (Scheme.singularLocus k T)
local notation "j[" T "]" => Scheme.branchSchemeToBlowup k T
local notation "P[" T "]" => MonoidHom.ker (LineBundleClass.pullbackHom (ν[T]))

namespace AlgebraicGeometry.Scheme.Hom

variable [IsSepClosed k] in
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

/-- Pullback along an oriented subdivision preserves the period of a class in the
normalization kernel. -/
theorem IsOrientedCycleSubdivision.period_pullback [IsAlgClosed k] {f : Z ⟶ X}
    [f.IsOver (Spec (.of k))] {A : NodalCycleNumbering pX n} {C : NodalCycleNumbering pZ m}
    (h : f.IsOrientedCycleSubdivision C A) (a : P[X]) :
    ∃ ha : LineBundleClass.pullback f a.val ∈ P[Z],
      Z.nodalPicardCycleMulEquiv C.endpoint_eq ⟨LineBundleClass.pullback f a.val, ha⟩ =
        X.nodalPicardCycleMulEquiv A.endpoint_eq a := by
  obtain ⟨_, hν, hnodes, keep, hkeep, hcollapse⟩ := h
  exact f.nodalPicardCycleMulEquiv_pullback_of_subdivision
    hν C.endpoint_eq A.endpoint_eq hnodes keep hkeep hcollapse a

end AlgebraicGeometry.Scheme.Hom

namespace CategoryTheory.Iso

variable [IsAlgClosed k]
  (A : NodalCycleNumbering pX n) (B : NodalCycleNumbering pY n)
  (C : NodalCycleNumbering pZ m) (D : NodalCycleNumbering pW m)

/-- The horizontal isomorphisms in a commuting square of oriented conductor
subdivisions have the same orientation sign on the numbered cycles. -/
theorem cycleOrientationSign_eq_of_orientedCycleSubdivisions
    (e : X ≅ Y) [e.hom.IsOver (Spec (.of k))]
    (t : Z ≅ W) [t.hom.IsOver (Spec (.of k))]
    {f : Z ⟶ X} {g : W ⟶ Y} [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    (hf : f.IsOrientedCycleSubdivision C A) (hg : g.IsOrientedCycleSubdivision D B)
    (h : CommSq t.hom f g e.hom) :
    cycleOrientationSign (e.boundaryCycleAction A B) =
      cycleOrientationSign (t.boundaryCycleAction C D) := by
  have hsign : Function.Injective (fun η : ℤˣ ↦ fun a : kˣ ↦ a ^ (η : ℤ)) := by
    classical
    obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset k)
    let a := Units.mk0 x (fun h ↦ hx (Finset.mem_insert.mpr (Or.inl h)))
    have hne : a ≠ a⁻¹ := by
      intro he
      have hsq : a ^ 2 = 1 ^ 2 := calc
        a ^ 2 = a * a⁻¹ := (pow_two a).trans (congrArg (a * ·) he)
        _ = 1 ^ 2 := by simp
      have h := (Units.eq_or_eq_neg_of_sq_eq_sq a 1 hsq).imp
        (congrArg (Units.val : kˣ → k)) (congrArg (Units.val : kˣ → k))
      exact hx (Finset.mem_insert.mpr (Or.inr (by
        simpa only [Finset.mem_insert, Finset.mem_singleton, a, Units.val_mk0, Units.val_one,
          Units.val_neg] using h)))
    intro η η' h
    have h' := congrFun h a
    rcases Int.units_eq_one_or η with rfl | rfl <;> rcases Int.units_eq_one_or η' with rfl | rfl
    · rfl
    · exact (hne (by simpa only [Units.val_one, Units.val_neg, zpow_neg_one, zpow_one]
        using h')).elim
    · exact (hne (by simpa only [Units.val_one, Units.val_neg, zpow_neg_one, zpow_one]
        using h'.symm)).elim
    · rfl
  apply hsign
  funext x
  obtain ⟨a, rfl⟩ := (Y.nodalPicardCycleMulEquiv B.endpoint_eq).surjective x
  let eA : P[X] := ⟨LineBundleClass.pullback e.hom a.val,
    e.pullback_mem_ker_pullback_blowupToBase_singularLocus a⟩
  obtain ⟨hfa, hpfa⟩ := hf.period_pullback eA
  obtain ⟨hga, hpga⟩ := hg.period_pullback a
  let gA : P[W] := ⟨LineBundleClass.pullback g a.val, hga⟩
  have hclass : LineBundleClass.pullback f eA.val =
      LineBundleClass.pullback t.hom gA.val := by
    dsimp only [eA, gA]
    rw [LineBundleClass.pullback_comp, ← h.w, LineBundleClass.pullback_comp]
  have hclasses : (⟨_, hfa⟩ : P[Z]) =
      ⟨LineBundleClass.pullback t.hom gA.val,
        t.pullback_mem_ker_pullback_blowupToBase_singularLocus gA⟩ := Subtype.ext hclass
  rw [hclasses] at hpfa
  exact (e.nodalPicardCycleMulEquiv_pullback_boundaryCycleAction A B a).symm.trans
    (hpfa.symm.trans
      ((t.nodalPicardCycleMulEquiv_pullback_boundaryCycleAction C D gA).trans
        (congrArg (· ^ (cycleOrientationSign (t.boundaryCycleAction C D) : ℤ)) hpga)))

end CategoryTheory.Iso
