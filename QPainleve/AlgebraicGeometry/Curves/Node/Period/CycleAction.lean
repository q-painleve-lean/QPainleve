/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.CycleAction
public import QPainleve.AlgebraicGeometry.Curves.Node.Period.Basic

/-!
# Pullback of periods on numbered nodal cycles

The orientation character of the induced dihedral element is the exponent in the
period pullback formula. This applies to a self-node and to a pair of parallel nodes.
-/

public section

open AlgebraicGeometry CategoryTheory DihedralGroup TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme (NodalCycleNumbering)

universe u v w

namespace CategoryTheory.Iso

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [PrestableFamily (X ↘ Spec (.of k))] [PrestableFamily (Y ↘ Spec (.of k))]
  {ι : Type v} {p : ι → (X ↘ Spec (.of k)).smoothLocus}
  {ι' : Type w} {q : ι' → (Y ↘ Spec (.of k)).smoothLocus} {n : ℕ} [NeZero n]
  (f : X ≅ Y) [f.hom.IsOver (Spec (.of k))]
  (C : NodalCycleNumbering p n) (D : NodalCycleNumbering q n)

/-- Pullback raises the period to the orientation sign of the induced action on
the numbered boundary cycle. -/
theorem nodalPicardCycleMulEquiv_pullback_boundaryCycleAction
    (a : MonoidHom.ker (LineBundleClass.pullbackHom (Y.singularLocus k).blowupToBase)) :
    Scheme.nodalPicardCycleMulEquiv C.endpoint_eq
      ⟨LineBundleClass.pullback f.hom a.val,
        f.pullback_mem_ker_pullback_blowupToBase_singularLocus a⟩ =
      (Scheme.nodalPicardCycleMulEquiv D.endpoint_eq a) ^
        (cycleOrientationSign (f.boundaryCycleAction C D) : ℤ) := by
  let η := cycleOrientationSign (f.boundaryCycleAction C D)
  have horder := f.branchOrder_boundaryCycleAction C D
  rcases Int.units_eq_one_or η with h | h
  · have hne : (1 : ℤˣ) ≠ -1 := by decide
    have hη : cycleOrientationSign (f.boundaryCycleAction C D) = 1 := h
    rw [hη, Units.val_one, zpow_one]
    exact f.nodalPicardCycleMulEquiv_pullback C.endpoint_eq D.endpoint_eq false
      (by simpa only [hη, hne, Bool.false_eq_true, ↓reduceIte] using horder) a
  · have hη : cycleOrientationSign (f.boundaryCycleAction C D) = -1 := h
    rw [hη, Units.val_neg, Units.val_one, zpow_neg_one]
    exact f.nodalPicardCycleMulEquiv_pullback C.endpoint_eq D.endpoint_eq true
      (by simpa only [hη, ite_true] using horder) a

end CategoryTheory.Iso

namespace AlgebraicGeometry.Scheme.NodalCycleNumbering

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [PrestableFamily (X ↘ Spec (.of k))]
  {ι : Type v} {p : ι → (X ↘ Spec (.of k)).smoothLocus} {n : ℕ} [NeZero n]

/-- Reversing a numbered boundary with its initial component fixed inverts its Picard period. -/
@[simp]
theorem nodalPicardCycleMulEquiv_reverse (C : NodalCycleNumbering p n)
    (a : MonoidHom.ker (LineBundleClass.pullbackHom (X.singularLocus k).blowupToBase)) :
    Scheme.nodalPicardCycleMulEquiv C.reverse.endpoint_eq a =
      (Scheme.nodalPicardCycleMulEquiv C.endpoint_eq a)⁻¹ := by
  have horder : Fin.revPerm = Equiv.swap (0 : Fin 2) 1 := by
    ext b
    fin_cases b <;> decide
  have hvertex : cycleVertexPerm (.sr (0 : ZMod n)) = Equiv.subLeft (-1 + 1) := by
    ext j
    simp [cycleVertexPerm_sr_apply]
  simpa only [reverse, horder, hvertex] using
    Scheme.nodalPicardCycleMulEquiv_reverse C.endpoint_eq (-1) a

end AlgebraicGeometry.Scheme.NodalCycleNumbering
