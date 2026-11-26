/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Search in an injectively indexed family

An equality search through an injective family selects the unique matching index.
-/

public section

namespace Fin

/-- For an injective family, searching for a value returns a given index exactly when the
family takes that value at the index. -/
theorem find?_decide_eq_some_iff_of_injective {n : ℕ} {α : Type*} [DecidableEq α]
    {f : Fin n → α} (hf : Function.Injective f) (a : α) (i : Fin n) :
    (find? fun j ↦ decide (f j = a)) = some i ↔ f i = a := by
  simp only [← Option.mem_def, mem_find?_iff, decide_eq_true_eq]
  exact ⟨And.left, fun hi ↦ ⟨hi, fun j hj heq ↦ hj.ne (hf (heq.trans hi.symm))⟩⟩

end Fin
