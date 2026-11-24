/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Sort

/-!
# Order-preserving matching within fibers

Two lists related by a permutation admit a reindexing which matches the first
occurrence of each value to its first occurrence, the second to the second,
and so on.
-/

public section

namespace List.Perm

/-- A permutation of the lists of values of two tuples admits an index equivalence
which is strictly increasing on the fiber of each value. -/
theorem exists_ordered_equiv_ofFn {A : Type*} {m n : ℕ} {f : Fin m → A} {g : Fin n → A}
    (h : (List.ofFn f).Perm (List.ofFn g)) :
    ∃ e : Fin m ≃ Fin n, (∀ j, g (e j) = f j) ∧
      ∀ a b, a < b → f a = f b → e a < e b := by
  classical
  have hcard (x : A) : Fintype.card {j // f j = x} = Fintype.card {j // g j = x} := by
    simpa only [List.count_ofFn, Fintype.card_subtype] using h.count_eq x
  let E (x : A) : {j // f j = x} ≃o {j // g j = x} :=
    (monoEquivOfFin _ (hcard x)).symm.trans (monoEquivOfFin _ rfl)
  let e := Equiv.ofFiberEquiv fun x ↦ (E x).toEquiv
  refine ⟨e, Equiv.ofFiberEquiv_map _, fun a b hab hval ↦ ?_⟩
  let a' : {j // f j = f a} := ⟨a, rfl⟩
  let b' : {j // f j = f a} := ⟨b, hval.symm⟩
  have hlt : E (f a) a' < E (f a) b' := (E (f a)).strictMono hab
  have he (j : Fin m) (x : A) (hx : f j = x) : e j = (E x ⟨j, hx⟩).val := by
    -- In `ofFiberEquiv`, the fiber at an index is selected by its value.
    subst x
    rfl
  rw [he a (f a) rfl, he b (f a) hval.symm]
  exact hlt

end List.Perm
