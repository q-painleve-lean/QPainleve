/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Tropical.Basic

/-!
# Tropical boundary labels of signed cluster words

Transport the source order vector along a word and search for its first matching row
in the target boundary order table. If a connecting word permutes the boundary labels,
the search on the transported loop computes the conjugate permutation.
-/

public section

open CategoryTheory QPainleve.Cluster

namespace Quiver.Path

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} {E E' : SkewExchangeMatrix ι}

local notation "trop[" w "]" =>
  DFunLike.coe (F := Equiv.Perm (ι → ℤ))
    (CategoryTheory.Functor.map (Paths.lift (tropicalPrefunctor (A := ℤ) ι)) w)

/-- The first target label whose order vector agrees with the tropical image of the source
orders along a word. -/
def tropicalBoundaryLabel (w : Word E E') (orders : Fin n → ι → ℤ) (source : ι → ℤ) :
    Option (Fin n) :=
  Fin.find? fun j ↦ decide (orders j = trop[w] source)

/-- The boundary label is computed by searching the rows in index order. -/
theorem tropicalBoundaryLabel_def (w : Word E E') (orders : Fin n → ι → ℤ) (source : ι → ℤ) :
    w.tropicalBoundaryLabel orders source =
      (Fin.find? fun j ↦ decide (orders j = trop[w] source)) :=
  (rfl)

/-- The search fails exactly when no target row has the transported orders. -/
@[simp]
theorem tropicalBoundaryLabel_eq_none_iff (w : Word E E') (orders : Fin n → ι → ℤ)
    (source : ι → ℤ) :
    w.tropicalBoundaryLabel orders source = none ↔ ∀ j, orders j ≠ trop[w] source := by
  simp [tropicalBoundaryLabel, Fin.find?_decide_eq_dite]

/-- A label is returned exactly when its row has the transported orders and every earlier
row differs from them. -/
theorem mem_tropicalBoundaryLabel_iff (w : Word E E') (orders : Fin n → ι → ℤ)
    (source : ι → ℤ) (j : Fin n) :
    j ∈ w.tropicalBoundaryLabel orders source ↔
      orders j = trop[w] source ∧ ∀ k, k < j → orders k ≠ trop[w] source := by
  simp only [tropicalBoundaryLabel_def, Fin.mem_find?_iff, decide_eq_true_eq]

/-- For distinct rows, the label search returns precisely the row with the transported
orders. -/
@[simp]
theorem tropicalBoundaryLabel_eq_some_iff (w : Word E E') {orders : Fin n → ι → ℤ}
    (source : ι → ℤ) (hinj : Function.Injective orders) (j : Fin n) :
    w.tropicalBoundaryLabel orders source = some j ↔ orders j = trop[w] source := by
  rw [← Option.mem_def, mem_tropicalBoundaryLabel_iff]
  exact ⟨And.left, fun hj ↦ ⟨hj, fun k hk ↦ (hinj.ne_iff' hj).2 hk.ne⟩⟩

/-- If a connecting word transports one table of boundary orders by `p`, and a
loop permutes the original table by `q`, then the transported loop's boundary
search at any target label `j` returns `p (q (p.symm j))`. -/
theorem tropicalBoundaryLabel_reverse_comp_comp
    (w : Word E E') (v : Word E E) {orders orders' : Fin n → ι → ℤ}
    (hinj : Function.Injective orders') (p q : Equiv.Perm (Fin n))
    (hw : ∀ j, trop[w] (orders j) = orders' (p j))
    (hv : ∀ j, trop[v] (orders j) = orders (q j)) (j : Fin n) :
    ((w.reverse.comp v).comp w).tropicalBoundaryLabel orders' (orders' j) =
      some (p (q (p.symm j))) := by
  have hreverse : trop[w.reverse] (orders' j) = orders (p.symm j) := by
    rw [tropical_reverse, SingleObj.inv_as_inv]
    exact (Equiv.symm_apply_eq _).mpr (by
      simpa only [Equiv.apply_symm_apply] using (hw (p.symm j)).symm)
  have himage : trop[(w.reverse.comp v).comp w] (orders' j) = orders' (p (q (p.symm j))) := by
    let F := Paths.lift (tropicalPrefunctor (A := ℤ) ι)
    -- Read the morphisms of the one-object category as permutations.
    let action {B C : SkewExchangeMatrix ι} (s : Word B C) : Equiv.Perm (ι → ℤ) :=
      F.map (X := (Paths.of _).obj B) (Y := (Paths.of _).obj C) s
    have hcomp {B C D : SkewExchangeMatrix ι} (s : Word B C) (t : Word C D) :
        action (s.comp t) = action t * action s :=
      F.map_comp (X := (Paths.of _).obj B) (Y := (Paths.of _).obj C) (Z := (Paths.of _).obj D) s t
    calc
      _ = action ((w.reverse.comp v).comp w) (orders' j) := rfl
      _ = action w (action v (action w.reverse (orders' j))) := by
        rw [hcomp, hcomp, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
      _ = action w (action v (orders (p.symm j))) := congrArg (action w ∘ action v) hreverse
      _ = action w (orders (q (p.symm j))) := congrArg (action w) (hv (p.symm j))
      _ = _ := hw (q (p.symm j))
  exact (tropicalBoundaryLabel_eq_some_iff _ _ hinj _).mpr himage.symm

end Quiver.Path
