/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality
import TauCeti.AlgebraicGeometry.Modules.Clopen
import TauCeti.AlgebraicGeometry.Modules.Products

/-!
# Line bundle classes on disjoint open covers

Restriction to a disjoint open cover detects equality of line bundle classes.
Tau Ceti's `Scheme.Modules.clopenCoverProductIso` identifies each sheaf of modules
with the product of the pushforwards of its restrictions.
-/

public section

open AlgebraicGeometry CategoryTheory Limits
open scoped Function

namespace TauCeti.AlgebraicGeometry.LineBundleClass

universe u

/-- Line bundle classes are equal if their restrictions to each member of a disjoint open
cover agree. -/
theorem eq_of_pullback_eq_of_clopenCover {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens}
    (hcover : ⨆ i, U i = ⊤) (hdisj : Pairwise (Disjoint on U)) {a b : LineBundleClass X}
    (h : ∀ i, pullback (U i).ι a = pullback (U i).ι b) : a = b := by
  obtain ⟨L, rfl⟩ := mk_surjective a
  obtain ⟨M, rfl⟩ := mk_surjective b
  have hIso (i : ι) : Nonempty
      ((Scheme.Modules.restrictFunctor (U i).ι).obj L.obj ≅
        (Scheme.Modules.restrictFunctor (U i).ι).obj M.obj) := by
    have hi := h i
    rw [pullback_mk, pullback_mk, mk_eq_mk_iff] at hi
    obtain ⟨e⟩ := hi
    let r := Scheme.Modules.restrictFunctorIsoPullback (U i).ι
    exact ⟨r.app L.obj ≪≫ e ≪≫ (r.app M.obj).symm⟩
  exact mk_eq_mk_iff.mpr ⟨Scheme.Modules.clopenCoverProductIso U hcover hdisj L.obj ≪≫
    Pi.mapIso (fun i ↦ (Scheme.Modules.pushforward (U i).ι).mapIso (hIso i).some) ≪≫
    (Scheme.Modules.clopenCoverProductIso U hcover hdisj M.obj).symm⟩

end TauCeti.AlgebraicGeometry.LineBundleClass
