/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality
import QPainleve.AlgebraicGeometry.Modules.Clopen

/-!
# Line bundle classes on disjoint open covers

Restriction to a disjoint open cover detects equality of line bundle classes.
Isomorphisms of the restricted modules extend to a global isomorphism by
`Scheme.Modules.exists_iso_of_pairwise_disjoint_openCover`.
-/

public section

open AlgebraicGeometry CategoryTheory
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
      ((_root_.AlgebraicGeometry.Scheme.Modules.pullback (U i).ι).obj L.obj ≅
        (_root_.AlgebraicGeometry.Scheme.Modules.pullback (U i).ι).obj M.obj) := by
    have hi := h i
    simpa only [pullback_mk, mk_eq_mk_iff, InvertibleSheaf.pullback_obj_obj] using hi
  obtain ⟨e, -⟩ :=
    _root_.AlgebraicGeometry.Scheme.Modules.exists_iso_of_pairwise_disjoint_openCover U hcover
      hdisj (fun i ↦ (hIso i).some)
  exact mk_eq_mk_iff.mpr ⟨e⟩

end TauCeti.AlgebraicGeometry.LineBundleClass
