/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import TauCeti.AlgebraicGeometry.Modules.Clopen

/-!
# Isomorphisms on disjoint open covers

A family of isomorphisms on a disjoint open cover determines a global isomorphism.
-/

public section

open CategoryTheory Limits TopologicalSpace
open scoped Function

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti.AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)

/-- Isomorphisms of modules over the members of a disjoint open cover extend to a
global isomorphism with the prescribed pullbacks. -/
theorem exists_iso_of_pairwise_disjoint_openCover
    (hU : ⨆ i, U i = ⊤) (hd : Pairwise (Disjoint on U)) {M N : X.Modules}
    (a : ∀ i, (pullback (U i).ι).obj M ≅ (pullback (U i).ι).obj N) :
    ∃ e : M ≅ N, ∀ i, (pullback (U i).ι).map e.hom = (a i).hom := by
  let r (i : ι) := restrictFunctorIsoPullback (U i).ι
  let b (i : ι) := (r i).app M ≪≫ a i ≪≫ ((r i).app N).symm
  let m := clopenCoverProductIso U hU hd M
  let n := clopenCoverProductIso U hU hd N
  let p := Pi.mapIso fun i ↦ (pushforward (U i).ι).mapIso (b i)
  let e := m ≪≫ p ≪≫ n.symm
  refine ⟨e, fun i ↦ ?_⟩
  have h : (restrictFunctor (U i).ι).map e.hom = (b i).hom := by
    let A := restrictAdjunction (U i).ι
    apply (A.homEquiv M _).injective
    have hn := A.unit.naturality e.hom
    simp only [Functor.id_map, Functor.comp_map] at hn
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, ← hn]
    rw [← clopenCoverProductIso_hom_π U hU hd N i]
    simp only [e, m, n, p, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id_assoc, Pi.mapIso_hom_π, Functor.mapIso_hom]
    exact (reassoc_of% (clopenCoverProductIso_hom_π U hU hd M i)) _
  apply (cancel_epi ((r i).hom.app M)).mp
  rw [← (r i).hom.naturality, h]
  simp [b]

end AlgebraicGeometry.Scheme.Modules
