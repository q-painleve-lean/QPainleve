/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Restrict

import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Global functions on a disjoint open cover

Restriction to a disjoint open cover identifies the ring of global functions
with the product of the rings of global functions on the individual opens.
-/

public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

universe u

/-- Global functions on a scheme are the product of the global functions on
the members of a pairwise disjoint open cover. -/
noncomputable def globalSectionsEquivOfDisjointCover (X : Scheme.{u})
    {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (hdisj : _root_.Pairwise (fun i j ↦ Disjoint (U i) (U j))) : Γ(X, ⊤) ≃+* Π i, Γ(U i, ⊤) :=
  RingEquiv.ofBijective (RingHom.pi fun i ↦ (U i).ι.appTop.hom) (by
    have hcomp (i : ι) :
        (U i).ι.appTop ≫ (U i).topIso.hom = X.presheaf.map (homOfLE le_top : U i ⟶ ⊤).op := by
      rw [Opens.ι_appTop, Opens.topIso_hom]
      erw [← X.presheaf.map_comp]
      congr 1
    have hglue (a : Π i, Γ(U i, ⊤)) :
        ∃! s : Γ(X, ⊤), ∀ i, (U i).ι.appTop s = a i := by
      let s₀ (i : ι) : Γ(X, U i) := (U i).topIso.hom (a i)
      have hcompat : TopCat.Presheaf.IsCompatible X.presheaf U s₀ := by
        intro i j
        by_cases hij : i = j
        · subst j
          congr 1
        · have hbot : U i ⊓ U j = ⊥ := (hdisj hij).eq_bot
          have : Subsingleton Γ(X, U i ⊓ U j) := by rw [hbot]; infer_instance
          exact Subsingleton.elim _ _
      obtain ⟨s, hs, huniq⟩ := X.sheaf.existsUnique_gluing' U ⊤
        (fun i ↦ homOfLE le_top) hU.ge s₀ hcompat
      have heq (t : Γ(X, ⊤)) (i : ι) :
          (U i).ι.appTop t = a i ↔
            X.presheaf.map (homOfLE le_top : U i ⟶ ⊤).op t = s₀ i := by
        rw [← hcomp, CommRingCat.comp_apply]
        exact (ConcreteCategory.bijective_of_isIso (U i).topIso.hom).injective.eq_iff.symm
      exact ⟨s, fun i ↦ (heq s i).mpr (hs i), fun t ht ↦
        huniq t fun i ↦ (heq t i).mp (ht i)⟩
    constructor
    · intro a b hab
      obtain ⟨c, -, hu⟩ := hglue (fun i ↦ (U i).ι.appTop b)
      exact (hu a (congrFun hab)).trans (hu b (fun _ ↦ rfl)).symm
    · intro a
      obtain ⟨s, hs, -⟩ := hglue a
      exact ⟨s, funext hs⟩)

/-- The coordinate on each open in the disjoint cover is restriction to that open. -/
@[simp]
theorem globalSectionsEquivOfDisjointCover_apply (X : Scheme.{u})
    {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (hdisj : _root_.Pairwise (fun i j ↦ Disjoint (U i) (U j)))
    (s : Γ(X, ⊤)) (i : ι) :
    X.globalSectionsEquivOfDisjointCover U hU hdisj s i = (U i).ι.appTop s :=
  (rfl)

end AlgebraicGeometry.Scheme
