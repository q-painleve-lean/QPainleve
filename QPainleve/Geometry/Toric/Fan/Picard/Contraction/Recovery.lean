/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Recovery

import QPainleve.AlgebraicGeometry.IdealSheaf.BaseChange

/-!
# Recovering the Picard marking after an internal contraction

A toric identification of the base of a specified internal contraction recovers the
ordered toric blowup of its disjoint smooth centers. The comparison identifies the
strict boundary via the given boundary isomorphism and preserves the total exceptional
classes used in reconstructing an isomorphism from periods in the proof of
[Gross, Hacking and Keel, Theorem 1.8][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S2
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower
open QPainleve (BlowupTower)
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

universe u

variable (k : Type u) [Field k]
  {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Module.Basis (Fin 2) ℤ N)
  {X Y W : Scheme} {n : ℕ} {T : BlowupTower X n W}

local notation "S" => Spec (CommRingCat.of k)
local notation "B[" h "]" => Φ.toricBoundaryIdeal k (IsComplete.nonempty_cones h)

private theorem toric_center_not_node (hc : Φ.IsComplete) {E : X.IdealSheafData}
    (t : X ⟶ S) [LocallyOfFinitePresentation (E.subschemeι ≫ t)]
    (a : X ≅ (Φ.finiteFanScheme k)) (ha : a.hom ≫ Φ.finiteFanSchemeToSpec k = t)
    (h : (B[hc]).comap a.hom = E) [IsReduced E.subscheme] {q : E.subscheme}
    (hq : q ∈ (E.subschemeι ≫ t).smoothLocus) :
    ¬ (B[hc]).IsNodeOfReducedBoundary (Φ.finiteFanSchemeToSpec k)
      (a.hom (E.subschemeι q)) := by
  have hnot : ¬ E.IsNodeOfReducedBoundary t (E.subschemeι q) := by
    rw [E.isNodeOfReducedBoundary_iff_of_isReduced]
    rintro ⟨z, hz, hn⟩
    exact (E.subschemeι ≫ t).not_isNodeAt_of_mem_smoothLocus
      (E.subschemeι.isClosedEmbedding.injective hz ▸ hq) hn
  have hnode := isNodeOfReducedBoundary_comap_iff_of_isOpenImmersion
    (B[hc]) (Φ.finiteFanSchemeToSpec k) a.hom (E.subschemeι q)
  rw [ha, h] at hnode
  exact fun hn ↦ hnot (hnode.mpr hn)

/-- Recover the ordered internal model of a specified contraction to a toric pair.
The distinct projected centers lie in the smooth locus of the contracted boundary.
The returned isomorphisms identify the original surface and strict boundary over
the prescribed base identification, and pull back the labeled total exceptional
classes to the given ones. -/
theorem exists_ordered_toric_model_of_boundary_contraction [IsAlgClosed k]
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) {D : Y.IdealSheafData} {E : X.IdealSheafData}
    (t : X ⟶ S) [LocallyOfFinitePresentation (E.subschemeι ≫ t)]
    (hT : T.IsClosedPointTower X) (d : Y ≅ W) (a : X ≅ (Φ.finiteFanScheme k))
    (ha : a.hom ≫ Φ.finiteFanSchemeToSpec k = t)
    (hB : (B[hc]).comap a.hom = E)
    (v : D.subscheme ≅ E.subscheme) (hv : v.hom ≫ E.subschemeι = D.subschemeι ≫ d.hom ≫ T.toBase)
    (hinj : Function.Injective hT.baseCenter)
    (hcenters : ∀ j, ∃ q : E.subscheme, E.subschemeι q = hT.baseCenter j ∧
      q ∈ (E.subschemeι ≫ t).smoothLocus) :
    letI := hc.nonempty_cones
    ∃ (s : Fin n → Φ.Ray) (c : Fin n → kˣ),
      let M := internalBlowupTower k b s c
      ∃ (e : M.1 ≅ Y) (eB : (B[hc]).subscheme ≅ D.subscheme),
        IsLift a T M.2.toTower (d.symm ≪≫ e.symm) ∧
        e.hom ≫ d.hom ≫ T.toBase ≫ t = M.2.toTower.toBase ≫ Φ.finiteFanSchemeToSpec k ∧
        eB.hom ≫ D.subschemeι = M.2.boundaryι ≫ e.hom ∧
        D.comap e.hom = M.2.boundaryι.ker ∧
        ∀ j, pullback e.hom (pullback d.hom (T.exceptionalClass j)) =
          M.2.toTower.exceptionalClass j := by
  let := hc.nonempty_cones
  obtain ⟨u, hu⟩ := (B[hc]).exists_iso_of_comap_eq_ker a E.subschemeι
    (hB.trans E.ker_subschemeι.symm)
  let : IsReduced (B[hc]).subscheme := inferInstance
  let : IsReduced E.subscheme := isReduced_of_isOpenImmersion u.hom
  let eB := u.symm ≪≫ v.symm
  let f := eB.hom ≫ D.subschemeι ≫ d.hom
  have hf : f ≫ T.toBase ≫ a.hom = (B[hc]).subschemeι := by
    simp only [f, eB, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [← reassoc_of% hv, Iso.inv_hom_id_assoc, ← hu, Iso.inv_hom_id_assoc]
  have hmem (j : Fin n) : a.hom (hT.baseCenter j) ∈ (B[hc]).support := by
    obtain ⟨q, hq, _⟩ := hcenters j
    rw [← SetLike.mem_coe, ← range_subschemeι]
    exact ⟨u.hom q, by simpa only [Scheme.Hom.comp_apply, hq] using
      (congrArg (fun g : E.subscheme ⟶ (Φ.finiteFanScheme k) ↦ g q) hu)⟩
  have hn (j : Fin n) : ¬ (B[hc]).IsNodeOfReducedBoundary (Φ.finiteFanSchemeToSpec k)
      (a.hom (hT.baseCenter j)) := by
    obtain ⟨q, hq, hs⟩ := hcenters j
    rw [← hq]
    exact toric_center_not_node k hc t a ha hB hs
  obtain ⟨z, ⟨-, ⟨g, ⟨hg, hgf⟩, -⟩⟩, -⟩ :=
    existsUnique_ordered_toric_model_of_disjoint_blowup_tower k (Φ := Φ)
      b hΦ hc hT a hinj hmem hn f hf
  let e := g.symm ≪≫ d.symm
  have hproj : e.hom ≫ d.hom = g.inv := by simp [e]
  have heB : eB.hom ≫ D.subschemeι =
      (internalBlowupTower k b (Prod.fst ∘ z) (Prod.snd ∘ z)).2.boundaryι ≫ e.hom := by
    rw [← hgf]
    simp [e, f]
  refine ⟨Prod.fst ∘ z, Prod.snd ∘ z, e, eB, ?_, ?_, heB, ?_, fun j ↦ ?_⟩
  · have hh : d.symm ≪≫ e.symm = g := by
      apply Iso.ext
      simp [e]
    exact hh.symm ▸ hg
  · rw [← Category.assoc, hproj, ← ha, ← reassoc_of% hg.hom_toBase, Iso.inv_hom_id_assoc]
  · have hk :
        ((internalBlowupTower k b (Prod.fst ∘ z) (Prod.snd ∘ z)).2.boundaryι ≫ e.hom).ker = D := by
      rw [← heB, Scheme.Hom.ker_comp_of_isIso, D.ker_subschemeι]
    rw [← hk, Scheme.Hom.comap_ker_comp_of_isClosedImmersion]
  · rw [pullback_comp, hproj, ← hg.pullback_exceptionalClass j, pullback_comp,
      Iso.inv_hom_id, pullback_id]

end TauCeti.Toric.Fan
