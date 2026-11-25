/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.StarSubdivision.Factorization

import QPainleve.Geometry.Toric.Cone.Coordinates
import QPainleve.Geometry.Toric.Fan.StarSubdivision.Generators
import QPainleve.Geometry.Toric.Fan.TwoDimensional

/-!
# Star subdivisions at distinct full cones

In a regular surface fan, a star subdivision at a two-ray cone leaves every
other two-ray cone in place. Thus an ordered list of distinct basis cones can
be subdivided at the original cones, and the added primitive generators are
the sums of the two basis vectors of each cone.
-/

public section

open Module PointedCone

namespace TauCeti.Toric.Fan

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

local notation "C[" b "]" => hull ℝ (Set.range (i ∘ ⇑b))
local notation "C[" b "," j "]" => hull ℝ {i (b 0 + b 1), i (b j)}

private theorem basisChart_le (b : Basis (Fin 2) ℤ N) (j : Fin 2) :
    C[b,j] ≤ C[b] := by
  apply Submodule.span_le.mpr
  rw [Set.insert_subset_iff, Set.singleton_subset_iff, map_add]
  exact ⟨add_mem (subset_hull (Set.mem_range_self 0)) (subset_hull (Set.mem_range_self 1)),
    subset_hull (Set.mem_range_self j)⟩

private theorem basisChart_mem_starSubdivisionAlong (hΦ : Φ.IsRegular)
    (b : Basis (Fin 2) ℤ N) (h : C[b] ∈ Φ.cones) (j : Fin 2) :
    C[b,j] ∈ (Φ.starSubdivisionAlong hΦ h).cones := by
  let hreg := isRegular_iff.mp hΦ _ h
  obtain ⟨e, he⟩ := hreg.exists_rayEquiv_of_basis Φ.lattice b rfl
  apply (Φ.mem_starSubdivisionAlong_cones hΦ h).mpr
  refine Or.inr ⟨_, h, le_rfl, ?_⟩
  have hj := hreg.starSubdivisionCone_pair_mem Φ.lattice e j
  dsimp only at hj
  rwa [hreg.starSubdivisionCone_pair_eq_hull Φ.lattice b e he] at hj

private theorem basisCone_card (hi : IsIntegralLattice i) (b : Basis (Fin 2) ℤ N) :
    Nat.card (ToricRay C[b]) = 2 := by
  let e := toricRayEquivOfLinearIndependent (i ∘ b) (hi.linearIndependent_basis b) rfl
  rw [Nat.card_congr e, Nat.card_fin]

private theorem basisCone_eq_of_le (hΦ : Φ.IsRegular) {b d : Basis (Fin 2) ℤ N}
    (hb : C[b] ∈ Φ.cones) (hd : C[d] ∈ Φ.cones) (hle : C[b] ≤ C[d]) :
    C[b] = C[d] := by
  have hdim : Module.finrank ℤ N = 2 := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  exact congrArg Subtype.val (Φ.eq_of_le_fullCone hΦ (σ := ⟨_, hb⟩) (τ := ⟨_, hd⟩)
    hdim (basisCone_card Φ.lattice b) hle)

/-- Successively subdividing distinct basis cones gives a regular fan whose rays are
the old rays together with the pairwise sums from those cones. Both new chart cones
at each subdivision remain in the final fan, as does every original cone containing
none of the centers. -/
theorem exists_starSubdivisionAlong_basis_list (hΦ : Φ.IsRegular)
    (B : List (Basis (Fin 2) ℤ N))
    (hB : (B.map (fun (b : Basis (Fin 2) ℤ N) ↦ C[b])).Nodup) (hmem : ∀ b ∈ B, C[b] ∈ Φ.cones) :
    ∃ Ψ : Fan i, Ψ.IsRegular ∧ Relation.ReflTransGen IsTwoRayStarSubdivision Φ Ψ ∧
      (Set.range (Ray.primitiveGenerator (Phi := Ψ)) =
        Set.range (Ray.primitiveGenerator (Phi := Φ)) ∪
          (fun b : Basis (Fin 2) ℤ N ↦ b 0 + b 1) '' {b | b ∈ B}) ∧
      (∀ b ∈ B, ∀ j : Fin 2, C[b,j] ∈ Ψ.cones) ∧
      ∀ σ ∈ Φ.cones, (∀ b ∈ B, ¬ C[b] ≤ σ) → σ ∈ Ψ.cones := by
  induction B generalizing Φ with
  | nil => exact ⟨Φ, hΦ, .refl, by simp⟩
  | cons b B ih =>
    have hb := hmem b List.mem_cons_self
    have hcard := basisCone_card Φ.lattice b
    have hrest (d) (hd : d ∈ B) : C[d] ∈ Φ.cones := hmem d (List.mem_cons_of_mem _ hd)
    have hne (d) (hd : d ∈ B) : C[b] ≠ C[d] := fun h ↦
      (List.nodup_cons.mp hB).1 (List.mem_map.mpr ⟨d, hd, h.symm⟩)
    have hnot (d) (hd : d ∈ B) : ¬ C[b] ≤ C[d] :=
      fun h ↦ hne d hd (basisCone_eq_of_le hΦ hb (hrest d hd) h)
    obtain ⟨Ψ, hΨ, hpath, hr, hchart, hkeep⟩ := ih (Φ.isRegular_starSubdivisionAlong hΦ hb)
      (List.nodup_cons.mp hB).2
      (fun d hd ↦ Φ.mem_starSubdivisionAlong_cones_of_not_le hΦ hb (hrest d hd) (hnot d hd))
    refine ⟨Ψ, hΨ, hpath.head (.along hΦ ⟨_, hb⟩ hcard), ?_, ?_, ?_⟩
    · have hnew := range_primitiveGenerator_starSubdivisionAlong hΦ ⟨_, hb⟩
        (ne_bot_of_card_toricRay_eq_two hcard)
      rw [primitiveGenerator_starSubdivisionAlongRay_of_basis hΦ ⟨_, hb⟩ b rfl] at hnew
      have hcons : {d | d ∈ b :: B} = insert b {d | d ∈ B} :=
        Set.ext fun _ ↦ List.mem_cons
      rw [hr, hnew, hcons, Set.image_insert_eq, Set.insert_union, Set.union_insert]
    · intro d hd j
      rcases List.mem_cons.mp hd with hd | hd
      · subst d
        exact hkeep _ (basisChart_mem_starSubdivisionAlong hΦ b hb j) (fun d hd hle ↦
          hne d hd (basisCone_eq_of_le hΦ (hrest d hd) hb (hle.trans (basisChart_le b j))).symm)
      · exact hchart d hd j
    · intro σ hσ hnone
      exact hkeep σ (Φ.mem_starSubdivisionAlong_cones_of_not_le hΦ hb hσ
        (hnone b List.mem_cons_self)) (fun d hd ↦ hnone d (List.mem_cons_of_mem _ hd))

end TauCeti.Toric.Fan
