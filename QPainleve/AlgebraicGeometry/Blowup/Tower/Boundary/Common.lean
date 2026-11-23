/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Boundary

/-!
# Lifting isomorphisms from compatible boundary maps

An ambient isomorphism can match the ordered centers by means of maps from a common
part of the two boundaries. The lift then identifies the strict transforms of that
part at every stage, including when a center is repeated.
-/

public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower

variable {D D' U X X' : Scheme.{u}} {i : D ⟶ X} {i' : D' ⟶ X'}
  [IsClosedImmersion i] [IsClosedImmersion i']

/-- An ambient isomorphism compatible with two maps from a common boundary scheme
lifts through ordered blowups whose centers factor through that scheme. The common
boundary maps remain compatible on the final surfaces. -/
theorem exists_isLift_alongBoundary_of_common (e : X ≅ X') (a : U ⟶ D) (a' : U ⟶ D')
    (ha : a ≫ i ≫ e.hom = a' ≫ i') {n : ℕ} {S : Fin n → Scheme.{u}}
    (t : ∀ j, S j ⟶ U) (s : ∀ j, S j ⟶ D) (s' : ∀ j, S j ⟶ D')
    (hs : ∀ j, t j ≫ a = s j) (hs' : ∀ j, t j ≫ a' = s' j)
    (hC : ∀ j, (s j).ker.IsEffectiveCartier) (hC' : ∀ j, (s' j).ker.IsEffectiveCartier)
    (hU : ∀ j, ((s j).ker.comap a).IsEffectiveCartier) :
    let A := alongBoundary i (fun j ↦ ⟨(s j).ker, hC j⟩)
    let A' := alongBoundary i' (fun j ↦ ⟨(s' j).ker, hC' j⟩)
    ∃ g : A.1 ≅ A'.1, IsLift e A.2.toTower A'.2.toTower g ∧
      a ≫ A.2.boundaryι ≫ g.hom = a' ≫ A'.2.boundaryι := by
  dsimp only
  induction n with
  | zero =>
    rw [alongBoundary_zero i, alongBoundary_zero i']
    simp only [WithBoundary.toTower_nil, WithBoundary.boundaryι_nil]
    exact ⟨e, IsLift.nil_iff.mpr rfl, ha⟩
  | succ n ih =>
    let T := (alongBoundary i (fun j : Fin n ↦ ⟨(s j.castSucc).ker, hC j.castSucc⟩)).2
    let T' := (alongBoundary i' (fun j : Fin n ↦ ⟨(s' j.castSucc).ker, hC' j.castSucc⟩)).2
    let j := Fin.last n
    obtain ⟨g, hg, hb⟩ := ih (t := fun k ↦ t k.castSucc) (s := fun k ↦ s k.castSucc)
      (s' := fun k ↦ s' k.castSucc) (fun k ↦ hs k.castSucc) (fun k ↦ hs' k.castSucc)
      (fun k ↦ hC k.castSucc) (fun k ↦ hC' k.castSucc) (fun k ↦ hU k.castSucc)
    have hpoint : (s j ≫ T.boundaryι) ≫ g.hom = s' j ≫ T'.boundaryι := by
      rw [← hs j, ← hs' j]
      simpa only [Category.assoc] using congrArg (t j ≫ ·) hb
    have hcenter : ((s' j).ker.map T'.boundaryι).comap g.hom =
        (s j).ker.map T.boundaryι := by
      rw [map_ker, ← hpoint, ← map_ker, comap_map_of_isClosedImmersion, map_ker]
    rw [alongBoundary_succ i, alongBoundary_succ i']
    simp only [WithBoundary.toTower_snoc]
    exact ⟨_, hg.snoc hcenter, T.comp_boundaryι_snoc_blowupIso_hom (s j).ker g a a' hb
      (s' j).ker hcenter (hC j) (hC' j) (hU j)⟩

end QPainleve.BlowupTower
