/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Boundary

/-!
# Recovering the centers of ordered boundary blowups

An isomorphism of ordered blowup towers recovers the prescribed center ideals on
the original boundary, even when later centers are infinitely near. At each step
the boundary embedding projects isomorphically onto the fixed boundary.
-/

public section

open AlgebraicGeometry CategoryTheory
open Scheme.IdealSheafData

namespace QPainleve.BlowupTower.IsLift

universe u

variable {D D' X X' : Scheme.{u}} {i : D ⟶ X} {i' : D' ⟶ X'}
  [IsClosedImmersion i] [IsClosedImmersion i'] {n : ℕ}
  {e : X ≅ X'} {d : D ≅ D'}
  {J : Fin n → {I : D.IdealSheafData // I.IsEffectiveCartier}}
  {J' : Fin n → {I : D'.IdealSheafData // I.IsEffectiveCartier}}
  {g : (alongBoundary i J).1 ≅ (alongBoundary i' J').1}

/-- A lift of the ordered towers matches the ideals of the original boundary centers
index by index. The base isomorphism restricts to the given boundary isomorphism. -/
theorem comap_centres_alongBoundary
    (h : IsLift e (alongBoundary i J).2.toTower (alongBoundary i' J').2.toTower g)
    (hi : i ≫ e.hom = d.hom ≫ i') (j : Fin n) :
    (J' j).val.comap d.hom = (J j).val := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    -- Rewrite the towers together with the types of their terminal schemes.
    revert g
    rw [alongBoundary_succ, alongBoundary_succ]
    intro g h
    let T := (alongBoundary i (fun k : Fin n ↦ J k.castSucc)).2
    let T' := (alongBoundary i' (fun k : Fin n ↦ J' k.castSucc)).2
    simp only [WithBoundary.toTower_snoc] at h
    obtain ⟨f, hf, hcenter, -⟩ := IsLift.snoc_iff.mp h
    refine Fin.lastCases ?_ (fun k ↦ ih hf k) j
    let C := (J (Fin.last n)).val
    let C' := (J' (Fin.last n)).val
    have hmap : (C.map T.boundaryι).map f.hom = C'.map T'.boundaryι := by
      rw [← hcenter, map_comap_of_isClosedImmersion, Scheme.Hom.ker_eq_bot_of_isIso, sup_bot_eq]
    have hbase := congrArg (fun I : Scheme.IdealSheafData _ ↦
      I.map T'.toTower.toBase) hmap
    have hs : f.hom ≫ T'.toTower.toBase = T.toTower.toBase ≫ e.hom := hf.hom_toBase
    rw [← map_comp C', ← map_comp (C.map T.boundaryι), ← map_comp C, hs,
      T.boundaryι_toBase_assoc, T'.boundaryι_toBase, hi, map_comp] at hbase
    have he : C.map d.hom = C' := by
      simpa only [comap_map_of_isClosedImmersion] using congrArg (fun I ↦ I.comap i') hbase
    exact (congrArg (fun I ↦ I.comap d.hom) he.symm).trans (comap_map_of_isClosedImmersion C _)

end QPainleve.BlowupTower.IsLift
