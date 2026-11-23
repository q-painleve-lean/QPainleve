/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Boundary
public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus

import TauCeti.AlgebraicGeometry.Blowup.Restriction

/-!
# Isomorphism locus of an ordered boundary blowup

An ordered blowup along a boundary is an isomorphism away from the images of
the original center supports. The argument includes repeated centers, since every
strict boundary embedding commutes with the projection to the original scheme.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Scheme.IdealSheafData

namespace QPainleve.BlowupTower

universe u

/-- Every open avoiding all the original centers is in the isomorphism locus of
the ordered blowup projection. -/
theorem isIso_morphismRestrict_alongBoundary {D X : Scheme.{u}} (i : D ⟶ X)
    [IsClosedImmersion i] {n : ℕ}
    (J : Fin n → {I : D.IdealSheafData // I.IsEffectiveCartier}) (U : X.Opens)
    (hU : ∀ j, Disjoint (U : Set X) (((J j).val.map i).support : Set X)) :
    IsIso ((alongBoundary i J).2.toTower.toBase ∣_ U) := by
  induction n with
  | zero =>
    rw [alongBoundary_zero i J]
    rw [WithBoundary.toTower_nil, toBase_nil]
    infer_instance
  | succ n ih =>
    let A := alongBoundary i fun j : Fin n ↦ J j.castSucc
    let T := A.2
    let K := (J (Fin.last n)).val
    have hprefix : IsIso (T.toTower.toBase ∣_ U) := ih _ (fun j ↦ hU j.castSucc)
    have hd : Disjoint (↑(T.toTower.toBase ⁻¹ᵁ U) : Set A.1)
        ((K.map T.boundaryι).support : Set A.1) := by
      rw [support_map, Closeds.coe_closure,
        (T.boundaryι.isClosedEmbedding.isClosedMap _ K.support.isClosed).closure_eq]
      apply Set.disjoint_left.mpr
      rintro _ hy ⟨z, hz, rfl⟩
      have hzi : i z ∈ U := by
        simpa only [← Scheme.Hom.comp_apply, T.boundaryι_toBase] using
          T.toTower.toBase.mem_preimage.mp hy
      apply Set.disjoint_left.mp (hU (Fin.last n)) hzi
      rw [support_map, Closeds.coe_closure]
      exact subset_closure ⟨z, hz, rfl⟩
    have hlast := (K.map T.boundaryι).isIso_blowupToBase_restrict_of_disjoint_support hd
    have hc : IsIso (((K.map T.boundaryι).blowupToBase ≫ T.toTower.toBase) ∣_ U) := by
      rw [morphismRestrict_comp]
      exact IsIso.comp_isIso' hlast hprefix
    rw [alongBoundary_succ i J]
    rw [WithBoundary.toTower_snoc, toBase_snoc]
    exact hc

/-- The centre of the projection from an ordered boundary blowup is contained in
the union of the original center supports. -/
theorem centre_subset_iUnion_alongBoundary {D X : Scheme.{u}} (i : D ⟶ X)
    [IsClosedImmersion i] {n : ℕ}
    (J : Fin n → {I : D.IdealSheafData // I.IsEffectiveCartier}) :
    (alongBoundary i J).2.toTower.toBase.centre ⊆
      ⋃ j, (((J j).val.map i).support : Set X) := by
  let V (j : Fin n) := (((J j).val.map i).support : Set X)
  let U : X.Opens := ⟨(⋃ j, V j)ᶜ, (isClosed_iUnion_of_finite fun j ↦
    ((J j).val.map i).support.isClosed).isOpen_compl⟩
  have hU (j : Fin n) : Disjoint (U : Set X) (V j) :=
    disjoint_compl_left.mono_right (Set.subset_iUnion V j)
  have h := ((alongBoundary i J).2.toTower.toBase.le_isoLocus_iff).mpr
    (isIso_morphismRestrict_alongBoundary i J U hU)
  intro x hx
  rw [Scheme.Hom.centre_def, Set.mem_compl_iff, SetLike.mem_coe] at hx
  by_contra hx'
  have hxU : x ∈ U := hx'
  exact hx (h hxU)

end QPainleve.BlowupTower
