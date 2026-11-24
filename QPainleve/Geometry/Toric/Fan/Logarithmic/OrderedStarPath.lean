/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Path.Vertices
public import QPainleve.Geometry.Toric.Fan.InternalBlowup
public import QPainleve.Geometry.Toric.Fan.Logarithmic.StarFactorization
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

import QPainleve.AlgebraicGeometry.Morphisms.Modification.Birational
import QPainleve.Geometry.Toric.Fan.Logarithmic.Comparison
import QPainleve.Geometry.Toric.Fan.StarSubdivision.Tower
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition

/-!
# Ordered internal models along resolved toric paths

The regular partial composites in a sequence of toric blowups and blowdowns can all be
read on one ordered internal blowup model. The intermediate fan refines every fan of
the path, and the ordered tower and its strict boundary are shared by all projections.
This applies to the toric portions of the resolved factorization in [Lutz, Theorem 8.4][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=68
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan.LogarithmicProjection

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "π[" H "]" => FanHom.algebraicMap (IsSubdivision.toFanHom H)

variable {Z : Scheme} [Z.Over S] [SmoothOfRelativeDimension 2 (Z ↘ S)]
  {D : Z.IdealSheafData} {A B : LogarithmicProjection i D}

private theorem StarStep.isModification_target (step : StarStep A B)
    (hN : Module.finrank ℤ N = 2) (hA : IsModification A.hom) : IsModification B.hom := by
  cases step with
  | blowup h comm =>
    let H := h.isSubdivision
    let : IsModification π[H] :=
      H.isModification_algebraicMap A.isRegular B.isRegular A.isComplete.nonempty_cones hN
    let : IsModification (B.hom ≫ π[H]) := comm.symm ▸ hA
    exact IsModification.of_comp_right B.hom π[H]
  | blowdown h comm =>
    let H := h.isSubdivision
    let : IsModification A.hom := hA
    let : IsModification π[H] :=
      H.isModification_algebraicMap B.isRegular A.isRegular B.isComplete.nonempty_cones hN
    rw [← comm]
    infer_instance

variable [IsIntegral Z] [Z.IsProjectiveOver ℂ]

/-- A specified ordered internal model of the first projection of a resolved toric
path realizes every projection on the path, by subdividing each successive target fan.
Every projection is a modification. The resolving isomorphism and the ordered
centers are the same at every vertex. -/
theorem exists_subdivisions_of_toric_internal_factorization (p : Quiver.Path A B)
    (b : Module.Basis (Fin 2) ℤ N) {Θ : Fan i} (hΘ : Θ.IsRegular)
    (J : Θ.IsSubdivision A.fan) {m : ℕ} (r : Fin m → Θ.Ray) (c : Fin m → ℂˣ) :
    letI := J.nonempty_cones_of_nonempty A.isComplete.nonempty_cones
    let T := Θ.internalBlowupTower b r c
    ∀ (e : T.1 ≅ Z), e.hom ≫ A.hom = T.2.toTower.toBase ≫ π[J] →
      D.comap e.hom = T.2.boundaryι.ker →
      ∀ C ∈ p.vertices, IsModification C.hom ∧ ∃ K : Θ.IsSubdivision C.fan,
        e.hom ≫ C.hom = T.2.toTower.toBase ≫ π[K] := by
  intro T e he hD
  have hN : Module.finrank ℤ N = 2 :=
    (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  have hA : IsModification A.hom := by
    let : Nonempty Θ.cones := J.nonempty_cones_of_nonempty A.isComplete.nonempty_cones
    let : IsModification T.2.toTower.toBase := Θ.isModification_internalBlowupTower_toBase b r c hΘ
    let : IsModification π[J] :=
      J.isModification_algebraicMap A.isRegular hΘ A.isComplete.nonempty_cones hN
    have h : A.hom = e.inv ≫ T.2.toTower.toBase ≫ π[J] := by
      rw [← he, Iso.inv_hom_id_assoc]
    rw [h]
    infer_instance
  induction p with
  | nil =>
    intro C hC
    have hCA : C = A := by simpa only [Quiver.Path.vertices_nil, List.mem_singleton] using hC
    subst C
    exact ⟨hA, J, he⟩
  | @cons U W p step ih =>
    intro C hC
    rcases (Quiver.Path.mem_vertices_cons p step).mp hC with hC | hCW
    · exact ih C hC
    subst C
    obtain ⟨hU, K, hk⟩ := ih U p.end_mem_vertices
    refine ⟨step.isModification_target hN hU, ?_⟩
    cases step with
    | blowup h comm =>
      let : IsModification U.hom := hU
      exact h.isSubdivision.exists_lift_of_toric_internal_factorization b U.isRegular
        W.isRegular U.isComplete hΘ K r c comm U.comap_boundaryIdeal e hk hD
    | blowdown h comm =>
      refine ⟨K.trans h.isSubdivision, ?_⟩
      rw [← comm, ← Category.assoc, hk, Category.assoc,
        IsSubdivision.toFanHom_trans K h.isSubdivision, FanHom.algebraicMap_comp]

/-- One regular fan and one ordered internal model suffice for all the specified
regular projections of a resolved toric path. The strict boundary of that model
pulls back the common pole ideal. -/
theorem exists_toric_internal_factorization_of_star_path (p : Quiver.Path A B)
    [IsModification A.hom] (b : Module.Basis (Fin 2) ℤ N) :
    ∃ (Θ : Fan i) (_ : Θ.IsRegular) (J : Θ.IsSubdivision A.fan),
      letI := J.nonempty_cones_of_nonempty A.isComplete.nonempty_cones
      ∃ (m : ℕ) (r : Fin m → Θ.Ray) (c : Fin m → ℂˣ),
        let T := Θ.internalBlowupTower b r c
        ∃ e : T.1 ≅ Z, D.comap e.hom = T.2.boundaryι.ker ∧
          ∀ C ∈ p.vertices, IsModification C.hom ∧ ∃ K : Θ.IsSubdivision C.fan,
            e.hom ≫ C.hom = T.2.toTower.toBase ≫ π[K] := by
  obtain ⟨Θ, hΘ, J, m, r, c, e, he, hD⟩ :=
    A.fan.exists_toric_internal_factorization_of_boundary_comap_eq b A.isRegular A.isComplete
      (IsModification.birationalOver A.hom) A.comap_boundaryIdeal
  exact ⟨Θ, hΘ, J, m, r, c, e, hD,
    exists_subdivisions_of_toric_internal_factorization p b hΘ J r c e he hD⟩

end TauCeti.Toric.Fan.LogarithmicProjection
