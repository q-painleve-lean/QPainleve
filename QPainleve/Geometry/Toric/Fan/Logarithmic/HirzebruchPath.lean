/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Factorization
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.QuadricPreparation

/-!
# Resolved paths for Hirzebruch preparation

Each elementary transformation in the preparation to a quadric is a blowup
followed by a blowdown. The projection to the common fan determines the
regular representative at each intermediate fan and gives all vertices the
same pole ideal. This is the preparation in
[Lutz, Proposition 8.11, Case C][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=73
-/

public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan.HirzebruchQuadricPreparation

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} {b : Module.Basis (Fin 2) ℤ N} {a : ℕ}
  (P : HirzebruchQuadricPreparation b a Φ)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "π[" H "]" => FanHom.algebraicMap (IsSubdivision.toFanHom H)
local notation "rankTwo" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)

variable {Z : Scheme} [Z.Over S] [SmoothOfRelativeDimension 2 (Z ↘ S)]
  {D : Z.IdealSheafData} (C : LogarithmicProjection i D) (hC : C.fan = P.common)

open LogarithmicProjection

/-- The toric preparation gives a resolved Sarkisov path with two edges per
elementary transformation, from the specified Hirzebruch projection to the
projection to the quadric. Its rational map identifies the dense tori. -/
theorem exists_sarkisov_path_of_quadric_preparation [IsIntegral Z] :
    ∃ (A B : LogarithmicProjection i D) (p : SarkisovPath A B),
      A.fan = Φ ∧ A.hom ≍ C.hom ≫ π[hC ▸ P.common_source] ∧
      B.fan = P.model 0 ∧ B.hom ≍ C.hom ≫ π[hC ▸ P.common_model 0] ∧
      @Quiver.Path.length _ sarkisovQuiver _ _ p = 2 * a ∧
      p.rationalMap = (Scheme.PartialIso.ofDenseOpenImmersions
        (Fan.denseTorusι A.fan inferInstance)
        (Fan.denseTorusι B.fan inferInstance)).toRationalMap := by
  let model (j : Fin (a + 1)) :=
    C.coarsen (hC ▸ P.common_model j) (P.model_regular j) rankTwo
  let link (j : Fin a) := C.coarsen (hC ▸ P.common_link j) (P.link_regular j) rankTwo
  have hpath (j : Fin (a + 1)) : ∃ p : Quiver.Path (model j) (model 0), p.length = 2 * j.val := by
    induction j using Fin.induction with
    | zero => exact ⟨.nil, rfl⟩
    | succ j ih =>
      obtain ⟨p, hp⟩ := ih
      obtain ⟨σ, τ, hσ, hτ, hcardσ, hcardτ, -, -, hσeq, hτeq⟩ := P.link_corners j
      have up : (P.model j.succ).IsTwoRayStarSubdivision (P.link j) :=
        hσeq ▸ .along hσ σ hcardσ
      have down : (P.model j.castSucc).IsTwoRayStarSubdivision (P.link j) :=
        hτeq ▸ .along hτ τ hcardτ
      let J : C.fan.IsSubdivision (P.link j) := hC ▸ P.common_link j
      let e₁ : StarStep (model j.succ) (link j) :=
        C.coarsenBlowup rankTwo (P.model_regular _) (P.link_regular j) up J
      let e₂ : StarStep (link j) (model j.castSucc) :=
        Quiver.reverse (a := model j.castSucc) (b := link j)
          (C.coarsenBlowup rankTwo (P.model_regular _) (P.link_regular j) down J)
      refine ⟨((Quiver.Path.nil.cons e₁).cons e₂).comp p, ?_⟩
      simp only [Quiver.Path.length_comp, Quiver.Path.length_cons, Quiver.Path.length_nil,
        hp, Fin.val_castSucc, Fin.val_succ]
      omega
  have hsource (Δ : Fan i) (h : P.model (Fin.last a) = Δ) :
      model (Fin.last a) =
        C.coarsen (hC ▸ h ▸ P.common_model (Fin.last a))
          (h ▸ P.model_regular (Fin.last a)) rankTwo := by
    cases h
    rfl
  let A := C.coarsen (hC ▸ P.common_source) (P.source_eq ▸ P.model_regular (Fin.last a)) rankTwo
  have hA : model (Fin.last a) = A := hsource Φ P.source_eq
  obtain ⟨p, hp⟩ := hA ▸ hpath (Fin.last a)
  refine ⟨A, model 0, SarkisovPath.ofStar p, coarsen_fan .., coarsen_hom ..,
    coarsen_fan .., coarsen_hom .., ?_, ?_⟩
  · simpa only [SarkisovPath.length_ofStar, Fin.val_last] using hp
  · rw [SarkisovPath.rationalMap_ofStar, pathRationalMap_eq_denseTorusPartialIso]

end TauCeti.Toric.Fan.HirzebruchQuadricPreparation
