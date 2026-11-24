/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Plane.Factorization
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Plane.Terminal.Path

import QPainleve.AlgebraicGeometry.IdealSheaf.Restriction
import TauCeti.Combinatorics.Quiver.Prefunctor

/-!
# The resolved plane step in Sarkisov induction

A specified plane-to-plane resolution either gives the terminal toric isomorphism
with translation, or gives a decreasing path on a nodal blowup tower. In the second
case the Hirzebruch marking supplies the next bidegree, and the original target
projection pulls back to the same resolving surface.

This is the plane-source step of [Lutz, Theorem 8.4](https://arxiv.org/pdf/2005.05010v3#page=73).
-/

public section

open AlgebraicGeometry CategoryTheory Module
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData TauCeti.SymmetricAlgebra
open TauCeti.Toric Fan.LogarithmicProjection
open scoped Sarkisov

namespace QPainleve.BlowupTower.IsClosedPointTower

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "s" => (P ↘ S)
local notation "coords" => Pi.basisFun ℂ (Fin 3)
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "plane[" d "," h "]" => Fan.projectiveSpace d h
local notation "planeIso[" d "," h "]" =>
  (Fan.projectivePlaneIso d h ≪≫ Basis.polynomialProjIso coords)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Basis (Fin 2) ℤ N} {hi : IsIntegralLattice i}
  {Y : Scheme} {n : ℕ} {T : BlowupTower P n Y}
  {hT : IsClosedPointTower P T} {g : Y ⟶ P} {D : Y.IdealSheafData}

local notation "over(" X ")" => (X ↘ S)
local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)

private theorem PlaneSarkisovDecrease.refinement_comp_over
    (R : PlaneSarkisovDecrease b hi hT g D) :
    R.refinement ≫ T.toBase ≫ s =
      R.first ≫ over(_) := by
  let J := Fan.starSubdivisionAlong_isSubdivision (plane[b,hi])
    (Fan.isRegular_projectiveSpace b hi)
    (Fan.projectiveSpaceMaximalCone b hi R.vertexIndex).property R.vertexCone_ne_bot
  let : Nonempty (plane[b,hi]).cones :=
    (Fan.isComplete_projectiveSpace b hi).nonempty_cones
  let : Nonempty (Fan.starSubdivisionAlong (plane[b,hi])
      (Fan.isRegular_projectiveSpace b hi)
      (Fan.projectiveSpaceMaximalCone b hi R.vertexIndex).property).cones :=
    J.nonempty_cones_of_nonempty inferInstance
  let := Fan.projectivePlaneIso_trans_polynomialProjIso_hom_isOver b hi coords
  have h := (reassoc_of% R.first_comp) s
  rw [comp_over (planeIso[b,hi]).hom S, comp_over J.toFanHom.algebraicMap S] at h
  simpa only [Category.assoc] using h.symm

/-- The decreasing plane block on the actual nodal tower, with both its starting
projection and the pulled-back plane target on the tower's top. Its last projection
is the one given by the marked Hirzebruch resolution. -/
private theorem PlaneSarkisovDecrease.exists_path_on_nodalTower
    (R : PlaneSarkisovDecrease b hi hT g D)
    (hD : D.IsEffectiveCartier)
    (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ T.toBase ≫ s)) :
    let : Y.Over S := ⟨T.toBase ≫ s⟩
    let : SmoothOfRelativeDimension 2 over(Y) := hT.smoothOfRelativeDimension s
    let : IsIntegral Y := hT.isIntegral s
    let : IsNoetherian Y := T.isNoetherian
    ∀ (A B : Fan.LogarithmicProjection i D),
      A.fan = plane[b,hi] → A.hom ≍ T.toBase ≫ (planeIso[b,hi]).inv →
      let : R.top.Over S := ⟨R.tower.toBase ≫ over(Y)⟩
      let : SmoothOfRelativeDimension 2 over(R.top) :=
        R.nodal.isClosedPointTower.smoothOfRelativeDimension over(Y)
      let : IsIntegral R.top := R.nodal.isClosedPointTower.isIntegral over(Y)
      let E := (D.comap R.tower.toBase).radical
      ∃ (A' C B' : Fan.LogarithmicProjection i E) (p : SarkisovPath A' C),
        A'.fan = A.fan ∧ A'.hom ≍ R.tower.toBase ≫ A.hom ∧
        C.fan = R.fan ∧ C.hom ≍ R.refinementIso.inv ≫ R.modelIso.hom ≫ R.modelTower.toBase ∧
        B'.fan = B.fan ∧ B'.hom ≍ R.tower.toBase ≫ B.hom ∧
        p.length = if R.index = 0 then 3 else 1 := by
  intro hY hSmooth hInt hNoeth A B hA ha hTop hSmoothTop hIntTop E
  let : R.tower.toBase.IsOver S := ⟨rfl⟩
  let : IsModification R.tower.toBase :=
    R.nodal.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two over(Y)
  let : R.resolving.Over S := ⟨R.first ≫ over(_)⟩
  let : SmoothOfRelativeDimension 2 over(R.resolving) := R.smooth
  let := R.integral
  have hq : R.refinementIso.inv ≫ R.refinement = R.tower.toBase := by
    rw [← R.refinementIso_comp, Iso.inv_hom_id_assoc]
  let : R.refinementIso.inv.IsOver S := ⟨by
    calc
      R.refinementIso.inv ≫ over(R.resolving) =
          R.refinementIso.inv ≫ R.refinement ≫ T.toBase ≫ s :=
        congrArg (R.refinementIso.inv ≫ ·) R.refinement_comp_over.symm
      _ = over(R.top) := by rw [← Category.assoc, hq]; rfl⟩
  let : Smooth over(R.top) := hSmoothTop.smooth
  let : Smooth over(R.resolving) := R.smooth.smooth
  have hPole := R.nodal.comap_eq_radical_mul_ramificationIdealSheaf_of_iso hD hNode
    (Iso.refl R.top) R.tower.toBase (Category.id_comp _)
  -- Identify the reduced total pole ideal on the tower with the one on the link model.
  have hIsoPole :
      ((D.comap R.refinement).radical).comap R.refinementIso.inv =
        E * ramificationIdealSheaf ℂ R.refinementIso.inv := by
    rw [ramificationIdealSheaf_eq_top_of_isOpenImmersion, mul_top,
      ← radical_comap_of_isOpenImmersion, ← comap_comp, hq]
  obtain ⟨A₀, C₀, p, hA₀, ha₀, hC₀, hc₀, hp⟩ := R.exists_path
  let F := precomposeSarkisov (i := i) rankTwo R.refinementIso.inv hIsoPole
  let G := precomposeSarkisov (i := i) rankTwo R.tower.toBase hPole
  refine ⟨F.obj A₀, F.obj C₀, G.obj B, F.mapPath p,
    (precomposeSarkisov_obj_fan ..).trans (hA₀.trans hA.symm), ?_,
    (precomposeSarkisov_obj_fan ..).trans hC₀, ?_,
    precomposeSarkisov_obj_fan .., precomposeSarkisov_obj_hom .., ?_⟩
  · have h := heq_comp (f := R.refinementIso.inv) (f' := R.refinementIso.inv)
      rfl rfl (congrArg Fan.algebraicRealization hA₀) HEq.rfl ha₀
    have hRefined : R.refinementIso.inv ≫ (R.refinement ≫ T.toBase ≫ (planeIso[b,hi]).inv) =
        R.tower.toBase ≫ (T.toBase ≫ (planeIso[b,hi]).inv) := by
      rw [← Category.assoc, hq]
    exact (precomposeSarkisov_obj_hom ..).trans (h.trans ((heq_of_eq hRefined).trans
      (heq_comp rfl rfl (congrArg Fan.algebraicRealization hA)
        (HEq.rfl : R.tower.toBase ≍ R.tower.toBase) ha).symm))
  · exact (precomposeSarkisov_obj_hom ..).trans
      (heq_comp rfl rfl (congrArg Fan.algebraicRealization hC₀) HEq.rfl hc₀)
  · simpa only [Prefunctor.length_mapPath] using hp

/-- A specified logarithmic plane resolution either terminates on the given
resolving surface or admits a decreasing block on a nodal refinement of length
at most one. The latter branch retains the Hirzebruch tower with its smaller
bidegree and the specified target map, ready for the next step of induction. -/
theorem exists_sarkisov_path_or_decrease_of_logarithmic_plane
    (b b' : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)
    (hT : IsClosedPointTower P T) (g : Y ⟶ P)
    (hg : g ≫ s = T.toBase ≫ s) (hbir : Scheme.BirationalOver g (𝟙 P))
    (hD : D.IsEffectiveCartier)
    (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ T.toBase ≫ s)) :
    let : Y.Over S := ⟨T.toBase ≫ s⟩
    let : SmoothOfRelativeDimension 2 over(Y) := hT.smoothOfRelativeDimension s
    let : IsIntegral Y := hT.isIntegral s
    let : IsNoetherian Y := T.isNoetherian
    ∀ (A B : Fan.LogarithmicProjection i D),
      A.fan = plane[b,hi] → B.fan = plane[b',hi] →
      A.hom ≍ T.toBase ≫ (planeIso[b,hi]).inv →
      B.hom ≍ g ≫ (planeIso[b',hi]).inv →
      (∃ p : SarkisovPath A B, p.length = 1) ∨
        ∃ R : PlaneSarkisovDecrease b hi hT g D,
          let : R.top.Over S := ⟨R.tower.toBase ≫ over(Y)⟩
          let : SmoothOfRelativeDimension 2 over(R.top) :=
            R.nodal.isClosedPointTower.smoothOfRelativeDimension over(Y)
          let : IsIntegral R.top := R.nodal.isClosedPointTower.isIntegral over(Y)
          let E := (D.comap R.tower.toBase).radical
          ∃ (A' C B' : Fan.LogarithmicProjection i E) (p : SarkisovPath A' C),
            A'.fan = A.fan ∧ A'.hom ≍ R.tower.toBase ≫ A.hom ∧
            C.fan = R.fan ∧ C.hom ≍ R.refinementIso.inv ≫ R.modelIso.hom ≫ R.modelTower.toBase ∧
            B'.fan = B.fan ∧ B'.hom ≍ R.tower.toBase ≫ B.hom ∧
            p.length = if R.index = 0 then 3 else 1 := by
  intro hY hSmooth hInt hNoeth A B hA hB ha hb
  let : IsNoetherian P := isNoetherian_of_finiteType s
  let x := (T.picardMarking hT s).symm (Additive.ofMul (pullback g H))
  by_cases hd : (Basis.picardTwistEquiv coords) x.1 = 1
  · obtain ⟨_, _, p, hp, -⟩ :=
      hT.exists_sarkisov_path_of_plane_degree_one b b' hi g hg hbir hd A B hA hB ha hb
    exact Or.inl ⟨p, hp⟩
  · rcases A with ⟨Φ, hreg, hc, a, haOver, haDom, haPole⟩
    dsimp only at hA ha
    subst Φ
    obtain rfl : a = T.toBase ≫ (planeIso[b,hi]).inv := eq_of_heq ha
    let : Smooth over(Y) := hSmooth.smooth
    let : T.toBase.IsOver S := ⟨rfl⟩
    let := Fan.projectivePlaneIso_trans_polynomialProjIso_hom_isOver b hi coords
    let : Nonempty (plane[b,hi]).cones := hc.nonempty_cones
    have hRank := (finrank_eq_card_basis b).trans (Fintype.card_fin 2)
    let : SmoothOfRelativeDimension 2 over((plane[b,hi]).algebraicRealization) := by
      simpa only [hRank, Fan.algebraicRealization_over] using
        (plane[b,hi]).smoothOfRelativeDimension_algebraicRealizationStructureMap hreg
    simp only [comap_comp, ramificationIdealSheaf_comp ℂ T.toBase (planeIso[b,hi]).inv 2,
      ramificationIdealSheaf_eq_top_of_isOpenImmersion, comap_top, mul_top,
      ← hT.ramificationIdealSheafToBase_def ℂ] at haPole
    obtain ⟨R⟩ := hT.nonempty_planeSarkisovDecrease b hi g D hg hbir hD hNode haPole hd
    exact Or.inr ⟨R, R.exists_path_on_nodalTower hD hNode _ B rfl HEq.rfl⟩

end QPainleve.BlowupTower.IsClosedPointTower
