/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Factorization.Iso
public import QPainleve.Geometry.Toric.Fan.Logarithmic.Induction
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Induction.Marking

import QPainleve.AlgebraicGeometry.Blowup.Tower.PlaneResolution
import QPainleve.AlgebraicGeometry.Curves.Node.Comap
import QPainleve.SignedClusterModularGroup.SarkisovDegree.Induction.NegativeSection
import QPainleve.SignedClusterModularGroup.SarkisovDegree.Plane.Induction
import QPainleve.SignedClusterModularGroup.SarkisovDegree.Quadric.Factorization
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced

/-!
# Marked steps of plane-target Sarkisov factorization

The terminal plane step and the decreasing plane, quadric and negative-section
blocks apply in the coordinates of a marked point tower. Transporting the block
back to the specified resolution keeps its two projections and the pole ideal,
including when one further nodal blowup is needed. The new marking computes the
decrease for the same target map.

See [Lutz, Theorem 8.4][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=73
-/

public section

open AlgebraicGeometry CategoryTheory Module QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan.LogarithmicProjection

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "s" => (P ↘ S)
local notation "coords" => Pi.basisFun ℂ (Fin 3)
local notation "H" => LineBundleClass.mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "plane[" b "," hi "]" => Fan.projectiveSpace b hi
local notation "planeIso[" b "," hi "]" =>
  (Fan.projectivePlaneIso b hi ≪≫ Basis.polynomialProjIso coords)
local notation "mark[" T "," hT "," f "," g "]" =>
  LinearEquiv.symm (BlowupTower.picardMarking T hT f) (Additive.ofMul (pullback g H))
local notation "obj[" F "," A "]" => @Prefunctor.obj _ sarkisovQuiver _ sarkisovQuiver F A
local notation "mapPath[" F "," p "]" =>
  @Prefunctor.mapPath _ sarkisovQuiver _ sarkisovQuiver F _ _ p

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {X : Scheme} [X.Over S] [SmoothOfRelativeDimension 2 (X ↘ S)]
  [IsIntegral X] [IsNoetherian X] {D : X.IdealSheafData}
  {A B : LogarithmicProjection i D}

local notation "over[" U "]" => OverClass.ofHom ((BlowupTower.toBase U) ≫ _ ↘ S)
local notation "smooth[" h "]" =>
  IsClosedPointTower.smoothOfRelativeDimension (IsPointTowerWith.isClosedPointTower h) (_ ↘ S)
local notation "integral[" h "]" =>
  IsClosedPointTower.isIntegral (IsPointTowerWith.isClosedPointTower h) (_ ↘ S)
local notation "total[" D "," U "]" =>
  Scheme.IdealSheafData.radical (Scheme.IdealSheafData.comap D (BlowupTower.toBase U))

/-- The decreasing alternative of plane-target Sarkisov induction. The path
starts at the pullback of the specified first projection. Its last vertex has a
strictly smaller marking with the pullback of the same target projection. -/
abbrev HasPlaneTargetDecrease (A B : LogarithmicProjection i D)
    (hRank : finrank ℤ N = 2) (hD : D.IsEffectiveCartier)
    (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S))
    (d : ℕ ×ₗ ℕ) : Prop :=
  ∃ (next : ℕ ×ₗ ℕ) (_ : next < d)
    (m : ℕ) (Y : Scheme) (U : BlowupTower X m Y)
    (hU : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) U),
    letI : Y.Over S := over[U]
    letI : SmoothOfRelativeDimension 2 (Y ↘ S) := smooth[hU]
    letI : IsIntegral Y := integral[hU]
    let F := precomposeSarkisovOfNodalTower (i := i) hRank hD hNode hU
    ∃ C : LogarithmicProjection i total[D,U],
      Nonempty (SarkisovPath (obj[F,A]) C) ∧ HasPlaneTargetMarking C (obj[F,B]) next

section Transport

variable {Y : Scheme} [Y.Over S] [SmoothOfRelativeDimension 2 (Y ↘ S)]
  [IsIntegral Y] [IsNoetherian Y]
  (hRank : finrank ℤ N = 2) (hD : D.IsEffectiveCartier)
  (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S))
  (k : X ≅ Y) [k.hom.IsOver S]

local notation "D₁" => Scheme.IdealSheafData.comap D (Iso.inv k)

omit [SmoothOfRelativeDimension 2 (X ↘ S)] [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
  [SmoothOfRelativeDimension 2 (Y ↘ S)] [IsIntegral Y] [AlgebraicGeometry.IsNoetherian Y] in
private theorem transported_tower_hom_comp {m m' : ℕ} {Z W : Scheme}
    {U : BlowupTower Y m W} {T : BlowupTower X m' Z}
    (e : Z ≅ W) (hT : T.toBase = e.hom ≫ U.toBase ≫ k.inv) :
    e.hom ≫ (U.toBase ≫ Y ↘ S) = T.toBase ≫ X ↘ S := by
  have : k.inv.IsOver S := inferInstance
  rw [hT]
  simp only [Category.assoc, comp_over k.inv S]

omit [SmoothOfRelativeDimension 2 (X ↘ S)] [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
  [SmoothOfRelativeDimension 2 (Y ↘ S)] [IsIntegral Y] [AlgebraicGeometry.IsNoetherian Y] in
private theorem nodalTower_from_iso {m : ℕ} {W : Scheme} {U : BlowupTower Y m W}
    (hU : IsNodalBoundaryTower D₁ (Y ↘ S) (𝟙 Y) U) :
    ∃ (Z : Scheme) (T : BlowupTower X (0 + m) Z) (e : Z ≅ W),
      IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T ∧
      T.toBase = e.hom ≫ U.toBase ≫ k.inv ∧
      total[D,T] = (total[D₁,U]).comap e.hom := by
  let hnil : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) (.nil : BlowupTower X 0 X) := .nil
  have hsup : (Scheme.IdealSheafData.comap D₁ k.hom).support =
      (D.comap (.nil : BlowupTower X 0 X).toBase).support := by
    simp [← comap_comp]
  simpa only [toBase_nil, Category.comp_id] using
    hnil.exists_append_of_iso hU k (by simp) hsup

include hD hNode in
private theorem HasPlaneTargetDecrease.of_iso {m : ℕ} {W : Scheme} {U : BlowupTower Y m W}
    (hU : IsNodalBoundaryTower D₁ (Y ↘ S) (𝟙 Y) U)
    {d next : ℕ ×ₗ ℕ} (hlt : next < d) :
    let : W.Over S := over[U]
    let : SmoothOfRelativeDimension 2 (W ↘ S) := smooth[hU]
    let : IsIntegral W := integral[hU]
    ∀ {A' C B' : LogarithmicProjection i total[D₁,U]} (_ : SarkisovPath A' C),
      A'.fan = A.fan → A'.hom ≍ U.toBase ≫ k.inv ≫ A.hom →
      B'.fan = B.fan → B'.hom ≍ U.toBase ≫ k.inv ≫ B.hom →
      HasPlaneTargetMarking C B' next → HasPlaneTargetDecrease A B hRank hD hNode d := by
  intro hW hSmoothW hIntegralW A' C B' p hA' hhA hB' hhB hmark
  let := hW
  let := hSmoothW
  let := hIntegralW
  obtain ⟨Z, T, e, hT, hbase, hE⟩ := nodalTower_from_iso k hU
  let : Z.Over S := over[T]
  let : SmoothOfRelativeDimension 2 (Z ↘ S) := smooth[hT]
  let : IsIntegral Z := integral[hT]
  let : e.hom.IsOver S := ⟨transported_tower_hom_comp k e hbase⟩
  let F := precomposeSarkisovOfIso (i := i) hRank e hE.symm
  let G := precomposeSarkisovOfNodalTower (i := i) hRank hD hNode hT
  have identify {L : LogarithmicProjection i D} {L' : LogarithmicProjection i total[D₁,U]}
      (hfan : L'.fan = L.fan) (hhom : L'.hom ≍ U.toBase ≫ k.inv ≫ L.hom) :
      obj[F,L'] = obj[G,L] := by
    refine LogarithmicProjection.ext
      (((precomposeSarkisovOfIso_obj_fan ..).trans hfan).trans
        (precomposeSarkisovOfNodalTower_obj_fan ..).symm) ?_
    have h := (precomposeSarkisovOfIso_obj_hom hRank e hE.symm L').trans
      (heq_comp rfl rfl (congrArg Fan.algebraicRealization hfan) HEq.rfl hhom)
    rw [← Category.assoc e.hom, ← Category.assoc (e.hom ≫ U.toBase),
      Category.assoc e.hom U.toBase k.inv, ← hbase] at h
    exact h.trans (precomposeSarkisovOfNodalTower_obj_hom ..).symm
  refine ⟨next, hlt, 0 + m, Z, T, hT, obj[F,C], ⟨identify hA' hhA ▸ mapPath[F,p]⟩, ?_⟩
  rw [← identify hB' hhB]
  exact hmark.of_iso e (precomposeSarkisovOfIso_obj_fan ..) (precomposeSarkisovOfIso_obj_fan ..)
    (precomposeSarkisovOfIso_obj_hom ..) (precomposeSarkisovOfIso_obj_hom ..)

include hD hNode in
private theorem HasPlaneTargetDecrease.of_path_on_iso
    (hn : AtWorstNodalOfRelativeDimensionOne ((D₁).subschemeι ≫ Y ↘ S))
    {d next : ℕ ×ₗ ℕ} (hlt : next < d) {A' C B' : LogarithmicProjection i D₁}
    (p : SarkisovPath A' C) (hA' : A'.fan = A.fan) (hhA : A'.hom ≍ k.inv ≫ A.hom)
    (hB' : B'.fan = B.fan) (hhB : B'.hom ≍ k.inv ≫ B.hom)
    (hm : HasPlaneTargetMarking C B' next) : HasPlaneTargetDecrease A B hRank hD hNode d := by
  let U : BlowupTower Y 0 Y := .nil
  let hU : IsNodalBoundaryTower D₁ (Y ↘ S) (𝟙 Y) U := .nil
  have hrad : (D₁).radical = D₁ := (isReduced_subscheme_iff_radical_eq _).mp hn.isReduced
  have hE : total[D₁,U] = D₁ := by
    simpa only [U, toBase_nil, comap_id] using hrad
  have hs : U.toBase ≫ Y ↘ S = Y ↘ S := by simp [U]
  -- The empty tower keeps the original surface and its reduced pole ideal.
  have transfer {s' : Y ⟶ S} (hs' : s' = Y ↘ S) (hSm : SmoothOfRelativeDimension 2 s')
      {J : Y.IdealSheafData} (hJ : J = D₁) :
      let : Y.Over S := ⟨s'⟩
      let : SmoothOfRelativeDimension 2 (Y ↘ S) := hSm
      ∃ L M R : LogarithmicProjection i J, Nonempty (SarkisovPath L M) ∧
        L.fan = A.fan ∧ L.hom ≍ k.inv ≫ A.hom ∧
        R.fan = B.fan ∧ R.hom ≍ k.inv ≫ B.hom ∧ HasPlaneTargetMarking M R next := by
    subst s' J
    exact ⟨A', C, B', ⟨p⟩, hA', hhA, hB', hhB, hm⟩
  obtain ⟨L, M, R, ⟨q⟩, hL, hhL, hR, hhR, hmark⟩ := transfer hs smooth[hU] hE
  exact HasPlaneTargetDecrease.of_iso hRank hD hNode k hU hlt q hL
    (by simpa only [U, toBase_nil, Category.id_comp] using hhL) hR
    (by simpa only [U, toBase_nil, Category.id_comp] using hhR) hmark

end Transport

section Plane

variable {Y : Scheme} {n : ℕ} {T : BlowupTower P n Y} {hT : IsClosedPointTower P T}
  {g : Y ⟶ P} {b b' : Basis (Fin 2) ℤ N}
  {hi : IsIntegralLattice i} {J : Y.IdealSheafData}

local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local macro "planeMeasure[" T:term "," hT:term "," g:term "]" : term =>
  `(let : AlgebraicGeometry.IsNoetherian P := isNoetherian_of_finiteType s
    let x := mark[$T,$hT,s,$g]
    planeSarkisovBidegree ((Basis.picardTwistEquiv coords) x.1).toNat (∑ j, (-x.2 j).toNat))

private theorem model_marking_of_plane_decrease
    (R : IsClosedPointTower.PlaneSarkisovDecrease b hi hT g J) :
    let : Y.Over S := ⟨T.toBase ≫ s⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension s
    let : R.top.Over S := over[R.tower]
    let : SmoothOfRelativeDimension 2 (R.top ↘ S) := smooth[R.nodal]
    let E := total[J,R.tower]
    ∀ {C B' : LogarithmicProjection i E},
      C.fan = R.fan → C.hom ≍ R.refinementIso.inv ≫ R.modelIso.hom ≫ R.modelTower.toBase →
      B'.fan = plane[b',hi] → B'.hom ≍ R.tower.toBase ≫ g ≫ (planeIso[b',hi]).inv →
      ∃ next, next < planeMeasure[T,hT,g] ∧ HasPlaneTargetMarking C B' next := by
  intro hY hSmoothY hTop hSmooth E C B' hC hCh hB' hBh
  let := hY
  let := hSmoothY
  let := hTop
  let := hSmooth
  let : R.fan.algebraicRealization.IsProjectiveOver ℂ := R.projective
  let : Nonempty R.fan.cones := R.complete.nonempty_cones
  let f := (R.fan.algebraicRealization ↘ S)
  let : SmoothOfRelativeDimension 2 f :=
    rankTwo ▸ R.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap R.regular
  let e := R.refinementIso.symm ≪≫ R.modelIso
  let g' := R.modelIso.inv ≫ R.refinement ≫ g
  let x := mark[R.modelTower,R.closedPoint,f,g']
  have hcomp : e.hom ≫ g' = R.tower.toBase ≫ g := by
    simp only [e, g', Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
      ← R.refinementIso_comp, Iso.inv_hom_id_assoc]
  rcases C with ⟨Φ, hreg, hc, c, hcOver, hcDom, hcPole⟩
  dsimp only at hC hCh
  subst Φ
  have hC' : c = e.hom ≫ R.modelTower.toBase := by
    simpa only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc] using eq_of_heq hCh
  have hB'' : B'.hom ≍ e.hom ≫ g' ≫ (planeIso[b',hi]).inv := by
    rw [← Category.assoc e.hom, hcomp, Category.assoc]
    exact hBh
  have hm := R.decreases.2
  obtain ⟨_, I, -, -, -, -, -, horders⟩ :=
    R.closedPoint.exists_moving_base_ideal_of_plane_resolution g' R.target_over
  have horder j : -x.2 j = (R.closedPoint.baseMultiplicities I j : ℤ) := horders j
  have hsum : (∑ j, -x.2 j).toNat = ∑ j, (-x.2 j).toNat := by
    simp only [horder, ← Nat.cast_sum, Int.toNat_natCast]
  refine ⟨_, ?_, HasPlaneTargetMarking.hirzebruch (A := ⟨_, hreg, hc, c, hcOver, hcDom, hcPole⟩)
    (B := B') R.basis b' R.index hi R.rays R.rayGenerators hB' R.modelTower R.closedPoint
    e g' hC' hB'' R.target_over R.target_birational⟩
  -- Use the same name for the marking in the sum identity and in the lexicographic comparison.
  change hirzebruchSarkisovBidegree
    ((R.fan.hirzebruchPicardBasis R.basis R.index R.regular R.rays R.rayGenerators).repr
      x.1 1).toNat (∑ j, -x.2 j).toNat < _
  rwa [hsum]

include hT in
/-- A marked plane-to-plane resolution is either terminal or has a decreasing
block for plane-target induction. The block is based on the given resolving
surface, even when the tower presenting its first projection has an isomorphic top. -/
theorem exists_sarkisov_step_of_plane_marking
    (hD : D.IsEffectiveCartier)
    (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S))
    (hA : A.fan = plane[b,hi]) (hB : B.fan = plane[b',hi]) (k : X ≅ Y)
    (hAh : A.hom ≍ k.hom ≫ T.toBase ≫ (planeIso[b,hi]).inv)
    (hBh : B.hom ≍ k.hom ≫ g ≫ (planeIso[b',hi]).inv)
    (hg : g ≫ s = T.toBase ≫ s) (hbir : Scheme.BirationalOver g (𝟙 P)) :
    Nonempty (SarkisovPath A B) ∨
      HasPlaneTargetDecrease A B rankTwo hD hNode planeMeasure[T,hT,g] := by
  let : Y.Over S := ⟨T.toBase ≫ s⟩
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension s
  let : IsIntegral Y := hT.isIntegral s
  let : IsNoetherian Y := T.isNoetherian
  let := Fan.projectivePlaneIso_trans_polynomialProjIso_hom_isOver b hi coords
  have ha : k.hom ≫ T.toBase ≫ s = X ↘ S := by
    rcases A with ⟨Φ, hreg, hc, a, ha, hdom, hpole⟩
    dsimp only at hA hAh
    subst Φ
    obtain rfl : a = k.hom ≫ T.toBase ≫ (planeIso[b,hi]).inv := eq_of_heq hAh
    let := ha
    let : (planeIso[b,hi]).inv.IsOver S := inferInstance
    simpa only [Category.assoc, comp_over (planeIso[b,hi]).inv S] using
      comp_over (k.hom ≫ T.toBase ≫ (planeIso[b,hi]).inv) S
  let : k.hom.IsOver S := ⟨ha⟩
  let : k.inv.IsOver S := inferInstance
  let : k.symm.hom.IsOver S := inferInstanceAs (k.inv.IsOver S)
  let F := precomposeSarkisovOfIso (i := i) rankTwo k.symm (rfl : D.comap k.inv = D.comap k.inv)
  have hh {L : LogarithmicProjection i D} {Φ : Fan i} {p : Y ⟶ Φ.algebraicRealization}
      (hL : L.fan = Φ) (h : L.hom ≍ k.hom ≫ p) : (obj[F,L]).hom ≍ p :=
    precomposeSarkisovOfIso_obj_hom_of_comp rankTwo k.symm rfl L hL h
  have hn : AtWorstNodalOfRelativeDimensionOne ((D.comap k.inv).subschemeι ≫ Y ↘ S) := by
    simpa only [comp_over k.inv S] using hNode.comap_of_etale k.inv
  rcases hT.exists_sarkisov_path_or_decrease_of_logarithmic_plane b b' hi g hg hbir
      (hD.comap k.inv) hn (obj[F,A]) (obj[F,B])
      ((precomposeSarkisovOfIso_obj_fan ..).trans hA)
      ((precomposeSarkisovOfIso_obj_fan ..).trans hB) (hh hA hAh) (hh hB hBh) with
    ⟨p, -⟩ | ⟨R, A', C, B', p, hA', hhA, hC, hhC, hB', hhB, -⟩
  · have hD' : (D.comap k.inv).comap k.hom = D := by simp [← comap_comp]
    let G := precomposeSarkisovOfIso (i := i) rankTwo k hD'
    let : k.symm.symm.hom.IsOver S := inferInstanceAs (k.hom.IsOver S)
    have h (L : LogarithmicProjection i D) : obj[G,obj[F,L]] = L :=
      precomposeSarkisovOfIso_obj_symm rankTwo k.symm rfl hD' L
    exact Or.inl ⟨h A ▸ h B ▸ mapPath[G,p]⟩
  · let : R.top.Over S := over[R.tower]
    let : SmoothOfRelativeDimension 2 (R.top ↘ S) := smooth[R.nodal]
    let : IsIntegral R.top := integral[R.nodal]
    have refineHom {L : LogarithmicProjection i D}
        {L' : LogarithmicProjection i total[D.comap k.inv,R.tower]}
        (hhL : L'.hom ≍ R.tower.toBase ≫ (obj[F,L]).hom) :
        L'.hom ≍ R.tower.toBase ≫ k.inv ≫ L.hom :=
      hhL.trans (heq_comp rfl rfl
        (congrArg Fan.algebraicRealization (precomposeSarkisovOfIso_obj_fan ..))
        HEq.rfl (precomposeSarkisovOfIso_obj_hom rankTwo k.symm rfl L))
    have hB'fan := (hB'.trans (precomposeSarkisovOfIso_obj_fan ..)).trans hB
    have hB'plane := hhB.trans (heq_comp rfl rfl
      (congrArg Fan.algebraicRealization ((precomposeSarkisovOfIso_obj_fan ..).trans hB))
      HEq.rfl (hh hB hBh))
    obtain ⟨next, hlt, hmark⟩ := model_marking_of_plane_decrease R hC hhC hB'fan hB'plane
    exact Or.inr (HasPlaneTargetDecrease.of_iso rankTwo hD hNode k R.nodal hlt p
      (hA'.trans (precomposeSarkisovOfIso_obj_fan ..)) (refineHom hhA)
      (hB'.trans (precomposeSarkisovOfIso_obj_fan ..)) (refineHom hhB) hmark)

end Plane

section Quadric

variable {Y : Scheme} {b b' : Basis (Fin 2) ℤ N} {hi : IsIntegralLattice i}
  (r : Fin 4 ≃ A.fan.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])
  {n : ℕ} {T : BlowupTower A.fan.algebraicRealization n Y}
  (hT : IsClosedPointTower A.fan.algebraicRealization T) (g : Y ⟶ P)

local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "fA" => (A.fan.algebraicRealization ↘ S)
local notation "quadricSmooth" =>
  Eq.mp (congrArg (fun n ↦ SmoothOfRelativeDimension n fA) rankTwo)
    (A.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap A.isRegular)

omit [IsIntegral X] [AlgebraicGeometry.IsNoetherian X] in
private theorem exists_path_with_smaller_marking_of_quadric
    (hg : g ≫ s = T.toBase ≫ fA) (hbir : Scheme.BirationalOver g (𝟙 P)) (J : Y.IdealSheafData) :
    let : SmoothOfRelativeDimension 2 fA := quadricSmooth
    let : Y.Over S := ⟨T.toBase ≫ fA⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension fA
    let : IsIntegral Y := hT.isIntegral fA
    let x := mark[T,hT,fA,g]
    let β := (A.fan.hirzebruchPicardBasis b 0 A.isRegular r hr).repr x.1 1
    let d := hirzebruchSarkisovBidegree β.toNat (∑ j, -x.2 j).toNat
    ∀ (L R : LogarithmicProjection i J),
      L.fan = A.fan → L.hom ≍ T.toBase →
      R.fan = plane[b',hi] → R.hom ≍ g ≫ (planeIso[b',hi]).inv →
      ∃ next, next < d ∧
        ∃ C : LogarithmicProjection i J, Nonempty (SarkisovPath L C) ∧
          HasPlaneTargetMarking C R next := by
  intro hSmoothA hY hSmooth hInt x β d L R hL hhL hR hhR
  let := hSmoothA
  let := hY
  let := hSmooth
  let := hInt
  have hpole : (A.fan.boundaryIdeal A.isComplete.nonempty_cones).comap T.toBase =
      J * hT.ramificationIdealSheafToBase ℂ := by
    rcases L with ⟨Φ, hreg, hc, l, hl, hdom, hpole⟩
    dsimp only at hL hhL
    subst Φ
    obtain rfl : l = T.toBase := eq_of_heq hhL
    let : T.toBase.IsOver S := ⟨rfl⟩
    rw [IsClosedPointTower.ramificationIdealSheafToBase_def]
    exact hpole
  obtain ⟨L', C, p, hL', hhL', hresult⟩ := hT.exists_sarkisov_path_decrease_of_quadric
    b A.isRegular A.isComplete r hr g hg hbir (D := J) hpole
  have hStart : L' = L := LogarithmicProjection.ext (hL'.trans hL.symm) (hhL'.trans hhL.symm)
  have targetHom {Z : Scheme} (e : Y ≅ Z) :
      R.hom ≍ e.hom ≫ (e.inv ≫ g) ≫ (planeIso[b',hi]).inv := by
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hhR
  rcases hresult with ⟨c, Z, m, U, hU, e, hC, hhC, hgo, hgb, -, -, hlt⟩ |
    ⟨a, c, t, ht, Z, m, U, hU, e, hhC, -, hgo, hgb, -, -, hlt⟩
  · let : IsNoetherian P := isNoetherian_of_finiteType s
    let y := mark[U,hU,s,e.inv ≫ g]
    obtain ⟨_, I, -, -, -, -, -, hx⟩ :=
      hU.exists_moving_base_ideal_of_plane_resolution (e.inv ≫ g) hgo
    have horder j : -y.2 j = (hU.baseMultiplicities I j : ℤ) := hx j
    have hsum : (∑ j, (-y.2 j).toNat) = (∑ j, -y.2 j).toNat := by
      simp only [horder, ← Nat.cast_sum, Int.toNat_natCast]
    refine ⟨_, ?_, C, ⟨hStart ▸ p⟩, .plane c b' hi hC hR U hU e (e.inv ≫ g)
      hhC (targetHom e) hgo hgb⟩
    -- The two bidegree formulas agree because the exceptional orders are nonnegative.
    change planeSarkisovBidegree ((Basis.picardTwistEquiv coords) y.1).toNat
      (∑ j, (-y.2 j).toNat) < d
    rwa [hsum]
  · exact ⟨_, hlt, C, ⟨hStart ▸ p⟩,
      .hirzebruch c b' a hi t ht hR U hU e (e.inv ≫ g) hhC (targetHom e) hgo hgb⟩

/-- A marked quadric-to-plane resolution gives a strictly decreasing block
in plane-target induction, with the original resolving surface and target. -/
theorem exists_sarkisov_step_of_quadric_marking
    (hD : D.IsEffectiveCartier)
    (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S))
    (hB : B.fan = plane[b',hi]) (k : X ≅ Y)
    (hAh : A.hom = k.hom ≫ T.toBase) (hBh : B.hom ≍ k.hom ≫ g ≫ (planeIso[b',hi]).inv)
    (hg : g ≫ s = T.toBase ≫ fA) (hbir : Scheme.BirationalOver g (𝟙 P)) :
    let : SmoothOfRelativeDimension 2 fA := quadricSmooth
    let x := mark[T,hT,fA,g]
    let β := (A.fan.hirzebruchPicardBasis b 0 A.isRegular r hr).repr x.1 1
    HasPlaneTargetDecrease A B rankTwo hD hNode
      (hirzebruchSarkisovBidegree β.toNat (∑ j, -x.2 j).toNat) := by
  intro hSmoothA x β
  let := hSmoothA
  let : Y.Over S := ⟨T.toBase ≫ fA⟩
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension fA
  let : IsIntegral Y := hT.isIntegral fA
  let : IsNoetherian Y := T.isNoetherian
  let : k.hom.IsOver S := ⟨(Category.assoc k.hom T.toBase fA).symm.trans
    (hAh ▸ comp_over A.hom S)⟩
  let : k.inv.IsOver S := inferInstance
  let : k.symm.hom.IsOver S := inferInstanceAs (k.inv.IsOver S)
  let F := precomposeSarkisovOfIso (i := i) rankTwo k.symm (rfl : D.comap k.inv = D.comap k.inv)
  have hL : (obj[F,A]).hom ≍ T.toBase :=
    precomposeSarkisovOfIso_obj_hom_of_comp rankTwo k.symm rfl A rfl (heq_of_eq hAh)
  have hR : (obj[F,B]).hom ≍ g ≫ (planeIso[b',hi]).inv :=
    precomposeSarkisovOfIso_obj_hom_of_comp rankTwo k.symm rfl B hB hBh
  have hn : AtWorstNodalOfRelativeDimensionOne ((D.comap k.inv).subschemeι ≫ Y ↘ S) := by
    simpa only [comp_over k.inv S] using hNode.comap_of_etale k.inv
  obtain ⟨next, hlt, C, ⟨p⟩, hm⟩ :=
    exists_path_with_smaller_marking_of_quadric r hr hT g hg hbir (D.comap k.inv)
      (obj[F,A]) (obj[F,B]) (precomposeSarkisovOfIso_obj_fan ..) hL
      ((precomposeSarkisovOfIso_obj_fan ..).trans hB) hR
  exact HasPlaneTargetDecrease.of_path_on_iso rankTwo hD hNode k hn hlt p
    (precomposeSarkisovOfIso_obj_fan ..) (precomposeSarkisovOfIso_obj_hom ..)
    (precomposeSarkisovOfIso_obj_fan ..) (precomposeSarkisovOfIso_obj_hom ..) hm

end Quadric

section NegativeSection

variable [A.fan.algebraicRealization.IsProjectiveOver ℂ]
  {Y : Scheme} {b b' : Basis (Fin 2) ℤ N} {hi : IsIntegralLattice i}
  {a : ℕ} (r : Fin 4 ≃ A.fan.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (a : ℤ) • b 0 - b 1])
  {n : ℕ} {T : BlowupTower A.fan.algebraicRealization n Y}
  (hT : IsClosedPointTower A.fan.algebraicRealization T) (g : Y ⟶ P)

local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "fA" => (A.fan.algebraicRealization ↘ S)
local notation "sourceSmooth" =>
  Eq.mp (congrArg (fun n ↦ SmoothOfRelativeDimension n fA) rankTwo)
    (A.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap A.isRegular)

/-- A marked positive-index Hirzebruch-to-plane resolution with all orders at most
half the ruling degree gives a strictly decreasing plane-target induction step.
The negative-section contraction keeps the original resolving surface and target. -/
theorem exists_sarkisov_step_of_hirzebruch_marking_of_no_high_order
    (ha : 0 < a) (hD : D.IsEffectiveCartier)
    (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S))
    (hB : B.fan = plane[b',hi]) (k : X ≅ Y)
    (hAh : A.hom = k.hom ≫ T.toBase) (hBh : B.hom ≍ k.hom ≫ g ≫ (planeIso[b',hi]).inv)
    (hg : g ≫ s = T.toBase ≫ fA) (hbir : Scheme.BirationalOver g (𝟙 P)) :
    let : SmoothOfRelativeDimension 2 fA := sourceSmooth
    let x := mark[T,hT,fA,g]
    let β := (A.fan.hirzebruchPicardBasis b a A.isRegular r hr).repr x.1 1
    (∀ j, 2 * (-x.2 j) ≤ β) →
      HasPlaneTargetDecrease A B rankTwo hD hNode
        (hirzebruchSarkisovBidegree β.toNat (∑ j, -x.2 j).toNat) := by
  intro hSmoothA x β hlow
  let := hSmoothA
  let : Smooth fA := hSmoothA.smooth
  let : IsNoetherian A.fan.algebraicRealization := isNoetherian_of_finiteType fA
  let : Y.Over S := ⟨T.toBase ≫ fA⟩
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension fA
  let : IsIntegral Y := hT.isIntegral fA
  let : IsNoetherian Y := T.isNoetherian
  let : k.hom.IsOver S := ⟨(Category.assoc k.hom T.toBase fA).symm.trans
    (hAh ▸ comp_over A.hom S)⟩
  let : k.inv.IsOver S := inferInstance
  let : k.symm.hom.IsOver S := inferInstanceAs (k.inv.IsOver S)
  let F := precomposeSarkisovOfIso (i := i) rankTwo k.symm (rfl : D.comap k.inv = D.comap k.inv)
  have hL := precomposeSarkisovOfIso_obj_fan rankTwo k.symm rfl A
  have hhL := precomposeSarkisovOfIso_obj_hom_of_comp rankTwo k.symm rfl A rfl (heq_of_eq hAh)
  have hR := (precomposeSarkisovOfIso_obj_fan rankTwo k.symm rfl B).trans hB
  have hhR := precomposeSarkisovOfIso_obj_hom_of_comp rankTwo k.symm rfl B hB hBh
  obtain ⟨next, hlt, C, _, _, ⟨p⟩, hm⟩ :=
    exists_sarkisov_path_with_smaller_plane_marking_of_no_high_order a A.isRegular A.isComplete
      r hr hT g ha hg hbir hlow hL hhL hR hhR
  have hn : AtWorstNodalOfRelativeDimensionOne ((D.comap k.inv).subschemeι ≫ Y ↘ S) := by
    simpa only [comp_over k.inv S] using hNode.comap_of_etale k.inv
  exact HasPlaneTargetDecrease.of_path_on_iso rankTwo hD hNode k hn hlt p hL
    (precomposeSarkisovOfIso_obj_hom ..) (precomposeSarkisovOfIso_obj_fan ..)
    (precomposeSarkisovOfIso_obj_hom ..) hm

end NegativeSection

end TauCeti.Toric.Fan.LogarithmicProjection
