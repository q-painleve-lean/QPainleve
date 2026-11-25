/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Induction.Step

import QPainleve.Geometry.Toric.Fan.Logarithmic.SarkisovReduction
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective
import QPainleve.SignedClusterModularGroup.SarkisovDegree.Induction.Hirzebruch
import QPainleve.SignedClusterModularGroup.SarkisovDegree.Pivots

/-!
# Marked factorization with a plane target

A marked plane-target resolution has a terminal path, admits a decreasing
block, or has all its high base orders over open orbits of invariant fibers on
a positive-index Hirzebruch surface. Providing a decrease for that last case
gives a single resolved path for any two specified toric projections.

The marked case distinction uses `hirzebruch_high_baseCenter_cases`. The
induction on bidegree uses `exists_sarkisov_path_of_bidegree_decrease` and follows
[Lutz, Theorem 8.4](https://arxiv.org/pdf/2005.05010v3#page=73).
-/

public section

open AlgebraicGeometry CategoryTheory Module QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra Scheme.IdealSheafData

namespace TauCeti.Toric.Fan.LogarithmicProjection

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "s" => (P ↘ S)
local notation "H" => LineBundleClass.mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "plane[" b "," hi "]" => Fan.projectiveSpace b hi
local notation "planeIso[" b "," hi "]" =>
  (Fan.projectivePlaneIso b hi ≪≫ Basis.polynomialProjIso (Pi.basisFun ℂ (Fin 3)))
local notation "rank[" b "]" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "mark[" T "," hT "," f "," g "]" =>
  LinearEquiv.symm (BlowupTower.picardMarking T hT f) (Additive.ofMul (pullback g H))
local notation "obj[" F "," A "]" => @Prefunctor.obj _ sarkisovQuiver _ sarkisovQuiver F A

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {X : Scheme} [X.Over S] [SmoothOfRelativeDimension 2 (X ↘ S)]
  {D : X.IdealSheafData} {A B : LogarithmicProjection i D}

local notation "sourceMap[" A "]" => Fan.algebraicRealization (LogarithmicProjection.fan A) ↘ S
local notation "sourceSmooth[" A "," b "]" =>
  Eq.mp (congrArg (fun d ↦ SmoothOfRelativeDimension d sourceMap[A]) rank[b])
    (Fan.smoothOfRelativeDimension_algebraicRealizationStructureMap
      (LogarithmicProjection.fan A) (LogarithmicProjection.isRegular A))
local notation "center[" b "," ρ "," c "]" => Fan.Ray.binomialCenter ρ rank[b]
  (Basis.detDualEquiv_self b (Fan.Ray.primitiveGenerator ρ))
  (Fan.Ray.surjective_detCharacter ρ b) c (IsLocalRing.closedPoint ℂ)
local notation "fiberRay[" r "," t "]" => r ((![1, 3] : Fin 2 → Fin 4) t)
local notation "degree[" β "," x "]" =>
  hirzebruchSarkisovBidegree (Int.toNat β)
    (Int.toNat (sarkisovSecondaryDegree ℂ (Additive.toMul (Prod.fst x))))

/-- A marked positive-index Hirzebruch-to-plane resolution with high base orders
over the open orbits of invariant fibers. The high orders are exactly the indices
in the displayed filter. There are one or two of them, each is the first above
its image on the Hirzebruch surface, and their fibers are distinct. -/
inductive HasHighFiberPlaneTargetMarking (A B : LogarithmicProjection i D) : ℕ ×ₗ ℕ → Prop
  /-- The marked source tower and the specified target morphism in its coordinates. -/
  | hirzebruch (b b' : Basis (Fin 2) ℤ N) (e : ℕ) (he : 0 < e) (hi : IsIntegralLattice i)
      (r : Fin 4 ≃ A.fan.Ray)
      (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (e : ℤ) • b 0 - b 1])
      (hB : B.fan = plane[b',hi])
      {Y : Scheme} {n : ℕ} (T : BlowupTower A.fan.algebraicRealization n Y)
      (hT : IsClosedPointTower A.fan.algebraicRealization T)
      (k : X ≅ Y) (g : Y ⟶ P)
      (hAh : A.hom = k.hom ≫ T.toBase)
      (hBh : B.hom ≍ k.hom ≫ g ≫ (planeIso[b',hi]).inv)
      (hg : g ≫ s = T.toBase ≫ sourceMap[A]) (hbir : Scheme.BirationalOver g (𝟙 P))
      (highFibers : let : SmoothOfRelativeDimension 2 sourceMap[A] := sourceSmooth[A,b]
        let x := mark[T,hT,sourceMap[A],g]
        let β := (A.fan.hirzebruchPicardBasis b e A.isRegular r hr).repr x.1 1
        let high := Finset.univ.filter (fun j ↦ β < 2 * (-x.2 j))
        (high.card = 1 ∨ high.card = 2) ∧
          ∃ fiber : (↑high : Type) ↪ Fin 2, ∀ j : high,
            -x.2 j ≤ β ∧ (∀ l < (j : Fin n), hT.baseCenter l ≠ hT.baseCenter j) ∧
            ∃ c : ℂˣ, hT.baseCenter j = center[b,fiberRay[r,fiber j],c]) :
      HasHighFiberPlaneTargetMarking A B (
        let : SmoothOfRelativeDimension 2 sourceMap[A] := sourceSmooth[A,b]
        let x := mark[T,hT,sourceMap[A],g]
        let β := (A.fan.hirzebruchPicardBasis b e A.isRegular r hr).repr x.1 1
        degree[β,x])

private theorem hirzebruch_marking_boundary_le_ramification [IsIntegral X]
    (b : Basis (Fin 2) ℤ N) {Y : Scheme} {n : ℕ}
    {T : BlowupTower A.fan.algebraicRealization n Y}
    (hT : IsClosedPointTower A.fan.algebraicRealization T)
    (k : X ≅ Y) (hAh : A.hom = k.hom ≫ T.toBase) :
    let : SmoothOfRelativeDimension 2 sourceMap[A] := sourceSmooth[A,b]
    (A.fan.boundaryIdeal A.isComplete.nonempty_cones).comap T.toBase ≤
      hT.ramificationIdealSheafToBase ℂ := by
  intro hSmoothA
  let := hSmoothA
  let : Y.Over S := ⟨T.toBase ≫ sourceMap[A]⟩
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension sourceMap[A]
  let : IsIntegral Y := hT.isIntegral sourceMap[A]
  let : k.hom.IsOver S := ⟨(Category.assoc k.hom T.toBase sourceMap[A]).symm.trans
    (hAh ▸ comp_over A.hom S)⟩
  let : k.symm.hom.IsOver S := inferInstanceAs (k.inv.IsOver S)
  let F := precomposeSarkisovOfIso (i := i) rank[b] k.symm (rfl : D.comap k.inv = D.comap k.inv)
  have hL := precomposeSarkisovOfIso_obj_fan rank[b] k.symm rfl A
  have hhL := precomposeSarkisovOfIso_obj_hom_of_comp rank[b] k.symm rfl A rfl (heq_of_eq hAh)
  let : T.toBase.IsOver S := ⟨rfl⟩
  -- Destructure the transported projection to align its fan and the target of its morphism.
  generalize obj[F,A] = L at hL hhL
  rcases L with ⟨Φ, hreg, hc, l, hl, hdom, hpole⟩
  dsimp only at hL hhL
  subst Φ
  obtain rfl : l = T.toBase := eq_of_heq hhL
  rw [hT.ramificationIdealSheafToBase_def ℂ, hpole]
  exact mul_le_of_le_one_left' le_top

section Steps

variable [IsIntegral X] [IsNoetherian X]

private theorem sarkisov_step_or_high_fibers_of_positive_index
    {Y : Scheme} {b b' : Basis (Fin 2) ℤ N} {hi : IsIntegralLattice i} {e n : ℕ}
    (he : 0 < e) (r : Fin 4 ≃ A.fan.Ray)
    (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (e : ℤ) • b 0 - b 1])
    {T : BlowupTower A.fan.algebraicRealization n Y}
    (hT : IsClosedPointTower A.fan.algebraicRealization T) (g : Y ⟶ P)
    (hD : D.IsEffectiveCartier)
    (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S))
    (hB : B.fan = plane[b',hi]) (k : X ≅ Y) (hAh : A.hom = k.hom ≫ T.toBase)
    (hBh : B.hom ≍ k.hom ≫ g ≫ (planeIso[b',hi]).inv)
    (hg : g ≫ s = T.toBase ≫ sourceMap[A]) (hbir : Scheme.BirationalOver g (𝟙 P)) :
    let : SmoothOfRelativeDimension 2 sourceMap[A] := sourceSmooth[A,b]
    let x := mark[T,hT,sourceMap[A],g]
    let β := (A.fan.hirzebruchPicardBasis b e A.isRegular r hr).repr x.1 1
    HasPlaneTargetDecrease A B rank[b] hD hNode degree[β,x] ∨
      HasHighFiberPlaneTargetMarking A B degree[β,x] := by
  intro hSmoothA x β
  let := hSmoothA
  let : A.fan.algebraicRealization.IsProjectiveOver ℂ :=
    A.fan.isProjectiveOver_algebraicRealization_of_isComplete A.isRegular A.isComplete b
  let high := Finset.univ.filter (fun j ↦ β < 2 * (-x.2 j))
  by_cases hhigh : high.Nonempty
  · have hlog := hirzebruch_marking_boundary_le_ramification b hT k hAh
    rcases hT.hirzebruch_high_baseCenter_cases b e A.isRegular A.isComplete r hr g hg hlog hhigh
      with ⟨j, hj, -, hp⟩ | ⟨hcard, fiber, hfiber⟩
    · have hpivot : (∃ σ : A.fan.cones, Nat.card (ToricRay σ.val) = 2 ∧
          hT.baseCenter j = A.fan.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ)) ∨
          ∃ t : Fin 2, ∃ c : ℂˣ, hT.baseCenter j = center[b,r ((![0, 2] : Fin 2 → Fin 4) t),c] := by
        rcases hp with ⟨σ, ⟨hσ, hpoint, -⟩, -⟩ | hsection
        · exact Or.inl ⟨σ, hσ, hpoint.symm⟩
        · exact Or.inr hsection
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt (Fin.pos_iff_nonempty.mpr ⟨j⟩))
      exact Or.inl (exists_sarkisov_step_of_hirzebruch_corner_or_section_marking r hr hT g hD hNode
        hB k hAh hBh hg hbir j hpivot (Finset.mem_filter.mp hj).2)
    · exact Or.inr (.hirzebruch b b' e he hi r hr hB T hT k g hAh hBh hg hbir
        ⟨hcard, fiber, fun j ↦ ⟨(hfiber j).1, (hfiber j).2.1, (hfiber j).2.2.1⟩⟩)
  · refine Or.inl (exists_sarkisov_step_of_hirzebruch_marking_of_no_high_order r hr hT g
      he hD hNode hB k hAh hBh hg hbir fun j ↦ le_of_not_gt ?_)
    exact fun hj ↦ hhigh ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩

/-- A marked plane-target resolution gives a terminal path, a decreasing block,
or a positive-index Hirzebruch marking with all high centers on open fiber
orbits. All three alternatives refer to the specified target projection. -/
theorem HasPlaneTargetMarking.sarkisov_step_or_high_fibers {d : ℕ ×ₗ ℕ}
    (h : HasPlaneTargetMarking A B d) (hRank : finrank ℤ N = 2)
    (hD : D.IsEffectiveCartier)
    (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S)) :
    Nonempty (SarkisovPath A B) ∨ HasPlaneTargetDecrease A B hRank hD hNode d ∨
      HasHighFiberPlaneTargetMarking A B d := by
  cases h with
  | plane b b' hi hA hB T hT k g hAh hBh hg hbir =>
    exact Or.imp_right Or.inl
      (exists_sarkisov_step_of_plane_marking (hT := hT) hD hNode hA hB k hAh hBh hg hbir)
  | hirzebruch b b' e hi r hr hB T hT k g hAh hBh hg hbir =>
    by_cases he : e = 0
    · subst e
      exact Or.inr (Or.inl (exists_sarkisov_step_of_quadric_marking r hr hT g hD hNode hB
        k hAh hBh hg hbir))
    · exact Or.inr (sarkisov_step_or_high_fibers_of_positive_index (Nat.pos_of_ne_zero he)
        r hr hT g hD hNode hB k hAh hBh hg hbir)

end Steps

/-- A decreasing block in the positive-index high-fiber case suffices to factor
the change between any two specified logarithmic projections onto complete
regular toric surfaces. The resulting path lives on one nodal tower and ends
at the pullback of the original target projection. -/
theorem sarkisov_factorization_of_high_fiber_steps
    (b : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)
    (highFiberStep : ∀ {Y : Scheme} [Y.Over S] [SmoothOfRelativeDimension 2 (Y ↘ S)]
      [IsIntegral Y] [IsNoetherian Y] {E : Y.IdealSheafData}
      {L R : LogarithmicProjection i E} {d : ℕ ×ₗ ℕ}
      (hE : E.IsEffectiveCartier)
      (hNodeE : AtWorstNodalOfRelativeDimensionOne (E.subschemeι ≫ Y ↘ S)),
      HasHighFiberPlaneTargetMarking L R d → HasPlaneTargetDecrease L R rank[b] hE hNodeE d)
    [IsIntegral X] [X.IsProjectiveOver ℂ]
    (A B : LogarithmicProjection i D) [IsModification A.hom] [IsModification B.hom]
    (hD : D.IsEffectiveCartier)
    (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S)) :
    letI : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
    HasResolvedSarkisovFactorization A B := by
  refine exists_resolved_sarkisov_factorization_of_plane b hi ?_ A B hD hNode
  intro Y hOver hInt hProj hSmooth E hE hNE L R hLmod hRmod hL hR
  let : IsNoetherian Y := isNoetherian_of_finiteType (Y ↘ S)
  obtain ⟨d, hd⟩ := exists_hasPlaneTargetMarking_of_plane L R b b hi hL hR
  refine hasResolvedSarkisovFactorization_iff.mpr
    (exists_sarkisov_path_of_bidegree_decrease rank[b] hE hNE
      (fun L R d ↦ HasPlaneTargetMarking L R d) ?_ d hd)
  intro Z hOverZ hSmoothZ hIntegralZ hNoetherianZ J L' R' d' hJ hNJ hd'
  rcases hd'.sarkisov_step_or_high_fibers rank[b] hJ hNJ with hp | hs | hf
  · exact Or.inl hp
  · exact Or.inr hs
  · exact Or.inr (highFiberStep hJ hNJ hf)

end TauCeti.Toric.Fan.LogarithmicProjection
