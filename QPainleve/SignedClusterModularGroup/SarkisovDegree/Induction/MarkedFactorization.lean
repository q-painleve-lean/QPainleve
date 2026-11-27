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
import QPainleve.SignedClusterModularGroup.SarkisovDegree.PositiveSection.Descent

/-!
# Marked factorization with a plane target

A marked plane-target resolution has a terminal path or admits a decreasing
block. When the high base orders occur over open orbits of invariant fibers on
a positive-index Hirzebruch surface, the positive-section preparation and quadric
exit give the decreasing block. Induction yields one resolved path between the
two specified toric projections.

The marked case distinction uses `hirzebruch_high_baseCenter_cases`. The
induction on bidegree uses `exists_sarkisov_path_of_bidegree_decrease` and follows
[Lutz, Theorem 8.4](https://arxiv.org/pdf/2005.05010v3#page=73).
-/

public section

open AlgebraicGeometry CategoryTheory Module QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra Scheme.IdealSheafData

namespace TauCeti.Toric.Fan.LogarithmicProjection

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "S" => Spec (CommRingCat.of k₀)
local notation "P" => Proj (homogeneousSubmodule k₀ (Fin 3 → k₀))
local notation "s" => (P ↘ S)
local notation "H" => LineBundleClass.mk (Proj.symmetricAlgebraTwistingBundle k₀ (Fin 3 → k₀) 1)
local notation "plane[" b "," hi "]" => Fan.projectiveSpace b hi
local notation "planeIso[" b "," hi "]" =>
  (Fan.projectivePlaneIso k₀ b hi ≪≫ Basis.polynomialProjIso (Pi.basisFun k₀ (Fin 3)))
local notation "rank[" b "]" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "mark[" T "," hT "," f "," g "]" =>
  LinearEquiv.symm (BlowupTower.picardMarking T hT f) (Additive.ofMul (pullback g H))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {X : Scheme} [X.Over (Spec (.of k₀))] [SmoothOfRelativeDimension 2 (X ↘ Spec
    (.of k₀))]
  {D : X.IdealSheafData} {A B : LogarithmicProjection k₀ i D}

local notation "sourceMap[" A "]" => Fan.finiteFanScheme k₀ (LogarithmicProjection.fan A) ↘ S
local notation "sourceSmooth[" A "," b "]" =>
  Eq.mp (congrArg (fun d ↦ SmoothOfRelativeDimension d sourceMap[A]) rank[b])
    (Fan.smoothOfRelativeDimension_finiteFanSchemeToSpec
      (LogarithmicProjection.fan A) k₀ (LogarithmicProjection.isRegular A))
local notation "center[" b "," ρ "," c "]" => Fan.Ray.binomialCenter ρ k₀ rank[b]
  (Basis.detDualEquiv_self b (Fan.Ray.primitiveGenerator ρ))
  (Fan.Ray.surjective_detCharacter ρ b) c (IsLocalRing.closedPoint k₀)
local notation "degree[" β "," x "]" =>
  hirzebruchSarkisovBidegree (Int.toNat β)
    (Int.toNat (sarkisovSecondaryDegree k₀ (Additive.toMul (Prod.fst x))))

private theorem hirzebruch_marking_boundary_le_ramification
    (b : Basis (Fin 2) ℤ N) {Y : Scheme} {n : ℕ}
    {T : BlowupTower (A.fan.finiteFanScheme k₀) n Y}
    (hT : IsClosedPointTower (A.fan.finiteFanScheme k₀) T)
    (k : X ≅ Y) (hAh : A.hom = k.hom ≫ T.toBase) :
    let : SmoothOfRelativeDimension 2 sourceMap[A] := sourceSmooth[A,b]
    (A.fan.toricBoundaryIdeal k₀ A.isComplete.nonempty_cones).comap T.toBase ≤
      hT.ramificationIdealSheafToBase k₀ := by
  intro hSmoothA
  let := hSmoothA
  let : Y.Over S := ⟨T.toBase ≫ sourceMap[A]⟩
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension sourceMap[A]
  let : k.hom.IsOver S := ⟨(Category.assoc k.hom T.toBase sourceMap[A]).symm.trans
    (hAh ▸ comp_over A.hom S)⟩
  let : T.toBase.IsOver S := ⟨rfl⟩
  let : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  rw [A.comap_boundaryIdeal_of_eq_iso_comp rank[b] k A.isComplete T.toBase rfl (heq_of_eq hAh),
    hT.ramificationIdealSheafToBase_def k₀]
  exact mul_le_of_le_one_left' le_top

section Steps

variable [IsIntegral X] [IsNoetherian X]

private theorem sarkisov_step_of_positive_index
    {Y : Scheme} {b b' : Basis (Fin 2) ℤ N} {hi : IsIntegralLattice i} {e n : ℕ}
    (he : 0 < e) (r : Fin 4 ≃ A.fan.Ray)
    (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (e : ℤ) • b 0 - b 1])
    {T : BlowupTower (A.fan.finiteFanScheme k₀) n Y}
    (hT : IsClosedPointTower (A.fan.finiteFanScheme k₀) T) (g : Y ⟶ P)
    (hD : D.IsEffectiveCartier)
    (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S))
    (hB : B.fan = plane[b',hi]) (k : X ≅ Y) (hAh : A.hom = k.hom ≫ T.toBase)
    (hBh : B.hom ≍ k.hom ≫ g ≫ (planeIso[b',hi]).inv)
    (hg : g ≫ s = T.toBase ≫ sourceMap[A]) (hbir : Scheme.BirationalOver g (𝟙 P)) :
    let : SmoothOfRelativeDimension 2 sourceMap[A] := sourceSmooth[A,b]
    let x := mark[T,hT,sourceMap[A],g]
    let β := (A.fan.hirzebruchPicardBasis k₀ b e A.isRegular r hr).repr x.1 1
    HasPlaneTargetDecrease A B rank[b] hD hNode degree[β,x] := by
  intro hSmoothA x β
  let := hSmoothA
  let : (A.fan.finiteFanScheme k₀).IsProjectiveOver k₀ :=
    A.fan.isProjectiveOver_finiteFanScheme_of_isComplete k₀ A.isRegular A.isComplete b
  let high := Finset.univ.filter (fun j ↦ β < 2 * (-x.2 j))
  by_cases hhigh : high.Nonempty
  · have hlog := hirzebruch_marking_boundary_le_ramification b hT k hAh
    rcases hT.hirzebruch_high_baseCenter_cases k₀ b e A.isRegular A.isComplete r hr g hg hlog hhigh
      with ⟨j, hj, -, hp⟩ | ⟨-, fiber, hfiber⟩
    · have hpivot : (∃ σ : A.fan.cones, Nat.card (ToricRay σ.val) = 2 ∧
          hT.baseCenter j = (A.fan.distinguishedSection (R := k₀) σ) (IsLocalRing.closedPoint k₀)) ∨
          ∃ t : Fin 2, ∃ c : k₀ˣ, hT.baseCenter j = center[b,r ((![0, 2] : Fin 2 →
            Fin 4) t),c] := by
        rcases hp with ⟨σ, ⟨hσ, hpoint, -⟩, -⟩ | hsection
        · exact Or.inl ⟨σ, hσ, hpoint.symm⟩
        · exact Or.inr hsection
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt (Fin.pos_iff_nonempty.mpr ⟨j⟩))
      exact exists_sarkisov_step_of_hirzebruch_corner_or_section_marking r hr hT g hD hNode
        hB k hAh hBh hg hbir j hpivot (Finset.mem_filter.mp hj).2
    · let M : HirzebruchPlaneResolution A B b' hi e n := {
        basis := b
        rays := r
        rays_eq := hr
        target_fan := hB
        top := Y
        tower := T
        closed := hT
        iso := k
        planeMap := g
        source_hom := hAh
        target_hom := hBh
        planeMap_over := hg
        planeMap_birational := hbir }
      have hstep := M.exists_sarkisov_step_of_high_fibers hD hNode
      simp only [M.fiberDegree_def, M.order_def, M.lineClass_def] at hstep
      obtain ⟨next, hlt, hpath⟩ := hstep hhigh fun j hj ↦
        ⟨fiber ⟨j, hj⟩, (hfiber ⟨j, hj⟩).2.2.1⟩
      have hle : hirzebruchSarkisovBidegree β.toNat 0 ≤ degree[β,x] := by
        rw [Prod.Lex.le_iff, ofLex_hirzebruchSarkisovBidegree, ofLex_hirzebruchSarkisovBidegree]
        exact Or.inr ⟨rfl, Nat.zero_le _⟩
      exact ⟨next, hlt.trans_le hle, hpath⟩
  · refine exists_sarkisov_step_of_hirzebruch_marking_of_no_high_order r hr hT g
      he hD hNode hB k hAh hBh hg hbir fun j ↦ le_of_not_gt ?_
    exact fun hj ↦ hhigh ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩

/-- A marked plane-target resolution gives a terminal path or a strictly decreasing
block. Both alternatives keep the specified target projection. -/
theorem HasPlaneTargetMarking.sarkisov_step {d : ℕ ×ₗ ℕ}
    (h : HasPlaneTargetMarking A B d) (hRank : finrank ℤ N = 2)
    (hD : D.IsEffectiveCartier)
    (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S)) :
    Nonempty (SarkisovPath A B) ∨ HasPlaneTargetDecrease A B hRank hD hNode d := by
  cases h with
  | plane b b' hi hA hB T hT k g hAh hBh hg hbir =>
    exact exists_sarkisov_step_of_plane_marking (hT := hT) hD hNode hA hB k hAh hBh hg hbir
  | hirzebruch b b' e hi r hr hB T hT k g hAh hBh hg hbir =>
    by_cases he : e = 0
    · subst e
      exact Or.inr (exists_sarkisov_step_of_quadric_marking r hr hT g hD hNode hB
        k hAh hBh hg hbir)
    · exact Or.inr (sarkisov_step_of_positive_index (Nat.pos_of_ne_zero he)
        r hr hT g hD hNode hB k hAh hBh hg hbir)

end Steps

/-- The birational change between two specified logarithmic projections onto complete
regular rank-two toric surfaces factors into Sarkisov links. A single nodal tower
resolves every vertex and the path ends at the pullback of the specified target. -/
theorem exists_resolved_sarkisov_factorization
    (b : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)
    [IsIntegral X] [X.IsProjectiveOver k₀]
    (A B : LogarithmicProjection k₀ i D) [IsModification A.hom] [IsModification B.hom]
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
  exact hd'.sarkisov_step rank[b] hJ hNJ

end TauCeti.Toric.Fan.LogarithmicProjection
