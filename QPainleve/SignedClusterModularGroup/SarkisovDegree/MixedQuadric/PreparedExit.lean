/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Induction.Step

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.Blowup.Tower.Nef
import QPainleve.AlgebraicGeometry.Curves.Degree.Ample
import QPainleve.AlgebraicGeometry.IntersectionNumber.Nef.Pullback
import QPainleve.Geometry.Toric.Fan.Picard.CurveIntersection
import QPainleve.SignedClusterModularGroup.SarkisovDegree.MixedQuadric.Marking

/-!
# The mixed exit after positive-section preparation

On the prepared quadric the two retained centers lie on opposite invariant fibers.
A retained center at a corner lies on the section opposite the one used for
preparation. If both centers were corners on that section, nefness would bound
the sum of their first orders by the transverse degree. When the sum exceeds
this degree, a corner therefore gives the mixed two-center link, with the
original marked plane target. The argument uses only the two retained orders.
The link uses the two-center construction in [Lutz, Proposition 8.11][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=72
-/

public section

open AlgebraicGeometry CategoryTheory Module QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra Chow

namespace TauCeti.Toric.Fan.LogarithmicProjection

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "H" => LineBundleClass.mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "plane[" b "," hi "]" => Fan.projectiveSpace b hi
local notation "planeIso[" b "," hi "]" =>
  (Fan.projectivePlaneIso b hi ≪≫ Basis.polynomialProjIso (Pi.basisFun ℂ (Fin 3)))
local notation "mark[" U "," hU "," f "," g "]" =>
  LinearEquiv.symm (BlowupTower.picardMarking U hU f) (Additive.ofMul (pullback g H))
local notation "fiber[" r "," t "]" => r ((![1, 3] : Fin 2 → Fin 4) t)
local notation "rankTwo[" b "]" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "pt" => IsLocalRing.closedPoint ℂ
local notation "center[" b "," ρ "," c "]" =>
  Fan.Ray.binomialCenter ρ rankTwo[b] (Basis.detDualEquiv_self b (Fan.Ray.primitiveGenerator ρ))
    (Fan.Ray.surjective_detCharacter ρ b) c pt

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {X : Scheme} [X.Over S] [SmoothOfRelativeDimension 2 (X ↘ S)]
  {D : X.IdealSheafData} {A B : LogarithmicProjection i D}
  {Y : Scheme} {b b' : Basis (Fin 2) ℤ N} {hi : IsIntegralLattice i}
  (r : Fin 4 ≃ A.fan.Ray)
  (hr : (fun t ↦ (r t).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])
  {n : ℕ} {T : BlowupTower A.fan.algebraicRealization (n + 2) Y}
  (hT : IsClosedPointTower A.fan.algebraicRealization T) (g : Y ⟶ P)

local notation "fA" => (A.fan.algebraicRealization ↘ S)
local notation "smooth[" b "]" =>
  (Eq.mp (congrArg (fun m ↦ SmoothOfRelativeDimension m fA) rankTwo[b])
    (A.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap A.isRegular))
local notation "C" => A.fan.hirzebruchPicardBasis b 0 A.isRegular r hr
local notation "orders[" j "]" => -(Prod.snd (mark[T,hT,fA,g])) j
local notation "onFiber[" t "," j "]" =>
  (∃ c : ℂˣ, hT.baseCenter j = center[b,fiber[r,t],c])
local notation "atCorner[" t "," j "]" =>
  (∃ σ : A.fan.cones, Nat.card (ToricRay σ.val) = 2 ∧ Fan.Ray.toCone A.fan (fiber[r,t]) ≤ σ ∧
    Fan.Ray.toCone A.fan (r 0) ≤ σ ∧ hT.baseCenter j = A.fan.distinguishedPointHom σ pt)

include hr in
private theorem sum_first_orders_le_section_degree [Nonempty A.fan.cones]
    [SmoothOfRelativeDimension 2 fA]
    (hg : g ≫ (P ↘ S) = T.toBase ≫ fA) {j l : Fin (n + 2)} (hjl : j ≠ l)
    (hj : hT.baseCenter j ∈ (A.fan.rayBoundaryIdeal A.isRegular (r 0)).support)
    (hl : hT.baseCenter l ∈ (A.fan.rayBoundaryIdeal A.isRegular (r 0)).support)
    (hjfirst : ∀ q < j, hT.baseCenter q ≠ hT.baseCenter j)
    (hlfirst : ∀ q < l, hT.baseCenter q ≠ hT.baseCenter l) :
    orders[j] + orders[l] ≤ (C).repr (mark[T,hT,fA,g]).1 0 := by
  classical
  let : A.fan.algebraicRealization.IsProjectiveOver ℂ :=
    A.fan.isProjectiveOver_quadric b A.isRegular A.isComplete r hr
  let : Y.Over S := ⟨T.toBase ≫ fA⟩
  let : g.IsOver S := ⟨hg⟩
  let x := mark[T,hT,fA,g]
  have hnef : (T.picardHom x).toMul.IsNef ℂ (T.toBase ≫ fA) := by
    rw [← T.picardMarking_apply hT fA, LinearEquiv.apply_symm_apply, toMul_ofMul]
    exact (isAmple_twistingSheaf ℂ (Fin 3 → ℂ) Nat.one_pos).isNef.pullback g
  let m (q : Fin (n + 2)) := (-x.2 q).toNat
  have hm (q : Fin (n + 2)) : (m q : ℤ) = -x.2 q :=
    Int.toNat_of_nonneg (neg_nonneg.mpr (hT.exceptionalCoeff_nonpos_of_isNef_picardHom hnef q))
  have hcoeff : (fun q ↦ -(m q : ℤ)) = x.2 := funext fun q ↦ by rw [hm, neg_neg]
  have hnef' : (T.picardHom (x.1, fun q ↦ -(m q : ℤ))).toMul.IsNef ℂ (T.toBase ≫ fA) := by
    simpa only [hcoeff, Prod.mk.eta] using hnef
  have hbound := (r 0).sum_first_base_orders_le_ray_degree b A.isRegular hT x.1 m {j, l} (by
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact ⟨hj, hjfirst⟩
      · obtain rfl := Finset.mem_singleton.mp hq
        exact ⟨hl, hlfirst⟩) hnef'
  -- The section of the quadric has square zero, so its degree is coordinate zero.
  have hdegree := (A.fan.hirzebruchPicardBasis_intersection_repr b 0 A.isRegular r hr
    A.isComplete x.1).2
  rw [Fan.hirzebruchPicardBasis_apply_one, zero_mul, sub_zero] at hdegree
  dsimp only at hbound
  rw [Finset.sum_pair hjl, hm, hm, hdegree] at hbound
  exact hbound

variable [IsIntegral X] [IsNoetherian X]

include hr in
private theorem decrease_of_mixed_centers [Nonempty A.fan.cones]
    [SmoothOfRelativeDimension 2 fA]
    (hD : D.IsEffectiveCartier)
    (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S))
    (hB : B.fan = plane[b',hi]) (k : X ≅ Y)
    (hAh : A.hom = k.hom ≫ T.toBase) (hBh : B.hom ≍ k.hom ≫ g ≫ (planeIso[b',hi]).inv)
    (hg : g ≫ (P ↘ S) = T.toBase ≫ fA) (hbir : Scheme.BirationalOver g (𝟙 P))
    (t : Fin 2) (j l : Fin (n + 2)) (c : ℂˣ) (hl : hT.baseCenter l = center[b,fiber[r,t],c])
    (hlfirst : ∀ q < l, hT.baseCenter q ≠ hT.baseCenter l)
    (σ : A.fan.cones) (hσ : Nat.card (ToricRay σ.val) = 2)
    (hopp : Fan.Ray.toCone A.fan (fiber[r,Equiv.swap 0 1 t]) ≤ σ)
    (hj : hT.baseCenter j = A.fan.distinguishedPointHom σ pt)
    (hjfirst : ∀ q < j, hT.baseCenter q ≠ hT.baseCenter j) (d : ℕ ×ₗ ℕ)
    (hsum : (C).repr (mark[T,hT,fA,g]).1 0 < orders[j] + orders[l])
    (hd : 3 * ((C).repr (mark[T,hT,fA,g]).1 1).toNat ≤ (ofLex d).1) :
    HasPlaneTargetDecrease A B rankTwo[b] hD hNode d := by
  obtain ⟨a, s, hs, -, hs₁, hpic⟩ :=
    A.fan.exists_hirzebruch_picardBasis_of_fiber b 0 r hr A.isRegular t
  have hoppGen : (fiber[r,Equiv.swap 0 1 t]).primitiveGenerator =
      -(fiber[r,t]).primitiveGenerator := by
    fin_cases t <;> simp [congrFun hr]
  have hs₃ : s 3 = fiber[r,Equiv.swap 0 1 t] := by
    apply Fan.Ray.primitiveGenerator_injective
    rw [hoppGen, ← hs₁]
    have h₁ : (s 1).primitiveGenerator = a 1 := congrFun hs 1
    rw [h₁]
    simpa using congrFun hs 3
  obtain ⟨c', hc'⟩ := (fiber[r,t]).exists_binomialCenter_eq_of_basis a b c
  have hl' : hT.baseCenter l = center[a,s 1,c'] := by rw [hs₁, hc', hl]
  apply exists_sarkisov_step_of_quadric_corner_and_smooth_centers s hs hT g hD hNode hB k
    hAh hBh hg hbir j l c' hl' hlfirst σ hσ (hs₃.symm ▸ hopp) hj hjfirst d
  · simpa only [hpic] using hsum
  · simpa only [hpic] using hd

/-- Suppose two distinct first centers on opposite invariant fibers of a marked
quadric-to-plane resolution have orders whose sum exceeds the transverse degree.
Each mark is either on its fiber's open orbit or at the corner on the designated
section `r 0`. Then either both marks are on the open orbits, or the mixed link
returns a decrease for the same marked plane target. This comparison works for
any reference bidegree with first coordinate at least three times the ruling
fiber degree, and for any orders at the other centers. -/
theorem open_fiber_centers_or_sarkisov_step_of_prepared_quadric
    (hD : D.IsEffectiveCartier)
    (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S))
    (hB : B.fan = plane[b',hi]) (k : X ≅ Y)
    (hAh : A.hom = k.hom ≫ T.toBase) (hBh : B.hom ≍ k.hom ≫ g ≫ (planeIso[b',hi]).inv)
    (hg : g ≫ (P ↘ S) = T.toBase ≫ fA) (hbir : Scheme.BirationalOver g (𝟙 P))
    {j l : Fin (n + 2)} (hjl : j ≠ l)
    (hjfirst : ∀ q < j, hT.baseCenter q ≠ hT.baseCenter j)
    (hlfirst : ∀ q < l, hT.baseCenter q ≠ hT.baseCenter l)
    (hj : onFiber[0,j] ∨ atCorner[0,j]) (hl : onFiber[1,l] ∨ atCorner[1,l]) (d : ℕ ×ₗ ℕ) :
    let : Nonempty A.fan.cones := A.isComplete.nonempty_cones
    let : SmoothOfRelativeDimension 2 fA := smooth[b]
    (C).repr (mark[T,hT,fA,g]).1 0 < orders[j] + orders[l] →
    3 * ((C).repr (mark[T,hT,fA,g]).1 1).toNat ≤ (ofLex d).1 →
    (onFiber[0,j] ∧ onFiber[1,l]) ∨ HasPlaneTargetDecrease A B rankTwo[b] hD hNode d := by
  intro hcones hdim hsum hd
  let := hcones
  let := hdim
  rcases hj with ⟨c, hj⟩ | ⟨σ, hσ, hσfiber, hσsection, hj⟩
  · rcases hl with ⟨a, hl⟩ | ⟨τ, hτ, hτfiber, -, hl⟩
    · exact Or.inl ⟨⟨c, hj⟩, a, hl⟩
    · exact Or.inr (decrease_of_mixed_centers r hr hT g hD hNode hB k hAh hBh hg hbir
        0 l j c hj hjfirst τ hτ hτfiber hl hlfirst d (by simpa only [add_comm] using hsum) hd)
  · rcases hl with ⟨a, hl⟩ | ⟨τ, -, -, hτsection, hl⟩
    · exact Or.inr (decrease_of_mixed_centers r hr hT g hD hNode hB k hAh hBh hg hbir
        1 j l a hl hlfirst σ hσ hσfiber hj hjfirst d hsum hd)
    · have hmem {q : Fin (n + 2)} {θ : A.fan.cones}
          (hq : hT.baseCenter q = A.fan.distinguishedPointHom θ pt)
          (hθ : (r 0).toCone ≤ θ) :
          hT.baseCenter q ∈ (A.fan.rayBoundaryIdeal A.isRegular (r 0)).support :=
        hq ▸ (A.fan.distinguishedPoint_mem_support_rayBoundaryIdeal_iff A.isRegular θ (r 0)).mpr hθ
      exact (not_lt_of_ge (sum_first_orders_le_section_degree r hr hT g hg hjl
        (hmem hj hσsection) (hmem hl hτsection) hjfirst hlfirst) hsum).elim

end TauCeti.Toric.Fan.LogarithmicProjection
