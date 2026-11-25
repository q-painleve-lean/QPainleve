/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Induction.Step

import QPainleve.Geometry.Toric.Fan.Picard.Quadric
import QPainleve.SignedClusterModularGroup.SarkisovDegree.Quadric.PlanePath
import QPainleve.SignedClusterModularGroup.SarkisovDegree.Quadric.SelectedCenters

/-!
# Marked exits at selected smooth quadric centers

A retained smooth center on an invariant fiber gives a marked path to a plane
resolution of the specified target map. Its degree depends on the two ruling
coefficients and the retained order. A strict bound on this degree suffices
for a primary bidegree decrease. A pair of selected smooth centers on opposite
fibers gives a marked quadric exit when the sum of their orders exceeds the
transverse ruling degree.
-/

public section

open AlgebraicGeometry CategoryTheory Module QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra

namespace TauCeti.Toric.Fan.LogarithmicProjection

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "s" => (P ↘ S)
local notation "H" => LineBundleClass.mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "coords" => Pi.basisFun ℂ (Fin 3)
local notation "degree" => Basis.picardTwistEquiv coords
local notation "plane[" b "," hi "]" => Fan.projectiveSpace b hi
local notation "planeIso[" b "," hi "]" =>
  (Fan.projectivePlaneIso b hi ≪≫ Basis.polynomialProjIso coords)
local notation "mark[" U "," hU "," f "," g "]" =>
  LinearEquiv.symm (BlowupTower.picardMarking U hU f) (Additive.ofMul (pullback g H))
local notation "obj[" F "," A "]" => @Prefunctor.obj _ sarkisovQuiver _ sarkisovQuiver F A
local notation "rankTwo[" b "]" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "point[" b "," ρ "," c "]" =>
  Fan.Ray.binomialCenter ρ rankTwo[b] (Basis.detDualEquiv_self b (Fan.Ray.primitiveGenerator ρ))
    (Fan.Ray.surjective_detCharacter ρ b) c (IsLocalRing.closedPoint ℂ)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Y : Scheme} {n : ℕ}

local notation "fiberRay[" r "," t "]" => r ((![1, 3] : Fin 2 → Fin 4) t)
local notation "smooth[" Φ "," b "," h "]" =>
  Eq.mp (congrArg (fun d ↦ SmoothOfRelativeDimension d (Fan.algebraicRealization Φ ↘ S)) rankTwo[b])
    (Fan.smoothOfRelativeDimension_algebraicRealizationStructureMap Φ h)

section Fiber

variable {Φ : Fan i} (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) {b : Basis (Fin 2) ℤ N}
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun l ↦ (r l).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])
  {T : BlowupTower Φ.algebraicRealization (n + 1) Y}
  (hT : IsClosedPointTower Φ.algebraicRealization T) (g : Y ⟶ P)

local notation "f" => (Φ.algebraicRealization ↘ S)

private theorem exists_sarkisov_path_to_plane_of_smooth_fiber_center
    (hg : g ≫ s = T.toBase ≫ f) (hbir : Scheme.BirationalOver g (𝟙 P))
    (t : Fin 2) (c : ℂˣ) (j : Fin (n + 1)) (hj : hT.baseCenter j = point[b,fiberRay[r,t],c])
    (hfirst : ∀ l < j, hT.baseCenter l ≠ hT.baseCenter j) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 f := smooth[Φ,b,hΦ]
    let : Y.Over S := ⟨T.toBase ≫ f⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f
    let : IsIntegral Y := hT.isIntegral f
    let x := mark[T,hT,f,g]
    let C := Φ.hirzebruchPicardBasis b 0 hΦ r hr
    ∀ {J : Y.IdealSheafData} (L : LogarithmicProjection i J),
      L.fan = Φ → L.hom ≍ T.toBase →
      ∃ (a : Basis (Fin 2) ℤ N) (M : LogarithmicProjection i J) (_ : SarkisovPath L M)
        (Z : Scheme) (U : BlowupTower P (1 + (1 + n)) Z) (hU : IsClosedPointTower P U)
        (e : Y ≅ Z),
        M.fan = plane[a,Φ.lattice] ∧ M.hom ≍ e.hom ≫ U.toBase ≫ (planeIso[a,Φ.lattice]).inv ∧
        (e.inv ≫ g) ≫ s = U.toBase ≫ s ∧ Scheme.BirationalOver (e.inv ≫ g) (𝟙 P) ∧
        let d' := degree (mark[U,hU,s,e.inv ≫ g]).1
        0 < d' ∧ d' = C.repr x.1 0 + C.repr x.1 1 - (-x.2 j) := by
  intro hCones hSmooth hOver hSmoothY hIntegral x C J L hL hhL
  let := hCones
  let := hSmooth
  let := hOver
  let := hSmoothY
  let := hIntegral
  have hPole : (Φ.boundaryIdeal hc.nonempty_cones).comap T.toBase =
      J * hT.ramificationIdealSheafToBase ℂ := by
    rcases L with ⟨Ψ, hΨ, hcΨ, l, hl, hDom, hpole⟩
    dsimp only at hL hhL
    subst Ψ
    obtain rfl : l = T.toBase := eq_of_heq hhL
    let : T.toBase.IsOver S := ⟨rfl⟩
    rw [hT.ramificationIdealSheafToBase_def ℂ]
    exact hpole
  obtain ⟨d, u, hu, hu₀, -, hPic⟩ := Φ.exists_quadric_picardBasis_of_fiber b hΦ r hr t
  obtain ⟨c', hc'⟩ := (fiberRay[r,t]).exists_binomialCenter_eq_of_basis d b c
  have hj' : hT.baseCenter j = point[d,u 0,c'] := by rw [hu₀, hc', hj]
  obtain ⟨a, -, L', M, p, Z, U, hU, e, hL', hhL', hM, hhM, -, -, hg', hbir', -,
      hdegree, -, -, -, hpos⟩ :=
    hT.exists_sarkisov_path_of_quadric_smooth_center d hΦ hc u hu g hg hbir
      c' j hj' (fun l hl ↦ hj' ▸ hfirst l hl) J hPole
  have he : L' = L := LogarithmicProjection.ext (hL'.trans hL.symm) (hhL'.trans hhL.symm)
  refine ⟨a, M, he ▸ p, Z, U, hU, e, hM, hhM, hg', hbir', hpos, ?_⟩
  simpa only [x, C, hPic, Basis.repr_reindex_apply, Equiv.symm_swap, Equiv.swap_apply_left,
    Equiv.swap_apply_right, add_comm] using hdegree

end Fiber

variable {X : Scheme} [X.Over S] [SmoothOfRelativeDimension 2 (X ↘ S)]
  [IsIntegral X] [IsNoetherian X] {D : X.IdealSheafData} {A B : LogarithmicProjection i D}

/-- A first center over a smooth point of an invariant fiber gives a decreasing
step from the specified quadric projection to a marked plane resolution.
With ruling coefficients `a, b`, fiber degree `b`, and selected order `m`,
the strict inequality `2 * (a + b - m) < 3 * b` gives a decrease against
any reference bidegree with first coordinate at least `3 * b`. -/
theorem exists_sarkisov_step_of_quadric_smooth_center
    {b b' : Basis (Fin 2) ℤ N} {hi : IsIntegralLattice i}
    (r : Fin 4 ≃ A.fan.Ray)
    (hr : (fun l ↦ (r l).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])
    {T : BlowupTower A.fan.algebraicRealization (n + 1) Y}
    (hT : IsClosedPointTower A.fan.algebraicRealization T) (g : Y ⟶ P)
    (hD : D.IsEffectiveCartier)
    (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S))
    (hB : B.fan = plane[b',hi]) (k : X ≅ Y)
    (hAh : A.hom = k.hom ≫ T.toBase) (hBh : B.hom ≍ k.hom ≫ g ≫ (planeIso[b',hi]).inv)
    (hg : g ≫ s = T.toBase ≫ (A.fan.algebraicRealization ↘ S))
    (hbir : Scheme.BirationalOver g (𝟙 P)) (t : Fin 2) (c : ℂˣ) (j : Fin (n + 1))
    (hj : hT.baseCenter j = point[b,fiberRay[r,t],c])
    (hfirst : ∀ l < j, hT.baseCenter l ≠ hT.baseCenter j) (d : ℕ ×ₗ ℕ) :
    let : SmoothOfRelativeDimension 2 (A.fan.algebraicRealization ↘ S) :=
      smooth[A.fan,b,A.isRegular]
    let x := mark[T,hT,(A.fan.algebraicRealization ↘ S),g]
    let C := A.fan.hirzebruchPicardBasis b 0 A.isRegular r hr
    2 * (C.repr x.1 0 + C.repr x.1 1 - (-x.2 j)) < 3 * C.repr x.1 1 →
    3 * (C.repr x.1 1).toNat ≤ (ofLex d).1 →
    HasPlaneTargetDecrease A B rankTwo[b] hD hNode d := by
  intro hSmooth x C hlt hd
  let := hSmooth
  let fA := A.fan.algebraicRealization ↘ S
  let : Y.Over S := ⟨T.toBase ≫ fA⟩
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension fA
  let : IsIntegral Y := hT.isIntegral fA
  let : IsNoetherian Y := T.isNoetherian
  let : k.hom.IsOver S := ⟨(Category.assoc k.hom T.toBase fA).symm.trans
    (hAh ▸ comp_over A.hom S)⟩
  let : k.symm.hom.IsOver S := inferInstanceAs (k.inv.IsOver S)
  let F := precomposeSarkisovOfIso (i := i) rankTwo[b] k.symm (rfl : D.comap k.inv = D.comap k.inv)
  have hL := precomposeSarkisovOfIso_obj_hom_of_comp rankTwo[b] k.symm rfl A rfl (heq_of_eq hAh)
  have hR := precomposeSarkisovOfIso_obj_hom_of_comp rankTwo[b] k.symm rfl B hB hBh
  obtain ⟨a, M, path, Z, U, hU, e, hM, hhM, hg', hbir', hpos, hdegree⟩ :=
    exists_sarkisov_path_to_plane_of_smooth_fiber_center A.isRegular A.isComplete r hr hT g hg hbir
      t c j hj hfirst (obj[F,A]) (precomposeSarkisovOfIso_obj_fan ..) hL
  have htarget : (obj[F,B]).hom ≍ e.hom ≫ (e.inv ≫ g) ≫ (planeIso[b',hi]).inv := by
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hR
  have hm := HasPlaneTargetMarking.plane (A := M) (B := obj[F,B]) a b' hi hM
    ((precomposeSarkisovOfIso_obj_fan ..).trans hB) U hU e (e.inv ≫ g) hhM htarget hg' hbir'
  refine HasPlaneTargetDecrease.of_path_on_iso rankTwo[b] hD hNode k ?_ path
    (precomposeSarkisovOfIso_obj_fan ..) (precomposeSarkisovOfIso_obj_hom ..)
    (precomposeSarkisovOfIso_obj_fan ..) (precomposeSarkisovOfIso_obj_hom ..) hm
  rw [Prod.Lex.lt_iff, ofLex_planeSarkisovBidegree]
  refine Or.inl (lt_of_lt_of_le ?_ hd)
  have hBound : 2 * degree (mark[U,hU,s,e.inv ≫ g]).1 < 3 * C.repr x.1 1 := by
    rw [hdegree]
    exact hlt
  omega

/-- Two first centers on opposite invariant quadric fibers give a decreasing
block for the specified plane target if their combined order exceeds the
transverse degree. The reference bidegree can have any secondary coordinate
and any primary coordinate at least three times the original fiber degree. -/
theorem exists_sarkisov_step_of_quadric_two_smooth_fiber_centers
    {b b' : Basis (Fin 2) ℤ N} {hi : IsIntegralLattice i}
    (r : Fin 4 ≃ A.fan.Ray)
    (hr : (fun l ↦ (r l).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])
    {T : BlowupTower A.fan.algebraicRealization n Y}
    (hT : IsClosedPointTower A.fan.algebraicRealization T) (g : Y ⟶ P)
    (hD : D.IsEffectiveCartier)
    (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S))
    (hB : B.fan = plane[b',hi]) (k : X ≅ Y)
    (hAh : A.hom = k.hom ≫ T.toBase) (hBh : B.hom ≍ k.hom ≫ g ≫ (planeIso[b',hi]).inv)
    (hg : g ≫ s = T.toBase ≫ (A.fan.algebraicRealization ↘ S))
    (hbir : Scheme.BirationalOver g (𝟙 P)) (j l : Fin n) (hjl : j ≠ l)
    (t : Fin 2) (c c' : ℂˣ)
    (hj : hT.baseCenter j = point[b,fiberRay[r,t],c])
    (hl : hT.baseCenter l = point[b,fiberRay[r,Equiv.swap 0 1 t],c'])
    (hjfirst : ∀ q < j, hT.baseCenter q ≠ hT.baseCenter j)
    (hlfirst : ∀ q < l, hT.baseCenter q ≠ hT.baseCenter l) (d : ℕ ×ₗ ℕ) :
    let : SmoothOfRelativeDimension 2 (A.fan.algebraicRealization ↘ S) :=
      smooth[A.fan,b,A.isRegular]
    let x := mark[T,hT,(A.fan.algebraicRealization ↘ S),g]
    let C := A.fan.hirzebruchPicardBasis b 0 A.isRegular r hr
    C.repr x.1 0 < -x.2 j + -x.2 l →
    3 * (C.repr x.1 1).toNat ≤ (ofLex d).1 →
    HasPlaneTargetDecrease A B rankTwo[b] hD hNode d := by
  intro hSmooth x C hsum hd
  let := hSmooth
  let fA := A.fan.algebraicRealization ↘ S
  let : Y.Over S := ⟨T.toBase ≫ fA⟩
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension fA
  let : IsIntegral Y := hT.isIntegral fA
  let : IsNoetherian Y := T.isNoetherian
  let : k.hom.IsOver S := ⟨(Category.assoc k.hom T.toBase fA).symm.trans
    (hAh ▸ comp_over A.hom S)⟩
  let : k.symm.hom.IsOver S := inferInstanceAs (k.inv.IsOver S)
  let F := precomposeSarkisovOfIso (i := i) rankTwo[b] k.symm (rfl : D.comap k.inv = D.comap k.inv)
  have hL := precomposeSarkisovOfIso_obj_hom_of_comp rankTwo[b] k.symm rfl A rfl (heq_of_eq hAh)
  have hR := precomposeSarkisovOfIso_obj_hom_of_comp rankTwo[b] k.symm rfl B hB hBh
  have hPole : (A.fan.boundaryIdeal A.isComplete.nonempty_cones).comap T.toBase =
      D.comap k.inv * hT.ramificationIdealSheafToBase ℂ := by
    have hF := precomposeSarkisovOfIso_obj_fan rankTwo[b] k.symm rfl A
    generalize obj[F,A] = L at hL hF
    rcases L with ⟨Ψ, hΨ, hcΨ, p, hp, hDom, hpole⟩
    dsimp only at hL hF
    subst Ψ
    obtain rfl : p = T.toBase := eq_of_heq hL
    let : T.toBase.IsOver S := ⟨rfl⟩
    simpa only [hT.ramificationIdealSheafToBase_def ℂ] using hpole
  obtain ⟨L, Q, p, a, u, hu, Z, m, U, hU, e, -, hLfan, hLhom, hQ, -, hg', hbir',
    -, hpos, -, hlt⟩ :=
    hT.exists_sarkisov_path_of_quadric_two_smooth_fiber_centers b A.isRegular A.isComplete r hr
      g hg hbir j l hjl t c c' hj hl hjfirst hlfirst hPole hsum
  have hEq : L = obj[F,A] := LogarithmicProjection.ext
    (hLfan.trans (precomposeSarkisovOfIso_obj_fan ..).symm) (hLhom.trans hL.symm)
  have htarget : (obj[F,B]).hom ≍ e.hom ≫ (e.inv ≫ g) ≫ (planeIso[b',hi]).inv := by
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hR
  have hm := HasPlaneTargetMarking.hirzebruch (A := Q) (B := obj[F,B]) a b' 0 hi u hu
    ((precomposeSarkisovOfIso_obj_fan ..).trans hB) U hU e (e.inv ≫ g) hQ htarget hg' hbir'
  refine HasPlaneTargetDecrease.of_path_on_iso rankTwo[b] hD hNode k ?_ (hEq ▸ p)
    (precomposeSarkisovOfIso_obj_fan ..) (precomposeSarkisovOfIso_obj_hom ..)
    (precomposeSarkisovOfIso_obj_fan ..) (precomposeSarkisovOfIso_obj_hom ..) hm
  have hnat := (Int.toNat_lt_toNat (hpos.trans hlt)).mpr hlt
  refine Prod.Lex.lt_iff.mpr (Or.inl ?_)
  simpa only [ofLex_hirzebruchSarkisovBidegree, Nat.cast_zero] using
    (Nat.mul_lt_mul_of_pos_left hnat (by decide : 0 < 3)).trans_le hd

end TauCeti.Toric.Fan.LogarithmicProjection
