/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Induction.Step

import QPainleve.Geometry.Toric.Fan.Subdivision.Projective
import QPainleve.SignedClusterModularGroup.SarkisovDegree.Path.Corner
import QPainleve.SignedClusterModularGroup.SarkisovDegree.SectionContraction

/-!
# The plane exit at a quadric corner

A toric elementary transformation at a quadric corner followed by contraction
of the negative section gives a resolved path to the plane. The plane degree
is the sum of the quadric coefficients minus the selected order. The plane
marking keeps the prescribed target morphism and the ordered exceptional classes.

The elementary transformation uses the degree formula of
[Lutz, Lemma 8.9](https://arxiv.org/pdf/2005.05010v3#page=71).
-/

public section

open AlgebraicGeometry CategoryTheory Module QPainleve TauCeti.Toric
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra
open Fan Fan.LogarithmicProjection

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" Δ "]" => Fan.algebraicRealization Δ
local notation "f[" Δ "]" => (X[Δ] ↘ S)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "fP" => (P ↘ S)
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "coords" => Pi.basisFun ℂ (Fin 3)
local notation "plane[" d "," hi "]" => Fan.projectiveSpace d hi
local notation "planeIso[" d "," hi "]" =>
  Fan.projectivePlaneIso d hi ≪≫ Basis.polynomialProjIso coords
local notation "mark[" U "," hU "," f "," g "]" =>
  LinearEquiv.symm (BlowupTower.picardMarking U hU f) (Additive.ofMul (pullback g H))

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])
  {Y : Scheme} {n : ℕ} {T : BlowupTower X[Φ] (n + 1) Y}
  (hT : IsClosedPointTower X[Φ] T) (g : Y ⟶ P)

local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "C" => Φ.hirzebruchPicardBasis b 0 hΦ r hr

/-- Blow up the first center over a quadric corner, contract the strict transform
of its fiber, and contract the resulting negative section. The three links are
resolved by the given tower and end at the marked plane projection, retaining the
specified target morphism. For quadric coefficients `a, β` and selected order `m`,
the new degree is `a + β - m` and the two new orders are `a - m` and `β - m`. -/
theorem exists_sarkisov_path_of_quadric_corner
    (hg : g ≫ fP = T.toBase ≫ f[Φ]) (hbir : Scheme.BirationalOver g (𝟙 P))
    (σ : Φ.cones) (hσ : Nat.card (ToricRay σ.val) = 2) (j : Fin (n + 1))
    (hj : hT.baseCenter j = Φ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ))
    (hfirst : ∀ l < j, hT.baseCenter l ≠ hT.baseCenter j) {D : Y.IdealSheafData} :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 f[Φ] := by
      rw [Fan.algebraicRealization_over, ← rankTwo]
      exact Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : Y.Over S := ⟨T.toBase ≫ f[Φ]⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f[Φ]
    let : IsIntegral Y := hT.isIntegral f[Φ]
    let x := mark[T,hT,f[Φ],g]
    ∀ (A : LogarithmicProjection i D), A.fan = Φ → A.hom ≍ T.toBase →
      ∃ (B : LogarithmicProjection i D) (p : SarkisovPath A B)
        (d : Basis (Fin 2) ℤ N) (Z : Scheme) (U : BlowupTower P (1 + (1 + n)) Z)
        (hU : IsClosedPointTower P U) (k : Y ≅ Z),
        B.fan = plane[d,Φ.lattice] ∧
        B.hom ≍ k.hom ≫ U.toBase ≫ (planeIso[d,Φ.lattice]).inv ∧
        @Quiver.Path.length _ sarkisovQuiver _ _ p = 3 ∧
        p.rationalMap = (Scheme.PartialIso.ofDenseOpenImmersions
          (Fan.denseTorusι A.fan inferInstance)
          (Fan.denseTorusι B.fan inferInstance)).toRationalMap ∧
        (k.inv ≫ g) ≫ fP = U.toBase ≫ fP ∧ Scheme.BirationalOver (k.inv ≫ g) (𝟙 P) ∧
        let y := mark[U,hU,fP,k.inv ≫ g]
        let degree := Basis.picardTwistEquiv coords y.1
        degree = (C).repr x.1 0 + (C).repr x.1 1 + x.2 j ∧ 0 < degree ∧
        y.2 (Fin.castAdd (1 + n) (0 : Fin 1)) = -((C).repr x.1 0) - x.2 j ∧
        y.2 (Fin.natAdd 1 (Fin.castAdd n (0 : Fin 1))) = -((C).repr x.1 1) - x.2 j ∧
        (∀ l : Fin n, y.2 (Fin.natAdd 1 (Fin.natAdd 1 l)) = x.2 (j.succAbove l)) := by
  intro hcones hdim hOver hSmooth hIntegral x A hA hAh
  let := hcones
  let := hdim
  let := hOver
  let := hSmooth
  let := hIntegral
  let : X[Φ].IsProjectiveOver ℂ := Φ.isProjectiveOver_algebraicRealization_of_isComplete hΦ hc b
  let : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : T.toBase.IsOver S := ⟨rfl⟩
  let : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two f[Φ]
  rcases A with ⟨Φ', hreg, hcomp, f, hf, hdom, hpole⟩
  dsimp only at hA hAh
  subst Φ'
  obtain rfl : f = T.toBase := eq_of_heq hAh
  -- Choose a frame at the corner without changing the two quadric coefficients.
  obtain ⟨a, e, s, hs, shift, hcone, hshift, he, hrepr⟩ :=
    Φ.exists_hirzebruch_corner_picardBasis b 0 hΦ r hr hc σ hσ
  have hshift0 : shift = 0 := hshift.elim id id
  have he0 : e = 0 := by simpa only [hshift0, mul_zero, sub_zero] using he
  subst he0
  obtain ⟨M, q, b', t, ht, W, R, hR, u, hlen, hmap, hM, hproj, hg', hbir', -, -, -, -, -,
    ha, hβ, hy, -, -, -⟩ :=
    hT.exists_sarkisov_path_of_toric_corner a 0 hΦ hc s hs g hg hbir σ hcone j hj hfirst D hpole
  let : X[M.fan].IsProjectiveOver ℂ := hproj
  obtain ⟨d, J, Z, U, hU, k, hproj, hg'', hbir'', hdeg, hneg, htail, -, hstar⟩ :=
    hR.exists_plane_resolution_of_hirzebruchOne b' M.isRegular M.isComplete t ht (u.inv ≫ g)
      hg' hbir'
  -- The negative-section contraction is a final resolved toric blowdown.
  let B := M.coarsen hstar.isSubdivision (Fan.isRegular_projectiveSpace d M.fan.lattice) rankTwo
  have hB : B.fan = plane[d,Φ.lattice] := M.coarsen_fan ..
  have up : StarStep B M := by
    have e := M.coarsenBlowup rankTwo
      (Fan.isRegular_projectiveSpace d M.fan.lattice) M.isRegular hstar (.refl M.fan)
    rwa [M.coarsen_refl rankTwo] at e
  let down : @Quiver.Path _ LogarithmicProjection.instQuiver M B :=
    @Quiver.Hom.toPath _ LogarithmicProjection.instQuiver M B
      (@Quiver.reverse _ LogarithmicProjection.instQuiver
        LogarithmicProjection.instHasInvolutiveReverse.toHasReverse B M up)
  have hBh : B.hom ≍ (u ≪≫ k).hom ≫ U.toBase ≫ (planeIso[d,Φ.lattice]).inv := by
    refine (M.coarsen_hom ..).trans (heq_of_eq ?_)
    rw [Iso.trans_hom, Category.assoc, ← Category.assoc _ U.toBase, hproj,
      hM, Category.assoc, Category.assoc]
    simp
  have hpos := (hR.hirzebruch_resolution_degree_bounds b' 1 M.isRegular M.isComplete t ht
    (u.inv ≫ g) hg' hbir')
  let p := @Quiver.Path.comp _ sarkisovQuiver _ _ _ q (SarkisovPath.ofStar down)
  refine ⟨B, p, d, Z, U, hU, u ≪≫ k, hB, hBh, ?_, ?_, ?_, ?_, ?_⟩
  · have h := @Quiver.Path.length_comp _ sarkisovQuiver _ _ q _ (SarkisovPath.ofStar down)
    exact h.trans (by rw [hlen, SarkisovPath.length_ofStar down]; rfl)
  · simp only [p, SarkisovPath.rationalMap_comp, SarkisovPath.rationalMap_ofStar,
      pathRationalMap_eq_denseTorusPartialIso, hmap,
        Scheme.PartialIso.ofDenseOpenImmersions_toRationalMap_comp]
  · simpa only [Iso.trans_inv, Category.assoc] using hg''
  · simpa only [Iso.trans_inv, Category.assoc] using hbir''
  · simp only [Iso.trans_inv, Category.assoc]
    simp only [zero_add] at ha hβ
    have ha' : (Φ.hirzebruchPicardBasis a 0 hΦ s hs).repr x.1 0 = (C).repr x.1 0 := by
      simpa only [hshift0, zero_mul, sub_zero] using (hrepr x.1).1
    have hβ' := (hrepr x.1).2
    have hαpos := hpos.1.trans_le (by simpa only [Nat.cast_one, one_mul] using hpos.2.1)
    refine ⟨hdeg.trans (ha.trans (by rw [ha', hβ'])), hdeg.symm ▸ hαpos, ?_, ?_, ?_⟩
    · rw [hneg, ha, hβ, ha']
      ring
    · rw [htail, hy, Fin.append_left, hβ']
    · intro l
      rw [htail, hy, Fin.append_right, Function.comp_apply]

end QPainleve.BlowupTower.IsClosedPointTower

namespace TauCeti.Toric.Fan.LogarithmicProjection

open QPainleve.BlowupTower

local notation "obj[" F "," A "]" => @Prefunctor.obj _ sarkisovQuiver _ sarkisovQuiver F A

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {X : Scheme.{0}} [X.Over S] [SmoothOfRelativeDimension 2 (X ↘ S)]
  [IsIntegral X] [IsNoetherian X] {D : X.IdealSheafData} {A B : LogarithmicProjection i D}
  {Y : Scheme} {b b' : Basis (Fin 2) ℤ N} {hi : IsIntegralLattice i}
  (r : Fin 4 ≃ A.fan.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])
  {n : ℕ} {T : BlowupTower A.fan.algebraicRealization (n + 1) Y}
  (hT : IsClosedPointTower A.fan.algebraicRealization T) (g : Y ⟶ P)

local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "fA" => (A.fan.algebraicRealization ↘ S)

/-- A retained first center at a quadric corner gives a marked plane exit whenever
its plane degree `a + β - m` satisfies `2 * (a + β - m) < 3 * β`. The comparison
uses only the primary degree of the reference marking and preserves the specified
plane target. -/
theorem exists_sarkisov_step_of_quadric_corner
    (hD : D.IsEffectiveCartier)
    (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S))
    (hB : B.fan = plane[b',hi]) (k : X ≅ Y)
    (hAh : A.hom = k.hom ≫ T.toBase) (hBh : B.hom ≍ k.hom ≫ g ≫ (planeIso[b',hi]).inv)
    (hg : g ≫ fP = T.toBase ≫ fA) (hbir : Scheme.BirationalOver g (𝟙 P))
    (σ : A.fan.cones) (hσ : Nat.card (ToricRay σ.val) = 2) (j : Fin (n + 1))
    (hj : hT.baseCenter j = A.fan.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ))
    (hfirst : ∀ l < j, hT.baseCenter l ≠ hT.baseCenter j) (d : ℕ ×ₗ ℕ) :
    let : Nonempty A.fan.cones := A.isComplete.nonempty_cones
    let : SmoothOfRelativeDimension 2 fA := by
      rw [Fan.algebraicRealization_over, ← rankTwo]
      exact A.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap A.isRegular
    let x := mark[T,hT,fA,g]
    let C := A.fan.hirzebruchPicardBasis b 0 A.isRegular r hr
    let β := C.repr x.1 1
    2 * (C.repr x.1 0 + β + x.2 j) < 3 * β →
    3 * β.toNat ≤ (ofLex d).1 →
    HasPlaneTargetDecrease A B rankTwo hD hNode d := by
  intro hcones hSmoothA x C β hdrop hd
  let := hcones
  let := hSmoothA
  let : Y.Over S := ⟨T.toBase ≫ fA⟩
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension fA
  let : IsIntegral Y := hT.isIntegral fA
  let : IsNoetherian Y := T.isNoetherian
  let : k.hom.IsOver S := ⟨(Category.assoc k.hom T.toBase fA).symm.trans
    (hAh ▸ comp_over A.hom S)⟩
  let : k.symm.hom.IsOver S := inferInstanceAs (k.inv.IsOver S)
  let F := precomposeSarkisovOfIso (i := i) rankTwo k.symm (rfl : D.comap k.inv = D.comap k.inv)
  have hL := precomposeSarkisovOfIso_obj_hom_of_comp rankTwo k.symm rfl A rfl (heq_of_eq hAh)
  have hR := precomposeSarkisovOfIso_obj_hom_of_comp rankTwo k.symm rfl B hB hBh
  obtain ⟨Q, p, a, Z, U, hU, e, hQ, hQh, -, -, hg', hbir', hdeg, hpos, -⟩ :=
    hT.exists_sarkisov_path_of_quadric_corner b A.isRegular A.isComplete r hr g hg hbir
      σ hσ j hj hfirst (obj[F,A]) (precomposeSarkisovOfIso_obj_fan ..) hL
  have htarget : (obj[F,B]).hom ≍ e.hom ≫ (e.inv ≫ g) ≫ (planeIso[b',hi]).inv := by
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hR
  let : IsNoetherian P := isNoetherian_of_finiteType fP
  let y := mark[U,hU,fP,e.inv ≫ g]
  let degree := Basis.picardTwistEquiv coords y.1
  have hm := HasPlaneTargetMarking.plane (A := Q) (B := obj[F,B]) a b' hi hQ
    ((precomposeSarkisovOfIso_obj_fan ..).trans hB) U hU e (e.inv ≫ g) hQh htarget hg' hbir'
  have hdegree : degree = C.repr x.1 0 + β + x.2 j := hdeg
  have hdegreePos : 0 < degree := hpos
  have hlt : 2 * degree.toNat < 3 * β.toNat := by omega
  refine HasPlaneTargetDecrease.of_path_on_iso rankTwo hD hNode k ?_ p
    (precomposeSarkisovOfIso_obj_fan ..) (precomposeSarkisovOfIso_obj_hom ..)
    (precomposeSarkisovOfIso_obj_fan ..) (precomposeSarkisovOfIso_obj_hom ..) hm
  exact Prod.Lex.lt_iff.mpr (Or.inl (by
    simpa only [ofLex_planeSarkisovBidegree] using hlt.trans_le hd))

end TauCeti.Toric.Fan.LogarithmicProjection
