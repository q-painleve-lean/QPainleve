/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.StarFactorization
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Plane.Step
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.SecondaryDegree

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.Blowup.Tower.Factorization
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition

/-!
# Markings of Sarkisov resolutions with a plane target

A marking records a closed-point tower presenting the specified source projection
and computes the bidegree of the specified map to the target plane. The tower
comes with an isomorphism from the resolving surface. This lets the same
induction use an initial plane marking and the plane or Hirzebruch markings
returned by decreasing blocks.

The bidegree uses the anticanonical intersection of the moving line class
for its secondary coordinate, as in [Lutz, Proposition 8.11][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=72
-/

public noncomputable section

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

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {X : Scheme} [X.Over S] [SmoothOfRelativeDimension 2 (X ↘ S)]
  {D : X.IdealSheafData}

/-- The prescribed projections admit a marked plane-target resolution of the
given Sarkisov bidegree. The source marking is either a plane frame or a
Hirzebruch frame. Its tower and top isomorphism represent the exact source
projection, and the target plane map in the tower coordinates is birational. -/
inductive HasPlaneTargetMarking (A B : LogarithmicProjection i D) : ℕ ×ₗ ℕ → Prop
  /-- A resolution whose source is a plane. -/
  | plane (b b' : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)
      (hA : A.fan = plane[b,hi]) (hB : B.fan = plane[b',hi])
      {Y : Scheme} {n : ℕ} (T : BlowupTower P n Y) (hT : IsClosedPointTower P T)
      (k : X ≅ Y) (g : Y ⟶ P)
      (hAh : A.hom ≍ k.hom ≫ T.toBase ≫ (planeIso[b,hi]).inv)
      (hBh : B.hom ≍ k.hom ≫ g ≫ (planeIso[b',hi]).inv)
      (hg : g ≫ s = T.toBase ≫ s) (hbir : Scheme.BirationalOver g (𝟙 P)) :
      HasPlaneTargetMarking A B (let : IsNoetherian P := isNoetherian_of_finiteType s
        let x := mark[T,hT,s,g]
        planeSarkisovBidegree ((Basis.picardTwistEquiv coords) x.1).toNat
          (sarkisovSecondaryDegree ℂ x.1.toMul).toNat)
  /-- A resolution whose source carries a Hirzebruch marking. The second
  Picard coordinate gives the degree on the chosen ruling fiber. -/
  | hirzebruch (b b' : Basis (Fin 2) ℤ N) (e : ℕ) (hi : IsIntegralLattice i)
      (r : Fin 4 ≃ A.fan.Ray)
      (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (e : ℤ) • b 0 - b 1])
      (hB : B.fan = plane[b',hi])
      {Y : Scheme} {n : ℕ} (T : BlowupTower A.fan.algebraicRealization n Y)
      (hT : IsClosedPointTower A.fan.algebraicRealization T)
      (k : X ≅ Y) (g : Y ⟶ P)
      (hAh : A.hom = k.hom ≫ T.toBase)
      (hBh : B.hom ≍ k.hom ≫ g ≫ (planeIso[b',hi]).inv)
      (hg : g ≫ s = T.toBase ≫ (A.fan.algebraicRealization ↘ S))
      (hbir : Scheme.BirationalOver g (𝟙 P)) :
      HasPlaneTargetMarking A B (let f := (A.fan.algebraicRealization ↘ S)
        let : SmoothOfRelativeDimension 2 f :=
          (Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)) ▸
            A.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap A.isRegular
        let x := mark[T,hT,f,g]
        hirzebruchSarkisovBidegree
          ((A.fan.hirzebruchPicardBasis b e A.isRegular r hr).repr x.1 1).toNat
          (sarkisovSecondaryDegree ℂ x.1.toMul).toNat)

/-- Two specified logarithmic plane projections which are modifications admit
a plane-target marking. The marked source tower factors the given projection
in plane coordinates, and the map to the target plane is transported by the
same top isomorphism. -/
theorem exists_hasPlaneTargetMarking_of_plane [IsIntegral X] [X.IsProjectiveOver ℂ]
    (A B : LogarithmicProjection i D) [IsModification A.hom] [IsModification B.hom]
    (b b' : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)
    (hA : A.fan = plane[b,hi]) (hB : B.fan = plane[b',hi]) :
    ∃ d, HasPlaneTargetMarking A B d := by
  rcases A with ⟨Φ, hΦ, hcΦ, a, ha, haDom, haPole⟩
  rcases B with ⟨Ψ, hΨ, hcΨ, q, hq, hqDom, hqPole⟩
  dsimp only at hA hB
  subst Φ Ψ
  let := ha
  let := hq
  let := Fan.projectivePlaneIso_trans_polynomialProjIso_hom_isOver b hi coords
  let := Fan.projectivePlaneIso_trans_polynomialProjIso_hom_isOver b' hi coords
  let a' := a ≫ (planeIso[b,hi]).hom
  let q' := q ≫ (planeIso[b',hi]).hom
  let : a'.IsOver S := inferInstanceAs ((a ≫ (planeIso[b,hi]).hom).IsOver S)
  let : IsModification a' := inferInstanceAs (IsModification (a ≫ (planeIso[b,hi]).hom))
  let : IsModification q' := inferInstanceAs (IsModification (q ≫ (planeIso[b',hi]).hom))
  obtain ⟨n, Y, T, k, hT, hk⟩ :=
    a'.exists_isClosedPointTower_factorization (k := ℂ) (IsModification.birationalOver a')
  let g := k.inv ≫ q'
  let : IsModification g := inferInstanceAs (IsModification (k.inv ≫ q'))
  have ha' : a = k.hom ≫ T.toBase ≫ (planeIso[b,hi]).inv := by
    rw [← Category.assoc, hk]
    simp [a']
  have hq' : q = k.hom ≫ g ≫ (planeIso[b',hi]).inv := by
    simp [g, q']
  have hg : g ≫ s = T.toBase ≫ s := by
    apply (cancel_epi k.hom).mp
    rw [← Category.assoc k.hom T.toBase s, hk, comp_over a' S]
    simp only [g, Iso.hom_inv_id_assoc, q', Category.assoc, comp_over]
  exact ⟨_, HasPlaneTargetMarking.plane b b' hi rfl rfl T hT k g
    (heq_of_eq ha') (heq_of_eq hq') hg (IsModification.birationalOver g)⟩

section Precompose

variable {W : Scheme} [W.Over S] [SmoothOfRelativeDimension 2 (W ↘ S)]
  {E : W.IdealSheafData}

/-- An isomorphism identifying the two projections transports a marking with
the same bidegree. The source tower and the map in its model coordinates are shared. -/
theorem HasPlaneTargetMarking.of_iso
    {A B : LogarithmicProjection i D} {d : ℕ ×ₗ ℕ} (h : HasPlaneTargetMarking A B d)
    (k : W ≅ X) {A' B' : LogarithmicProjection i E}
    (hA' : A'.fan = A.fan) (hB' : B'.fan = B.fan)
    (hhA : A'.hom ≍ k.hom ≫ A.hom) (hhB : B'.hom ≍ k.hom ≫ B.hom) :
    HasPlaneTargetMarking A' B' d := by
  have hh {C : LogarithmicProjection i D} {C' : LogarithmicProjection i E}
      {Φ : Fan i} {Y : Scheme} {q : X ⟶ Y} {p : Y ⟶ Φ.algebraicRealization}
      (hC : C.fan = Φ) (he : C'.hom ≍ k.hom ≫ C.hom)
      (h : C.hom ≍ q ≫ p) : C'.hom ≍ (k.hom ≫ q) ≫ p := by
    rw [Category.assoc]
    exact he.trans (heq_comp rfl rfl (congrArg Fan.algebraicRealization hC) HEq.rfl h)
  cases h with
  | plane b b' hi hA hB T hT e g hAh hBh hg hbir =>
    exact .plane b b' hi (hA'.trans hA) (hB'.trans hB) T hT (k ≪≫ e) g
      (hh hA hhA hAh) (hh hB hhB hBh) hg hbir
  | hirzebruch b b' n hi r hr hB T hT e g hAh hBh hg hbir =>
    rcases A' with ⟨Φ, hreg, hc, a, ha, hdom, hpole⟩
    dsimp only at hA'
    subst Φ
    exact HasPlaneTargetMarking.hirzebruch (A := ⟨_, hreg, hc, a, ha, hdom, hpole⟩)
      (B := B') b b' n hi r hr (hB'.trans hB) T hT (k ≪≫ e) g
      (eq_of_heq (hh rfl hhA (heq_of_eq hAh))) (hh hB hhB hBh) hg hbir

end Precompose

end TauCeti.Toric.Fan.LogarithmicProjection
