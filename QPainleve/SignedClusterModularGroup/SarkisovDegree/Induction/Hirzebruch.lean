/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Induction.Step

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective
import QPainleve.SignedClusterModularGroup.SarkisovDegree.Path.SectionOrCorner

/-!
# Marked Sarkisov steps at Hirzebruch corners and sections

A high base order above a toric corner or an invariant section gives a decreasing
plane-target marking. The new marking is for the same target projection on the
specified resolving surface. The decrease is the corner or section case of
[Lutz, Proposition 8.11][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=72
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
local notation "planeIso[" b "," hi "]" =>
  (Fan.projectivePlaneIso b hi ≪≫ Basis.polynomialProjIso (Pi.basisFun ℂ (Fin 3)))
local notation "mark[" T "," hT "," f "," g "]" =>
  LinearEquiv.symm (BlowupTower.picardMarking T hT f) (Additive.ofMul (pullback g H))
local notation "obj[" F "," A "]" => @Prefunctor.obj _ sarkisovQuiver _ sarkisovQuiver F A

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {X : Scheme} [X.Over S] [SmoothOfRelativeDimension 2 (X ↘ S)]
  [IsIntegral X] [IsNoetherian X] {D : X.IdealSheafData}
  {A B : LogarithmicProjection i D}
  {Y : Scheme} {b b' : Basis (Fin 2) ℤ N} {hi : IsIntegralLattice i} {a n : ℕ}
  (r : Fin 4 ≃ A.fan.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (a : ℤ) • b 0 - b 1])
  {T : BlowupTower A.fan.algebraicRealization (n + 1) Y}
  (hT : IsClosedPointTower A.fan.algebraicRealization T) (g : Y ⟶ P)

local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "fA" => (A.fan.algebraicRealization ↘ S)
local notation "hirzebruchSmooth" =>
  Eq.mp (congrArg (fun d ↦ SmoothOfRelativeDimension d fA) rankTwo)
    (A.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap A.isRegular)
local notation "center[" ρ "," c "]" => Fan.Ray.binomialCenter ρ rankTwo
  (Basis.detDualEquiv_self b (Fan.Ray.primitiveGenerator ρ))
  (Fan.Ray.surjective_detCharacter ρ b) c (IsLocalRing.closedPoint ℂ)

/-- A marked Hirzebruch-to-plane resolution with a high order above a toric
corner or a smooth point of an invariant section gives a decreasing block for
the same plane target. The given order can be at an infinitely near center. -/
theorem exists_sarkisov_step_of_hirzebruch_corner_or_section_marking
    (hD : D.IsEffectiveCartier)
    (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S))
    (hB : B.fan = Fan.projectiveSpace b' hi) (k : X ≅ Y)
    (hAh : A.hom = k.hom ≫ T.toBase) (hBh : B.hom ≍ k.hom ≫ g ≫ (planeIso[b',hi]).inv)
    (hg : g ≫ s = T.toBase ≫ fA) (hbir : Scheme.BirationalOver g (𝟙 P))
    (j : Fin (n + 1))
    (hp : (∃ σ : A.fan.cones, Nat.card (ToricRay σ.val) = 2 ∧
        hT.baseCenter j = A.fan.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ)) ∨
      ∃ t : Fin 2, ∃ c : ℂˣ, hT.baseCenter j = center[r ((![0, 2] : Fin 2 → Fin 4) t),c]) :
    let : SmoothOfRelativeDimension 2 fA := hirzebruchSmooth
    let x := mark[T,hT,fA,g]
    let β := (A.fan.hirzebruchPicardBasis b a A.isRegular r hr).repr x.1 1
    β < 2 * (-x.2 j) →
      HasPlaneTargetDecrease A B rankTwo hD hNode
        (hirzebruchSarkisovBidegree β.toNat (sarkisovSecondaryDegree ℂ x.1.toMul).toNat) := by
  intro hSmoothA x β hhigh
  let := hSmoothA
  let : Y.Over S := ⟨T.toBase ≫ fA⟩
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension fA
  let : IsIntegral Y := hT.isIntegral fA
  let : IsNoetherian Y := T.isNoetherian
  let : A.fan.algebraicRealization.IsProjectiveOver ℂ :=
    A.fan.isProjectiveOver_algebraicRealization_of_isComplete A.isRegular A.isComplete b
  let : k.hom.IsOver S := ⟨(Category.assoc k.hom T.toBase fA).symm.trans
    (hAh ▸ comp_over A.hom S)⟩
  let : k.inv.IsOver S := inferInstance
  let : k.symm.hom.IsOver S := inferInstanceAs (k.inv.IsOver S)
  let E := D.comap k.inv
  let F := precomposeSarkisovOfIso (i := i) rankTwo k.symm (rfl : D.comap k.inv = E)
  have hL : (obj[F,A]).hom ≍ T.toBase :=
    precomposeSarkisovOfIso_obj_hom_of_comp rankTwo k.symm rfl A rfl (heq_of_eq hAh)
  have hR : (obj[F,B]).hom ≍ g ≫ (planeIso[b',hi]).inv :=
    precomposeSarkisovOfIso_obj_hom_of_comp rankTwo k.symm rfl B hB hBh
  obtain ⟨_, C, p, a', d, t, ht, Z, U, hU, e, -, -, -, hCh, hproj, -, hg', hbir', -, -, -, hlt⟩ :=
    hT.exists_sarkisov_path_decrease_of_hirzebruch_corner_or_section b a A.isRegular A.isComplete
      r hr g hg hbir j hp (D := E) (obj[F,A]) (precomposeSarkisovOfIso_obj_fan ..) hL hhigh
  have hRh : (obj[F,B]).hom ≍ e.hom ≫ (e.inv ≫ g) ≫ (planeIso[b',hi]).inv := by
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hR
  have hm := HasPlaneTargetMarking.hirzebruch (A := C) (B := obj[F,B]) d b' a' hi t ht
    ((precomposeSarkisovOfIso_obj_fan ..).trans hB) U hU e (e.inv ≫ g) hCh hRh hg' hbir'
  let := hproj
  let : Nonempty C.fan.cones := C.isComplete.nonempty_cones
  let : SmoothOfRelativeDimension 2 (C.fan.algebraicRealization ↘ S) := by
    simpa only [← Fan.algebraicRealization_over, rankTwo] using
      C.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap C.isRegular
  refine HasPlaneTargetDecrease.of_path_on_iso rankTwo hD hNode k ?_ p
    (precomposeSarkisovOfIso_obj_fan ..) (precomposeSarkisovOfIso_obj_hom ..)
    (precomposeSarkisovOfIso_obj_fan ..) (precomposeSarkisovOfIso_obj_hom ..) hm
  dsimp only
  rw [hT.sarkisovSecondaryDegree_eq_sum g hg hbir,
    hU.sarkisovSecondaryDegree_eq_sum (e.inv ≫ g) hg' hbir']
  exact hlt

end TauCeti.Toric.Fan.LogarithmicProjection
