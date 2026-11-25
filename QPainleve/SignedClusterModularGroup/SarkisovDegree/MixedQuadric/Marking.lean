/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Induction.Step
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.MixedQuadric.Exit

/-!
# A marked Sarkisov step at a quadric corner and smooth center

The mixed two-center link strictly lowers the primary degree whenever the two
chosen orders sum to more than the other ruling coefficient. Its marked
endpoint retains the prescribed map to the plane. The decrease compares
against any earlier bidegree with at least the same primary degree.
-/

public section

open AlgebraicGeometry CategoryTheory Module PointedCone QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra

namespace TauCeti.Toric.Fan.LogarithmicProjection

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "H" => LineBundleClass.mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "coords" => Pi.basisFun ℂ (Fin 3)
local notation "plane[" b "," hi "]" => Fan.projectiveSpace b hi
local notation "planeIso[" b "," hi "]" =>
  (Fan.projectivePlaneIso b hi ≪≫ Basis.polynomialProjIso coords)
local notation "mark[" U "," hU "," f "," g "]" =>
  LinearEquiv.symm (BlowupTower.picardMarking U hU f) (Additive.ofMul (pullback g H))
local notation "obj[" F "," A "]" => @Prefunctor.obj _ sarkisovQuiver _ sarkisovQuiver F A

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {X : Scheme} [X.Over S] [SmoothOfRelativeDimension 2 (X ↘ S)]
  [IsIntegral X] [IsNoetherian X] {D : X.IdealSheafData} {A B : LogarithmicProjection i D}
  {Y : Scheme} {b b' : Basis (Fin 2) ℤ N} {hi : IsIntegralLattice i}
  (r : Fin 4 ≃ A.fan.Ray)
  (hr : (fun t ↦ (r t).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])
  {n : ℕ} {T : BlowupTower A.fan.algebraicRealization (n + 2) Y}
  (hT : IsClosedPointTower A.fan.algebraicRealization T) (g : Y ⟶ P)

local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "fA" => (A.fan.algebraicRealization ↘ S)
local notation "pt" => IsLocalRing.closedPoint ℂ
local notation "center[" ρ "," c "]" =>
  Fan.Ray.binomialCenter ρ rankTwo (Basis.detDualEquiv_self b (Fan.Ray.primitiveGenerator ρ))
    (Fan.Ray.surjective_detCharacter ρ b) c pt

/-- The first centers at a corner of one invariant fiber and a smooth point of the
other give a decreasing step for the specified plane target when their orders
sum to more than the fiber coefficient of the base Picard class. The comparison
can use any reference bidegree whose first coordinate is at least three times
the fiber degree. -/
theorem exists_sarkisov_step_of_quadric_corner_and_smooth_centers
    (hD : D.IsEffectiveCartier)
    (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S))
    (hB : B.fan = plane[b',hi]) (k : X ≅ Y)
    (hAh : A.hom = k.hom ≫ T.toBase) (hBh : B.hom ≍ k.hom ≫ g ≫ (planeIso[b',hi]).inv)
    (hg : g ≫ (P ↘ S) = T.toBase ≫ fA) (hbir : Scheme.BirationalOver g (𝟙 P))
    (j l : Fin (n + 2)) (c : ℂˣ)
    (hl : hT.baseCenter l = center[r 1,c])
    (hlfirst : ∀ t < l, hT.baseCenter t ≠ hT.baseCenter l)
    (σ : A.fan.cones) (hσ : Nat.card (ToricRay σ.val) = 2) (hopp : (r 3).toCone ≤ σ)
    (hj : hT.baseCenter j = A.fan.distinguishedPointHom σ pt)
    (hjfirst : ∀ t < j, hT.baseCenter t ≠ hT.baseCenter j) (d : ℕ ×ₗ ℕ) :
    let : Nonempty A.fan.cones := A.isComplete.nonempty_cones
    let : SmoothOfRelativeDimension 2 fA := by
      rw [Fan.algebraicRealization_over, ← rankTwo]
      exact A.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap A.isRegular
    let x := mark[T,hT,fA,g]
    let C := A.fan.hirzebruchPicardBasis b 0 A.isRegular r hr
    C.repr x.1 0 < -x.2 j + -x.2 l →
    3 * (C.repr x.1 1).toNat ≤ (ofLex d).1 →
    HasPlaneTargetDecrease A B rankTwo hD hNode d := by
  intro hcones hSmoothA x C hsum hd
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
  obtain ⟨Q, path, a, t, ht, Z, U, hU, e, hQ, _, hg', hbir', _, hpos, hdegree⟩ :=
    hT.exists_sarkisov_path_of_quadric_opposite_corner_and_smooth_center b A.isRegular A.isComplete
      r hr g hg hbir j l c hl hlfirst σ hσ hopp hj hjfirst (obj[F,A])
      (precomposeSarkisovOfIso_obj_fan ..) hL
  have htarget : (obj[F,B]).hom ≍ e.hom ≫ (e.inv ≫ g) ≫ (planeIso[b',hi]).inv := by
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hR
  have hm := HasPlaneTargetMarking.hirzebruch (A := Q) (B := obj[F,B]) a b' 0 hi t ht
    ((precomposeSarkisovOfIso_obj_fan ..).trans hB) U hU e (e.inv ≫ g) hQ htarget hg' hbir'
  refine HasPlaneTargetDecrease.of_path_on_iso rankTwo hD hNode k ?_ path
    (precomposeSarkisovOfIso_obj_fan ..) (precomposeSarkisovOfIso_obj_hom ..)
    (precomposeSarkisovOfIso_obj_fan ..) (precomposeSarkisovOfIso_obj_hom ..) hm
  apply Prod.Lex.lt_iff.mpr
  left
  simp only [ofLex_hirzebruchSarkisovBidegree, Nat.cast_zero]
  apply lt_of_lt_of_le (_ : _ < 3 * (C.repr x.1 1).toNat) hd
  refine Nat.mul_lt_mul_of_pos_left ?_ (by decide)
  dsimp only [C, x] at hsum ⊢
  omega

end TauCeti.Toric.Fan.LogarithmicProjection
