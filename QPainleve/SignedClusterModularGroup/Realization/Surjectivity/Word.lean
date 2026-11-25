/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Surjectivity

import QPainleve.SignedClusterModularGroup.Realization.PairIso.ConnectingWord

/-!
# Cluster loops realizing specified isomorphisms of marked fibers

The common ordered models of a pair isomorphism are the endpoints of the resolved
factorization. Reading the factorization in the original seed produces a loop with the
specified Picard pullback and branch sign, and the evaluation square descends to the
source fiber.

The fixed-center comparison is
`CompleteToricPresentation.exists_connecting_word_of_pair_iso`.
-/

public section

open AlgebraicGeometry CategoryTheory MulOpposite Scheme
open QPainleve.CharacterTorus QPainleve.Cluster
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Fan Fan.LogarithmicProjection

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

open MarkedSurface (surfaceIso boundaryIso)
open SignedBoundaryIsometryGroup (sign toIsometry)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "classOf(" h ")" =>
  (LineBundleClass.mk (Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "χ[" c "]" => pointsEquiv ℂ _
  (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "eval[" E "," w "]" => op (signedClusterModularGroupMap ℂ E (End.of w))
local notation "Cw[" w "," P "]" => Quiver.Path.centerPartialMap ℂ w P

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {E : SkewExchangeMatrix (Fin r)} {Q : CompleteToricPresentation i b r L γ}
  {M : Point Centers[r] → MarkedSurface ℂ n B XTor[r]}
  {d : ZMod n → L} {hD : ∀ c, D[M c].IsEffectiveCartier}
  {hmark : ∀ c j, (M c).boundaryClass (hD c) j = d j}

local instance instNonemptyCones : Nonempty Q.fan.cones := Q.complete.nonempty_cones
local instance instPrestableBoundary :
    PrestableFamily ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme ↘ S) :=
  Q.prestable
local instance instNeZeroBoundaryLength : NeZero Q.length := Q.neZero

local notation "Models[" C "]" =>
  HasToricTargetModels (T₀ := Centers[r]) (T₁ := Centers[r]) (b := b) (s := Q.rays)
    (hΦ := Q.regular) (T := Q.cycle) (origin := Q.origin) (ι := Q.inclusion) (P₁ := M)
    (fun c ↦ χ[c]) C

/-- A specified isomorphism of two fibers of a marked toric presentation gives a
loop with the same Picard pullback, branch sign, and fixed-center X evaluation.
If the specified action preserves orientation, the loop uses no inversions. -/
theorem exists_word_signedPicardHom_eq_of_pair_iso
    (P : ChargeSeed E N) (hform : P.form = b.detDualEquiv.toLinearMap)
    (hcharge : P.charge = Fan.rayChargeMap Q.rays)
    (models : ∀ c : Point Centers[r], c.left (default : S) ∈ Quiver.Path.nil.centerOpen ℂ P →
      Q.HasNodalModel c (M c))
    {c₀ c₁ : Point Centers[r]} (hP : Q.HasNodalModel c₁ (M c₁))
    (hnef : (classOf(hD c₀)).IsNef ℂ ((M c₀).surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ (M c₀).surface classOf(hD c₀) classOf(hD c₀) = 0)
    (hprim : IsPrimitive (Additive.ofMul classOf(hD c₀)))
    (hgeneric : ∀ w : Word E E, c₀.left (default : S) ∈ w.centerOpen ℂ P)
    (ρ : (SignedClusterModularGroup ℂ E)ᵐᵒᵖ →* signedBoundaryIsometryGroup B d)
    (hρ : ∀ (w : Word E E) (R : GeometricRealization M M Cw[w,P] (w.xRationalMap ℂ)),
      Models[Cw[w,P]] → ρ eval[E,w] = R.toSignedBoundaryIsometry d hD hmark)
    (e : (M c₀).pair ≅ (M c₁).pair) {g : signedBoundaryIsometryGroup B d}
    (hpic : ∀ a, (M c₀).picardMarking ((toIsometry B d g).val a) =
      Additive.ofMul (LineBundleClass.pullback (surfaceIso e).hom ((M c₁).picardMarking a).toMul))
    (hsgn : letI : PrestableFamily ((M c₀).boundary ↘ S) := (M c₀).prestable
      letI : PrestableFamily ((M c₁).boundary ↘ S) := (M c₁).prestable
      DihedralGroup.cycleOrientationSign ((boundaryIso e).boundaryCycleAction
        (M c₀).cycle (M c₁).cycle) = sign B d g) :
    letI : IsIntegral (M c₀).surface := (M c₀).integral
    ∃ w : Word E E, ρ eval[E,w] = g ∧ (sign B d g = 1 → w.inversionCount = 0) ∧
      ∃ h, (M c₀).evaluation.compOfDefined (w.xRationalMap ℂ) h =
        (surfaceIso e).hom.toRationalMap.comp (M c₁).evaluation := by
  let : IsIntegral (M c₀).surface := (M c₀).integral
  have hM := models c₀ (hgeneric Quiver.Path.nil)
  have hword := Q.exists_connecting_word_of_pair_iso Q hM hP e (hD c₀) (hD c₁)
  have hmatrix : Fan.rayExchangeMatrix b Q.rays = E :=
    SkewExchangeMatrix.ext (by simpa only [Fan.rayExchangeMatrix_matrix, ← hform, ← hcharge]
      using P.matrix_eq)
  rw [hmatrix] at hword
  obtain ⟨w, hw⟩ := hword
  exact exists_word_signedPicardHom_eq_of_comp_evaluation_eq
    P hform hcharge models hP hnef hsq hprim ρ hρ e w (hgeneric w) hw hpic hsgn

end QPainleve.SignedClusterModularGroup.GeometricRealization
