/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Surjectivity.Basic
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Induction.MarkedFactorization

import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.Geometry.Toric.Fan.Logarithmic.Word.Factorization
import QPainleve.SignedClusterModularGroup.Realization.PairIso

/-!
# Cluster loops of specified pair isomorphisms

For two fibers of a fixed ordered toric presentation, the change of toric
projections induced by a specified pair isomorphism is the input to
[Lutz's factorization theorem][HKL]. Given the high-fiber decrease in the
marked Sarkisov induction, the resulting word realizes the fixed-center
evaluation of the isomorphism on the original source surface and represents
its signed Picard action.

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=68
-/

public section

open AlgebraicGeometry CategoryTheory Module MulOpposite
open QPainleve.CharacterTorus QPainleve.Cluster
open Scheme Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Fan Fan.LogarithmicProjection

namespace QPainleve.SignedClusterModularGroup

open GeometricRealization (Point)
open MarkedSurface (surfaceIso boundaryIso)
open SignedBoundaryIsometryGroup (sign toIsometry)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "χ[" c "]" => pointsEquiv ℂ _
  (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "Cw[" w "," P "]" => Quiver.Path.centerPartialMap ℂ w P
local notation "dst[" C "," x "]" =>
  x ≫ PartialMap.domainTarget (X := Centers[_]) (Y := Centers[_]) C
local notation "eval[" E "," w "]" => op (signedClusterModularGroupMap ℂ E (End.of w))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {E : SkewExchangeMatrix (Fin r)}

namespace CompleteToricPresentation

/-- A specified pair isomorphism between two nodal fibers gives a cluster loop
intertwining their fixed-center evaluations, given a decrease in the high-fiber
case of the Sarkisov induction. The target evaluation is pulled back along the
specified isomorphism, with the composition defined on the source fiber. -/
theorem exists_word_of_pair_iso_of_high_fiber_steps
    (Q : CompleteToricPresentation i b r L γ)
    (highFiberStep : ∀ {Y : Scheme} [Y.Over S] [SmoothOfRelativeDimension 2 (Y ↘ S)]
      [IsIntegral Y] [IsNoetherian Y] {F : Y.IdealSheafData}
      {A A' : LogarithmicProjection i F} {d : ℕ ×ₗ ℕ}
      (hF : F.IsEffectiveCartier)
      (hNode : AtWorstNodalOfRelativeDimensionOne (F.subschemeι ≫ Y ↘ S)),
      HasHighFiberPlaneTargetMarking A A' d →
        HasPlaneTargetDecrease A A' ((finrank_eq_card_basis b).trans (Fintype.card_fin 2))
          hF hNode d)
    {c₀ c₁ : Point Centers[r]} {M P : MarkedSurface ℂ n B XTor[r]}
    (hM : Q.HasNodalModel c₀ M) (hP : Q.HasNodalModel c₁ P)
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (e : M.pair ≅ P.pair) (hD : D[M].IsEffectiveCartier) (hD' : D[P].IsEffectiveCartier) :
    letI : IsIntegral M.surface := M.integral
    ∃ w : Word E E, ∃ h, M.evaluation.compOfDefined (w.xRationalMap ℂ) h =
      (surfaceIso e).hom.toRationalMap.comp P.evaluation := by
  let : IsIntegral M.surface := M.integral
  let : IsIntegral P.surface := P.integral
  let : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
  let : M.surface.IsProjectiveOver ℂ := M.projective
  let : M.surface.IsSeparated := Scheme.IsSeparated.of_isSeparated (M.surface ↘ S)
  let : IsNoetherian M.surface := isNoetherian_of_finiteType (M.surface ↘ S)
  obtain ⟨_, W, T, hT, π, s, hSm, hmod, hπ, hs, A, A', U, U', hR, _, _, hAmod, hA'mod,
    hU, hU', heval, heval'⟩ := Q.exists_common_ordered_models_of_pair_iso hM hP e hD hD'
  subst π s
  let : W.Over S := ⟨T.toBase ≫ M.surface ↘ S⟩
  let : IsIntegral W := hT.isClosedPointTower.isIntegral (M.surface ↘ S)
  let : SmoothOfRelativeDimension 2 (W ↘ S) := hSm
  let : W.IsProjectiveOver ℂ := T.isProjectiveOver ℂ
  let : IsNoetherian W := isNoetherian_of_finiteType (W ↘ S)
  let : IsModification T.toBase := hmod
  let : IsModification A.hom := hAmod
  let : IsModification A'.hom := hA'mod
  have hNode : AtWorstNodalOfRelativeDimensionOne
      ((D[M].comap T.toBase).radical.subschemeι ≫ W ↘ S) :=
    (hT.radical_comap_toBase hD M.boundaryIdeal_nodal).2
  have hfactor :=
    sarkisov_factorization_of_high_fiber_steps b A.fan.lattice highFiberStep A A' hR hNode
  obtain ⟨w, _, hw⟩ := exists_word_of_resolved_sarkisov_factorization hfactor U U' hR
  -- Dominance of the common projection detects both generic definedness and equality downstairs.
  rw [heval, heval'] at hw
  simp only [← Hom.toRationalMap_compHom, ← RationalMap.comp_toRationalMap,
    RationalMap.comp_assoc] at hw
  have h₀ : U.exchangeMatrix = E := SkewExchangeMatrix.ext (hU.trans hE.symm)
  have h₁ : U'.exchangeMatrix = E := SkewExchangeMatrix.ext (hU'.trans hE.symm)
  generalize U.exchangeMatrix = E₀ at w h₀ hw
  generalize U'.exchangeMatrix = E₁ at w h₁ hw
  subst E₀ E₁
  exact ⟨w, (T.toBase.toRationalMap.compOfDefined_eq_iff_of_dominant _ _ _).mp hw⟩

end CompleteToricPresentation

namespace GeometricRealization

variable {Q : CompleteToricPresentation i b r L γ}
  {M : Point Centers[r] → MarkedSurface ℂ n B XTor[r]}
  {d : ZMod n → L} {hD : ∀ c, D[M c].IsEffectiveCartier}
  {hmark : ∀ c j, (M c).boundaryClass (hD c) j = d j}

local notation "Models[" C "]" =>
  HasToricTargetModels (T₀ := Centers[r]) (T₁ := Centers[r]) (b := b) (s := Q.rays)
    (hΦ := Q.regular) (T := Q.cycle) (origin := Q.origin) (ι := Q.inclusion) (P₁ := M)
    (fun c : Point Centers[r] ↦ χ[c]) C

/-- A specified pair isomorphism between two marked fibers realizes its signed
Picard action by a loop once the high-fiber decrease is supplied. The source
center belongs to every loop domain, so it can be chosen before the factorization.
The loop gives the isomorphism's evaluation on the original source surface and
can be taken inversion-free for a positive action. -/
theorem exists_word_signedPicardHom_eq_of_pair_iso_of_high_fiber_steps
    (highFiberStep : ∀ {Y : Scheme} [Y.Over S] [SmoothOfRelativeDimension 2 (Y ↘ S)]
      [IsIntegral Y] [IsNoetherian Y] {F : Y.IdealSheafData}
      {A A' : LogarithmicProjection i F} {d : ℕ ×ₗ ℕ}
      (hF : F.IsEffectiveCartier)
      (hNode : AtWorstNodalOfRelativeDimensionOne (F.subschemeι ≫ Y ↘ S)),
      HasHighFiberPlaneTargetMarking A A' d →
        HasPlaneTargetDecrease A A' ((finrank_eq_card_basis b).trans (Fintype.card_fin 2))
          hF hNode d)
    (P : ChargeSeed E N) (hform : P.form = b.detDualEquiv.toLinearMap)
    (hcharge : P.charge = Fan.rayChargeMap Q.rays)
    (models : ∀ c : Point Centers[r], c.left (default : S) ∈ Quiver.Path.nil.centerOpen ℂ P →
      Q.HasNodalModel c (M c))
    {c₀ c₁ : Point Centers[r]}
    (hP : Q.HasNodalModel c₁ (M c₁)) [IsRationalOver ((M c₀).surface ↘ S)]
    (hnef : (classOf(hD c₀)).IsNef ℂ ((M c₀).surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ (M c₀).surface classOf(hD c₀) classOf(hD c₀) = 0)
    (hcan : letI : SmoothOfRelativeDimension 2 ((M c₀).surface ↘ S) := (M c₀).smooth
      classOf(hD c₀) = (LineBundleClass.mk (canonicalBundle ℂ (M c₀).surface 2))⁻¹)
    (hprim : IsPrimitive (Additive.ofMul classOf(hD c₀)))
    (hgeneric : ∀ w : Word E E, c₀.left (default : S) ∈ w.centerOpen ℂ P)
    (ρ : (SignedClusterModularGroup ℂ E)ᵐᵒᵖ →* signedBoundaryIsometryGroup B d)
    (hρ : letI := Q.complete.nonempty_cones
      letI := Q.neZero
      letI := Q.prestable
      ∀ (w : Word E E) (R : GeometricRealization M M Cw[w,P] (w.xRationalMap ℂ)),
        Models[Cw[w,P]] → ρ eval[E,w] = R.toSignedBoundaryIsometry d hD hmark)
    (g : signedBoundaryIsometryGroup B d) (e : (M c₀).pair ≅ (M c₁).pair)
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
  let := Q.complete.nonempty_cones
  let := Q.neZero
  let := Q.prestable
  have hE := P.matrix_eq.symm.trans (congrArg₂ chargeExchangeMatrix hform hcharge)
  have hM := models c₀ (hgeneric Quiver.Path.nil)
  have hindex := Q.chargeIndex_ne_zero_of_anticanonical_cycle hM (hD c₀) hnef hsq hcan hprim
  have hker : E.matrix.mulVecLin.ker = P.charge.ker := by
    rw [hE, hcharge]
    exact Fan.ker_chargeExchangeMatrix_rayChargeMap b Q.rays hindex
  obtain ⟨w, hw⟩ := Q.exists_word_of_pair_iso_of_high_fiber_steps highFiberStep hM hP hE e
    (hD c₀) (hD c₁)
  obtain ⟨R, hη, _, htarget⟩ := exists_realize_signed_loop w P Q hform hcharge M
    (fun x ↦ models _ (Quiver.Path.nil.centerPoint_endpoints_mem_noncollision P hker x).2)
    hM hD hnef hsq hcan hprim d hmark
  have htargets : Models[Cw[w,P]] := fun x ↦ by
    obtain ⟨q, _⟩ := (Q.hasNodalModel_iff _ _).mp (htarget x)
    exact ⟨q⟩
  obtain ⟨q, _⟩ := (Q.hasNodalModel_iff c₁ (M c₁)).mp hP
  have hvalue := hρ w R htargets
  have hparity : sign B d (ρ eval[E,w]) = (-1 : ℤˣ) ^ w.inversionCount := by
    rw [hvalue, SignedBoundaryIsometryGroup.sign_apply, coe_toSignedBoundaryIsometry, hη]
  obtain ⟨v, hvw, hv, hfree⟩ := exists_word_signedPicardHom_eq_of_pair_iso_on_resolution
    P R hvalue hparity (hgeneric w) htargets q (Q.inclusion_injective hM)
    hindex e (RationalMap.id (M c₀).surface)
    (by simpa only [RationalMap.id_comp] using hw) hpic hsgn
  refine ⟨v, hv, hfree, ?_⟩
  rw [(Quiver.Path.xRationalMap_eq_iff ℂ v w).mpr hvw]
  exact hw

end GeometricRealization

end QPainleve.SignedClusterModularGroup
