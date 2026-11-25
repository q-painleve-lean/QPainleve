/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Endpoint.PicardAction

import QPainleve.Geometry.Toric.Fan.Presentation.Genus
import QPainleve.SignedClusterModularGroup.Realization.Anticanonical
import QPainleve.SignedClusterModularGroup.Realization.Endpoint.Kernel
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber
import QPainleve.SignedClusterModularGroup.Realization.Surjectivity.Torelli
import QPainleve.SignedClusterModularGroup.Realization.Surjectivity.Word

/-!
# Surjectivity of the marked signed Picard action

Choose compatible periods on root-free fibers of a fixed marked toric presentation,
then factor the change of toric projections of the resulting Torelli isomorphism.
The resulting loop realizes the specified Picard action and branch sign. For a
boundary rotation it can be chosen inversion-free.

The construction joins
`CompleteToricPresentation.exists_root_free_pair_iso_of_signed_boundary_isometry`
and `GeometricRealization.exists_word_signedPicardHom_eq_of_pair_iso`.
-/

public section

open AlgebraicGeometry CategoryTheory MulOpposite Quiver
open QPainleve.CharacterTorus QPainleve.Cluster
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

open MarkedSurface (boundaryIso)
open SignedBoundaryIsometryGroup (sign)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "χ[" c "]" => pointsEquiv ℂ _ (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "eval[" E "," w "]" => op (signedClusterModularGroupMap ℂ E (End.of w))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {E : SkewExchangeMatrix (Fin r)} {Q : CompleteToricPresentation i b r L γ}
  {M : Point Centers[r] → MarkedSurface ℂ n B XTor[r]}
  {d : ZMod n → L} {hD : ∀ c, D[M c].IsEffectiveCartier}
  {hmark : ∀ c j, (M c).boundaryClass (hD c) j = d j}

local instance instSurjectivityNonemptyCones : Nonempty Q.fan.cones := Q.complete.nonempty_cones
local instance instSurjectivityPrestableBoundary :
    PrestableFamily ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme ↘ S) :=
  Q.prestable
local instance instSurjectivityNeZeroLength : NeZero Q.length := Q.neZero

local notation "Models[" C "]" =>
  HasToricTargetModels (T₀ := Centers[r]) (T₁ := Centers[r]) (b := b) (s := Q.rays)
    (hΦ := Q.regular) (T := Q.cycle) (origin := Q.origin) (ι := Q.inclusion) (P₁ := M)
    (fun c ↦ χ[c]) C

/-- Every signed boundary isometry of a marked toric presentation of a primitive
nef square-zero anticanonical cycle occurs as the Picard action of a signed
cluster loop. An orientation-preserving action has an inversion-free representative.
The reference fiber may lie outside the initial noncollision open. -/
theorem exists_word_signedPicardHom_eq_of_presentation
    (P : ChargeSeed E N) (hform : P.form = b.detDualEquiv.toLinearMap)
    (hcharge : P.charge = Fan.rayChargeMap Q.rays)
    (models : ∀ c : Point Centers[r], c.left (default : S) ∈ Path.nil.centerOpen ℂ P →
      Q.HasNodalModel c (M c))
    {c : Point Centers[r]} (href : Q.HasNodalModel c (M c))
    (hprim : IsPrimitive (Additive.ofMul classOf(hD c)))
    (hnef : (classOf(hD c)).IsNef ℂ ((M c).surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ (M c).surface classOf(hD c) classOf(hD c) = 0)
    (ρ : (SignedClusterModularGroup ℂ E)ᵐᵒᵖ →* signedBoundaryIsometryGroup B d)
    (hρ : ∀ (w : Word E E)
      (R : GeometricRealization M M (w.centerPartialMap ℂ P) (w.xRationalMap ℂ)),
      Models[w.centerPartialMap ℂ P] → ρ eval[E,w] = R.toSignedBoundaryIsometry d hD hmark)
    (g : signedBoundaryIsometryGroup B d) :
    ∃ w : Word E E, ρ eval[E,w] = g ∧ (sign B d g = 1 → w.inversionCount = 0) := by
  have hK : P.charge.ker ≤ (Fan.rayChargeMap Q.rays).ker :=
    le_of_eq (congrArg LinearMap.ker hcharge)
  obtain ⟨c₀, c₁, -, hm₁, hword, hprim₀, hnef₀, hsq₀, -, -, e, act, hsign, -, hact, hpic⟩ :=
    Q.exists_root_free_pair_iso_of_signed_boundary_isometry P hK hD
      (fun c' ↦ funext (hmark c')) href hprim hnef hsq models g
  have hsgn :
      letI : PrestableFamily ((M c₀).boundary ↘ S) := (M c₀).prestable
      letI : PrestableFamily ((M c₁).boundary ↘ S) := (M c₁).prestable
      DihedralGroup.cycleOrientationSign ((boundaryIso e).boundaryCycleAction
        (M c₀).cycle (M c₁).cycle) = sign B d g := by
    rw [hact, hsign]
  obtain ⟨w, hw, hfree, -⟩ := exists_word_signedPicardHom_eq_of_pair_iso P hform hcharge
    models hm₁ hnef₀ hsq₀ hprim₀ (fun w ↦ (hword w).1) ρ hρ e hpic hsgn
  exact ⟨w, hw, hfree⟩

/-- The marked Picard pullback identifies the opposite signed cluster modular
group with the signed boundary isometry group. The comparison computes the
Picard pullback on every compatible loop realization, and its sign kernel on
the group of point maps is the unsigned subgroup. The component and branch
markings can have any positive cycle length. -/
theorem existsUnique_signedPicardEquiv_of_presentation
    (P : ChargeSeed E N) (hform : P.form = b.detDualEquiv.toLinearMap)
    (hcharge : P.charge = Fan.rayChargeMap Q.rays)
    (models : ∀ c : Point Centers[r], c.left (default : S) ∈ Path.nil.centerOpen ℂ P →
      Q.HasNodalModel c (M c))
    {c : Point Centers[r]} (href : Q.HasNodalModel c (M c))
    (hprim : IsPrimitive (Additive.ofMul classOf(hD c)))
    (hnef : (classOf(hD c)).IsNef ℂ ((M c).surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ (M c).surface classOf(hD c) classOf(hD c) = 0) :
    ∃! Θ : (SignedClusterModularGroup ℂ E)ᵐᵒᵖ ≃* signedBoundaryIsometryGroup B d,
      (∀ (w : Word E E),
        sign B d (Θ eval[E,w]) = (-1 : ℤˣ) ^ w.inversionCount ∧
        ∀ {C : Centers[r].left.PartialMap Centers[r].left} [IsDominant C.hom]
          [C.IsOver Centers[r].hom Centers[r].hom]
          (R : GeometricRealization M M C (w.xRationalMap ℂ)),
          Models[C] → Θ eval[E,w] = R.toSignedBoundaryIsometry d hD hmark) ∧
      ((sign B d).comp Θ.toMonoidHom).ker.unop = (clusterModularGroupInclusion ℂ E).range := by
  classical
  let : IsRationalOver ((M c).surface ↘ S) := href.isRationalOver
  have hcan := congrArg Inv.inv (href.canonicalClass (hD c))
  have hindex := Q.chargeIndex_ne_zero_of_anticanonical_cycle href (hD c) hnef hsq hcan hprim
  have hker : E.matrix.mulVecLin.ker = P.charge.ker := by
    rw [← P.matrix_eq, hform, hcharge]
    exact Fan.ker_chargeExchangeMatrix_rayChargeMap b Q.rays hindex
  obtain ⟨ρ, ⟨hρ, hsignker⟩, huniq⟩ :=
    existsUnique_signedPicardHom_of_presentation P Q hform hcharge M
      (fun x ↦ models _ (Path.nil.centerPoint_endpoints_mem_noncollision P hker x).2)
      href hD hnef hsq hcan hprim d hmark
  -- Read the nodal contractions used by the comparison directly from the family models.
  have hcontract (c' : Point Centers[r]) (hc' : c'.left (default : S) ∈ Path.nil.centerOpen ℂ P) :
      ∃ p : ContractedToricFiber b Q.rays Q.regular Q.cycle Q.origin Q.inclusion χ[c'] (M c'),
        p.IsNodalContraction := by
    have hm := models c' hc'
    let : (M c').surface.IsProjectiveOver ℂ := (M c').projective
    let : SmoothOfRelativeDimension 2 ((M c').surface ↘ S) := (M c').smooth
    let : IsIntegral (M c').surface := (M c').integral
    let : PrestableFamily (D[M c'].subscheme ↘ S) := (M c').prestable_boundaryImage
    obtain ⟨p, Y, l, W, e, hW, he⟩ := (Q.hasNodalModel_iff c' (M c')).mp hm
    refine ⟨p, hD c', ?_, l, Y, W, hW, e, he.symm⟩
    exact hm.hasToricPresentation.genus_blowupComponent_eq_zero (hD c')
  choose p hp using hcontract
  have hinj := ρ.ker_eq_bot_iff.mp
    (signedPicardHom_ker_eq_bot_of_presentation Q P hform hcharge M p hp hD
      href hnef hsq hcan hprim d hmark ρ (fun w _ _ _ ↦ (hρ w).2))
  have hsurj : Function.Surjective ρ := by
    intro g
    obtain ⟨w, hw, -⟩ := exists_word_signedPicardHom_eq_of_presentation
      P hform hcharge models href hprim hnef hsq ρ (fun w ↦ (hρ (End.of w)).2) g
    exact ⟨eval[E,w], hw⟩
  let Θ := MulEquiv.ofBijective ρ ⟨hinj, hsurj⟩
  refine ⟨Θ, ⟨fun w ↦ hρ (End.of w), hsignker⟩, fun Θ' hΘ' ↦ ?_⟩
  exact MulEquiv.toMonoidHom_injective (huniq Θ'.toMonoidHom
    ⟨fun w ↦ hΘ'.1 (End.asHom w), hΘ'.2⟩)

end QPainleve.SignedClusterModularGroup.GeometricRealization
