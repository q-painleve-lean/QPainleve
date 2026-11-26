/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Surjectivity

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
and `GeometricRealization.nonempty_picardLoopRealization_of_pair_iso`.
-/

public section

open AlgebraicGeometry CategoryTheory MulOpposite Quiver
open QPainleve.CharacterTorus QPainleve.Cluster
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

open MarkedSurface (boundaryIso surfaceIso)
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
cluster loop. The witness records the two centers, the pair isomorphism with the
prescribed signed action, and its X-evaluation equation. The source center lies in
the loop's noncollision open, and an orientation-preserving action has an
inversion-free representative.
The reference fiber may lie outside the initial noncollision open. -/
theorem nonempty_presentationPicardLoopRealization
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
    Nonempty (PresentationPicardLoopRealization M P ρ g) := by
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
  let signedIso : SignedPicardPairIso (M c₀) (M c₁) g := ⟨e, hsgn, hpic⟩
  obtain ⟨R⟩ := nonempty_picardLoopRealization_of_pair_iso P hform hcharge
    models hm₁ hnef₀ hsq₀ hprim₀ (fun w ↦ (hword w).1) ρ hρ signedIso
  exact ⟨⟨c₀, c₁, signedIso, R, (hword R.word).1⟩⟩

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
      IsSignedPicardAction Q M hD hmark Θ.toMonoidHom := by
  obtain ⟨ρ, ⟨hρ, hker⟩, huniq⟩ := existsUnique_faithful_signedPicardHom_of_presentation
    Q P hform hcharge M models href hD hnef hsq hprim d hmark
  have hinj := ρ.ker_eq_bot_iff.mp hker
  have hsurj : Function.Surjective ρ := by
    intro g
    obtain ⟨R⟩ := nonempty_presentationPicardLoopRealization
      P hform hcharge models href hprim hnef hsq ρ
      (fun w R hR ↦ hρ.apply_of_realization w R hR) g
    exact ⟨eval[E,R.loop.word], R.loop.picard_eq⟩
  let Θ := MulEquiv.ofBijective ρ ⟨hinj, hsurj⟩
  refine ⟨Θ, hρ, fun Θ' hΘ' ↦ ?_⟩
  exact MulEquiv.toMonoidHom_injective
    (huniq Θ'.toMonoidHom ⟨hΘ', Θ'.toMonoidHom.ker_eq_bot_iff.mpr Θ'.injective⟩)

end QPainleve.SignedClusterModularGroup.GeometricRealization
