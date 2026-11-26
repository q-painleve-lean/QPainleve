/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Conjugation.Basic

/-!
# Picard base change along a connecting word

A `PicardBaseChange` gives a realization of a specified connecting word with its branch sign
and the signed change-of-marking square. The same realization gives the unsigned square for
any rotation equivalences compatible with the inclusions into the signed groups.
-/

public section

open AlgebraicGeometry CategoryTheory
open QPainleve.CharacterTorus QPainleve.Cluster TauCeti.AlgebraicGeometry
open Scheme

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "SignedMaps[" E "]" => (SignedClusterModularGroup ℂ E)ᵐᵒᵖ
local notation "UnsignedMaps[" E "]" => (ClusterModularGroup ℂ E)ᵐᵒᵖ
local notation "incl[" E "]" => MonoidHom.op (clusterModularGroupInclusion ℂ E)

variable {r n : ℕ} [NeZero n] {E₀ E₁ : SkewExchangeMatrix (Fin r)} {w : Word E₀ E₁}
  {L₀ L₁ : Type} [AddCommGroup L₀] [AddCommGroup L₁]
  {B₀ : LinearMap.BilinForm ℤ L₀} {B₁ : LinearMap.BilinForm ℤ L₁}
  {T₀ T₁ : Over S} [Nonempty T₀.left] [Smooth T₀.hom]
  {M₀ : Point T₀ → MarkedSurface ℂ n B₀ XTor[r]}
  {M₁ : Point T₁ → MarkedSurface ℂ n B₁ XTor[r]}
  {d₀ : ZMod n → L₀} {d₁ : ZMod n → L₁}
  {hD₀ : ∀ c, (M₀ c).pair.hom.left.ker.IsEffectiveCartier}
  {hD₁ : ∀ c, (M₁ c).pair.hom.left.ker.IsEffectiveCartier}

/-- A realization of a connecting word that intertwines the two signed Picard equivalences
and whose ordered branch sign is the inversion parity of the word. -/
@[ext]
structure PicardBaseChange (w : Word E₀ E₁)
    (C : T₀.left.PartialMap T₁.left) [IsDominant C.hom] [C.IsOver T₀.hom T₁.hom]
    (hmark₀ : ∀ c j, (M₀ c).boundaryClass (hD₀ c) j = d₀ j)
    (hmark₁ : ∀ c j, (M₁ c).boundaryClass (hD₁ c) j = d₁ j)
    (Θ₀ : SignedMaps[E₀] ≃* signedBoundaryIsometryGroup B₀ d₀)
    (Θ₁ : SignedMaps[E₁] ≃* signedBoundaryIsometryGroup B₁ d₁) where
  /-- The connecting realization on the marked families. -/
  realization : GeometricRealization M₀ M₁ C (w.xRationalMap ℂ)
  /-- The sign on the ordered branches agrees with the inversion sign of the word. -/
  orientation_eq : realization.orientation = (-1 : ℤˣ) ^ w.inversionCount
  /-- Conjugation by the word corresponds to conjugation by its marked Picard pullback. -/
  signed_trans_eq : (MulEquiv.op (signedClusterModularGroupCongr ℂ w)).trans Θ₁ =
    Θ₀.trans (realization.signedBoundaryIsometryGroupCongr hmark₀ hmark₁)

attribute [simp] PicardBaseChange.orientation_eq

namespace PicardBaseChange

variable {C : T₀.left.PartialMap T₁.left} [IsDominant C.hom] [C.IsOver T₀.hom T₁.hom]
  {hmark₀ : ∀ c j, (M₀ c).boundaryClass (hD₀ c) j = d₀ j}
  {hmark₁ : ∀ c j, (M₁ c).boundaryClass (hD₁ c) j = d₁ j}
  {Θ₀ : SignedMaps[E₀] ≃* signedBoundaryIsometryGroup B₀ d₀}
  {Θ₁ : SignedMaps[E₁] ≃* signedBoundaryIsometryGroup B₁ d₁}
  (R : PicardBaseChange w C hmark₀ hmark₁ Θ₀ Θ₁)

/-- The signed change-of-marking square evaluated on a point-map group element. -/
theorem signed_apply (g : SignedMaps[E₀]) :
    Θ₁ (MulEquiv.op (signedClusterModularGroupCongr ℂ w) g) =
      R.realization.signedBoundaryIsometryGroupCongr hmark₀ hmark₁ (Θ₀ g) := by
  simpa only [MulEquiv.trans_apply] using DFunLike.congr_fun R.signed_trans_eq g

/-- The unsigned change-of-marking square for Picard equivalences that agree with the
signed ones on the included subgroups. -/
theorem unsigned_trans_eq
    (φ₀ : UnsignedMaps[E₀] ≃* boundaryRotationGroup B₀ d₀)
    (φ₁ : UnsignedMaps[E₁] ≃* boundaryRotationGroup B₁ d₁)
    (hφ₀ : ∀ x, SignedBoundaryIsometryGroup.rotationInclusion B₀ d₀ (φ₀ x) = Θ₀ (incl[E₀] x))
    (hφ₁ : ∀ x, SignedBoundaryIsometryGroup.rotationInclusion B₁ d₁ (φ₁ x) = Θ₁ (incl[E₁] x)) :
    (MulEquiv.op (clusterModularGroupCongr ℂ w)).trans φ₁ =
      φ₀.trans (R.realization.boundaryRotationGroupCongr hmark₀ hmark₁) := by
  apply MulEquiv.ext
  intro x
  apply SignedBoundaryIsometryGroup.rotationInclusion_injective B₁ d₁
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hφ₁,
    ← R.realization.signedBoundaryIsometryGroupCongr_rotationInclusion, hφ₀]
  simpa only [MonoidHom.op_apply_apply, MulEquiv.op_apply_apply, Function.comp_apply,
    MulOpposite.unop_op, signedClusterModularGroupCongr_inclusion] using R.signed_apply (incl[E₀] x)

end PicardBaseChange

end QPainleve.SignedClusterModularGroup.GeometricRealization
