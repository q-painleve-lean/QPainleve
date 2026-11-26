/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.PicardAction
public import QPainleve.SignedClusterModularGroup.Realization.Presentation

/-!
# Picard group identifications on marked nodal models

A marked family of nodal models identifies the opposite signed cluster modular group
with the signed boundary isometries of its common Picard lattice. The identification
computes the marked pullback and the sign on loop representatives. Its restriction via
`GeometricRealization.picardRotationEquiv` identifies the unsigned group with the rotations.
-/

public section

open AlgebraicGeometry CategoryTheory MulOpposite
open QPainleve.CharacterTorus QPainleve.Cluster QPainleve.SignedBoundaryIsometryGroup
open Scheme TauCeti TauCeti.AlgebraicGeometry

namespace QPainleve.SignedClusterModularGroup.CompleteToricPresentation

open GeometricRealization

local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "χ[" c "]" => pointsEquiv ℂ _ (Subtype.mk (Over.Hom.left c) (Over.w c))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}

/-- The Picard group identification of a complete toric presentation with fixed numbered
boundary classes. The geometry is over ℂ, and `k` is the coefficient field for the
independent X maps of the seed `E`. -/
@[ext]
structure NodalPicardGroupIdentification (Q : CompleteToricPresentation i b r L γ)
    (k : Type*) [Field k] (E : SkewExchangeMatrix (Fin r)) (d : ZMod n → L) where
  /-- The marked surface at each choice of ordered centers. -/
  family : Point Centers[r] → MarkedSurface ℂ n B XTor[r]
  /-- Every fiber has a nodal model in the given presentation. -/
  hasNodalModel (z : Point Centers[r]) : Q.HasNodalModel z (family z)
  /-- The numbered boundary classes are constant in the moving marking. -/
  boundaryClass_eq (z : Point Centers[r]) (j : ZMod n) :
    (family z).boundaryClass (family z).isEffectiveCartier_boundaryIdeal j = d j
  /-- Picard pullback identifies opposite signed X maps with signed boundary isometries. -/
  signedEquiv : (SignedClusterModularGroup k E)ᵐᵒᵖ ≃* signedBoundaryIsometryGroup B d
  /-- The Picard sign of a loop is its inversion parity. -/
  sign_signedEquiv_apply_word (w : Word E E) :
    (signedEquiv (op (signedClusterModularGroupMap k E (End.of w)))).val.2 =
      (-1 : ℤˣ) ^ w.inversionCount
  /-- The signed action on a loop gives the marked pullback and ordered branch sign
  of every compatible geometric realization over ℂ. -/
  signedEquiv_apply_word (w : Word E E) :
    letI := Q.complete.nonempty_cones
    letI := Q.prestable
    letI := Q.neZero
    ∀ {C : Centers[r].left.PartialMap Centers[r].left} [IsDominant C.hom]
      [C.IsOver Centers[r].hom Centers[r].hom]
      (R : GeometricRealization family family C (w.xRationalMap ℂ)),
      HasToricTargetModels (T₀ := Centers[r]) (T₁ := Centers[r]) (b := b) (s := Q.rays)
        (hΦ := Q.regular) (T := Q.cycle) (origin := Q.origin) (ι := Q.inclusion) (P₁ := family)
        (fun z : Point Centers[r] ↦ χ[z]) C →
      signedEquiv (op (signedClusterModularGroupMap k E (End.of w))) =
        R.toSignedBoundaryIsometry d (fun z ↦ (family z).isEffectiveCartier_boundaryIdeal)
          boundaryClass_eq
  /-- The sign kernel on point maps is the image of the unsigned group. -/
  sign_ker_unop : ((sign B d).comp signedEquiv.toMonoidHom).ker.unop =
    (clusterModularGroupInclusion k E).range

namespace NodalPicardGroupIdentification

attribute [simp] boundaryClass_eq sign_signedEquiv_apply_word

variable {Q : CompleteToricPresentation i b r L γ} {k : Type*} [Field k]
  {E : SkewExchangeMatrix (Fin r)} {d : ZMod n → L}
  (P : NodalPicardGroupIdentification (B := B) Q k E d)

/-- The unsigned Picard equivalence is the restriction to boundary rotations. -/
noncomputable def unsignedEquiv :
    (ClusterModularGroup k E)ᵐᵒᵖ ≃* boundaryRotationGroup B d :=
  picardRotationEquiv P.signedEquiv P.sign_ker_unop

/-- The unsigned Picard equivalence agrees with the signed equivalence under inclusion. -/
@[simp]
theorem rotationInclusion_unsignedEquiv_apply (x : (ClusterModularGroup k E)ᵐᵒᵖ) :
    rotationInclusion B d (P.unsignedEquiv x) =
      P.signedEquiv (MonoidHom.op (clusterModularGroupInclusion k E) x) :=
  rotationInclusion_picardRotationEquiv_apply P.signedEquiv P.sign_ker_unop x

end NodalPicardGroupIdentification

end QPainleve.SignedClusterModularGroup.CompleteToricPresentation
