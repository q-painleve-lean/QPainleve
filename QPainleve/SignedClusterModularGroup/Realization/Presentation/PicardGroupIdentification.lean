/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.LinearAlgebra.BilinearForm.Conjugation
public import QPainleve.SignedClusterModularGroup.Realization.Presentation.NodalPicardGroupIdentification
public import QPainleve.SignedClusterModularGroup.Realization.Presentation.Reference.Finite
public import QPainleve.SignedClusterModularGroup.Realization.Surface.PrimeClass

import QPainleve.SignedClusterModularGroup.Boundary.Conjugation

/-!
# Picard group identifications of numbered anticanonical pairs

A nodal Picard group identification and a marking on the numbered reference
fiber determine the group equivalences on the original Picard lattice. The
signed equivalence transports the marked action by boundary conjugation. Its
sign kernel gives the unsigned equivalence by restriction.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module MulOpposite Quiver
open QPainleve.CharacterTorus QPainleve.Cluster QPainleve.SignedBoundaryIsometryGroup
open Scheme Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric

namespace QPainleve.SignedClusterModularGroup

open GeometricRealization

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "χ[" c "]" => pointsEquiv ℂ _ (Subtype.mk (Over.Hom.left c) (Over.w c))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {X : Scheme} [X.Over S] [X.IsProjectiveOver ℂ] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ S)]
  {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ S)] {n : ℕ} [NeZero n]

local instance instNoetherianPicardIdentification : IsNoetherian X :=
  isNoetherian_of_finiteType (X ↘ S)

local instance instFactorialPicardIdentification (x : X) :
    UniqueFactorizationMonoid (X.presheaf.stalk x) :=
  (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two x

local notation "B" => Chow.intersectionBilinForm ℂ X
local notation "classes[" A "," hD "]" =>
  (fun j ↦ Additive.ofMul (LineBundleClass.primeDivisorClass
    (D.boundaryPrimeEmbedding (Scheme.NodalCycleNumbering.boundaryPrimeEquiv A hD j))))

/-- The Picard group equivalences of a toric seed with `r` ordered centers for a
numbered anticanonical pair. The reference fiber uses the original surface and
boundary numbering. The nodal identification computes the group action in the
moving marking. -/
@[ext]
structure PicardGroupIdentification {i : N →+ V} {r : ℕ}
    {A : Scheme.NodalCycleNumbering (X := D.subscheme)
      (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n}
    (R : FiniteMarkedReferenceFiber i r A) (hD : D.IsEffectiveCartier) where
  /-- The Picard identification of the family with the numbered classes in the moving marking. -/
  nodal : CompleteToricPresentation.NodalPicardGroupIdentification R.reference.presentation ℂ
    R.reference.exchangeMatrix (R.marking.symm ∘ classes[A,hD])
  /-- The reference fiber is the original pair with its marking and X evaluation. -/
  family_center : nodal.family R.reference.center = R.reference.markedSurface

namespace PicardGroupIdentification

attribute [simp] family_center

variable {i : N →+ V} {r : ℕ}
  {A : Scheme.NodalCycleNumbering (X := D.subscheme)
    (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n} {hD : D.IsEffectiveCartier}
  {R₀ : FiniteMarkedReferenceFiber i r A} (P : PicardGroupIdentification R₀ hD)

local notation "E" => R₀.reference.exchangeMatrix
local notation "Q" => R₀.reference.presentation
local notation "Γs" => (SignedClusterModularGroup ℂ E)ᵐᵒᵖ
local notation "Γ" => (ClusterModularGroup ℂ E)ᵐᵒᵖ
local notation "d" => classes[A,hD]

/-- Opposite signed cluster maps act on the original Picard group by the marked Picard
action conjugated along the reference marking, with their branch sign. -/
def signedEquiv : Γs ≃* signedBoundaryIsometryGroup B d :=
  P.nodal.signedEquiv.trans (SignedBoundaryIsometryGroup.congr R₀.marking.symm
    (ε := 1) (a := 0) fun j ↦ by simp)

/-- The signed Picard image on the original surface is the conjugate of the marked image. -/
@[simp]
theorem coe_signedEquiv_apply (x : Γs) :
    (P.signedEquiv x).val =
      (R₀.marking.isometryGroupCongr (P.nodal.signedEquiv x).val.1,
        (P.nodal.signedEquiv x).val.2) := by
  simp only [signedEquiv, MulEquiv.trans_apply, coe_congr,
    LinearMap.BilinForm.IsometryEquiv.symm_symm]

/-- The signed equivalence evaluates by geometric pullback and the ordered branch sign
for every compatible realization of a loop. -/
theorem signedEquiv_apply_word (w : Word E E) :
    letI := (Q).complete.nonempty_cones
    letI := (Q).prestable
    letI := (Q).neZero
    ∀ {C : Centers[r].left.PartialMap Centers[r].left} [IsDominant C.hom]
      [C.IsOver Centers[r].hom Centers[r].hom]
      (R : GeometricRealization P.nodal.family P.nodal.family C (w.xRationalMap ℂ)),
      HasToricTargetModels (T₀ := Centers[r]) (T₁ := Centers[r]) (b := R₀.basis)
        (s := (Q).rays) (hΦ := (Q).regular) (T := (Q).cycle)
        (origin := (Q).origin) (ι := (Q).inclusion) (P₁ := P.nodal.family)
        (fun z : Point Centers[r] ↦ χ[z]) C →
      (P.signedEquiv (op (signedClusterModularGroupMap ℂ E (End.of w)))).val =
        (R₀.marking.isometryGroupCongr (R₀.form.isometryGroupEquivIsometryEquiv.symm R.picard),
          R.orientation) := by
  intro C _ _ R hR
  simp only [coe_signedEquiv_apply, P.nodal.signedEquiv_apply_word w R hR,
    coe_toSignedBoundaryIsometry]

/-- The sign kernel on point maps is the image of the unsigned group. -/
theorem sign_ker_unop :
    ((sign B d).comp P.signedEquiv.toMonoidHom).ker.unop =
      (clusterModularGroupInclusion ℂ E).range := by
  have hsign : (sign B d).comp P.signedEquiv.toMonoidHom =
      (sign R₀.form (R₀.marking.symm ∘ d)).comp P.nodal.signedEquiv.toMonoidHom :=
    MonoidHom.ext fun x ↦ by simp
  rw [hsign]
  exact P.nodal.sign_ker_unop

/-- The unsigned Picard equivalence is the restriction of the signed action to rotations. -/
def unsignedEquiv : Γ ≃* boundaryRotationGroup B d :=
  picardRotationEquiv P.signedEquiv P.sign_ker_unop

/-- The unsigned equivalence agrees with the signed equivalence under rotation inclusion. -/
@[simp]
theorem rotationInclusion_unsignedEquiv_apply (x : Γ) :
    rotationInclusion B d (P.unsignedEquiv x) =
      P.signedEquiv (MonoidHom.op (clusterModularGroupInclusion ℂ E) x) :=
  rotationInclusion_picardRotationEquiv_apply P.signedEquiv P.sign_ker_unop x

end PicardGroupIdentification

end QPainleve.SignedClusterModularGroup
