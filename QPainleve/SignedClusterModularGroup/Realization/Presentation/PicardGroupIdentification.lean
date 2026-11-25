/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.ModularGroup
public import QPainleve.LinearAlgebra.BilinearForm.Conjugation
public import QPainleve.SignedClusterModularGroup.Realization.Presentation
public import QPainleve.SignedClusterModularGroup.Realization.Surface.PrimeClass

import QPainleve.SignedClusterModularGroup.Realization.PicardAction

/-!
# Picard group identifications of numbered anticanonical pairs

A marked toric family with a prescribed numbered reference fiber determines
signed and unsigned group equivalences on the original Picard lattice. The
identification records the seed, the family, and the formulas for evaluating
the signed equivalence on geometric loop realizations. Restricting it to the
sign kernel gives the unsigned equivalence.
-/

public section

open AlgebraicGeometry CategoryTheory Module MulOpposite Quiver
open QPainleve.CharacterTorus QPainleve.Cluster QPainleve.SignedBoundaryIsometryGroup
open Scheme Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric

namespace QPainleve.SignedClusterModularGroup

open GeometricRealization

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
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

local notation "Pic" => Additive (LineBundleClass X)
local notation "L" => (Fin (Module.finrank ℤ Pic) → ℤ)
local notation "B" => Chow.intersectionBilinForm ℂ X
local notation "classes[" A "," hD "]" =>
  (fun j ↦ Additive.ofMul (LineBundleClass.primeDivisorClass
    (D.boundaryPrimeEmbedding (Scheme.NodalCycleNumbering.boundaryPrimeEquiv A hD j))))

/-- The Picard group equivalences of a toric seed with `r` ordered centers for a
numbered anticanonical pair. The reference fiber uses the original surface and
boundary numbering, and both equivalences take values on its Picard lattice. -/
structure PicardGroupIdentification (i : N →+ V) (r : ℕ)
    (A : Scheme.NodalCycleNumbering (X := D.subscheme)
      (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n) (hD : D.IsEffectiveCartier) where
  /-- The intersection form in the coordinates of the moving Picard marking. -/
  form : LinearMap.BilinForm ℤ L
  /-- The marking on the original surface's Picard lattice. -/
  marking : form.IsometryEquiv B
  /-- The oriented frame of the toric presentation. -/
  basis : Basis (Fin 2) ℤ N
  /-- The ordered toric presentation supplying the nodal models. -/
  presentation : CompleteToricPresentation i basis r L Empty
  /-- The center of the original surface in the family. -/
  center : Point Centers[r]
  /-- The rational X evaluation on the original surface. -/
  evaluation : X ⤏ XTor[r]
  /-- The seed's exchange matrix. -/
  exchangeMatrix : SkewExchangeMatrix (Fin r)
  /-- The family of marked surfaces over the center torus. -/
  family : Point Centers[r] → MarkedSurface ℂ n form XTor[r]
  /-- The opposite signed cluster modular group identifies with signed boundary isometries. -/
  signedEquiv : (SignedClusterModularGroup ℂ exchangeMatrix)ᵐᵒᵖ ≃*
    signedBoundaryIsometryGroup B classes[A,hD]
  /-- The exchange matrix comes from the ordered ray charges in the oriented frame. -/
  matrix_eq : exchangeMatrix.matrix =
    chargeExchangeMatrix basis.detDualEquiv.toLinearMap (Fan.rayChargeMap presentation.rays)
  /-- The reference fiber is the original pair with its marking and X evaluation. -/
  family_center : family center = MarkedSurface.ofBoundary D A marking evaluation
  /-- Each fiber has a nodal model in the same presentation. -/
  hasNodalModel (z : Point Centers[r]) : presentation.HasNodalModel z (family z)
  /-- In the moving Picard marking the numbered boundary classes are constant. -/
  boundaryClass_eq (z : Point Centers[r]) (j : ZMod n) :
    (family z).boundaryClass (family z).isEffectiveCartier_boundaryIdeal j =
      marking.symm (classes[A,hD] j)
  /-- The Picard sign of a loop is its inversion parity. -/
  sign_signedEquiv_apply_word (w : Word exchangeMatrix exchangeMatrix) :
    (signedEquiv (op (signedClusterModularGroupMap ℂ exchangeMatrix (End.of w)))).val.2 =
      (-1 : ℤˣ) ^ w.inversionCount
  /-- The signed equivalence gives the marked pullback and ordered branch sign of every
  compatible geometric realization of a loop. -/
  signedEquiv_apply_word (w : Word exchangeMatrix exchangeMatrix) :
    letI := presentation.complete.nonempty_cones
    letI := presentation.prestable
    letI := presentation.neZero
    ∀ {C : Centers[r].left.PartialMap Centers[r].left} [IsDominant C.hom]
      [C.IsOver Centers[r].hom Centers[r].hom]
      (R : GeometricRealization family family C (w.xRationalMap ℂ)),
      HasToricTargetModels (T₀ := Centers[r]) (T₁ := Centers[r]) (b := basis)
        (s := presentation.rays) (hΦ := presentation.regular) (T := presentation.cycle)
        (origin := presentation.origin) (ι := presentation.inclusion) (P₁ := family)
        (fun z : Point Centers[r] ↦ χ[z]) C →
      (signedEquiv (op (signedClusterModularGroupMap ℂ exchangeMatrix (End.of w)))).val =
        (marking.isometryGroupCongr (form.isometryGroupEquivIsometryEquiv.symm R.picard),
          R.orientation)
  /-- The sign kernel on point maps is the image of the unsigned group. -/
  sign_ker_unop : ((sign B classes[A,hD]).comp signedEquiv.toMonoidHom).ker.unop =
    (clusterModularGroupInclusion ℂ exchangeMatrix).range

attribute [simp] PicardGroupIdentification.family_center
  PicardGroupIdentification.sign_signedEquiv_apply_word

namespace PicardGroupIdentification

variable {i : N →+ V} {r : ℕ}
  {A : Scheme.NodalCycleNumbering (X := D.subscheme)
    (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n} {hD : D.IsEffectiveCartier}
  (P : PicardGroupIdentification i r A hD)

/-- The Picard equivalence on unsigned maps is the restriction to the sign kernel,
identified with the group of boundary rotations. -/
noncomputable def unsignedEquiv : (ClusterModularGroup ℂ P.exchangeMatrix)ᵐᵒᵖ ≃*
    boundaryRotationGroup B classes[A,hD] :=
  picardRotationEquiv P.signedEquiv P.sign_ker_unop

/-- Including the boundary rotation gives the signed Picard action on the same map. -/
@[simp]
theorem rotationInclusion_unsignedEquiv_apply
    (x : (ClusterModularGroup ℂ P.exchangeMatrix)ᵐᵒᵖ) :
    rotationInclusion B classes[A,hD] (P.unsignedEquiv x) =
      P.signedEquiv (MonoidHom.op (clusterModularGroupInclusion ℂ P.exchangeMatrix) x) :=
  rotationInclusion_picardRotationEquiv_apply P.signedEquiv P.sign_ker_unop x

end PicardGroupIdentification

end QPainleve.SignedClusterModularGroup
