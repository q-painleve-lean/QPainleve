/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.Cremona
public import QPainleve.SignedClusterModularGroup.Realization.Presentation.Cremona.Comparison
public import QPainleve.SignedClusterModularGroup.Realization.Presentation.PicardGroupIdentification

import QPainleve.SignedClusterModularGroup.Boundary.Cremona

/-!
# Cluster modular group identifications with Cremona isometries

The Picard identification of a numbered anticanonical pair gives a canonical
Cremona projection when the cycle is nef and square zero and the surface has
no internal `(-2)` curves. The same projection computes the Cremona coordinate
in both the large-boundary equivalence and the small-boundary product.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory MulOpposite Quiver
open QPainleve.CharacterTorus QPainleve.Cluster QPainleve.SignedBoundaryIsometryGroup
open Scheme Scheme.IdealSheafData TauCeti.AlgebraicGeometry

namespace QPainleve.SignedClusterModularGroup

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "δ[" h "]" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "χ[" c "]" => pointsEquiv ℂ _ (Subtype.mk (Over.Hom.left c) (Over.w c))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {X : Scheme} [X.Over S] [X.IsProjectiveOver ℂ] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ S)] [Scheme.IsRationalOver (X ↘ S)]
  {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ S)] {n : ℕ} [NeZero n]

local instance instNoetherianCremonaIdentification : IsNoetherian X :=
  isNoetherian_of_finiteType (X ↘ S)

local instance instFactorialCremonaIdentification (x : X) :
    UniqueFactorizationMonoid (X.presheaf.stalk x) :=
  (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two x

local notation "Cr" => Chow.cremonaIsometryGroup ℂ X

/-- A Picard group identification of a nef square-zero anticanonical cycle
without internal `(-2)` curves. The Cremona maps are determined by the Picard
identification and act on the Picard lattice of the original surface. -/
@[ext]
structure CremonaGroupIdentification (i : N →+ V) (r : ℕ)
    (A : Scheme.NodalCycleNumbering (X := D.subscheme)
      (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n) (hD : D.IsEffectiveCartier) where
  /-- The two Picard equivalences and their marked toric family. -/
  picard : PicardGroupIdentification i r A hD
  /-- The boundary ideal represents the canonical class. -/
  canonicalClass_eq : LineBundleClass.mk hD.toInvertibleSheaf =
    LineBundleClass.mk (QPainleve.canonicalBundle ℂ X 2)
  /-- The anticanonical boundary class is nef. -/
  nef : δ[hD].IsNef ℂ (X ↘ S)
  /-- The total boundary class has self-intersection zero. -/
  selfIntersection_eq_zero : Chow.classIntersectionNumber ℂ X δ[hD] δ[hD] = 0
  /-- Every prime divisor disjoint from the boundary has self-intersection different from `-2`. -/
  noInternalRoots (p : CodimensionOnePoint X) (hp : Disjoint (closure {(p : X)}) D.support) :
    let a := LineBundleClass.primeDivisorClass p
    Chow.classIntersectionNumber ℂ X a a ≠ -2

namespace CremonaGroupIdentification

open GeometricRealization

variable {i : N →+ V} {r : ℕ}
  {A : Scheme.NodalCycleNumbering (X := D.subscheme)
    (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n} {hD : D.IsEffectiveCartier}
  (P : CremonaGroupIdentification i r A hD)

local notation "E" => P.picard.exchangeMatrix
local notation "Γs" => (SignedClusterModularGroup ℂ E)ᵐᵒᵖ
local notation "π" =>
  A.cremonaProjection hD P.canonicalClass_eq P.nef P.selfIntersection_eq_zero P.noInternalRoots

/-- The Cremona projection and branch sign of the ordered toric seed. -/
def comparison : ClusterCremonaComparison (k := ℂ) E n Cr :=
  ClusterCremonaComparison.ofPicardEquiv P.picard.signedEquiv P.picard.sign_ker_unop π
    (A.cremonaProjection_surjective hD P.canonicalClass_eq P.nef P.selfIntersection_eq_zero
      P.noInternalRoots)
    (A.cremonaProjection_injective hD P.canonicalClass_eq P.nef P.selfIntersection_eq_zero
      P.noInternalRoots)
    (A.signedBoundaryIsometryEquivCremonaProd hD P.canonicalClass_eq P.nef
      P.selfIntersection_eq_zero P.noInternalRoots)
    (A.signedBoundaryIsometryEquivCremonaProd_apply hD P.canonicalClass_eq P.nef
      P.selfIntersection_eq_zero P.noInternalRoots)

/-- The Cremona projection acts by the underlying signed Picard isometry. -/
@[simp]
theorem val_projection_apply (x : Γs) :
    (P.comparison.projection x).val = (P.picard.signedEquiv x).val.1 := by
  simpa only [comparison, ClusterCremonaComparison.ofPicardEquiv_projection_apply,
    toIsometry_apply] using
    A.val_cremonaProjection_apply hD P.canonicalClass_eq P.nef P.selfIntersection_eq_zero
      P.noInternalRoots (P.picard.signedEquiv x)

/-- The Cremona comparison retains the ordered branch sign of the Picard image. -/
@[simp]
theorem sign_apply (x : Γs) :
    P.comparison.sign x = (P.picard.signedEquiv x).val.2 := by
  simp only [comparison, ClusterCremonaComparison.ofPicardEquiv_sign_apply,
    SignedBoundaryIsometryGroup.sign_apply]

/-- On a realized loop, the Cremona projection evaluates by the marked Picard pullback. -/
theorem val_projection_apply_word (w : Word E E) :
    letI := P.picard.presentation.complete.nonempty_cones
    letI := P.picard.presentation.prestable
    letI := P.picard.presentation.neZero
    ∀ {C : Centers[r].left.PartialMap Centers[r].left} [IsDominant C.hom]
      [C.IsOver Centers[r].hom Centers[r].hom]
      (R : GeometricRealization P.picard.family P.picard.family C (w.xRationalMap ℂ)),
      HasToricTargetModels (T₀ := Centers[r]) (T₁ := Centers[r]) (b := P.picard.basis)
        (s := P.picard.presentation.rays) (hΦ := P.picard.presentation.regular)
        (T := P.picard.presentation.cycle) (origin := P.picard.presentation.origin)
        (ι := P.picard.presentation.inclusion) (P₁ := P.picard.family)
        (fun z : Point Centers[r] ↦ χ[z]) C →
      (P.comparison.projection (op (signedClusterModularGroupMap ℂ E (End.of w)))).val =
        P.picard.marking.isometryGroupCongr
          (P.picard.form.isometryGroupEquivIsometryEquiv.symm R.picard) := by
  intro C _ _ R hR
  rw [val_projection_apply]
  exact congrArg Prod.fst (P.picard.signedEquiv_apply_word w R hR)

end CremonaGroupIdentification

end QPainleve.SignedClusterModularGroup
