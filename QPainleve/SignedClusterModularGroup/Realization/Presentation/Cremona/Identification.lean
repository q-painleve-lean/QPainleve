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

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]

local notation "S" => Spec (CommRingCat.of k₀)
local notation "Centers[" r "]" => Over.mk (structureMap k₀ (Fin r → ℤ))
local notation "δ[" h "]" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "χ[" c "]" => pointsEquiv k₀ _ (Subtype.mk (Over.Hom.left c) (Over.w c))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {X : Scheme} [X.Over (Spec (.of k₀))] [X.IsProjectiveOver k₀] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k₀))] [Scheme.IsRationalOver (X ↘ Spec (.of k₀))]
  {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ Spec (.of k₀))] {n : ℕ} [NeZero n]

local notation "Cr" => Chow.cremonaIsometryGroup k₀ X

/-- A Picard group identification of a nef square-zero anticanonical cycle
without internal `(-2)` curves. The Cremona maps are determined by the Picard
identification and act on the Picard lattice of the original surface. -/
@[ext]
structure CremonaGroupIdentification {i : N →+ V} {r : ℕ}
    {A : Scheme.NodalCycleNumbering (X := D.subscheme)
      (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n}
    (R : FiniteMarkedReferenceFiber i r A) (hD : D.IsEffectiveCartier) where
  /-- The two Picard equivalences and their marked toric family. -/
  picard : PicardGroupIdentification R hD
  /-- The boundary ideal represents the canonical class. -/
  canonicalClass_eq : LineBundleClass.mk hD.toInvertibleSheaf =
    LineBundleClass.mk (QPainleve.canonicalBundle k₀ X 2)
  /-- The anticanonical boundary class is nef. -/
  nef : δ[hD].IsNef k₀ (X ↘ S)
  /-- The total boundary class has self-intersection zero. -/
  selfIntersection_eq_zero : Chow.classIntersectionNumber k₀ X δ[hD] δ[hD] = 0
  /-- Every prime divisor disjoint from the boundary has self-intersection different from `-2`. -/
  noInternalRoots (p : CodimensionOnePoint X) (hp : Disjoint (closure {(p : X)}) D.support) :
    let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ S)
    let := (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let a := LineBundleClass.primeDivisorClass p
    Chow.classIntersectionNumber k₀ X a a ≠ -2

namespace CremonaGroupIdentification

open GeometricRealization

variable {i : N →+ V} {r : ℕ}
  {A : Scheme.NodalCycleNumbering (X := D.subscheme)
    (Empty.elim : Empty → (D.subscheme ↘ Spec (.of k₀)).smoothLocus) n} {hD : D.IsEffectiveCartier}
  {R₀ : FiniteMarkedReferenceFiber i r A} (P : CremonaGroupIdentification R₀ hD)

local notation "E" => R₀.reference.exchangeMatrix
local notation "Γs" => (SignedClusterModularGroup k₀ E)ᵐᵒᵖ
local notation "Q" => R₀.reference.presentation
local notation "M" => P.picard.nodal.family
local notation "π" =>
  A.cremonaProjection hD P.canonicalClass_eq P.nef P.selfIntersection_eq_zero P.noInternalRoots

/-- The Cremona projection and branch sign of the ordered toric seed. -/
def comparison : ClusterCremonaComparison (k := k₀) E n Cr := by
  let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  let := (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  exact ClusterCremonaComparison.ofPicardEquiv P.picard.signedEquiv P.picard.sign_ker_unop π
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
  let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  let := (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
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
    letI := (Q).complete.nonempty_cones
    letI := (Q).prestable
    letI := (Q).neZero
    ∀ {C : Centers[r].left.PartialMap Centers[r].left} [IsDominant C.hom]
      [C.IsOver Centers[r].hom Centers[r].hom]
      (R : GeometricRealization M M C (w.xRationalMap k₀)),
      HasToricTargetModels (T₀ := Centers[r]) (T₁ := Centers[r]) (b := R₀.basis)
        (s := (Q).rays) (hΦ := (Q).regular) (T := (Q).cycle) (origin := (Q).origin)
        (ι := (Q).inclusion) (P₁ := M)
        (fun z : Point Centers[r] ↦ χ[z]) C →
      (P.comparison.projection (op (signedClusterModularGroupMap k₀ E (End.of w)))).val =
        R₀.marking.isometryGroupCongr (R₀.form.isometryGroupEquivIsometryEquiv.symm R.picard) := by
  intro C _ _ R hR
  rw [val_projection_apply]
  exact congrArg Prod.fst (P.picard.signedEquiv_apply_word w R hR)

end CremonaGroupIdentification

end QPainleve.SignedClusterModularGroup
