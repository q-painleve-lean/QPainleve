/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.Cremona
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
local notation "Γ" => (ClusterModularGroup ℂ E)ᵐᵒᵖ
local notation "π" =>
  A.cremonaProjection hD P.canonicalClass_eq P.nef P.selfIntersection_eq_zero P.noInternalRoots

/-- Picard pullback as a homomorphism from opposite signed cluster maps to Cremona isometries. -/
def projection : Γs →* Cr := (π).comp P.picard.signedEquiv.toMonoidHom

/-- The Cremona projection acts on Picard classes by the underlying signed Picard isometry. -/
@[simp]
theorem val_projection_apply (x : Γs) : (P.projection x).val = (P.picard.signedEquiv x).val.1 := by
  simpa only [projection, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, toIsometry_apply] using
    A.val_cremonaProjection_apply hD P.canonicalClass_eq P.nef P.selfIntersection_eq_zero
      P.noInternalRoots (P.picard.signedEquiv x)

/-- Every Cremona isometry is realized by a signed cluster map. -/
theorem projection_surjective : Function.Surjective P.projection :=
  (A.cremonaProjection_surjective hD P.canonicalClass_eq P.nef P.selfIntersection_eq_zero
    P.noInternalRoots).comp P.picard.signedEquiv.surjective

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
      (P.projection (op (signedClusterModularGroupMap ℂ E (End.of w)))).val =
        P.picard.marking.isometryGroupCongr
          (P.picard.form.isometryGroupEquivIsometryEquiv.symm R.picard) := by
  intro C _ _ R hR
  rw [val_projection_apply]
  exact congrArg Prod.fst (P.picard.signedEquiv_apply_word w R hR)

/-- With at least three boundary components, Picard pullback is a Cremona equivalence. -/
def signedEquiv (hn : 3 ≤ n) : Γs ≃* Cr :=
  MulEquiv.ofBijective P.projection
    ⟨(A.cremonaProjection_injective hD P.canonicalClass_eq P.nef P.selfIntersection_eq_zero
      P.noInternalRoots hn).comp P.picard.signedEquiv.injective, P.projection_surjective⟩

/-- The large-boundary equivalence evaluates by the Cremona projection. -/
@[simp]
theorem signedEquiv_apply (hn : 3 ≤ n) (x : Γs) :
    P.signedEquiv hn x = P.projection x :=
  (rfl)

/-- With one or two components, record both the Cremona isometry and the branch sign. -/
def signedProdEquiv (hn : n ≤ 2) : Γs ≃* Cr × ℤˣ :=
  P.picard.signedEquiv.trans
    (A.signedBoundaryIsometryEquivCremonaProd hD P.canonicalClass_eq P.nef
      P.selfIntersection_eq_zero P.noInternalRoots hn)

/-- The small-boundary product evaluates by Picard pullback and the branch sign. -/
@[simp]
theorem signedProdEquiv_apply (hn : n ≤ 2) (x : Γs) :
    P.signedProdEquiv hn x = (P.projection x, (P.picard.signedEquiv x).val.2) := by
  simpa only [signedProdEquiv, MulEquiv.trans_apply, projection, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, SignedBoundaryIsometryGroup.sign_apply] using
    A.signedBoundaryIsometryEquivCremonaProd_apply hD P.canonicalClass_eq P.nef
      P.selfIntersection_eq_zero P.noInternalRoots hn (P.picard.signedEquiv x)

/-- With one or two components, unsigned cluster maps identify with the Cremona isometries. -/
def unsignedEquiv (hn : n ≤ 2) : Γ ≃* Cr :=
  P.picard.unsignedEquiv.trans
    (A.boundaryRotationEquivCremona hD P.canonicalClass_eq P.nef
      P.selfIntersection_eq_zero P.noInternalRoots hn)

/-- The unsigned equivalence evaluates by the same Cremona projection after inclusion. -/
@[simp]
theorem unsignedEquiv_apply (hn : n ≤ 2) (x : Γ) :
    P.unsignedEquiv hn x =
      P.projection (MonoidHom.op (clusterModularGroupInclusion ℂ E) x) := by
  simp only [unsignedEquiv, MulEquiv.trans_apply,
    Scheme.NodalCycleNumbering.boundaryRotationEquivCremona_apply,
    P.picard.rotationInclusion_unsignedEquiv_apply, projection, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom]

/-- The unsigned subgroup maps to the Cremona factor with positive branch sign. -/
theorem signedProdEquiv_apply_inclusion (hn : n ≤ 2) (x : Γ) :
    P.signedProdEquiv hn (MonoidHom.op (clusterModularGroupInclusion ℂ E) x) =
      (P.unsignedEquiv hn x, 1) := by
  rw [signedProdEquiv_apply, unsignedEquiv_apply, ← P.picard.rotationInclusion_unsignedEquiv_apply]
  simp only [coe_rotationInclusion]

end CremonaGroupIdentification

end QPainleve.SignedClusterModularGroup
