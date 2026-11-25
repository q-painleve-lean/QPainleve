/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Presentation.Identification

import QPainleve.Geometry.Toric.Fan.Picard.Complexity
import QPainleve.Geometry.Toric.Fan.Presentation.Induction

/-!
# Cluster modular groups of anticanonical pairs

A numbered primitive nef square-zero anticanonical cycle on a smooth projective
rational complex surface determines a seed with one label for each internal center
of a toric presentation. The number of labels is twelve minus the number of
boundary components. The opposite cluster modular groups of the resulting seed
act by signed boundary isometries and boundary rotations on the original Picard
lattice. The moving family retains the original pair as its reference fiber.

The construction combines `IdealSheafData.hasToricPresentation_of_anticanonical_cycle` with
`exists_picardGroupEquivs_of_toric_presentation`.
-/

public section

open AlgebraicGeometry CategoryTheory Module MulOpposite Quiver
open QPainleve.CharacterTorus QPainleve.Cluster
open QPainleve.SignedBoundaryIsometryGroup
open Scheme Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric

namespace QPainleve.SignedClusterModularGroup

open GeometricRealization

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "δ[" h "]" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "ideal[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "χ[" c "]" => pointsEquiv ℂ _ (Subtype.mk (Over.Hom.left c) (Over.w c))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Basis (Fin 2) ℤ N}
  {X : Scheme} [X.Over S] [X.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (X ↘ S)] [Scheme.IsRationalOver (X ↘ S)]
  {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ S)]
  {n : ℕ} [NeZero n]

local instance : IsIntegral X :=
  letI : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  Scheme.IsRationalOver.isIntegral_of_smooth (f := X ↘ S) inferInstance

local notation "Pic" => Additive (LineBundleClass X)
local notation "B" => Chow.intersectionBilinForm ℂ X
local notation "K" => LineBundleClass.mk (canonicalBundle ℂ X 2)
local notation "classes[" A "," hD "]" =>
  (fun j ↦ Additive.ofMul (LineBundleClass.primeDivisorClass
    (D.boundaryPrimeEmbedding (Scheme.NodalCycleNumbering.boundaryPrimeEquiv A hD j))))
local notation "Models[" b₀ "," Q "," M "," C "]" =>
  HasToricTargetModels (T₀ := Centers[12 - n]) (T₁ := Centers[12 - n]) (b := b₀)
    (s := CompleteToricPresentation.rays Q)
    (hΦ := CompleteToricPresentation.regular Q) (T := CompleteToricPresentation.cycle Q)
    (origin := CompleteToricPresentation.origin Q) (ι := CompleteToricPresentation.inclusion Q)
    (P₁ := M) (fun z : Point Centers[12 - n] ↦ χ[z]) C

/-- A numbered primitive nef square-zero anticanonical cycle on a smooth projective
rational complex surface admits a toric seed on `Fin (12 - n)`. Its signed and
unsigned opposite cluster modular groups identify with the signed boundary
isometries and rotations of the original Picard lattice. The family retains
the original numbered surface. On loops the signed equivalence evaluates by
geometric Picard pullback and retains the sign on the ordered branches. -/
theorem exists_picardGroupEquivs_of_anticanonical_cycle
    (hi : IsIntegralLattice i)
    (A : Scheme.NodalCycleNumbering (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n)
    (hD : D.IsEffectiveCartier) (hcan : LineBundleClass.mk hD.toInvertibleSheaf = K)
    (hprim : IsPrimitive (Additive.ofMul δ[hD])) (hnef : δ[hD].IsNef ℂ (X ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ X δ[hD] δ[hD] = 0) :
    letI : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
    letI := (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let d := classes[A,hD]
    let r := 12 - n
    let L := Fin (Module.finrank ℤ Pic) → ℤ
    ∃ (H : LinearMap.BilinForm ℤ L) (μ : H.IsometryEquiv B)
      (b' : Basis (Fin 2) ℤ N) (Q : CompleteToricPresentation i b' r L Empty),
    letI := Q.complete.nonempty_cones
    letI := Q.prestable
    letI := Q.neZero
    ∃ (c : Point Centers[r]) (f : X ⤏ XTor[r]) (E : SkewExchangeMatrix (Fin r))
      (M : Point Centers[r] → MarkedSurface ℂ n H XTor[r])
      (hD' : ∀ z, ideal[M z].IsEffectiveCartier)
      (Θ : (SignedClusterModularGroup ℂ E)ᵐᵒᵖ ≃* signedBoundaryIsometryGroup B d)
      (Θrot : (ClusterModularGroup ℂ E)ᵐᵒᵖ ≃* boundaryRotationGroup B d),
      (b' = b ∨ b' = b.reindex (Equiv.swap 0 1)) ∧
      E.matrix = chargeExchangeMatrix b'.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays) ∧
      M c = MarkedSurface.ofBoundary D A μ f ∧ (∀ z, Q.HasNodalModel z (M z)) ∧
      (∀ z j, (M z).boundaryClass (hD' z) j = μ.symm (d j)) ∧
      (∀ (w : Word E E),
        sign B d (Θ (op (signedClusterModularGroupMap ℂ E (End.of w)))) =
          (-1 : ℤˣ) ^ w.inversionCount ∧
        ∀ {C : Centers[r].left.PartialMap Centers[r].left} [IsDominant C.hom]
          [C.IsOver Centers[r].hom Centers[r].hom]
          (R : GeometricRealization M M C (w.xRationalMap ℂ)),
          Models[b',Q,M,C] →
          (Θ (op (signedClusterModularGroupMap ℂ E (End.of w)))).val =
            (μ.isometryGroupCongr (H.isometryGroupEquivIsometryEquiv.symm R.picard),
              R.orientation)) ∧
      ((sign B d).comp Θ.toMonoidHom).ker.unop = (clusterModularGroupInclusion ℂ E).range ∧
      (∀ x, rotationInclusion B d (Θrot x) =
        Θ (MonoidHom.op (clusterModularGroupInclusion ℂ E) x)) := by
  obtain ⟨r, ⟨P⟩⟩ := (hasToricPresentation_iff ..).mp
    (D.hasToricPresentation_of_anticanonical_cycle b hi A hD hcan)
  have hr := Fan.centerCount_eq_of_square_zero P.regular P.complete P.rays P.parameters
    P.isNodal P.iso P.iso_boundary A hD hcan hsq
  subst r
  obtain ⟨H, μ, b', Q, c, f, E, M, hD', Θ, Θrot, hframe, -, hE, hM, hmodels, hmark,
    hwords, hsign, hrot⟩ :=
    exists_picardGroupEquivs_of_toric_presentation P A hD hprim hnef hsq
  exact ⟨H, μ, b', Q, c, f, E, M, hD', Θ, Θrot, hframe.imp And.left And.left, hE, hM, hmodels,
    hmark, hwords, hsign, hrot⟩

end QPainleve.SignedClusterModularGroup
