/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Cremona
public import QPainleve.SignedClusterModularGroup.Realization.Endpoint.PicardAction

import QPainleve.SignedClusterModularGroup.Realization.Anticanonical
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber
import QPainleve.SignedClusterModularGroup.Realization.Presentation.Group

/-!
# Cluster modular groups and Cremona isometries

For a marked toric presentation of a primitive nef square-zero anticanonical
cycle without internal `(-2)` curves, Picard pullback maps the opposite signed
cluster modular group onto the Cremona isometry group. The projection is an
equivalence for at least three boundary components. With one or two components,
the signed equivalence also records the branch sign, and the unsigned group
maps isomorphically to the Cremona isometries.

The comparison combines `CompleteToricPresentation.exists_picardGroupEquivs_of_nodal_model`
with `MarkedSurface.cremonaPicardHom` to produce a `ClusterCremonaComparison`.
-/

public section

open AlgebraicGeometry CategoryTheory MulOpposite Quiver
open QPainleve.CharacterTorus QPainleve.Cluster QPainleve.SignedBoundaryIsometryGroup
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData LineBundleClass

namespace QPainleve.SignedClusterModularGroup.CompleteToricPresentation

open GeometricRealization

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "χ[" c "]" => pointsEquiv ℂ _ (Subtype.mk (Over.Hom.left c) (Over.w c))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {E : SkewExchangeMatrix (Fin r)}
  (Q : CompleteToricPresentation i b r L γ)
  {c : Point Centers[r]} {M₀ : MarkedSurface ℂ n B XTor[r]}

local instance instNonemptyCremonaCones : Nonempty Q.fan.cones := Q.complete.nonempty_cones
local instance instNeZeroCremonaBoundaryLength : NeZero Q.length := Q.neZero
local instance instPrestableCremonaBoundary :
    PrestableFamily ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme ↘ S) := Q.prestable

local notation "Models[" M "," C "]" =>
  HasToricTargetModels (T₀ := Centers[r]) (T₁ := Centers[r]) (b := b) (s := Q.rays)
    (hΦ := Q.regular) (T := Q.cycle) (origin := Q.origin) (ι := Q.inclusion) (P₁ := M)
    (fun z : Point Centers[r] ↦ χ[z]) C

local notation "Cr" => Chow.cremonaIsometryGroup ℂ M₀.surface
local notation "d" => M₀.boundaryClass M₀.isEffectiveCartier_boundaryIdeal

/-- Picard pullback identifies the Cremona isometries of a marked reference fiber
without internal `(-2)` curves as a quotient of the opposite signed cluster modular
group. With at least three boundary components this projection is an equivalence.
With one or two components the projection and the branch sign give a product
equivalence, restricting to the Cremona equivalence on the unsigned subgroup. -/
theorem exists_cluster_cremona_equivs_of_nodal_model
    (href : Q.HasNodalModel c M₀)
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (hprim : IsPrimitive (Additive.ofMul classOf(M₀.isEffectiveCartier_boundaryIdeal)))
    (hnef : (classOf(M₀.isEffectiveCartier_boundaryIdeal)).IsNef ℂ (M₀.surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ M₀.surface classOf(M₀.isEffectiveCartier_boundaryIdeal)
      classOf(M₀.isEffectiveCartier_boundaryIdeal) = 0)
    (hroot : letI : SmoothOfRelativeDimension 2 (M₀.surface ↘ S) := M₀.smooth
      letI : M₀.surface.IsProjectiveOver ℂ := M₀.projective
      letI : IsNoetherian M₀.surface := isNoetherian_of_finiteType (M₀.surface ↘ S)
      letI := (M₀.surface ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
      ∀ x : CodimensionOnePoint M₀.surface, Disjoint (closure {(x : M₀.surface)}) D[M₀].support →
        let p := primeDivisorClass x
        Chow.classIntersectionNumber ℂ M₀.surface p p ≠ -2) :
    letI : SmoothOfRelativeDimension 2 (M₀.surface ↘ S) := M₀.smooth
    letI : M₀.surface.IsProjectiveOver ℂ := M₀.projective
    ∃ (M : Point Centers[r] → MarkedSurface ℂ n B XTor[r])
      (hmark : ∀ z j, (M z).boundaryClass (M z).isEffectiveCartier_boundaryIdeal j = d j)
      (P : ClusterCremonaComparison (k := ℂ) E n Cr),
      M c = M₀ ∧ (∀ z, Q.HasNodalModel z (M z)) ∧
      ∀ (w : Word E E),
        let x := op (signedClusterModularGroupMap ℂ E (End.of w))
        P.sign x = (-1 : ℤˣ) ^ w.inversionCount ∧
        ∀ {C : Centers[r].left.PartialMap Centers[r].left} [IsDominant C.hom]
          [C.IsOver Centers[r].hom Centers[r].hom]
          (R : GeometricRealization M M C (w.xRationalMap ℂ)), Models[M,C] →
          (P.projection x).val = M₀.marking.isometryGroupCongr
            (toIsometry B d (R.toSignedBoundaryIsometry d
              (fun z ↦ (M z).isEffectiveCartier_boundaryIdeal) hmark)) := by
  obtain ⟨G, hGc⟩ :=
    Q.exists_picardGroupEquivs_of_nodal_model href hE hprim hnef hsq
  let : SmoothOfRelativeDimension 2 (M₀.surface ↘ S) := M₀.smooth
  let : M₀.surface.IsProjectiveOver ℂ := M₀.projective
  let : IsRationalOver (M₀.surface ↘ S) := href.isRationalOver
  have hcan := congrArg Inv.inv (href.canonicalClass M₀.isEffectiveCartier_boundaryIdeal)
  let P :=
    M₀.clusterCremonaComparison hcan hnef hsq hroot rfl G.signedEquiv G.sign_ker_unop
  refine ⟨G.family, G.boundaryClass_eq, P, hGc, G.hasNodalModel, fun w ↦ ⟨?_, fun R hR ↦ ?_⟩⟩
  · simpa only [P, MarkedSurface.clusterCremonaComparison_sign_apply] using
      G.sign_signedEquiv_apply_word w
  · simp only [P, MarkedSurface.val_clusterCremonaComparison_projection_apply,
      G.signedEquiv_apply_word w R hR]

end QPainleve.SignedClusterModularGroup.CompleteToricPresentation
