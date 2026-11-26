/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Cremona
public import QPainleve.SignedClusterModularGroup.Realization.Presentation.Cremona.Comparison
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

namespace QPainleve.SignedClusterModularGroup.MarkedSurface

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {k : Type*} [Field k]
  {n : ℕ} [NeZero n] {L : Type u} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {X : Scheme.{u}} {ι : Type*} [DecidableEq ι] {E : SkewExchangeMatrix ι}
  (M : MarkedSurface K n B X)

local notation "S" => Spec (CommRingCat.of K)
local notation "base" => (M.surface ↘ S)
local notation "Cr" => Chow.cremonaIsometryGroup K M.surface
local notation "Γs" => (SignedClusterModularGroup k E)ᵐᵒᵖ

local instance : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
local instance : M.surface.IsProjectiveOver K := M.projective
local instance : IsNoetherian M.surface := isNoetherian_of_finiteType base
local instance (x : M.surface) : UniqueFactorizationMonoid (M.surface.presheaf.stalk x) :=
  (base).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two x

variable [IsRationalOver (M.surface ↘ Spec (CommRingCat.of K))]
  (hcan : (LineBundleClass.mk M.isEffectiveCartier_boundaryIdeal.toInvertibleSheaf)⁻¹ =
    (LineBundleClass.mk (QPainleve.canonicalBundle K M.surface 2))⁻¹)
  (hnef : (LineBundleClass.mk M.isEffectiveCartier_boundaryIdeal.toInvertibleSheaf)⁻¹.IsNef K
    (M.surface ↘ Spec (CommRingCat.of K)))
  (hsq : let a := (LineBundleClass.mk M.isEffectiveCartier_boundaryIdeal.toInvertibleSheaf)⁻¹
    Chow.classIntersectionNumber K M.surface a a = 0)
  (hroot : ∀ p : CodimensionOnePoint M.surface, Disjoint (closure {(p : M.surface)})
    M.pair.hom.left.ker.support →
    Chow.classIntersectionNumber K M.surface (primeDivisorClass p) (primeDivisorClass p) ≠ -2)
  {d' : ZMod n → L} (hd : M.boundaryClass M.isEffectiveCartier_boundaryIdeal = d')
  (Θ : (SignedClusterModularGroup k E)ᵐᵒᵖ ≃* signedBoundaryIsometryGroup B d')
  (hΘ : ((sign B d').comp Θ.toMonoidHom).ker.unop = (clusterModularGroupInclusion k E).range)

include hd in
/-- The signed Picard identification on a marked surface with no internal `(-2)` curves
gives the projection to Cremona isometries together with the boundary sign. -/
noncomputable def clusterCremonaComparison : ClusterCremonaComparison (k := k) E n Cr := by
  subst d'
  let π := M.cremonaPicardHom hcan hnef hsq hroot
  have hinj (hn : 3 ≤ n) : Function.Injective π := by
    intro x y hxy
    apply (M.signedBoundaryIsometryEquivCremona hcan hnef hsq hroot hn).injective
    simpa only [M.signedBoundaryIsometryEquivCremona_apply] using hxy
  exact ClusterCremonaComparison.ofPicardEquiv Θ hΘ π
    (M.cremonaPicardHom_surjective hcan hnef hsq hroot) hinj
    (M.signedBoundaryIsometryEquivCremonaProd hcan hnef hsq hroot)
    (M.signedBoundaryIsometryEquivCremonaProd_apply hcan hnef hsq hroot)

/-- The Cremona projection is the lattice action of the signed Picard image in the
marking of the chosen surface. -/
@[simp]
theorem val_clusterCremonaComparison_projection_apply (x : Γs) :
    ((M.clusterCremonaComparison hcan hnef hsq hroot hd Θ hΘ).projection x).val =
      M.marking.isometryGroupCongr (toIsometry B d' (Θ x)) := by
  subst d'
  dsimp only [clusterCremonaComparison]
  erw [ClusterCremonaComparison.ofPicardEquiv_projection_apply]
  exact M.cremonaPicardHom_apply hcan hnef hsq hroot (Θ x)

/-- The sign of the Cremona comparison is the sign of the signed Picard image. -/
@[simp]
theorem clusterCremonaComparison_sign_apply (x : Γs) :
    (M.clusterCremonaComparison hcan hnef hsq hroot hd Θ hΘ).sign x =
      (Θ x).val.2 := by
  subst d'
  dsimp only [clusterCremonaComparison]
  erw [ClusterCremonaComparison.ofPicardEquiv_sign_apply,
    SignedBoundaryIsometryGroup.sign_apply]

end QPainleve.SignedClusterModularGroup.MarkedSurface

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
