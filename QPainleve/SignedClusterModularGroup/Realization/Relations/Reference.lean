/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Relations
public import QPainleve.SignedClusterModularGroup.Realization.Presentation
public import QPainleve.SignedClusterModularGroup.Realization.Tropical

import QPainleve.Algebra.Cluster.Word.SubtractionFree
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber
import QPainleve.SignedClusterModularGroup.Realization.Presentation.Family
import QPainleve.SignedClusterModularGroup.Realization.Relations.Presentation

/-!
# Deciding signed loop relations from a reference contraction

A single reference nodal contraction supplies the boundary orders and the moving
models used in the geometric criterion. The comparison applies over any
characteristic-zero field by interpreting the same universal Y-seed coefficients.
It combines `CompleteToricPresentation.exists_marked_family_of_nodal_model` with
`GeometricRealization.xPullback_eq_iff_signedLoopInvariants_eq_of_presentation`.
-/

public section

open AlgebraicGeometry CategoryTheory Quiver
open QPainleve.CharacterTorus QPainleve.Cluster
open Scheme Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric

namespace QPainleve.SignedClusterModularGroup.CompleteToricPresentation

open GeometricRealization (Point)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "χ[" c "]" => pointsEquiv ℂ _ (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "cartier[" M "]" => MarkedSurface.isEffectiveCartier_boundaryIdeal M
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {E : SkewExchangeMatrix (Fin r)}
  (Q : CompleteToricPresentation i b r L γ)
  {c₀ : Point Centers[r]} {M₀ : MarkedSurface ℂ n B XTor[r]}

local instance instNonemptyReferenceRelationCones : Nonempty Q.fan.cones :=
  Q.complete.nonempty_cones
local instance instNeZeroReferenceRelationLength : NeZero Q.length := Q.neZero
local instance instPrestableReferenceRelationBoundary :
    PrestableFamily ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme ↘ S) :=
  Q.prestable

local notation "fiber[" M "," c "]" =>
  ContractedToricFiber b Q.rays Q.regular Q.cycle Q.origin Q.inclusion χ[c] M
local notation "orders[" p "," M "]" => (fun j : Fin n ↦ Fan.rayBoundaryOrders b Q.rays
  (ContractedToricFiber.numberedBoundaryRays p cartier[M] (RingEquiv.toEquiv (ZMod.finEquiv n) j)))

variable (k : Type*) [Field k] [CharZero k]

/-- For signed loops of a primitive nef square-zero anticanonical cycle, equality of independent
X pullbacks is equivalent to agreement of the inversion sign, transported exchange-kernel
basis columns, and the forward boundary label of component zero. The reference contraction
may have repeated centers. -/
theorem xPullback_eq_iff_signedLoopInvariants_eq_of_nodal_contraction
    (p₀ : fiber[M₀,c₀]) (hnodal₀ : p₀.IsNodalContraction)
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (hprim : IsPrimitive (Additive.ofMul classOf(cartier[M₀])))
    (hnef : (classOf(cartier[M₀])).IsNef ℂ (M₀.surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ M₀.surface classOf(cartier[M₀])
      classOf(cartier[M₀]) = 0)
    (w v : Word E E) {m : ℕ} (β : Module.Basis (Fin m) ℤ E.matrix.mulVecLin.ker) :
    let orders := orders[p₀,M₀]
    w.xPullback k = v.xPullback k ↔
      w.signedLoopInvariants (fun j ↦ (β j : Fin r → ℤ)) orders (orders 0) =
        v.signedLoopInvariants (fun j ↦ (β j : Fin r → ℤ)) orders (orders 0) := by
  obtain ⟨M, _, hM, hfamily⟩ :=
    Q.exists_marked_family_of_nodal_model (Q.hasNodalModel_of_contraction hnodal₀) cartier[M₀]
  subst M₀
  dsimp only
  let P : ChargeSeed E N :=
    ⟨b.detDualEquiv.toLinearMap, Fan.rayChargeMap Q.rays, b.detDualEquiv_self, hE.symm⟩
  choose p hp using fun c ↦ (hfamily c).1.exists_isNodalContraction cartier[M c]
  have hmark (c : Point Centers[r]) (j : ZMod n) :
      (M c).boundaryClass cartier[M c] j = (M c₀).boundaryClass cartier[M c₀] j :=
    congrFun (hfamily c).2 j
  calc
    w.xPullback k = v.xPullback k ↔ w.xPullback ℂ = v.xPullback ℂ :=
      (w.xPullback_eq_iff_ySeed_coefficient_eq k v).trans
        (w.xPullback_eq_iff_ySeed_coefficient_eq ℂ v).symm
    _ ↔ _ := GeometricRealization.xPullback_eq_iff_signedLoopInvariants_eq_of_presentation
      Q P rfl rfl M p₀ hnodal₀ (fun c _ ↦ p c) (fun c _ ↦ hp c) hnef hsq hprim hmark
      Q.exists_cone_of_numbered_node w v β

end QPainleve.SignedClusterModularGroup.CompleteToricPresentation
