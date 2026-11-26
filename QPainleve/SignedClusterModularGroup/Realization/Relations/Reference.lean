/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.LoopComparison.List
public import QPainleve.SignedClusterModularGroup.Realization.Presentation
public import QPainleve.SignedClusterModularGroup.Realization.Tropical

import QPainleve.Geometry.Toric.Fan.ExchangeMatrix
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber
import QPainleve.SignedClusterModularGroup.Realization.Presentation.Family
import QPainleve.SignedClusterModularGroup.Realization.Relations.Presentation

/-!
# Deciding signed loop relations from a reference contraction

A single reference nodal contraction supplies the boundary orders and the moving
models used in the geometric criterion. The resulting integer comparison decides
equality of independent X pullbacks over any field for typed loops and lists of
generators.
The same certificate of the exchange matrix and order table serves both checkers.
Their correctness uses `CompleteToricPresentation.exists_marked_family_of_nodal_model`
and `GeometricRealization.xPullback_eq_iff_signedLoopInvariants_eq_of_presentation`.
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

/-- The discrete input of the loop checker agrees with a marked reference fiber.
The exchange matrix is the determinant pairing of the center charges, and the order
table is indexed by the numbered boundary components. -/
structure IsSignedLoopComparisonInput (p₀ : fiber[M₀,c₀])
    (E : SkewExchangeMatrix (Fin r)) (orders : Fin n → Fin r → ℤ) : Prop where
  /-- The entries of the seed matrix are the determinant pairings of the labeled rays. -/
  matrix_eq :
    E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays)
  /-- The order table is indexed by the original numbering of the surviving boundary. -/
  orders_eq : orders = p₀.numberedBoundaryOrders cartier[M₀]

namespace IsSignedLoopComparisonInput

variable {Q} {orders : Fin n → Fin r → ℤ}

/-- For signed loops of a primitive nef square-zero anticanonical cycle, equality of independent
X pullbacks over any field is equivalent to agreement of the inversion sign, transported
exchange-kernel basis columns, and the forward boundary label of component zero. The reference
contraction may have repeated centers. -/
theorem xPullback_eq_iff_signedLoopInvariants_eq {p₀ : fiber[M₀,c₀]}
    (h : Q.IsSignedLoopComparisonInput p₀ E orders) (k : Type*) [Field k]
    (hnodal₀ : p₀.IsNodalContraction)
    (hprim : IsPrimitive (Additive.ofMul classOf(cartier[M₀])))
    (hnef : (classOf(cartier[M₀])).IsNef ℂ (M₀.surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ M₀.surface classOf(cartier[M₀])
      classOf(cartier[M₀]) = 0)
    (w v : Word E E) {m : ℕ} (β : Module.Basis (Fin m) ℤ E.matrix.mulVecLin.ker) :
    w.xPullback k = v.xPullback k ↔
      w.signedLoopInvariants (fun j ↦ (β j : Fin r → ℤ)) orders (orders 0) =
        v.signedLoopInvariants (fun j ↦ (β j : Fin r → ℤ)) orders (orders 0) := by
  rw [h.orders_eq]
  have hE := h.matrix_eq
  obtain ⟨M, _, hM, hfamily⟩ :=
    Q.exists_marked_family_of_nodal_model (Q.hasNodalModel_of_contraction hnodal₀) cartier[M₀]
  subst M₀
  let P := Fan.rayChargeSeed b Q.rays hE
  choose p hp using fun c ↦ (hfamily c).1.exists_isNodalContraction cartier[M c]
  have hmark (c : Point Centers[r]) (j : ZMod n) :
      (M c).boundaryClass cartier[M c] j = (M c₀).boundaryClass cartier[M c₀] j :=
    congrFun (hfamily c).2 j
  exact GeometricRealization.xPullback_eq_iff_signedLoopInvariants_eq_of_presentation
    Q P (Fan.rayChargeSeed_form _ _ _) (Fan.rayChargeSeed_charge _ _ _)
    M p₀ hnodal₀ (fun c _ ↦ p c) (fun c _ ↦ hp c) hnef hsq hprim hmark
    Q.exists_cone_of_numbered_node w v β

/-- A certified exchange matrix and order table for a nodal contraction make the typed
integer comparison correct over every coefficient field. -/
theorem compareSignedLoops_eq_true_iff_xPullback_eq {p₀ : fiber[M₀,c₀]}
    (h : Q.IsSignedLoopComparisonInput p₀ E orders) (k : Type*) [Field k]
    (hnodal₀ : p₀.IsNodalContraction)
    (hprim : IsPrimitive (Additive.ofMul classOf(cartier[M₀])))
    (hnef : (classOf(cartier[M₀])).IsNef ℂ (M₀.surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ M₀.surface classOf(cartier[M₀])
      classOf(cartier[M₀]) = 0)
    (w v : Word E E) :
    E.compareSignedLoops orders w v = true ↔ w.xPullback k = v.xPullback k := by
  exact SkewExchangeMatrix.compareSignedLoops_eq_true_iff_xPullback_eq E k orders w v
    (h.xPullback_eq_iff_signedLoopInvariants_eq k hnodal₀ hprim hnef hsq w v)

/-- Decide equality of signed loop pullbacks from the certified discrete input. -/
def decidableXPullbackEq {p₀ : fiber[M₀,c₀]}
    (h : Q.IsSignedLoopComparisonInput p₀ E orders) (k : Type*) [Field k]
    (hnodal₀ : p₀.IsNodalContraction)
    (hprim : IsPrimitive (Additive.ofMul classOf(cartier[M₀])))
    (hnef : (classOf(cartier[M₀])).IsNef ℂ (M₀.surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ M₀.surface classOf(cartier[M₀])
      classOf(cartier[M₀]) = 0)
    (w v : Word E E) : Decidable (w.xPullback k = v.xPullback k) :=
  decidable_of_iff (E.compareSignedLoops orders w v = true)
    (h.compareSignedLoops_eq_true_iff_xPullback_eq k hnodal₀ hprim hnef hsq w v)

/-- On certified input from a nodal contraction, a Boolean result witnesses two loops and
is true exactly when their independent X pullbacks agree over the given field. -/
theorem compareSignedLoopLists_eq_some_iff_xPullback_eq {p₀ : fiber[M₀,c₀]}
    (h : Q.IsSignedLoopComparisonInput p₀ E orders) (k : Type*) [Field k]
    (hnodal₀ : p₀.IsNodalContraction)
    (hprim : IsPrimitive (Additive.ofMul classOf(cartier[M₀])))
    (hnef : (classOf(cartier[M₀])).IsNef ℂ (M₀.surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ M₀.surface classOf(cartier[M₀])
      classOf(cartier[M₀]) = 0)
    (gs hs : List (Generator (Fin r))) (result : Bool) :
    E.compareSignedLoopLists orders gs hs = some result ↔
      ∃ w v : Word E E, w.generators = gs ∧ v.generators = hs ∧
        (result = true ↔ w.xPullback k = v.xPullback k) :=
  SkewExchangeMatrix.compareSignedLoopLists_eq_some_iff_xPullback_eq E k orders
    (h.compareSignedLoops_eq_true_iff_xPullback_eq k hnodal₀ hprim hnef hsq) gs hs result

end IsSignedLoopComparisonInput

end QPainleve.SignedClusterModularGroup.CompleteToricPresentation
