/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.LoopComparison.List
public import QPainleve.SignedClusterModularGroup.Realization.Presentation
public import QPainleve.SignedClusterModularGroup.Realization.Tropical

import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
import QPainleve.Algebra.Cluster.Word.CoefficientChange
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber
import QPainleve.SignedClusterModularGroup.Realization.Reflection
import QPainleve.SignedClusterModularGroup.Realization.Relations.PicardAction

/-!
# Deciding signed loop relations from a reference contraction

A single reference nodal contraction supplies the boundary orders and the moving
models used in the geometric criterion. The resulting integer comparison decides
equality of independent X pullbacks over any field for typed loops and lists of
generators.
The same certificate of the exchange matrix and order table serves both checkers.
The relation criterion uses the signed Picard comparison for the reference fiber.
-/

public section

open AlgebraicGeometry CategoryTheory MulOpposite Quiver
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
    (w v : Word E E) {κ : Type*} (β : Module.Basis κ ℤ E.matrix.mulVecLin.ker) :
    w.xPullback k = v.xPullback k ↔
      w.signedLoopInvariants (fun j ↦ (β j : Fin r → ℤ)) orders (orders 0) =
        v.signedLoopInvariants (fun j ↦ (β j : Fin r → ℤ)) orders (orders 0) := by
  rw [h.orders_eq]
  have href := Q.hasNodalModel_of_contraction hnodal₀
  have hne := href.exchangeMatrix_ne_zero h.matrix_eq hprim hnef hsq
  refine ⟨fun heq ↦ Path.signedLoopInvariants_eq_of_xPullback_eq hne heq β _ _, ?_⟩
  intro hinvariants
  obtain ⟨A⟩ := Q.nonempty_signedLoopPicardComparison_of_nodal_contraction
    p₀ hnodal₀ h.matrix_eq hprim hnef hsq
  let : M₀.surface.IsProjectiveOver ℂ := M₀.projective
  let : SmoothOfRelativeDimension 2 (M₀.surface ↘ S) := M₀.smooth
  let : IsRationalOver (M₀.surface ↘ S) := href.isRationalOver
  let : Module.Free ℤ (Additive (LineBundleClass M₀.surface)) :=
    M₀.surface.free_picard_of_isRationalOver ℂ
  let : Module.Finite ℤ (Additive (LineBundleClass M₀.surface)) :=
    M₀.surface.finite_picard_of_isRationalOver ℂ
  let : Module.Free ℤ L := Module.Free.of_equiv M₀.picardMarking.symm
  let : Module.Finite ℤ L := Module.Finite.of_surjective _ M₀.picardMarking.symm.surjective
  have heq := (A.signedEquiv_apply_word_eq_iff_signedLoopInvariants_eq M₀.isSymm
    M₀.isPerfPair_of_isRationalOver.nondegenerate
    (M₀.intersectionForm_boundaryClass cartier[M₀] hnef hsq)
    (M₀.boundaryClass_injective_of_nef_square_zero cartier[M₀] hnef hsq) w v β).mpr hinvariants
  apply Path.xPullback_eq_of_charZero k ℂ
  exact (signedClusterModularGroupMap_eq_iff ℂ E (End.of w) (End.of v)).mp
    (op_injective (A.identification.signedEquiv.injective heq))

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
