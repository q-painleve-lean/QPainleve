/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Relations
public import QPainleve.SignedClusterModularGroup.Realization.Presentation.Casimir
public import QPainleve.SignedClusterModularGroup.Realization.Tropical

import QPainleve.Geometry.Toric.Fan.ExchangeMatrix
import QPainleve.SignedClusterModularGroup.BoundaryCycle
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber
import QPainleve.SignedClusterModularGroup.Realization.Presentation.Group
import QPainleve.SignedClusterModularGroup.Realization.Relations.Presentation

/-!
# Integer loop invariants for the signed Picard equivalence

From a single nodal contraction, the signed Picard equivalence recovers the sign,
the transported Casimir columns, and the boundary label of a signed cluster loop.
The formula for the boundary action uses the inverse of the forward permutation,
as required for Picard pullback. Both the Casimir and boundary formulas use
the same signed Picard equivalence of the marked family.
-/

public section

open AlgebraicGeometry CategoryTheory MulOpposite Quiver
open QPainleve.CharacterTorus QPainleve.Cluster QPainleve.SignedBoundaryIsometryGroup
open Scheme Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric

namespace QPainleve.SignedClusterModularGroup.CompleteToricPresentation

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]

open GeometricRealization

local notation "S" => Spec (CommRingCat.of k₀)
local notation "Centers[" r "]" => Over.mk (structureMap k₀ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme k₀ (Fin r →₀ ℤ)
local notation "χ[" c "]" => pointsEquiv k₀ _ (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "cartier[" M "]" => MarkedSurface.isEffectiveCartier_boundaryIdeal M
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "eval[" w "]" => op (signedClusterModularGroupMap k₀ _ (End.of w))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {E : SkewExchangeMatrix (Fin r)}
  (Q : CompleteToricPresentation k₀ i b r L γ)
  {c₀ : Point (Over.mk (QPainleve.CharacterTorus.structureMap k₀ (Fin r →
    ℤ)))} {M₀ : MarkedSurface k₀ n B (QPainleve.CharacterTorus.scheme k₀ (Fin r →₀ ℤ))}

local instance instNonemptyPicardActionCones : Nonempty Q.fan.cones := Q.complete.nonempty_cones
local instance instNeZeroPicardActionBoundaryLength : NeZero Q.length := Q.neZero
local instance instPrestablePicardActionToricBoundary :
    PrestableFamily ((Q.fan.toricBoundaryIdeal k₀ Q.complete.nonempty_cones).subscheme ↘ S) :=
  Q.prestable

local notation "fiber[" M "," c "]" =>
  ContractedToricFiber b Q.rays Q.regular Q.cycle Q.origin Q.inclusion χ[c] M
local notation "K" => E.matrix.mulVecLin.ker
local notation "classes[" M "]" => MarkedSurface.boundaryClass M cartier[M]

/-- The signed Picard and Casimir identifications for a specified reference fiber,
together with the forward tropical boundary search and its Picard pullback formula. -/
@[ext]
structure SignedLoopPicardComparison (p₀ : fiber[M₀,c₀])
    (E : SkewExchangeMatrix (Fin r)) where
  /-- The marked family and signed Picard equivalence. -/
  identification : Q.NodalPicardGroupIdentification (B := B) k₀ E classes[M₀]
  /-- The marked family has the specified reference fiber. -/
  family_center : identification.family c₀ = M₀
  /-- The signed comparison with exchange-kernel transport. -/
  casimir : Q.CasimirActionComparison E B classes[M₀]
  /-- The Casimir comparison uses the same Picard pullback as the marked family. -/
  casimir_picardEquiv : casimir.picardEquiv = identification.signedEquiv
  /-- The tropical search yields the forward label of component zero. The corresponding
  Picard pullback acts by the inverse signed boundary permutation. -/
  boundaryLabel_spec (w : Word E E) :
    let orders := p₀.numberedBoundaryOrders cartier[M₀]
    let d := classes[M₀]
    let g := identification.signedEquiv eval[w]
    ∃ j : Fin n, w.tropicalBoundaryLabel orders (orders 0) = some j ∧
      ∀ l, (toIsometry B d g).val (d l) =
        d (sign B d g • (l - (ZMod.finEquiv n).toEquiv j))

namespace SignedLoopPicardComparison

attribute [simp] family_center casimir_picardEquiv

variable {Q}

/-- The signed Picard equivalence recovers all three computed integer invariants.
The kernel columns are in ambient exponent coordinates and the boundary label
is the forward image of component zero. -/
theorem signedLoopInvariants_eq {p₀ : fiber[M₀,c₀]} (A : Q.SignedLoopPicardComparison p₀ E)
    (w : Word E E) {κ : Type*} (vectors : κ → K) :
    let orders := p₀.numberedBoundaryOrders cartier[M₀]
    let d := classes[M₀]
    let g := A.identification.signedEquiv eval[w]
    let η := sign B d g
    ∃ j : Fin n,
      w.signedLoopInvariants (fun k ↦ (vectors k : Fin r → ℤ)) orders (orders 0) =
        ⟨η, Matrix.of (fun i k ↦
          (LinearEquiv.autCongr A.casimir.exchangeKernelEquiv
            (signedOrthogonalRestriction B d g).val (vectors k) : Fin r → ℤ) i), some j⟩ ∧
        ∀ l, (toIsometry B d g).val (d l) = d (η • (l - (ZMod.finEquiv n).toEquiv j)) := by
  dsimp only
  obtain ⟨j, hlabel, hboundary⟩ := A.boundaryLabel_spec w
  have haction := A.casimir.exchangeKernelEquiv_eq_autCongr w
  rw [A.casimir_picardEquiv] at haction
  refine ⟨j, SignedLoopInvariants.ext ?_ ?_ ?_, hboundary⟩
  · simp only [Path.signedLoopInvariants_sign, SignedBoundaryIsometryGroup.sign_apply,
      A.identification.sign_signedEquiv_apply_word]
  · simp only [Path.signedLoopInvariants_kernelColumns, ← Path.coe_exchangeKernelEquiv_apply,
      haction]
  · simpa only [Path.signedLoopInvariants_boundaryLabel] using hlabel

/-- Equality of the marked signed Picard actions is equivalent to equality of the
integer loop invariants. The sign still distinguishes the two branch orientations
when there are only one or two boundary components. -/
theorem signedEquiv_apply_word_eq_iff_signedLoopInvariants_eq {p₀ : fiber[M₀,c₀]}
    (A : Q.SignedLoopPicardComparison p₀ E)
    [Module.Free ℤ L] [Module.Finite ℤ L]
    (hSymm : B.IsSymm) (hB : B.Nondegenerate)
    (hGram : ∀ j l, B (classes[M₀] j) (classes[M₀] l) =
      (-2 : ℤ) * (if j = l then 1 else 0) + (if l = j + 1 then 1 else 0) +
        (if l = j - 1 then 1 else 0))
    (hD : Function.Injective classes[M₀])
    (w v : Word E E) {κ : Type*} (β : Module.Basis κ ℤ K) :
    let orders := p₀.numberedBoundaryOrders cartier[M₀]
    A.identification.signedEquiv eval[w] = A.identification.signedEquiv eval[v] ↔
      w.signedLoopInvariants (fun j ↦ (β j : Fin r → ℤ)) orders (orders 0) =
        v.signedLoopInvariants (fun j ↦ (β j : Fin r → ℤ)) orders (orders 0) := by
  intro orders
  let d := classes[M₀]
  let Θ := A.identification.signedEquiv
  obtain ⟨j, hj, hboundary⟩ := A.boundaryLabel_spec w
  obtain ⟨l, hl, hboundary'⟩ := A.boundaryLabel_spec v
  have atZero (u : Word E E) (a : Fin n)
      (hu : ∀ x, (toIsometry B d (Θ eval[u])).val (d x) =
        d (sign B d (Θ eval[u]) • (x - ZMod.finEquiv n a))) :
      (toIsometry B d (Θ eval[u])).val (d (ZMod.finEquiv n a)) = d 0 := by
    simpa only [sub_self, smul_zero] using hu (ZMod.finEquiv n a)
  have hsign (u : Word E E) :
      sign B d (Θ eval[u]) = (-1) ^ u.inversionCount := by
    simpa only [SignedBoundaryIsometryGroup.sign_apply]
      using A.identification.sign_signedEquiv_apply_word u
  have hres (u : Word E E) :
      u.exchangeKernelEquiv = LinearEquiv.autCongr A.casimir.exchangeKernelEquiv
        (signedOrthogonalRestriction B d (Θ eval[u])).val := by
    simpa only [A.casimir_picardEquiv] using A.casimir.exchangeKernelEquiv_eq_autCongr u
  rw [eq_iff_of_boundary_pullback hSymm hB.1 (BoundaryCycle.span_sup_orthogonal_rat hGram hSymm hB)
    hD (atZero w j hboundary) (atZero v l hboundary')]
  rw [Path.signedLoopInvariants_eq_iff, hsign w, hsign v, hres w, hres v,
    (LinearEquiv.autCongr A.casimir.exchangeKernelEquiv).injective.eq_iff,
    Subtype.coe_injective.eq_iff, hj, hl, Option.some.injEq, (ZMod.finEquiv n).injective.eq_iff]

end SignedLoopPicardComparison

/-- A reference nodal contraction of a primitive nef square-zero anticanonical cycle
supplies the Picard and Casimir identifications and the complete integer invariant formula.
The reference center may lie outside the noncollision open. -/
theorem nonempty_signedLoopPicardComparison_of_nodal_contraction
    [Uncountable k₀] [NeZero (2 : k₀)]
    (p₀ : fiber[M₀,c₀]) (hnodal₀ : p₀.IsNodalContraction)
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (hprim : IsPrimitive (Additive.ofMul classOf(cartier[M₀])))
    (hnef : (classOf(cartier[M₀])).IsNef k₀ (M₀.surface ↘ S))
    (hsq : Chow.classIntersectionNumber k₀ M₀.surface classOf(cartier[M₀])
      classOf(cartier[M₀]) = 0) :
    Nonempty (Q.SignedLoopPicardComparison p₀ E) := by
  obtain ⟨⟨M, hmodels, hmark, Θ, hsign, happly, hker⟩, hM⟩ :=
    Q.exists_picardGroupEquivs_of_nodal_model
      (Q.hasNodalModel_of_contraction hnodal₀) hE hprim hnef hsq
  -- The identification is indexed by the boundary classes of the reference fiber.
  -- Substitute the fiber before reassembling the identification at those classes.
  dsimp only at hM
  subst M₀
  let G : Q.NodalPicardGroupIdentification (B := B) k₀ E classes[M c₀] :=
    ⟨M, hmodels, hmark, Θ, hsign, happly, hker⟩
  obtain ⟨A, hA⟩ := G.exists_casimirActionComparison (c := c₀) hE hprim hnef hsq
  choose p hp using fun c ↦ (hmodels c).exists_isNodalContraction cartier[M c]
  let P := Fan.rayChargeSeed b Q.rays hE
  have hform := Fan.rayChargeSeed_form b Q.rays hE
  have hcharge := Fan.rayChargeSeed_charge b Q.rays hE
  refine ⟨⟨G, rfl, A, hA, fun w ↦ ?_⟩⟩
  obtain ⟨R, _, _, j, hlabel, hboundary⟩ :=
    exists_realize_signed_loop_with_boundary_label Q P hform hcharge M p₀ hnodal₀
      (fun c _ ↦ p c) (fun c _ ↦ hp c) hnef hsq hprim hmark w
  have hR : G.signedEquiv eval[w] =
      R.toSignedBoundaryIsometry classes[M c₀] (fun c ↦ cartier[M c]) hmark :=
    G.signedEquiv_apply_word w R (fun _ ↦ ⟨p _⟩)
  refine ⟨j, hlabel, fun l ↦ ?_⟩
  simpa only [← hR, SignedBoundaryIsometryGroup.sign_apply, G.sign_signedEquiv_apply_word]
    using hboundary l

end QPainleve.SignedClusterModularGroup.CompleteToricPresentation
