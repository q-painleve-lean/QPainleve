/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.ModularGroup
public import QPainleve.Algebra.Cluster.Word.Relations
public import QPainleve.SignedClusterModularGroup.Boundary.Restriction
public import QPainleve.SignedClusterModularGroup.Realization.Presentation
public import QPainleve.SignedClusterModularGroup.Realization.Tropical

import QPainleve.Geometry.Toric.Fan.ExchangeMatrix
import QPainleve.SignedClusterModularGroup.Realization.Endpoint.Casimir
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber
import QPainleve.SignedClusterModularGroup.Realization.Presentation.Group
import QPainleve.SignedClusterModularGroup.Realization.Relations.Presentation

/-!
# Integer loop invariants for the signed Picard equivalence

From a single nodal contraction, the signed Picard equivalence recovers the sign,
the transported Casimir columns, and the boundary label of a signed cluster loop.
The formula for the boundary action uses the inverse of the forward permutation,
as required for Picard pullback. The comparison combines
`CompleteToricPresentation.exists_picardGroupEquivs_of_nodal_model`,
`GeometricRealization.existsUnique_exchangeKernelEquiv_of_presentation`, and
`GeometricRealization.exists_realize_signed_loop_with_boundary_label`.
-/

public section

open AlgebraicGeometry CategoryTheory MulOpposite Quiver
open QPainleve.CharacterTorus QPainleve.Cluster QPainleve.SignedBoundaryIsometryGroup
open Scheme Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric

namespace QPainleve.SignedClusterModularGroup.CompleteToricPresentation

open GeometricRealization

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "χ[" c "]" => pointsEquiv ℂ _ (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "cartier[" M "]" => MarkedSurface.isEffectiveCartier_boundaryIdeal M
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "eval[" w "]" => op (signedClusterModularGroupMap ℂ _ (End.of w))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {E : SkewExchangeMatrix (Fin r)}
  (Q : CompleteToricPresentation i b r L γ)
  {c₀ : Point Centers[r]} {M₀ : MarkedSurface ℂ n B XTor[r]}

local instance instNonemptyPicardActionCones : Nonempty Q.fan.cones := Q.complete.nonempty_cones
local instance instNeZeroPicardActionBoundaryLength : NeZero Q.length := Q.neZero
local instance instPrestablePicardActionToricBoundary :
    PrestableFamily ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme ↘ S) :=
  Q.prestable

local notation "fiber[" M "," c "]" =>
  ContractedToricFiber b Q.rays Q.regular Q.cycle Q.origin Q.inclusion χ[c] M
local notation "K" => E.matrix.mulVecLin.ker
local notation "Models[" M "," C "]" =>
  HasToricTargetModels (T₀ := Centers[r]) (T₁ := Centers[r]) (b := b) (s := Q.rays)
    (hΦ := Q.regular) (T := Q.cycle) (origin := Q.origin) (ι := Q.inclusion) (P₁ := M)
    (fun z : Point Centers[r] ↦ χ[z]) C

/-- For the signed Picard equivalence of a primitive nef square-zero anticanonical cycle,
the computed sign is the branch sign, and the computed columns are the signed orthogonal
restriction in exchange-kernel coordinates. The boundary search returns the forward
image `j` of component zero, so the isometry pulls back component `l` to `η • (l - j)`.
The single reference contraction may be outside the noncollision open. The equivalence
gives the marked pullback of realizations with compatible target models and identifies
the unsigned subgroup with the sign kernel. -/
theorem exists_picardEquiv_signedLoopInvariants_of_nodal_contraction
    (p₀ : fiber[M₀,c₀]) (hnodal₀ : p₀.IsNodalContraction)
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (hprim : IsPrimitive (Additive.ofMul classOf(cartier[M₀])))
    (hnef : (classOf(cartier[M₀])).IsNef ℂ (M₀.surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ M₀.surface classOf(cartier[M₀])
      classOf(cartier[M₀]) = 0) :
    let d := M₀.boundaryClass cartier[M₀]
    let orders := p₀.numberedBoundaryOrders cartier[M₀]
    ∃ (M : Point Centers[r] → MarkedSurface ℂ n B XTor[r])
      (hD : ∀ z, D[M z].IsEffectiveCartier)
      (hmark : ∀ z j, (M z).boundaryClass (hD z) j = d j)
      (Θ : (SignedClusterModularGroup ℂ E)ᵐᵒᵖ ≃* signedBoundaryIsometryGroup B d)
      (e : B.orthogonal (Submodule.span ℤ (Set.range d)) ≃ₗ[ℤ] K),
      M c₀ = M₀ ∧ (∀ z, Q.HasNodalModel z (M z)) ∧
      (∀ w : Word E E,
        sign B d (Θ eval[w]) = (-1 : ℤˣ) ^ w.inversionCount ∧
          ∀ {C : Centers[r].left.PartialMap Centers[r].left} [IsDominant C.hom]
            [C.IsOver Centers[r].hom Centers[r].hom]
            (R : GeometricRealization M M C (w.xRationalMap ℂ)),
            Models[M,C] → Θ eval[w] = R.toSignedBoundaryIsometry d hD hmark) ∧
      (∀ x, (Q.inclusion x.val).2 = -(e x : Fin r → ℤ)) ∧
      ((sign B d).comp Θ.toMonoidHom).ker.unop = (clusterModularGroupInclusion ℂ E).range ∧
      ∀ (w : Word E E) {κ : Type*} (vectors : κ → K),
        let g := Θ eval[w]
        let η := sign B d g
        ∃ j : Fin n,
          w.signedLoopInvariants (fun k ↦ (vectors k : Fin r → ℤ)) orders (orders 0) =
            (η, Matrix.of (fun i k ↦
              ((LinearEquiv.autCongr e (signedOrthogonalRestriction B d g).val)
                (vectors k) : Fin r → ℤ) i), some j) ∧
          ∀ l, (toIsometry B d g).val (d l) =
            d (η • (l - (ZMod.finEquiv n).toEquiv j)) := by
  -- Use the same marked family for the Picard, Casimir, and boundary comparisons.
  obtain ⟨M, hD, hmark, Θ, _, hM, hfamily, hΘ, hsignker, -⟩ :=
    Q.exists_picardGroupEquivs_of_nodal_model (Q.hasNodalModel_of_contraction hnodal₀)
      hE hprim hnef hsq
  subst M₀
  dsimp only
  let d := (M c₀).boundaryClass cartier[M c₀]
  let P := Fan.rayChargeSeed b Q.rays hE
  have hform : P.form = b.detDualEquiv.toLinearMap := Fan.rayChargeSeed_form _ _ _
  have hcharge : P.charge = Fan.rayChargeMap Q.rays := Fan.rayChargeSeed_charge _ _ _
  obtain ⟨e, ⟨hcoords, hCasimir, -⟩, -⟩ := existsUnique_exchangeKernelEquiv_of_presentation
    Q P hform hcharge M (fun c ↦ cartier[M c]) (hfamily c₀) (fun c _ ↦ hfamily c)
    hnef hsq hprim d hmark Θ.toMonoidHom (fun w ↦ (hΘ (End.asHom w)).2)
  choose p hp using fun c ↦ (hfamily c).exists_isNodalContraction (cartier[M c])
  refine ⟨M, hD, hmark, Θ, e, rfl, hfamily, hΘ, hcoords, hsignker, fun w _ vectors ↦ ?_⟩
  obtain ⟨R, _, _, j, hfind, hboundary⟩ :=
    exists_realize_signed_loop_with_boundary_label Q P hform hcharge M p₀ hnodal₀
      (fun c _ ↦ p c) (fun c _ ↦ hp c) hnef hsq hprim hmark w (fun k ↦ vectors k)
  have hR := (hΘ w).2 R fun _ ↦ ⟨p _⟩
  have hsign := (hΘ w).1
  have haction := DFunLike.congr_fun hCasimir eval[w]
  simp only [exchangeKernelAction_op_loop, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    Subgroup.subtype_apply] at haction
  refine ⟨j, ?_, ?_⟩
  · refine Prod.ext ?_ (Prod.ext ?_ hfind)
    · simpa only [Path.signedLoopInvariants_def] using hsign.symm
    · rw [← haction]
      simp only [Path.signedLoopInvariants_def, Path.coe_exchangeKernelEquiv_apply]
  · simpa only [← hR, hsign] using hboundary

end QPainleve.SignedClusterModularGroup.CompleteToricPresentation
