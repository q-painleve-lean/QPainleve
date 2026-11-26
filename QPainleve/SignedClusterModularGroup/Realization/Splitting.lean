/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Presentation.Group
public import QPainleve.SignedClusterModularGroup.SignExtension

import QPainleve.SignedClusterModularGroup.Realization.Anticanonical
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber
import QPainleve.SignedClusterModularGroup.Realization.Reflection

/-!
# The sign extension of marked cluster modular groups

The marked Picard equivalence transports a boundary reflection to an involution
of the signed group of independent X point maps. Its section gives the
semidirect product of unsigned maps and signs with the corresponding Picard
conjugation action. For one or two boundary components, the pure sign change
gives a central involution and a direct product.
-/

public noncomputable section

open CategoryTheory MulOpposite Quiver
open QPainleve.Cluster QPainleve.SignedBoundaryIsometryGroup

namespace QPainleve.SignedClusterModularGroup

namespace CompleteToricPresentation

open AlgebraicGeometry QPainleve.CharacterTorus
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData
open GeometricRealization (Point)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {E : SkewExchangeMatrix (Fin r)} (Q : CompleteToricPresentation i b r L γ)
  (P : ChargeSeed E N) {c : Point Centers[r]} {M : MarkedSurface ℂ n B XTor[r]}

local notation "d" => M.boundaryClass M.isEffectiveCartier_boundaryIdeal
local notation "δ" => classOf(M.isEffectiveCartier_boundaryIdeal)
local notation "δL" => ∑ j, d j
local notation "Γ₀" => ClusterModularGroup ℂ E
local notation "Γₛ" => SignedClusterModularGroup ℂ E

local instance splittingFanNonempty : Nonempty Q.fan.cones := Q.complete.nonempty_cones
local instance splittingCycleNeZero : NeZero Q.length := Q.neZero
local instance splittingBoundaryPrestable :
    PrestableFamily ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme ↘ S) :=
  Q.prestable

local notation "χ[" t "]" => pointsEquiv ℂ _ (Subtype.mk (Over.Hom.left t) (Over.w t))
local notation "eval[" w "]" => op (signedClusterModularGroupMap ℂ E (End.of w))
local notation "models[" F "," C "]" =>
  GeometricRealization.HasToricTargetModels (T₀ := Centers[r]) (T₁ := Centers[r])
    (b := b) (s := Q.rays) (hΦ := Q.regular) (T := Q.cycle) (origin := Q.origin)
    (ι := Q.inclusion) (P₁ := F) (fun t ↦ χ[t]) C

local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))

/-- The signed Picard lift of a boundary reflection has order two and splits
the inversion-sign extension for a primitive nef square-zero anticanonical cycle.
The unsigned subgroup has index two. The signed and unsigned Picard equivalences
identify the resulting conjugation actions and semidirect products after inversion.
For a cycle of one or two components, the pure sign change lifts to a central
involution and multiplication gives the product with its cyclic subgroup.
The reference marked nodal model may have repeated centers. -/
theorem exists_signedPicardSplitting_of_nodal_model
    (hform : P.form = b.detDualEquiv.toLinearMap) (hcharge : P.charge = Fan.rayChargeMap Q.rays)
    (href : Q.HasNodalModel c M)
    (hnef : (δ).IsNef ℂ (M.surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ M.surface δ δ = 0)
    (hprim : IsPrimitive (Additive.ofMul δ)) :
    ∃ (F : Point Centers[r] → MarkedSurface ℂ n B XTor[r])
      (hmark : ∀ t j, (F t).boundaryClass (F t).isEffectiveCartier_boundaryIdeal j = d j),
      F c = M ∧ (∀ t, Q.HasNodalModel t (F t)) ∧
      ∃ (Θ : (Γₛ)ᵐᵒᵖ ≃* signedBoundaryIsometryGroup B d)
        (Θrot : (Γ₀)ᵐᵒᵖ ≃* boundaryRotationGroup B d) (hE : E.matrix ≠ 0)
        (hs : Function.Surjective (signedInversionSign ℂ E hE))
        (s : (signedInversionSignExtension ℂ E hE hs).Splitting),
        (∀ x, rotationInclusion B d (Θrot x) =
          Θ (MonoidHom.op (clusterModularGroupInclusion ℂ E) x)) ∧
        (∀ w : Word E E, sign B d (Θ eval[w]) = (-1 : ℤˣ) ^ w.inversionCount ∧
          ∀ {C : Centers[r].left.PartialMap Centers[r].left} [IsDominant C.hom]
            [C.IsOver Centers[r].hom Centers[r].hom]
            (R : GeometricRealization F F C (w.xRationalMap ℂ)), models[F,C] →
            Θ eval[w] = R.toSignedBoundaryIsometry d
              (fun t ↦ (F t).isEffectiveCartier_boundaryIdeal) hmark) ∧
        (clusterModularGroupInclusion ℂ E).range.index = 2 ∧
        orderOf (s (-1)) = 2 ∧
        (∃ (j₀ : ZMod n) (a : L) (g : signedBoundaryIsometryGroup B d)
          (hg : sign B d g = -1) (hgg : g * g = 1),
          let t := signSplitting B d g hg hgg
          let g₀ := (toIsometry B d g).val
          B a a = -1 ∧ (∀ j, B a (d j) = if j = j₀ then 1 else 0) ∧
          g₀ a = a ∧ g₀ δL = δL ∧ (∀ j, g₀ (d j) = d (2 * j₀ - j)) ∧
          (∀ x ∈ B.orthogonal (Submodule.span ℤ (Set.range d)), g₀ x = -x + (2 * B x a) • δL) ∧
          (∀ ε, Θ (op (s ε)) = t ε) ∧
          (∀ ε x, Θrot (op (s.conjAct ε x)⁻¹) = t.conjAct ε (Θrot (op x⁻¹))) ∧
          ∀ x : Γ₀ ⋊[s.conjAct] ℤˣ,
            Θ (op (s.semidirectProductMulEquiv x)⁻¹) =
              t.semidirectProductMulEquiv ⟨Θrot (op x.left⁻¹), x.right⟩) ∧
        ∀ hn : n ≤ 2, ∃ z : Γₛ,
          Θ (op z) = centralSign B d hn ∧ z ∈ Subgroup.center Γₛ ∧ orderOf z = 2 ∧
          ∃ e : Γ₀ × Subgroup.zpowers z ≃* Γₛ, ∀ (f : Γ₀) (u : Subgroup.zpowers z),
            e (f, u) = clusterModularGroupInclusion ℂ E f * u.val := by
  let : IsRationalOver (M.surface ↘ S) := href.isRationalOver
  have hcan := congrArg Inv.inv (href.canonicalClass M.isEffectiveCartier_boundaryIdeal)
  have hindex := Q.chargeIndex_ne_zero_of_anticanonical_cycle
    (M := fun _ ↦ M) href M.isEffectiveCartier_boundaryIdeal hnef hsq hcan hprim
  have hE := Q.exchangeMatrix_ne_zero_of_chargeIndex_ne_zero P hform hcharge hindex
  have hmatrix := P.matrix_eq.symm.trans (congrArg₂ chargeExchangeMatrix hform hcharge)
  obtain ⟨G, hFc⟩ :=
    Q.exists_picardGroupEquivs_of_nodal_model href hmatrix hprim hnef hsq
  obtain ⟨reflection⟩ := M.nonempty_cycleReversingInvolution hcan hnef hsq hprim
  let g := reflection.element
  have hg : sign B d g = -1 := by simp [g]
  have hgg : g * g = 1 := reflection.element_mul_self
  let Θ := G.signedEquiv
  let Θrot := G.unsignedEquiv
  have hsign (w : Word E E) := (sign_apply B _ _).trans (G.sign_signedEquiv_apply_word w)
  have hrot := G.rotationInclusion_unsignedEquiv_apply
  let t := signSplitting B d g hg hgg
  have hs := signedInversionSign_surjective_of_picardEquiv Θ hsign hE
    (sign_surjective B d g hg)
  let s := picardSignSplitting Θ hsign hE t
  have horder : orderOf (s (-1)) = 2 :=
    (orderOf_injective s.toMonoidHom s.rightInverse_rightHom.injective (-1)).trans (by simp)
  exact ⟨G.family, G.boundaryClass_eq, hFc, G.hasNodalModel, Θ, Θrot, hE, hs, s, hrot,
    fun w ↦ ⟨hsign w, G.signedEquiv_apply_word w⟩,
    index_range_clusterModularGroupInclusion ℂ E hE hs, horder,
    ⟨reflection.cut, reflection.cutClass, g, hg, hgg, reflection.cutClass_sq,
      reflection.pairing_cutClass, by simp [g], toIsometry_apply_sum B d g,
      fun j ↦ by simp [g],
      by simpa only [g, toIsometry_apply] using reflection.toIsometry_apply_orthogonal,
      fun ε ↦ by simp [s, t],
      picardSignSplitting_conjAct Θ hsign hE t Θrot hrot,
      picardSignSplitting_semidirectProductMulEquiv Θ hsign hE t Θrot hrot⟩,
    exists_central_involution_of_picardEquiv Θ hsign hE⟩

end CompleteToricPresentation

end QPainleve.SignedClusterModularGroup
