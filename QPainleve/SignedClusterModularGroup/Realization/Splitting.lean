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

public section

open AlgebraicGeometry CategoryTheory MulOpposite
open QPainleve.CharacterTorus QPainleve.Cluster QPainleve.SignedBoundaryIsometryGroup
open Scheme Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric

namespace QPainleve.SignedClusterModularGroup.CompleteToricPresentation

open GeometricRealization (Point)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {E : SkewExchangeMatrix (Fin r)}

/-- A marked Picard identification with a chosen boundary reversal. Its reflection
determines the splitting on both the Picard lattice and the group of signed X maps. -/
@[ext]
structure SignedPicardSplitting (Q : CompleteToricPresentation i b r L γ)
    (E : SkewExchangeMatrix (Fin r)) (d : ZMod n → L) where
  /-- The signed Picard equivalence of the marked nodal family. -/
  identification : NodalPicardGroupIdentification (B := B) Q ℂ E d
  /-- The chosen signed reversal of the numbered boundary. -/
  reflection : CycleReversingInvolution B d
  /-- The exchange matrix is nonzero, so inversion parity descends to the group of X maps. -/
  matrix_ne_zero : E.matrix ≠ 0

namespace SignedPicardSplitting

variable {Q : CompleteToricPresentation i b r L γ} {d : ZMod n → L}
  (P : SignedPicardSplitting (B := B) Q E d)

local notation "Θ" => P.identification.signedEquiv
local notation "Θrot" => P.identification.unsignedEquiv
local notation "Γ₀" => ClusterModularGroup ℂ E

private theorem sign_apply_word (w : Word E E) :
    sign B d (Θ (op (signedClusterModularGroupMap ℂ E (End.of w)))) =
      (-1 : ℤˣ) ^ w.inversionCount := by
  rw [SignedBoundaryIsometryGroup.sign_apply, P.identification.sign_signedEquiv_apply_word]

/-- The inversion sign on signed point maps is surjective. -/
theorem signedInversionSign_surjective :
    Function.Surjective (signedInversionSign ℂ E P.matrix_ne_zero) :=
  signedInversionSign_surjective_of_picardEquiv Θ P.sign_apply_word P.matrix_ne_zero
    (sign_surjective B d P.reflection.element (by simp))

/-- The section of the inversion sign obtained by transporting the boundary reflection
through the marked Picard equivalence. -/
noncomputable def splitting :
    (signedInversionSignExtension ℂ E P.matrix_ne_zero
      P.signedInversionSign_surjective).Splitting :=
  picardSignSplitting Θ P.sign_apply_word P.matrix_ne_zero P.reflection.signSplitting

/-- The section has the signed Picard action of the lattice section at each sign. -/
@[simp]
theorem signedEquiv_apply_splitting (ε : ℤˣ) :
    Θ (op (P.splitting ε)) = P.reflection.signSplitting ε := by
  simp only [splitting, picardSignSplitting_apply, op_unop, MulEquiv.apply_symm_apply]

include P in
/-- The unsigned point maps form a subgroup of index two in the signed group. -/
theorem index_range_clusterModularGroupInclusion :
    (clusterModularGroupInclusion ℂ E).range.index = 2 :=
  Cluster.index_range_clusterModularGroupInclusion ℂ E P.matrix_ne_zero
    P.signedInversionSign_surjective

/-- The negative sign lifts to an involution of order two. -/
@[simp]
theorem orderOf_splitting_neg_one : orderOf (P.splitting (-1)) = 2 :=
  (orderOf_injective P.splitting.toMonoidHom P.splitting.rightInverse_rightHom.injective
    (-1)).trans (by simp)

/-- The unsigned Picard equivalence after inversion intertwines the actions of the two
sign sections on their respective kernels. -/
theorem unsignedEquiv_apply_splitting_conjAct (ε : ℤˣ) (x : Γ₀) :
    Θrot (op (P.splitting.conjAct ε x)⁻¹) =
      P.reflection.signSplitting.conjAct ε (Θrot (op x⁻¹)) :=
  picardSignSplitting_conjAct Θ P.sign_apply_word P.matrix_ne_zero P.reflection.signSplitting
    Θrot P.identification.rotationInclusion_unsignedEquiv_apply ε x

/-- Under signed Picard pullback after inversion, the semidirect product sends the
unsigned coordinate to its Picard rotation and preserves the sign. -/
theorem signedEquiv_apply_splitting_semidirectProductMulEquiv (x : Γ₀ ⋊[P.splitting.conjAct] ℤˣ) :
    Θ (op (P.splitting.semidirectProductMulEquiv x)⁻¹) =
      P.reflection.signSplitting.semidirectProductMulEquiv ⟨Θrot (op x.left⁻¹), x.right⟩ :=
  picardSignSplitting_semidirectProductMulEquiv Θ P.sign_apply_word P.matrix_ne_zero
    P.reflection.signSplitting Θrot P.identification.rotationInclusion_unsignedEquiv_apply x

end SignedPicardSplitting

variable (Q : CompleteToricPresentation i b r L γ)
  {c : Point Centers[r]} {M : MarkedSurface ℂ n B XTor[r]}

local notation "δ" => classOf(M.isEffectiveCartier_boundaryIdeal)

/-- One marked nodal model of a primitive nef square-zero anticanonical cycle supplies
a splitting of the sign extension through the signed Picard action. The model at the
reference center may have repeated points. -/
theorem exists_signedPicardSplitting_of_nodal_model
    (href : Q.HasNodalModel c M)
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (hprim : IsPrimitive (Additive.ofMul δ))
    (hnef : (δ).IsNef ℂ (M.surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ M.surface δ δ = 0) :
    ∃ P : SignedPicardSplitting (B := B) Q E (M.boundaryClass M.isEffectiveCartier_boundaryIdeal),
      P.identification.family c = M := by
  obtain ⟨G, hGc⟩ := Q.exists_picardGroupEquivs_of_nodal_model href hE hprim hnef hsq
  let : IsRationalOver (M.surface ↘ S) := href.isRationalOver
  have hmatrix_ne_zero := href.exchangeMatrix_ne_zero hE hprim hnef hsq
  have hcan := congrArg Inv.inv (href.canonicalClass M.isEffectiveCartier_boundaryIdeal)
  obtain ⟨reflection⟩ := M.nonempty_cycleReversingInvolution hcan hnef hsq hprim
  exact ⟨⟨G, reflection, hmatrix_ne_zero⟩, hGc⟩

end QPainleve.SignedClusterModularGroup.CompleteToricPresentation
