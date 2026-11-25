/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Specialization
public import QPainleve.SignedClusterModularGroup.Realization.Presentation.Group

import QPainleve.Algebra.Cluster.Word.SignExtension
import QPainleve.SignedClusterModularGroup.Realization.Anticanonical
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber
import QPainleve.SignedClusterModularGroup.Realization.Relations.Reference

/-!
# Field specialization for marked cluster modular groups

For a toric presentation of a primitive nef square-zero anticanonical cycle,
specializing the field of independent X coordinates preserves both cluster modular
groups. The integer invariants of a specialized loop are recovered from its X
pullback, and the marked relation criterion then recovers its complex pullback.
Consequently the Picard identifications over the complex numbers transport to
every coefficient field with their evaluation on loop representatives.

The comparison uses `Quiver.Path.signedLoopInvariants_eq_of_xPullback_eq` and
`CompleteToricPresentation.xPullback_eq_iff_signedLoopInvariants_eq_of_nodal_contraction`.
-/

public section

open AlgebraicGeometry CategoryTheory MulOpposite Quiver
open QPainleve.CharacterTorus QPainleve.Cluster QPainleve.SignedBoundaryIsometryGroup
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData

namespace QPainleve.SignedClusterModularGroup.CompleteToricPresentation

open GeometricRealization

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "χ[" c "]" => pointsEquiv ℂ _ (Subtype.mk (Over.Hom.left c) (Over.w c))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {E : SkewExchangeMatrix (Fin r)}
  (Q : CompleteToricPresentation i b r L γ)
  {c : Point Centers[r]} {M₀ : MarkedSurface ℂ n B XTor[r]}

local notation "Models[" M "," C "]" =>
  HasToricTargetModels (T₀ := Centers[r]) (T₁ := Centers[r]) (b := b) (s := Q.rays)
    (hΦ := Q.regular) (T := Q.cycle) (origin := Q.origin) (ι := Q.inclusion) (P₁ := M)
    (fun z : Point Centers[r] ↦ χ[z]) C

local notation "cartier" => M₀.isEffectiveCartier_boundaryIdeal
local notation "δ" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf cartier))⁻¹

variable (k : Type*) [Field k]

/-- The exchange matrix of a marked primitive nef square-zero anticanonical
cycle is nonzero over the exponent ring `ℤ`. -/
private theorem exchangeMatrix_ne_zero_of_nodal_model
    (href : Q.HasNodalModel c M₀)
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (hprim : IsPrimitive (Additive.ofMul δ))
    (hnef : LineBundleClass.IsNef ℂ (M₀.surface ↘ S) δ)
    (hsq : Chow.classIntersectionNumber ℂ M₀.surface δ δ = 0) :
    E.matrix ≠ 0 := by
  let : IsRationalOver (M₀.surface ↘ S) := href.isRationalOver
  let P : ChargeSeed E N :=
    ⟨b.detDualEquiv.toLinearMap, Fan.rayChargeMap Q.rays, b.detDualEquiv_self, hE.symm⟩
  have hindex := Q.chargeIndex_ne_zero_of_anticanonical_cycle (M := fun _ ↦ M₀)
    href cartier hnef hsq (congrArg Inv.inv (href.canonicalClass cartier)) hprim
  exact Q.exchangeMatrix_ne_zero_of_chargeIndex_ne_zero P rfl rfl hindex

/-- Specialization from complex coefficients is bijective on signed point maps of
a marked primitive nef square-zero anticanonical cycle. -/
theorem signedClusterModularGroupSpecialization_bijective_of_nodal_model
    (href : Q.HasNodalModel c M₀)
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (hprim : IsPrimitive (Additive.ofMul δ))
    (hnef : LineBundleClass.IsNef ℂ (M₀.surface ↘ S) δ)
    (hsq : Chow.classIntersectionNumber ℂ M₀.surface δ δ = 0) :
    Function.Bijective (signedClusterModularGroupSpecialization ℂ k E) := by
  refine ⟨?_, signedClusterModularGroupSpecialization_surjective ℂ k E⟩
  intro g g' hg
  obtain ⟨w, rfl⟩ := signedClusterModularGroupMap_surjective ℂ E g
  obtain ⟨v, rfl⟩ := signedClusterModularGroupMap_surjective ℂ E g'
  simp only [signedClusterModularGroupSpecialization_apply,
    signedClusterModularGroupMap_eq_iff] at hg ⊢
  let := Q.complete.nonempty_cones
  let := Q.prestable
  let := Q.neZero
  obtain ⟨p, hp⟩ := href.exists_isNodalContraction cartier
  let β := Module.finBasis ℤ E.matrix.mulVecLin.ker
  have hnonzero := Q.exchangeMatrix_ne_zero_of_nodal_model href hE hprim hnef hsq
  exact (Q.xPullback_eq_iff_signedLoopInvariants_eq_of_nodal_contraction
    ℂ p hp hE hprim hnef hsq w.asHom v.asHom β).mpr
      (Path.signedLoopInvariants_eq_of_xPullback_eq hnonzero hg β _ _)

/-- The Picard identifications of the opposite signed and unsigned cluster
modular groups hold over every field of X coefficients. They retain the
ordered branch sign and compute the complex geometric Picard pullback of
each loop. The unsigned inclusion corresponds to the boundary rotations. -/
theorem exists_picardGroupEquivs_over_field_of_nodal_model
    (href : Q.HasNodalModel c M₀)
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (hprim : IsPrimitive (Additive.ofMul δ))
    (hnef : LineBundleClass.IsNef ℂ (M₀.surface ↘ S) δ)
    (hsq : Chow.classIntersectionNumber ℂ M₀.surface δ δ = 0) :
    letI := Q.complete.nonempty_cones
    letI := Q.prestable
    letI := Q.neZero
    let d := M₀.boundaryClass M₀.isEffectiveCartier_boundaryIdeal
    ∃ (M : Point Centers[r] → MarkedSurface ℂ n B XTor[r])
      (hD : ∀ z, D[M z].IsEffectiveCartier)
      (hmark : ∀ z j, (M z).boundaryClass (hD z) j = d j)
      (Θ : (SignedClusterModularGroup k E)ᵐᵒᵖ ≃* signedBoundaryIsometryGroup B d)
      (Θrot : (ClusterModularGroup k E)ᵐᵒᵖ ≃* boundaryRotationGroup B d),
      M c = M₀ ∧ (∀ z, Q.HasNodalModel z (M z)) ∧
      (∀ (w : Word E E),
        sign B d (Θ (op (signedClusterModularGroupMap k E (End.of w)))) =
          (-1 : ℤˣ) ^ w.inversionCount ∧
        ∀ {C : Centers[r].left.PartialMap Centers[r].left} [IsDominant C.hom]
          [C.IsOver Centers[r].hom Centers[r].hom]
          (R : GeometricRealization M M C (w.xRationalMap ℂ)),
          Models[M,C] →
          Θ (op (signedClusterModularGroupMap k E (End.of w))) =
            R.toSignedBoundaryIsometry d hD hmark) ∧
      ((sign B d).comp Θ.toMonoidHom).ker.unop = (clusterModularGroupInclusion k E).range ∧
      (∀ x, rotationInclusion B d (Θrot x) =
        Θ (MonoidHom.op (clusterModularGroupInclusion k E) x)) := by
  let := Q.complete.nonempty_cones
  let := Q.prestable
  let := Q.neZero
  obtain ⟨M, hD, hmark, Θ, Θrot, hM, hmodels, hΘ, _, hinc⟩ :=
    Q.exists_picardGroupEquivs_of_nodal_model href hE hprim hnef hsq
  have hbij := Q.signedClusterModularGroupSpecialization_bijective_of_nodal_model
    k href hE hprim hnef hsq
  let signedEquiv := MulEquiv.ofBijective (signedClusterModularGroupSpecialization ℂ k E) hbij
  let unsignedEquiv := MulEquiv.ofBijective (clusterModularGroupSpecialization ℂ k E)
    ⟨clusterModularGroupSpecialization_injective_of_signed ℂ k E hbij.1,
      clusterModularGroupSpecialization_surjective ℂ k E⟩
  have hsword (w : End (Prefunctor.obj (Paths.of (SkewExchangeMatrix (Fin r))) E)) :
      signedEquiv.symm (signedClusterModularGroupMap k E w) = signedClusterModularGroupMap ℂ E w :=
    signedEquiv.symm_apply_eq.mpr (signedClusterModularGroupSpecialization_apply ℂ k E _).symm
  have hcomm (g : ClusterModularGroup k E) :
      signedEquiv.symm (clusterModularGroupInclusion k E g) =
        clusterModularGroupInclusion ℂ E (unsignedEquiv.symm g) := by
    apply signedEquiv.injective
    rw [MulEquiv.apply_symm_apply]
    exact ((signedClusterModularGroupSpecialization_inclusion ℂ k E (unsignedEquiv.symm g)).trans
      (congrArg (clusterModularGroupInclusion k E) (unsignedEquiv.apply_symm_apply g))).symm
  have hsop (g : (SignedClusterModularGroup k E)ᵐᵒᵖ) :
      MulEquiv.op signedEquiv.symm g = op (signedEquiv.symm g.unop) := rfl
  have huop (g : (ClusterModularGroup k E)ᵐᵒᵖ) :
      MulEquiv.op unsignedEquiv.symm g = op (unsignedEquiv.symm g.unop) := rfl
  refine ⟨M, hD, hmark, (MulEquiv.op signedEquiv.symm).trans Θ,
    (MulEquiv.op unsignedEquiv.symm).trans Θrot, hM, hmodels, ?_, ?_, ?_⟩
  · intro w
    simpa only [MulEquiv.trans_apply, hsop, unop_op, hsword] using hΘ w
  · have hnonzero := Q.exchangeMatrix_ne_zero_of_nodal_model href hE hprim hnef hsq
    rw [range_clusterModularGroupInclusion k E hnonzero]
    ext g
    obtain ⟨w, rfl⟩ := signedClusterModularGroupMap_surjective k E g
    have hsign :
        sign B (M₀.boundaryClass cartier) (Θ (op (signedClusterModularGroupMap ℂ E w))) =
          (-1 : ℤˣ) ^ w.asHom.inversionCount := (hΘ w.asHom).1
    simp only [Subgroup.mem_unop, MonoidHom.mem_ker, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply, hsop, unop_op, hsword,
      signedInversionSign_apply, hsign]
  · intro g
    simpa only [MulEquiv.trans_apply, hsop, huop, MonoidHom.op_apply_apply,
      Function.comp_apply, unop_op, hcomm] using hinc (MulEquiv.op unsignedEquiv.symm g)

end QPainleve.SignedClusterModularGroup.CompleteToricPresentation
