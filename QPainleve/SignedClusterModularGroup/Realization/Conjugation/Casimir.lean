/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Center
public import QPainleve.Algebra.Cluster.Word.RationalMap
public import QPainleve.SignedClusterModularGroup.Realization.Presentation

import QPainleve.Algebra.Cluster.Word.Monomial
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective
import QPainleve.SignedClusterModularGroup.Realization.ChargeKernel.Transport
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber
import QPainleve.SignedClusterModularGroup.Realization.Orthogonal
import QPainleve.SignedClusterModularGroup.Realization.Presentation.Boundary

/-!
# Casimir coordinates for change of seed

In two marked toric presentations, the exchange-kernel transport of a connecting
word is the marked Picard pullback on boundary orthogonals multiplied by the
branch sign. The coordinates at either end are the negatives of the total
exceptional coefficients. This makes the connecting Picard action available in
the same integral bases used to compare relations between signed loops.

The comparison uses `GeometricRealization.exponentEquiv_eq_signed_picard_pullback`
for charge coordinates and Mathlib's `LinearMap.toMatrix` for both markings.
-/

public section

open AlgebraicGeometry CategoryTheory Module Quiver
open Scheme TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open QPainleve.CharacterTorus QPainleve.Cluster

namespace QPainleve.SignedClusterModularGroup

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "Orth[" H "," d "]" =>
  LinearMap.BilinForm.orthogonal H (Submodule.span ℤ (Set.range d))
local notation "K[" E "]" => LinearMap.ker (Matrix.mulVecLin (SkewExchangeMatrix.matrix E))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Basis (Fin 2) ℤ N} {L γ : Type} [AddCommGroup L]
  {r n : ℕ} [NeZero n] {B : LinearMap.BilinForm ℤ L}

local instance instNonemptyCasimirCones (Q : CompleteToricPresentation i b r L γ) :
    Nonempty Q.fan.cones := Q.complete.nonempty_cones

local instance instNeZeroCasimirBoundaryLength (Q : CompleteToricPresentation i b r L γ) :
    NeZero Q.length := Q.neZero

local instance instPrestableCasimirToricBoundary (Q : CompleteToricPresentation i b r L γ) :
    PrestableFamily ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme ↘ S) :=
  Q.prestable

local instance (Q : CompleteToricPresentation i b r L γ) :
    Q.fan.algebraicRealization.IsProjectiveOver ℂ :=
  Q.fan.isProjectiveOver_algebraicRealization_of_isComplete Q.regular Q.complete b

local instance (Q : CompleteToricPresentation i b r L γ) :
    SmoothOfRelativeDimension 2 (Q.fan.algebraicRealization ↘ S) := by
  have h : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  rw [← h, Q.fan.algebraicRealization_over]
  exact Q.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap Q.regular

local instance (Q : CompleteToricPresentation i b r L γ) :
    (LinearMap.BilinForm.prod (Chow.intersectionBilinForm ℂ Q.fan.algebraicRealization)
      (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ)))).IsPerfPair :=
  Q.isPerfPair_auxiliaryPicardForm

local notation "aux[" Q "]" =>
  LinearMap.BilinForm.prod
    (Chow.intersectionBilinForm ℂ (Fan.algebraicRealization (CompleteToricPresentation.fan Q)))
    (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ)))

namespace CompleteToricPresentation.HasNodalModel

variable {Q : CompleteToricPresentation i b r L γ} {E : SkewExchangeMatrix (Fin r)}
  {c : GeometricRealization.Point Centers[r]} {M : MarkedSurface ℂ n B XTor[r]}
  {d : ZMod n → L}

private theorem exists_chargeKernelEquiv (h : Q.HasNodalModel c M)
    (hd : M.boundaryClass M.isEffectiveCartier_boundaryIdeal = d) :
    ∃ e : Orth[B,d] ≃ₗ[ℤ] (Fan.rayChargeMap Q.rays).ker,
      ∀ x, Q.inclusion (e.symm x).val =
        ((Fan.boundaryOrthogonalEquivChargeKernel Q.regular Q.rays aux[Q]).symm x).val := by
  obtain ⟨_, e, he, _⟩ := h.existsUnique_chargeKernelEquiv M.isEffectiveCartier_boundaryIdeal hd
  exact ⟨e, he⟩

omit [NeZero n] in
private theorem exceptionalCoordinates_chargeKernelEquiv
    (e : Orth[B,d] ≃ₗ[ℤ] (Fan.rayChargeMap Q.rays).ker)
    (he : ∀ x, Q.inclusion (e.symm x).val =
      ((Fan.boundaryOrthogonalEquivChargeKernel Q.regular Q.rays aux[Q]).symm x).val)
    (x : Orth[B,d]) :
    (Q.inclusion x.val).2 = -(e x : Fin r → ℤ) := by
  simpa only [LinearEquiv.symm_apply_apply, Fan.boundaryOrthogonalEquivChargeKernel_symm_snd]
    using congrArg Prod.snd (he (e x))

/-- A reference nodal model supplies exchange-kernel coordinates in its marked boundary
orthogonal whenever the exchange and charge kernels agree. These coordinates are uniquely
determined by the total exceptional coefficients of the marked classes. -/
theorem existsUnique_exchangeKernelEquiv (h : Q.HasNodalModel c M)
    (hd : M.boundaryClass M.isEffectiveCartier_boundaryIdeal = d)
    (hker : K[E] = (Fan.rayChargeMap Q.rays).ker) :
    ∃! e : Orth[B,d] ≃ₗ[ℤ] K[E], ∀ x, (Q.inclusion x.val).2 = -(e x : Fin r → ℤ) := by
  obtain ⟨e, he⟩ := h.exists_chargeKernelEquiv hd
  let e' := e.trans (LinearEquiv.ofEq _ _ hker.symm)
  have h' (x : Orth[B,d]) : (Q.inclusion x.val).2 = -(e' x : Fin r → ℤ) := by
    simpa only [e', LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply]
      using exceptionalCoordinates_chargeKernelEquiv e he x
  exact ⟨e', h', fun f hf ↦ LinearEquiv.ext fun x ↦
    Subtype.ext (neg_injective ((hf x).symm.trans (h' x)))⟩

end CompleteToricPresentation.HasNodalModel

namespace GeometricRealization

variable {N₀ N₁ V₀ V₁ : Type} [AddCommGroup N₀] [AddCommGroup N₁]
  [AddCommGroup V₀] [AddCommGroup V₁] [Module ℝ V₀] [Module ℝ V₁]
  {i₀ : N₀ →+ V₀} {i₁ : N₁ →+ V₁} {b₀ : Basis (Fin 2) ℤ N₀} {b₁ : Basis (Fin 2) ℤ N₁}
  {L₀ L₁ γ₀ γ₁ : Type} [AddCommGroup L₀] [AddCommGroup L₁]
  {B₀ : LinearMap.BilinForm ℤ L₀} {B₁ : LinearMap.BilinForm ℤ L₁}
  {E₀ E₁ : SkewExchangeMatrix (Fin r)} {w : Word E₀ E₁}
  {M₀ : Point Centers[r] → MarkedSurface ℂ n B₀ XTor[r]}
  {M₁ : Point Centers[r] → MarkedSurface ℂ n B₁ XTor[r]}
  {C : Centers[r].left.PartialMap Centers[r].left}
  [IsDominant C.hom] [C.IsOver Centers[r].hom Centers[r].hom]
  (R : GeometricRealization (T₀ := Centers[r]) (T₁ := Centers[r]) M₀ M₁ C (w.xRationalMap ℂ))
  {d₀ : ZMod n → L₀} {d₁ : ZMod n → L₁}
  (hmark₀ : ∀ c j, (M₀ c).boundaryClass (M₀ c).isEffectiveCartier_boundaryIdeal j = d₀ j)
  (hmark₁ : ∀ c j, (M₁ c).boundaryClass (M₁ c).isEffectiveCartier_boundaryIdeal j = d₁ j)

variable (Q₀ : CompleteToricPresentation i₀ b₀ r L₀ γ₀)
  (Q₁ : CompleteToricPresentation i₁ b₁ r L₁ γ₁)
  (models₀ : ∀ p : CenterPoint (U := Centers[r]) (V := Centers[r]) C,
    let c := p ≫ PartialMap.domainSource (X := Centers[r]) (Y := Centers[r]) C
    Q₀.HasNodalModel c (M₀ c))
  (models₁ : ∀ p : CenterPoint (U := Centers[r]) (V := Centers[r]) C,
    let c := p ≫ PartialMap.domainTarget (X := Centers[r]) (Y := Centers[r]) C
    Q₁.HasNodalModel c (M₁ c))
  (hC : C.hom = C.domain.ι ≫ (w.centerIso ℂ).hom)

include models₀ models₁ hC

/-- In the unique exchange-kernel coordinates of the endpoint markings, the pullback of
a realized word is its Picard pullback times its branch sign. Both endpoint fans and
the integral coordinates of their Picard lattices can vary independently. -/
theorem exchangeKernelEquiv_toLinearMap_eq_smul_picard_pullback
    (e₀ : Orth[B₀,d₀] ≃ₗ[ℤ] K[E₀]) (e₁ : Orth[B₁,d₁] ≃ₗ[ℤ] K[E₁])
    (he₀ : ∀ x, (Q₀.inclusion x.val).2 = -(e₀ x : Fin r → ℤ))
    (he₁ : ∀ x, (Q₁.inclusion x.val).2 = -(e₁ x : Fin r → ℤ)) :
    w.exchangeKernelEquiv.toLinearMap =
      (R.orientation : ℤ) •
        ((e₁.symm.trans (R.boundaryOrthogonalEquiv hmark₀ hmark₁)).trans e₀).toLinearMap := by
  obtain ⟨p⟩ := nonempty_centerPoint C
  obtain ⟨f₀, hf₀⟩ := CompleteToricPresentation.HasNodalModel.exists_chargeKernelEquiv
    (models₀ p) (funext (hmark₀ _))
  obtain ⟨f₁, hf₁⟩ := CompleteToricPresentation.HasNodalModel.exists_chargeKernelEquiv
    (models₁ p) (funext (hmark₁ _))
  have h₀ (x : Orth[B₀,d₀]) : (f₀ x : Fin r → ℤ) = e₀ x :=
    neg_injective ((CompleteToricPresentation.HasNodalModel.exceptionalCoordinates_chargeKernelEquiv
      f₀ hf₀ x).symm.trans (he₀ x))
  have h₁ (x : Orth[B₁,d₁]) : (f₁ x : Fin r → ℤ) = e₁ x :=
    neg_injective ((CompleteToricPresentation.HasNodalModel.exceptionalCoordinates_chargeKernelEquiv
      f₁ hf₁ x).symm.trans (he₁ x))
  have htransport (x : Orth[B₁,d₁]) :=
    R.exponentEquiv_eq_signed_picard_pullback hmark₀ hmark₁ f₀ f₁ hf₀ hf₁ hC
      Q₀.rayOrder (fun j ↦ (Q₀.cycle.component_apply j).symm.trans (Q₀.component_eq j))
      (fun j ↦ (Q₀.positive j).1) Q₀.exists_cone_of_numbered_node
      Q₁.rayOrder (fun j ↦ (Q₁.cycle.component_apply j).symm.trans (Q₁.component_eq j))
      (fun j ↦ (Q₁.positive j).1) Q₁.exists_cone_of_numbered_node
      (fun q ↦ by
        obtain ⟨P, hP⟩ :=
          (models₀ q).exists_isNodalContraction (M₀ _).isEffectiveCartier_boundaryIdeal
        exact ⟨⟨P⟩, hP.genus_zero⟩)
      (fun q ↦ by
        obtain ⟨P, hP⟩ :=
          (models₁ q).exists_isNodalContraction (M₁ _).isEffectiveCartier_boundaryIdeal
        exact ⟨⟨P⟩, hP.genus_zero⟩) x
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simpa only [h₀, h₁, LinearEquiv.apply_symm_apply, Path.coe_exchangeKernelEquiv_apply,
    LinearEquiv.trans_apply, LinearEquiv.coe_coe, LinearMap.smul_apply, Units.smul_def,
    Submodule.coe_smul, map_zsmul] using htransport (e₁.symm x)

variable {κ₀ κ₁ : Type*}
  (β₀ : Basis κ₀ ℤ K[E₀]) (β₁ : Basis κ₁ ℤ K[E₁])

/-- The connecting word's integral transport matrix is the branch sign times the matrix of the
marked Picard pullback, in the boundary-orthogonal bases corresponding to the chosen exchange
kernel bases. The bases at the two ends may have different index types. -/
theorem toMatrix_exchangeKernelEquiv_eq_smul_picard [Finite κ₀] [Fintype κ₁] [DecidableEq κ₁]
    (e₀ : Orth[B₀,d₀] ≃ₗ[ℤ] K[E₀]) (e₁ : Orth[B₁,d₁] ≃ₗ[ℤ] K[E₁])
    (he₀ : ∀ x, (Q₀.inclusion x.val).2 = -(e₀ x : Fin r → ℤ))
    (he₁ : ∀ x, (Q₁.inclusion x.val).2 = -(e₁ x : Fin r → ℤ)) :
    LinearMap.toMatrix β₁ β₀ w.exchangeKernelEquiv.toLinearMap =
      (R.orientation : ℤ) • LinearMap.toMatrix (β₁.map e₁.symm) (β₀.map e₀.symm)
        (R.boundaryOrthogonalEquiv hmark₀ hmark₁).toLinearMap := by
  rw [R.exchangeKernelEquiv_toLinearMap_eq_smul_picard_pullback hmark₀ hmark₁
    Q₀ Q₁ models₀ models₁ hC e₀ e₁ he₀ he₁, map_zsmul,
    LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right]
  rfl

/-- The exchange-kernel matrix of the conjugated loop is obtained by conjugating with the
ordinary Picard pullback matrix. The two branch factors cancel, also for an odd connecting
word. The inverse matrix is computed from the inverse Picard pullback in the reverse bases. -/
theorem toMatrix_exchangeKernelEquiv_reverse_comp_comp_of_picard
    [Fintype κ₀] [Fintype κ₁] [DecidableEq κ₀] [DecidableEq κ₁]
    (e₀ : Orth[B₀,d₀] ≃ₗ[ℤ] K[E₀]) (e₁ : Orth[B₁,d₁] ≃ₗ[ℤ] K[E₁])
    (he₀ : ∀ x, (Q₀.inclusion x.val).2 = -(e₀ x : Fin r → ℤ))
    (he₁ : ∀ x, (Q₁.inclusion x.val).2 = -(e₁ x : Fin r → ℤ))
    (v : Word E₀ E₀) :
    let P := R.boundaryOrthogonalEquiv hmark₀ hmark₁
    LinearMap.toMatrix β₁ β₁ ((w.reverse.comp v).comp w).exchangeKernelEquiv.toLinearMap =
      LinearMap.toMatrix (β₀.map e₀.symm) (β₁.map e₁.symm) P.symm.toLinearMap *
        LinearMap.toMatrix β₀ β₀ v.exchangeKernelEquiv.toLinearMap *
        LinearMap.toMatrix (β₁.map e₁.symm) (β₀.map e₀.symm) P.toLinearMap := by
  dsimp only
  let e := (e₁.symm.trans (R.boundaryOrthogonalEquiv hmark₀ hmark₁)).trans e₀
  let η := R.orientation
  have hw (x : K[E₁]) : w.exchangeKernelEquiv x = η • e x :=
    LinearMap.congr_fun (R.exchangeKernelEquiv_toLinearMap_eq_smul_picard_pullback hmark₀ hmark₁
      Q₀ Q₁ models₀ models₁ hC e₀ e₁ he₀ he₁) x
  have hinv (x : K[E₀]) : w.exchangeKernelEquiv.symm x = e.symm (η⁻¹ • x) := by
    apply w.exchangeKernelEquiv.injective
    rw [LinearEquiv.apply_symm_apply, hw, LinearEquiv.apply_symm_apply, smul_inv_smul]
  have hcomp : ((w.reverse.comp v).comp w).exchangeKernelEquiv.toLinearMap =
      (e.symm.toLinearMap.comp v.exchangeKernelEquiv.toLinearMap).comp e.toLinearMap := by
    apply LinearMap.ext
    intro x
    simp only [Path.exchangeKernelEquiv_comp, Path.exchangeKernelEquiv_reverse,
      LinearEquiv.coe_coe, LinearEquiv.trans_apply, hw, hinv, LinearMap.comp_apply,
      LinearMapClass.map_smul_of_tower, smul_inv_smul]
  rw [hcomp, LinearMap.toMatrix_comp β₁ β₀ β₁, LinearMap.toMatrix_comp β₀ β₀ β₁]
  simp only [LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right, LinearEquiv.symm_symm]
  rfl

end GeometricRealization

end QPainleve.SignedClusterModularGroup
