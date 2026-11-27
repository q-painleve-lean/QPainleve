/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.MarkedComparison
public import QPainleve.SignedClusterModularGroup.Realization.Presentation

import QPainleve.Geometry.Toric.Fan.Picard.Contraction.ChargeKernel
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber
import QPainleve.SignedClusterModularGroup.Realization.Presentation.Boundary

/-!
# Charge coordinates in a fixed Picard marking

The integral comparison of a nodal contraction with its ordered toric model
identifies the boundary orthogonal in the fixed Picard lattice with the charge
kernel. The inverse comparison is characterized by its image in the toric and
total exceptional coordinates. Thus the comparison is independent of the center
and of the nodal tower used to construct it.

When the charge and exchange kernels agree, the negative total exceptional
coefficients give the exchange-kernel coordinates in the same marking.

The construction uses `Fan.existsUnique_contractedPicardMarkingOfRaySet_chargeKernelEquiv`.
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative
open QPainleve.BlowupTower TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open QPainleve.CharacterTorus QPainleve.Cluster
open Scheme Scheme.IdealSheafData LineBundleClass

namespace QPainleve.SignedClusterModularGroup

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]

local notation "S" => Spec (CommRingCat.of k₀)
local notation "Xtor[" r "]" => Spec (CommRingCat.of (LaurentRing k₀ (Fin r)))
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))

namespace ContractedToricFiber

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones]
  {r n m : ℕ} [NeZero n] [NeZero m]
  {L : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {P : MarkedSurface k₀ n B (QPainleve.CharacterTorus.scheme k₀ (Fin r →₀ ℤ))} {b : Module.Basis
    (Fin 2) ℤ N}
  {s : Fin r → Φ.Ray} {hΦ : Φ.IsRegular}
  [PrestableFamily ((Φ.toricBoundaryIdeal k₀ h₀).subscheme ↘ Spec (.of k₀))]
  {γ : Type*} {a : γ → ((Φ.toricBoundaryIdeal k₀ h₀).subscheme ↘ Spec (.of k₀)).smoothLocus}
  {T : NodalCycleNumbering a m} {o : ZMod m}
  {J : L →ₗ[ℤ] Additive (LineBundleClass (Φ.finiteFanScheme k₀)) × (Fin r → ℤ)}
  {c : Multiplicative (Fin r → ℤ) →* k₀ˣ}
  (p : ContractedToricFiber b s hΦ T o J c P)

local notation "K" => LinearMap.ker (Fan.rayChargeMap s)
local notation "centers" => (fun j : Fin r ↦ c (ofAdd (Pi.single j 1)))
local notation "Model" => Fan.internalBlowupTower k₀ b s centers
local notation "Btor" => LinearMap.BilinForm.prod
  (Chow.intersectionBilinForm k₀ (Φ.finiteFanScheme k₀))
  (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ)))

variable [(Φ.finiteFanScheme k₀).IsProjectiveOver k₀]
  [SmoothOfRelativeDimension 2 ((Φ.finiteFanScheme k₀) ↘ Spec (.of k₀))]
variable [LinearMap.IsPerfPair ((Chow.intersectionBilinForm k₀ (Φ.finiteFanScheme k₀)).prod
  (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ))))] [B.IsPerfPair]

include p in
private theorem exists_markedBoundaryOrthogonalEquivChargeKernel (hp : p.IsNodalContraction)
    (hD : D[P].IsEffectiveCartier) {d : ZMod n → L} (hd : P.boundaryClass hD = d) :
    ∃ e : B.orthogonal (Submodule.span ℤ (Set.range d)) ≃ₗ[ℤ] K,
      ∀ x : K, J (e.symm x).val =
        ((Fan.boundaryOrthogonalEquivChargeKernel k₀ hΦ s Btor).symm x).val := by
  classical
  let : P.surface.IsProjectiveOver k₀ := P.projective
  let : SmoothOfRelativeDimension 2 (P.surface ↘ S) := P.smooth
  let : (Chow.intersectionBilinForm k₀ P.surface).IsPerfPair := P.isPerfPair_intersectionForm
  obtain ⟨l, Y, W, hW, u, hu⟩ := hp.exists_tower
  have hproj : u.inv ≫ W.toBase ≫ (P.surface ↘ S) =
      Model.2.toTower.toBase ≫ (Φ.finiteFanSchemeToSpec k₀) := by
    rw [← Category.assoc, hu, p.projection_over]
  have hsupport : (D[P].comap (u.inv ≫ W.toBase)).support =
      Model.2.boundaryι.ker.support := hu ▸ p.support_comap
  let R := Fan.contractedRaySet k₀ hΦ b s centers hW u.symm hsupport
  obtain ⟨_, q, hq, _⟩ :=
    Fan.existsUnique_contractedPicardMarkingOfRaySet_chargeKernelEquiv k₀ hΦ b s centers
      hW u.symm hproj hsupport R rfl
  let f := q.trans (LinearEquiv.ofEq _ _ (D[P].boundaryOrthogonal_def k₀).symm)
  let g := P.boundaryOrthogonalMarking hD
  let e := ((LinearEquiv.ofEq _ _ (by rw [hd])).trans g).trans f.symm
  have he (x : K) : J (e.symm x).val =
      ((Fan.boundaryOrthogonalEquivChargeKernel k₀ hΦ s Btor).symm x).val := by
    have hclass : P.picardMarking (e.symm x).val = (q x).val := by
      simp only [e, g, f, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
        LinearEquiv.symm_symm, LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply]
      rw [← P.coe_boundaryOrthogonalMarking_apply hD, LinearEquiv.apply_symm_apply,
        LinearEquiv.coe_ofEq_apply]
    have hcoords := congrArg Subtype.val (hq x)
    rw [← ofMul_toMul (q x).val,
      Fan.coe_contractedPicardMarkingOfRaySet_symm_apply k₀ hΦ b s centers
        hW u.symm hproj hsupport R rfl,
      Fan.coe_contractedChargeKernelHom_apply k₀ hΦ s Btor, Iso.symm_hom, hu] at hcoords
    exact (p.marked_pullback (e.symm x).val).symm.trans
      (by simpa only [hclass, ofMul_toMul] using hcoords)
  exact ⟨e, he⟩

/-- The charge coordinates of the boundary orthogonal in a fixed Picard marking.
The inverse preserves the toric and total exceptional coordinates of a charge relation. -/
noncomputable def markedBoundaryOrthogonalEquivChargeKernel (hp : p.IsNodalContraction)
    (hD : D[P].IsEffectiveCartier) {d : ZMod n → L} (hd : P.boundaryClass hD = d) :
    B.orthogonal (Submodule.span ℤ (Set.range d)) ≃ₗ[ℤ] K :=
  (p.exists_markedBoundaryOrthogonalEquivChargeKernel hp hD hd).choose

/-- The inverse charge class has the coordinates of the same relation on the internal blowup
model. -/
@[simp]
theorem markedBoundaryOrthogonalEquivChargeKernel_symm_apply (hp : p.IsNodalContraction)
    (hD : D[P].IsEffectiveCartier) {d : ZMod n → L} (hd : P.boundaryClass hD = d) (x : K) :
    J ((p.markedBoundaryOrthogonalEquivChargeKernel hp hD hd).symm x).val =
      ((Fan.boundaryOrthogonalEquivChargeKernel k₀ hΦ s Btor).symm x).val :=
  (p.exists_markedBoundaryOrthogonalEquivChargeKernel hp hD hd).choose_spec x

/-- The charge coordinates are the negatives of the total exceptional coefficients. -/
@[simp]
theorem coe_markedBoundaryOrthogonalEquivChargeKernel_apply (hp : p.IsNodalContraction)
    (hD : D[P].IsEffectiveCartier) {d : ZMod n → L} (hd : P.boundaryClass hD = d)
    (x : B.orthogonal (Submodule.span ℤ (Set.range d))) :
    (p.markedBoundaryOrthogonalEquivChargeKernel hp hD hd x : Fin r → ℤ) = -(J x.val).2 := by
  let e := p.markedBoundaryOrthogonalEquivChargeKernel hp hD hd
  simpa only [e, LinearEquiv.symm_apply_apply, Fan.boundaryOrthogonalEquivChargeKernel_symm_snd,
    neg_neg] using (congrArg (fun y ↦ -y.2)
      (p.markedBoundaryOrthogonalEquivChargeKernel_symm_apply hp hD hd (e x))).symm

end ContractedToricFiber

namespace CompleteToricPresentation

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {Q : CompleteToricPresentation k₀ i b r L γ}
  {c : GeometricRealization.Point (Over.mk (structureMap k₀ (Fin r → ℤ)))}
  {M : MarkedSurface k₀ n B (scheme k₀ (Fin r →₀ ℤ))}

local instance instChargeCoordinateNonemptyCones : Nonempty Q.fan.cones :=
  Q.complete.nonempty_cones

local notation "Aux" => LinearMap.BilinForm.prod
  (Chow.intersectionBilinForm k₀ (Q.fan.finiteFanScheme k₀))
  (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ)))

local notation "Orth[" d "]" => B.orthogonal (Submodule.span ℤ (Set.range d))

/-- A nodal model identifies the boundary orthogonal of the marking with the charge kernel. -/
noncomputable def HasNodalModel.chargeKernelEquiv (h : Q.HasNodalModel c M)
    (hD : D[M].IsEffectiveCartier) {d : ZMod n → L} (hd : M.boundaryClass hD = d) :
    Orth[d] ≃ₗ[ℤ] (Fan.rayChargeMap Q.rays).ker := by
  let := Q.prestable
  let := Q.neZero
  let := Q.fan.isProjectiveOver_finiteFanScheme_of_isComplete k₀ Q.regular Q.complete b
  let := Q.smoothOfRelativeDimension_fan
  let : M.surface.IsProjectiveOver k₀ := M.projective
  let : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
  let : IsRationalOver (M.surface ↘ S) := h.isRationalOver
  let : B.IsPerfPair := M.isPerfPair_of_isRationalOver
  let := Q.isPerfPair_auxiliaryPicardForm
  exact (h.exists_isNodalContraction hD).choose.markedBoundaryOrthogonalEquivChargeKernel
    (h.exists_isNodalContraction hD).choose_spec hD hd

/-- The marked class attached to a charge relation has the same coordinates as its class on the
internal blowup model. -/
@[simp]
theorem HasNodalModel.chargeKernelEquiv_symm_apply [(Q.fan.finiteFanScheme k₀).IsProjectiveOver k₀]
    [SmoothOfRelativeDimension 2 ((Q.fan.finiteFanScheme k₀) ↘ S)] [(Aux).IsPerfPair]
    (h : Q.HasNodalModel c M) (hD : D[M].IsEffectiveCartier) {d : ZMod n → L}
    (hd : M.boundaryClass hD = d) (x : (Fan.rayChargeMap Q.rays).ker) :
    Q.inclusion ((h.chargeKernelEquiv hD hd).symm x).val =
      ((Fan.boundaryOrthogonalEquivChargeKernel k₀ Q.regular Q.rays Aux).symm x).val := by
  simp only [HasNodalModel.chargeKernelEquiv,
    ContractedToricFiber.markedBoundaryOrthogonalEquivChargeKernel_symm_apply]

/-- The marked charge equivalence reads the negative total exceptional coefficients. -/
@[simp]
theorem HasNodalModel.coe_chargeKernelEquiv_apply (h : Q.HasNodalModel c M)
    (hD : D[M].IsEffectiveCartier) {d : ZMod n → L} (hd : M.boundaryClass hD = d)
    (x : Orth[d]) :
    (h.chargeKernelEquiv hD hd x : Fin r → ℤ) = -(Q.inclusion x.val).2 := by
  simp only [HasNodalModel.chargeKernelEquiv,
    ContractedToricFiber.coe_markedBoundaryOrthogonalEquivChargeKernel_apply]

/-- Exchange-kernel coordinates in the marked boundary orthogonal, when the exchange and
charge kernels coincide. -/
noncomputable def HasNodalModel.exchangeKernelEquiv (h : Q.HasNodalModel c M)
    (hD : D[M].IsEffectiveCartier) {d : ZMod n → L} (hd : M.boundaryClass hD = d)
    {E : SkewExchangeMatrix (Fin r)}
    (hker : E.matrix.mulVecLin.ker = (Fan.rayChargeMap Q.rays).ker) :
    Orth[d] ≃ₗ[ℤ] E.matrix.mulVecLin.ker :=
  (h.chargeKernelEquiv hD hd).trans (LinearEquiv.ofEq _ _ hker).symm

/-- The exchange equivalence is the charge equivalence transported along the equality of kernels. -/
theorem HasNodalModel.exchangeKernelEquiv_def (h : Q.HasNodalModel c M)
    (hD : D[M].IsEffectiveCartier) {d : ZMod n → L} (hd : M.boundaryClass hD = d)
    {E : SkewExchangeMatrix (Fin r)}
    (hker : E.matrix.mulVecLin.ker = (Fan.rayChargeMap Q.rays).ker) :
    h.exchangeKernelEquiv hD hd hker =
      (h.chargeKernelEquiv hD hd).trans (LinearEquiv.ofEq _ _ hker).symm := (rfl)

/-- Exchange-kernel coordinates are the negative total exceptional coefficients. -/
@[simp]
theorem HasNodalModel.coe_exchangeKernelEquiv_apply (h : Q.HasNodalModel c M)
    (hD : D[M].IsEffectiveCartier) {d : ZMod n → L} (hd : M.boundaryClass hD = d)
    {E : SkewExchangeMatrix (Fin r)}
    (hker : E.matrix.mulVecLin.ker = (Fan.rayChargeMap Q.rays).ker) (x : Orth[d]) :
    (h.exchangeKernelEquiv hD hd hker x : Fin r → ℤ) = -(Q.inclusion x.val).2 := by
  simp [HasNodalModel.exchangeKernelEquiv]

end CompleteToricPresentation

end QPainleve.SignedClusterModularGroup
