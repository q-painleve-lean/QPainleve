/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.MarkedComparison

import QPainleve.Geometry.Toric.Fan.Picard.Contraction.ChargeKernel

/-!
# Charge coordinates in a fixed Picard marking

The integral comparison of a nodal contraction with its ordered toric model
identifies the boundary orthogonal in the fixed Picard lattice with the charge
kernel. The inverse comparison is characterized by its image in the toric and
total exceptional coordinates. Thus the comparison is independent of the center
and of the nodal tower used to construct it.

The construction uses `Fan.existsUnique_contractedPicardMarkingOfRaySet_chargeKernelEquiv`.
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative
open QPainleve.BlowupTower TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData LineBundleClass

namespace QPainleve.SignedClusterModularGroup

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Xtor[" r "]" => Spec (CommRingCat.of (LaurentRing ℂ (Fin r)))
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))

namespace ContractedToricFiber

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones]
  {r n m : ℕ} [NeZero n] [NeZero m]
  {L : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {P : MarkedSurface ℂ n B Xtor[r]} {b : Module.Basis (Fin 2) ℤ N}
  {s : Fin r → Φ.Ray} {hΦ : Φ.IsRegular}
  [PrestableFamily ((Φ.boundaryIdeal h₀).subscheme ↘ S)]
  {γ : Type*} {a : γ → ((Φ.boundaryIdeal h₀).subscheme ↘ S).smoothLocus}
  {T : NodalCycleNumbering a m} {o : ZMod m}
  {J : L →ₗ[ℤ] Additive (LineBundleClass Φ.algebraicRealization) × (Fin r → ℤ)}
  {c : Multiplicative (Fin r → ℤ) →* ℂˣ}
  (p : ContractedToricFiber b s hΦ T o J c P)

local instance : IsIntegral P.surface := P.integral
local instance : P.surface.IsProjectiveOver ℂ := P.projective
local instance : SmoothOfRelativeDimension 2 (P.surface ↘ S) := P.smooth

local notation "K" => LinearMap.ker (Fan.rayChargeMap s)
local notation "centers" => (fun j : Fin r ↦ c (ofAdd (Pi.single j 1)))
local notation "Model" => Fan.internalBlowupTower b s centers
local notation "Btor" => LinearMap.BilinForm.prod
  (Chow.intersectionBilinForm ℂ Φ.algebraicRealization)
  (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ)))

variable [Φ.algebraicRealization.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ S)]
variable [LinearMap.IsPerfPair ((Chow.intersectionBilinForm ℂ Φ.algebraicRealization).prod
  (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ))))] [B.IsPerfPair]

include p in
/-- A nodal toric model supplies the integral charge coordinates of the fixed Picard
marking. Inverse charge classes have the prescribed toric and total exceptional
coordinates under the fixed inclusion. -/
theorem existsUnique_markedBoundaryOrthogonalEquivChargeKernel (hp : p.IsNodalContraction)
    (hD : D[P].IsEffectiveCartier) {d : ZMod n → L} (hd : P.boundaryClass hD = d) :
    ∃! e : B.orthogonal (Submodule.span ℤ (Set.range d)) ≃ₗ[ℤ] K,
      ∀ x : K, J (e.symm x).val =
        ((Fan.boundaryOrthogonalEquivChargeKernel hΦ s Btor).symm x).val := by
  classical
  let : (Chow.intersectionBilinForm ℂ P.surface).IsPerfPair := P.isPerfPair_intersectionForm
  obtain ⟨l, Y, W, hW, u, hu⟩ := hp.exists_tower
  have hproj : u.inv ≫ W.toBase ≫ (P.surface ↘ S) =
      Model.2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap := by
    rw [← Category.assoc, hu, p.projection_over]
  have hsupport : (D[P].comap (u.inv ≫ W.toBase)).support =
      Model.2.boundaryι.ker.support := hu ▸ p.support_comap
  let R := Fan.contractedRaySet hΦ b s centers hW u.symm hsupport
  obtain ⟨_, q, hq, _⟩ :=
    Fan.existsUnique_contractedPicardMarkingOfRaySet_chargeKernelEquiv hΦ b s centers
      hW u.symm hproj hsupport R rfl
  let f := q.trans (LinearEquiv.ofEq _ _ (D[P].boundaryOrthogonal_def ℂ).symm)
  let g := P.boundaryOrthogonalMarking hD
  let e := ((LinearEquiv.ofEq _ _ (by rw [hd])).trans g).trans f.symm
  have he (x : K) : J (e.symm x).val =
      ((Fan.boundaryOrthogonalEquivChargeKernel hΦ s Btor).symm x).val := by
    have hclass : P.picardMarking (e.symm x).val = (q x).val := by
      simp only [e, g, f, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
        LinearEquiv.symm_symm, LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply]
      rw [← P.coe_boundaryOrthogonalMarking_apply hD, LinearEquiv.apply_symm_apply,
        LinearEquiv.coe_ofEq_apply]
    have hcoords := congrArg Subtype.val (hq x)
    rw [← ofMul_toMul (q x).val, Fan.coe_contractedPicardMarkingOfRaySet_symm_apply,
      Fan.coe_contractedChargeKernelHom_apply, Iso.symm_hom, hu] at hcoords
    exact (p.marked_pullback (e.symm x).val).symm.trans
      (by simpa only [hclass, ofMul_toMul] using hcoords)
  refine ⟨e, he, fun e' he' ↦ LinearEquiv.ext fun z ↦ Subtype.ext ?_⟩
  have hcoords (f : _ ≃ₗ[ℤ] K)
      (hf : ∀ x : K, J (f.symm x).val =
        ((Fan.boundaryOrthogonalEquivChargeKernel hΦ s Btor).symm x).val) :
      (J z.val).2 = -(f z : Fin r → ℤ) := by
    simpa only [LinearEquiv.symm_apply_apply, Fan.boundaryOrthogonalEquivChargeKernel_symm_snd]
      using congrArg Prod.snd (hf (f z))
  exact neg_injective ((hcoords e' he').symm.trans (hcoords e he))

end ContractedToricFiber

end QPainleve.SignedClusterModularGroup
