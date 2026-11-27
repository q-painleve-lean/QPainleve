/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.ChargeKernel.Action
public import QPainleve.SignedClusterModularGroup.Boundary.Restriction
public import QPainleve.SignedClusterModularGroup.Realization.ChargeKernel.Transport

/-!
# Picard and Casimir actions of a realized loop

For a loop, the signed Picard pullback in charge coordinates is the action of the
opposite cluster modular group on the charge kernel.
-/

public section

open AlgebraicGeometry CategoryTheory DihedralGroup MulOpposite Multiplicative Quiver
open Scheme Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open QPainleve.Cluster QPainleve.CharacterTorus QPainleve.SignedBoundaryIsometryGroup

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]

local notation "S" => Spec (CommRingCat.of k₀)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones]
  {r m n : ℕ} [NeZero m] [NeZero n] {L : Type} [AddCommGroup L]
  {B : LinearMap.BilinForm ℤ L} {E : SkewExchangeMatrix (Fin r)}
  {b : Module.Basis (Fin 2) ℤ N} {s : Fin r → Φ.Ray} {hΦ : Φ.IsRegular}

local notation "A" => (Fin r → ℤ)
local notation "Tcent" => Over.mk (structureMap k₀ A)
local notation "ChargeKernel" => LinearMap.ker (Fan.rayChargeMap s)
local notation "Ex" => LinearMap.ker (Matrix.mulVecLin (SkewExchangeMatrix.matrix E))
local notation "Qform" => LinearMap.BilinForm.prod
  (Chow.intersectionBilinForm k₀ (Φ.finiteFanScheme k₀))
  (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ A))

local notation "χ[" p "]" => pointsEquiv k₀ A
  (Subtype.mk (Over.Hom.left (p : Point Tcent)) (Over.w (p : Point Tcent)))

variable {C : (scheme k₀ (Fin r → ℤ)).PartialMap (scheme k₀ (Fin r → ℤ))}
  [IsDominant C.hom]
  [C.IsOver (Over.mk (structureMap k₀ (Fin r → ℤ))).hom
    (Over.mk (structureMap k₀ (Fin r → ℤ))).hom]

local notation "src[" p "]" => p ≫ PartialMap.domainSource (X := Tcent) (Y := Tcent) C
local notation "dst[" p "]" => p ≫ PartialMap.domainTarget (X := Tcent) (Y := Tcent) C

variable [PrestableFamily ((Φ.toricBoundaryIdeal k₀ h₀).subscheme ↘ Spec (.of k₀))]
  {γ : Type*} {a : γ → ((Φ.toricBoundaryIdeal k₀ h₀).subscheme ↘ Spec (.of k₀)).smoothLocus}
  {T : NodalCycleNumbering a m} {origin : ZMod m}
  {ι : L →ₗ[ℤ] Additive (LineBundleClass (Φ.finiteFanScheme k₀)) × (Fin r → ℤ)}
  [(Φ.finiteFanScheme k₀).IsProjectiveOver k₀]
  [SmoothOfRelativeDimension 2 ((Φ.finiteFanScheme k₀) ↘ Spec (.of k₀))]
  [LinearMap.IsPerfPair
    ((Chow.intersectionBilinForm k₀ (Φ.finiteFanScheme k₀)).prod
      (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ))))]

local notation "aux" => (LinearEquiv.symm (Fan.boundaryOrthogonalEquivChargeKernel k₀ hΦ s Qform))

variable (u : ZMod m ≃ Φ.Ray)
  (hvertices : ∀ j, Scheme.dualGraphVertexEquiv (Φ.toricBoundaryIdeal k₀ h₀).subscheme a
    (T.vertex j) =
    Φ.boundaryNormalizationComponentEquiv k₀ hΦ (u j))
  (hdet : ∀ j, b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1)
  (hnodes : ∀ j, ∃ σ : Φ.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ ∧
    (Φ.toricBoundaryIdeal k₀ h₀).subschemeι
      (Scheme.dualGraphEdgeEquiv (Φ.toricBoundaryIdeal k₀ h₀).subscheme a (T.edge j)).val =
      (Φ.distinguishedSection (R := k₀) σ) (IsLocalRing.closedPoint k₀))

variable {P : Point (Over.mk (structureMap k₀ (Fin r → ℤ))) →
  MarkedSurface k₀ n B (Spec (CommRingCat.of (LaurentRing k₀ (Fin r))))}
  (D : ZMod n → L) (hD : ∀ c, D[P c].IsEffectiveCartier)
  (hmark : ∀ c j, (P c).boundaryClass (hD c) j = D j)

local notation "Orth" => LinearMap.BilinForm.orthogonal B (Submodule.span ℤ (Set.range D))
local notation "ρ" => signedOrthogonalRestriction B D

include hvertices hdet hnodes in
/-- In the charge coordinates of a fixed ordered presentation, a realized signed
loop acts on the charge kernel by the restriction of its Picard pullback times
its branch sign. The center map is the loop's monomial center map restricted to
the realization domain. The coordinate identification is characterized by the
toric and total exceptional classes of each charge relation. -/
theorem chargeKernelAction_eq_signedOrthogonalRestriction
    (w : Word E E) (R : GeometricRealization P P C (w.xRationalMap k₀))
    (hC : C.hom = C.domain.ι ≫ (w.centerIso k₀).hom)
    (Q : ChargeSeed E N) (hcharge : Q.charge = Fan.rayChargeMap s)
    (hker : Ex = Q.charge.ker) (e : Orth ≃ₗ[ℤ] ChargeKernel)
    (he : ∀ x : ChargeKernel, ι (e.symm x).val = (aux x).val)
    {U : Set (Point Tcent)}
    (hends : ∀ c : CenterPoint (U := Tcent) (V := Tcent) C, src[c] ∈ U ∧ dst[c] ∈ U)
    (hgenus : ∀ t ∈ U,
      letI := (P t).prestable_boundaryImage
      ∀ v : irreducibleComponents (D[P t].subscheme.singularLocus k₀).blowup,
        (D[P t].subscheme.blowupComponent (K := k₀) v).toScheme.genus k₀ = 0)
    (hmodel : ∀ t ∈ U,
      Nonempty (ContractedToricFiber (h₀ := h₀) b s hΦ T origin ι (χ[t]) (P t))) :
    LinearEquiv.autCongr
      (LinearEquiv.ofEq Q.charge.ker ChargeKernel (congrArg LinearMap.ker hcharge))
      (chargeKernelAction k₀ Q hker (op (signedClusterModularGroupMap k₀ E (End.of w)))) =
      LinearEquiv.autCongr e (ρ (R.toSignedBoundaryIsometry D hD hmark)).val := by
  let v := (ρ (R.toSignedBoundaryIsometry D hD hmark)).val
  apply LinearEquiv.ext
  intro x
  have hv : v (e.symm x) = R.orientation • R.boundaryOrthogonalEquiv hmark hmark (e.symm x) := by
    apply Subtype.ext
    simp only [v, coe_signedOrthogonalRestriction_apply, toIsometry_apply,
      SignedBoundaryIsometryGroup.sign_apply, coe_toSignedBoundaryIsometry,
      LinearMap.BilinForm.coe_isometryGroupEquivIsometryEquiv_symm, Units.smul_def,
      Submodule.coe_smul, coe_boundaryOrthogonalEquiv_apply]
  have h := R.exponentEquiv_eq_signed_picard_pullback hmark hmark e e he he hC
    u hvertices hdet hnodes u hvertices hdet hnodes
    (fun p ↦ ⟨hmodel _ (hends p).1, hgenus _ (hends p).1⟩)
    (fun p ↦ ⟨hmodel _ (hends p).2, hgenus _ (hends p).2⟩) (e.symm x)
  rw [LinearEquiv.apply_symm_apply, ← hv] at h
  apply Subtype.ext
  simpa only [LinearEquiv.autCongr_apply_apply, chargeKernelAction_op_loop,
    LinearEquiv.trans_apply, Path.coe_chargeKernelEquiv_apply, LinearEquiv.ofEq_symm,
    LinearEquiv.coe_ofEq_apply] using h

end QPainleve.SignedClusterModularGroup.GeometricRealization
