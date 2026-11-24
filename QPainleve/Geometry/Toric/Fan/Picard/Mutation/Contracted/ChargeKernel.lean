/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Contraction.ChargeKernel
public import QPainleve.Geometry.Toric.Fan.Picard.Mutation.ChargeKernel
public import QPainleve.Geometry.Toric.Fan.Picard.Mutation.Contracted.Isometry

/-!
# Charge transport after nodal contraction

The restriction of the full mutation isometry to the contracted Picard lattices
acts on the embedded charge relations by the cluster exponent change. This
gives the comparison on the original pair as well as on its internal blowup
model. The ambient mutation calculation is that of Gross, Hacking and Keel,
[*Birational geometry of cluster algebras*, Theorems 5.5 and 5.6]
(https://arxiv.org/html/1309.2573v2#S5).
-/

public noncomputable section

open AlgebraicGeometry Module PointedCone
open LinearMap (BilinForm IsPerfPair)
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Chow (intersectionBilinForm)

namespace TauCeti.Toric.Fan

variable {N : Type} {V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Fintype ι] [DecidableEq ι]
  (b : Basis (Fin 2) ℤ N) (s : ι → Φ.Ray) (k : ι)
  (hop : hull ℝ {i (-(s k).primitiveGenerator)} ∈ Φ.cones) (hΦ : Φ.IsRegular)
  (hc : Φ.IsComplete) [pΦ : Φ.algebraicRealization.IsProjectiveOver ℂ]

local notation "hv" => Ray.primitiveGenerator_ne_zero (s k)
local notation "hp" => Ray.hull_primitiveGenerator_mem (s k)
local notation "Ψ" => Φ.mutationFan b hv hp hop
local notation "r" => Φ.mutationFanRayEquiv b hv hp hop
local notation "t" => Φ.mutationFanCenterRays b s k hop
local notation "hΨ" => Iff.mpr (Φ.isRegular_mutationFan_iff b hv hp hop) hΦ
local notation "nΦ" => Nonempty.intro (Ray.toCone Φ (s k))
local notation "nΨ" => Nonempty.intro (Ray.toCone (Ψ) (r (s k)))
local notation "K" => mutationFanChargeKernelEquiv b s k hop

local notation "rankTwo" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "smooth" Ξ:arg h:arg =>
  Eq.mpr (congrArg (SmoothOfRelativeDimension 2) (Fan.algebraicRealization_over Ξ))
    (Eq.mp (congrArg
      (fun n ↦ SmoothOfRelativeDimension n (Fan.algebraicRealizationStructureMap Ξ)) rankTwo)
      (Fan.smoothOfRelativeDimension_algebraicRealizationStructureMap Ξ h))
local notation "B[" Ξ "," h "," p "]" =>
  LinearMap.BilinForm.prod
    (@intersectionBilinForm ℂ _ _ (Fan.algebraicRealization Ξ)
      (Fan.algebraicRealizationOver Ξ) p _ (smooth Ξ h))
    (-(dotProductBilin ℤ ℤ : BilinForm ℤ (ι → ℤ)))

open Classical in
/-- The contracted Picard isometry intertwines the target and source charge embeddings
with the integral mutation on charge relations. The formula is independent of the
centers and uses no rank condition on the charge lattice. -/
theorem mutationContractedPicardIsometry_contractedChargeKernelHom
    [pΨ : @Scheme.IsProjectiveOver ℂ _ (Fan.algebraicRealization Ψ)
      (Fan.algebraicRealizationOver Ψ)]
    (R : Set Φ.Ray) (x : (rayChargeMap t).ker) :
    letI : Nonempty Φ.cones := nΦ
    letI : Nonempty (Ψ).cones := nΨ
    ∀ [IsPerfPair B[Φ,hΦ,pΦ]] [IsPerfPair B[Ψ,hΨ,pΨ]],
    mutationContractedPicardIsometry b s k hop hΦ hc (pΨ := pΨ) R
      (contractedChargeKernelHom hΨ t B[Ψ,hΨ,pΨ] (r '' R) x) =
      contractedChargeKernelHom hΦ s B[Φ,hΦ,pΦ] R (K x) := by
  intro _ _
  apply Subtype.ext
  simp only [coe_mutationContractedPicardIsometry_apply, coe_contractedChargeKernelHom_apply]
  let : Nonempty Φ.cones := nΦ
  let : Nonempty (Ψ).cones := nΨ
  refine mutationPicardEquiv_boundaryOrthogonalEquivChargeKernel_symm
    b s k hop hΦ B[Φ,hΦ,pΦ] B[Ψ,hΨ,pΨ] (fun y z ↦ ?_) x
  simpa only [mutationPicardIsometry_apply] using
    (mutationPicardIsometry b hΦ s k hop hc (hTarget := pΨ)).map_app z y

end TauCeti.Toric.Fan
