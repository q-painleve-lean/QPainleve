/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Contraction.Marking
public import QPainleve.Geometry.Toric.Fan.Picard.Orthogonal

import QPainleve.AlgebraicGeometry.Morphisms.Smooth.Factorial

/-!
# Charge relations in contracted Picard markings

A charge relation gives a marked class orthogonal to every strict boundary class.
It therefore belongs to the fixed Picard lattice of any nodal contraction of the
model, with its toric and total exceptional coordinates unchanged. A fixed
ray marking identifies the embedded charge lattice with the boundary orthogonal
of the contracted surface.
-/

public noncomputable section

open LinearMap (BilinForm IsPerfPair)
open TauCeti.AlgebraicGeometry (LineBundleClass)

namespace TauCeti.Toric.Fan

variable {N : Type} {V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] [Finite ι] [DecidableEq Φ.Ray]
  (hΦ : Φ.IsRegular) (s : ι → Φ.Ray)

local notation "Pic(" X ")" => Additive (LineBundleClass X)
local notation "P(" R ")" =>
  Submodule.span ℤ ((fun ρ ↦ markedBoundaryMap hΦ s (Pi.single ρ 1)) '' R)

variable (B : BilinForm ℤ (Pic(Φ.algebraicRealization) × (ι → ℤ))) [IsPerfPair B]

/-- Embed a charge relation into the lattice orthogonal to the strict classes of
the contracted rays. The ambient class uses the inverse marked charge comparison. -/
def contractedChargeKernelHom (R : Set Φ.Ray) : (rayChargeMap s).ker →ₗ[ℤ] B.orthogonal (P(R)) :=
  (Submodule.inclusion (BilinForm.orthogonal_le (B := B)
      (Submodule.span_le.mpr (by rintro _ ⟨ρ, -, rfl⟩; exact LinearMap.mem_range_self _ _)))).comp
    (boundaryOrthogonalEquivChargeKernel hΦ s B).symm.toLinearMap

/-- The charge class in the contracted lattice has the same ambient coordinates
as its class on the internal blowup model. -/
@[simp]
theorem coe_contractedChargeKernelHom_apply (R : Set Φ.Ray) (x : (rayChargeMap s).ker) :
    (contractedChargeKernelHom hΦ s B R x).val =
      ((boundaryOrthogonalEquivChargeKernel hΦ s B).symm x).val := (rfl)

/-- Distinct charge relations give distinct classes in the contracted marking. -/
theorem contractedChargeKernelHom_injective (R : Set Φ.Ray) :
    Function.Injective (contractedChargeKernelHom hΦ s B R) := by
  unfold contractedChargeKernelHom
  rw [LinearMap.coe_comp]
  apply Function.Injective.comp (Submodule.inclusion_injective _)
  exact (boundaryOrthogonalEquivChargeKernel hΦ s B).symm.injective

end TauCeti.Toric.Fan

open AlgebraicGeometry CategoryTheory Module QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData
open TauCeti.AlgebraicGeometry.Chow (intersectionBilinForm)

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones]
  [Φ.algebraicRealization.IsProjectiveOver ℂ] {n : ℕ}
  (hΦ : Φ.IsRegular) (b : Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray) (c : Fin n → ℂˣ)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Z" => Φ.algebraicRealization
local notation "d₂" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "J" => (fun j ↦ Ray.internalCenter (h₀ := h₀) b (s j) (c j))
local notation "hJ" => (fun j ↦ Ray.internalCenter_val (h₀ := h₀) b (s j) (c j))
local notation "m" => (fun j ↦ LinearMap.toAddMonoidHom
  (Basis.detDualEquiv b (Ray.primitiveGenerator (s j))))
local notation "hm" => (fun j ↦ Basis.detDualEquiv_self b (Ray.primitiveGenerator (s j)))
local notation "hprim" => (fun j ↦ Ray.surjective_detCharacter (s j) b)
local notation "smoothZ" =>
  Eq.mpr (congrArg (SmoothOfRelativeDimension 2) (Fan.algebraicRealization_over Φ))
    (Eq.mp (congrArg (fun d ↦ SmoothOfRelativeDimension d Φ.algebraicRealizationStructureMap) d₂)
      (Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ))
local notation "F" => LinearMap.BilinForm.prod (@intersectionBilinForm ℂ _ _ Z _ _ _ smoothZ)
  (-(dotProductBilin ℤ ℤ : BilinForm ℤ (Fin n → ℤ)))

variable {X Y : Scheme} [X.Over S] [X.IsProjectiveOver ℂ] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ S)] [IsPerfPair (intersectionBilinForm ℂ X)]
  {D : X.IdealSheafData} {d : ℕ} {T : QPainleve.BlowupTower X d Y}
  (hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T)

local instance : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
local instance : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
  (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two

local notation "K" => LinearMap.ker (rayChargeMap s)
local notation "KX" => BilinForm.orthogonal (intersectionBilinForm ℂ X)
  (Scheme.Opens.primeDivisorSpanCompl
    (TopologicalSpace.Closeds.compl (Scheme.IdealSheafData.support D)))
local notation "Model" => (Σ W, WithBoundary (subschemeι (Fan.boundaryIdeal Φ h₀)) n W)
local notation "U" A:arg => WithBoundary.toTower (Sigma.snd A)

include hT in
private theorem exists_chargeEquiv_of_internalModel
    (A : Model) (hA : A = alongBoundary (Φ.boundaryIdeal h₀).subschemeι J)
    (u : A.1 ≅ Y)
    (hu : u.hom ≫ T.toBase ≫ (X ↘ S) = (U A).toBase ≫ Φ.algebraicRealizationStructureMap)
    (hD : (D.comap (u.hom ≫ T.toBase)).support = A.2.boundaryι.ker.support) :
    ∃ (hF : IsPerfPair F) (q : K ≃ₗ[ℤ] KX), letI := hF; ∀ x,
      (U A).picardHom ((boundaryOrthogonalEquivChargeKernel hΦ s F).symm x).val =
        Additive.ofMul (pullback (u.hom ≫ T.toBase) (q x).val.toMul) := by
  subst A
  have hD' := (congrArg Scheme.IdealSheafData.support
    (comap_comp D u.hom T.toBase)).symm.trans hD
  let : IsPerfPair F := isPerfPair_internal_markedForm hΦ d₂ s m hm hprim c J hJ hT u.symm hu
  refine ⟨‹IsPerfPair F›,
    (picardBoundaryOrthogonalEquivChargeKernel hΦ d₂ s m hm hprim c J hJ hT u.symm hu hD').symm,
    fun x ↦ Additive.toMul.injective ?_⟩
  exact picardHom_boundaryOrthogonalEquivChargeKernel_symm
    hΦ d₂ s m hm hprim c J hJ hT u.symm hu hD' x

open Classical in
/-- The fixed ray marking identifies the embedded charge lattice with the boundary
orthogonal of the contracted surface. This property characterizes the equivalence,
whose inverse on the contracted surface is given by intersections with the total
exceptional classes after pullback. -/
theorem existsUnique_contractedPicardMarkingOfRaySet_chargeKernelEquiv
    (u : (internalBlowupTower b s c).1 ≅ Y)
    (hu : u.hom ≫ T.toBase ≫ (X ↘ S) =
      (internalBlowupTower b s c).2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap)
    (hD : (D.comap (u.hom ≫ T.toBase)).support =
      (internalBlowupTower b s c).2.boundaryι.ker.support)
    (R : Set Φ.Ray) (hR : R = contractedRaySet hΦ b s c hT u hD) :
    ∃ (hF : IsPerfPair F), letI := hF; ∃! q : K ≃ₗ[ℤ] KX, ∀ x,
      (contractedPicardMarkingOfRaySet hΦ b s c hT u hu hD R hR).symm (q x).val =
        contractedChargeKernelHom hΦ s F R x := by
  obtain ⟨hF, q, hq⟩ := exists_chargeEquiv_of_internalModel hΦ b s c hT
    (internalBlowupTower b s c) (internalBlowupTower_eq_alongBoundary b s c) u hu hD
  let := hF
  let μ := contractedPicardMarkingOfRaySet hΦ b s c hT u hu hD R hR
  have hq' (x : K) : μ.symm (q x).val = contractedChargeKernelHom hΦ s F R x := by
    apply Subtype.ext
    rw [← ofMul_toMul (q x).val, coe_contractedPicardMarkingOfRaySet_symm_apply,
      coe_contractedChargeKernelHom_apply]
    apply (internalBlowupPicardMarking b s c hΦ).injective
    rw [LinearEquiv.apply_symm_apply, internalBlowupPicardMarking_apply]
    exact (hq x).symm
  refine ⟨hF, q, hq', fun q' hq'' ↦ ?_⟩
  apply LinearEquiv.ext
  intro x
  exact Subtype.ext (μ.symm.injective ((hq'' x).trans (hq' x).symm))

end TauCeti.Toric.Fan
