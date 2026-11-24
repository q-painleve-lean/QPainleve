/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Contraction.Marking
public import QPainleve.Geometry.Toric.Fan.Picard.Mutation.Isometry

/-!
# The Picard isometry on the contracted lattices

The mutation isometry sends the strict ray classes by the inverse shear. It therefore
restricts to the orthogonal complements of corresponding contracted ray spans. These
are the Picard lattices of the original surfaces in the toric markings, and the
restriction depends only on the ordered ray labels and the contracted set.

The ambient mutation is the elementary transformation of Gross, Hacking and Keel,
[*Birational geometry of cluster algebras*, §3.1](https://arxiv.org/html/1309.2573v2#S3.SS1).
-/

public noncomputable section

open AlgebraicGeometry LinearMap Module PointedCone
open TauCeti.AlgebraicGeometry (LineBundleClass)
open TauCeti.AlgebraicGeometry.Chow (intersectionBilinForm)

namespace TauCeti.Toric.Fan

variable {N : Type} {V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Fintype ι] [DecidableEq ι]
  (b : Basis (Fin 2) ℤ N) (s : ι → Φ.Ray) (k : ι)
  (hop : hull ℝ {i (-(s k).primitiveGenerator)} ∈ Φ.cones) (hΦ : Φ.IsRegular)

local notation "hv" => Ray.primitiveGenerator_ne_zero (s k)
local notation "hp" => Ray.hull_primitiveGenerator_mem (s k)
local notation "Ψ" => Φ.mutationFan b hv hp hop
local notation "r" => Φ.mutationFanRayEquiv b hv hp hop
local notation "t" => Φ.mutationFanCenterRays b s k hop
local notation "hΨ" => Iff.mpr (Φ.isRegular_mutationFan_iff b hv hp hop) hΦ
local notation "nΦ" => Nonempty.intro (Ray.toCone Φ (s k))
local notation "nΨ" => Nonempty.intro (Ray.toCone (Ψ) (r (s k)))
local notation "I" => mutationPicardEquiv b s k hop hΦ
local notation "Rays[" h "," s "," R "]" =>
  Submodule.span ℤ ((fun ρ ↦ markedBoundaryMap h s (Pi.single ρ 1)) '' R)

omit [Fintype ι] in
open Classical in
/-- Picard mutation carries the span of the strict ray classes on the sheared set
onto the span of the strict ray classes on the original set. -/
theorem map_span_markedBoundaryMap_mutationPicardEquiv (R : Set Φ.Ray) :
    letI : Nonempty Φ.cones := nΦ
    letI : Nonempty (Ψ).cones := nΨ
    (Rays[hΨ,t,r '' R]).map (I).toLinearMap = Rays[hΦ,s,R] := by
  let : Nonempty Φ.cones := nΦ
  let : Nonempty (Ψ).cones := nΨ
  rw [Submodule.map_span, Set.image_image, Set.image_image]
  congr 1
  apply Set.image_congr
  intro ρ _
  simp only [LinearEquiv.coe_coe, mutationPicardEquiv_markedBoundaryMap,
    Pi.single_comp_equiv, Equiv.symm_apply_apply]

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
    (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (ι → ℤ)))

variable (hc : Φ.IsComplete) [pΦ : Φ.algebraicRealization.IsProjectiveOver ℂ]

local notation "B₀" => B[Φ,hΦ,pΦ]
local notation "B₁[" p "]" => B[Ψ,hΨ,p]
local notation "E[" p "]" => mutationPicardIsometry b hΦ s k hop hc (hTarget := p)

open Classical in
/-- The center-independent Picard isometry for a mutation of contracted toric
presentations. Its domain is the orthogonal complement of the sheared contracted ray
span, and its codomain is the orthogonal complement of the original span. -/
def mutationContractedPicardIsometry
    [pΨ : @Scheme.IsProjectiveOver ℂ _ (Fan.algebraicRealization Ψ)
      (Fan.algebraicRealizationOver Ψ)] (R : Set Φ.Ray) :
    letI : Nonempty Φ.cones := nΦ
    letI : Nonempty (Ψ).cones := nΨ
    ((B₁[pΨ]).restrict ((B₁[pΨ]).orthogonal (Rays[hΨ,t,r '' R]))).IsometryEquiv
      ((B₀).restrict ((B₀).orthogonal (Rays[hΦ,s,R]))) := by
  letI : Nonempty Φ.cones := nΦ
  letI : Nonempty (Ψ).cones := nΨ
  have h : (E[pΨ]).toLinearEquiv = I :=
    mutationPicardIsometry_toLinearEquiv b hΦ s k hop hc (hTarget := pΨ)
  have hspan : (Rays[hΨ,t,r '' R]).map (E[pΨ]).toLinearMap = Rays[hΦ,s,R] :=
    (congrArg (fun (f : _ ≃ₗ[ℤ] _) ↦ (Rays[hΨ,t,r '' R]).map f.toLinearMap) h).trans
      (map_span_markedBoundaryMap_mutationPicardEquiv b s k hop hΦ R)
  exact (E[pΨ]).ofSubmodules _ _ (((E[pΨ]).map_orthogonal _).trans (congrArg (B₀).orthogonal hspan))

open Classical in
/-- On ambient Picard coordinates, the contracted isometry applies the ordered mutation
formula. -/
@[simp]
theorem coe_mutationContractedPicardIsometry_apply
    [pΨ : @Scheme.IsProjectiveOver ℂ _ (Fan.algebraicRealization Ψ)
      (Fan.algebraicRealizationOver Ψ)] (R : Set Φ.Ray)
    (x : let : Nonempty (Ψ).cones := nΨ; (B₁[pΨ]).orthogonal (Rays[hΨ,t,r '' R])) :
    let : Nonempty Φ.cones := nΦ
    ((mutationContractedPicardIsometry b s k hop hΦ hc (pΨ := pΨ) R x).val) = I x.val := by
  let : Nonempty Φ.cones := nΦ
  let : Nonempty (Ψ).cones := nΨ
  exact (LinearMap.BilinForm.IsometryEquiv.coe_ofSubmodules_apply (E[pΨ]) _ x).trans
    (mutationPicardIsometry_apply b hΦ s k hop hc (hTarget := pΨ) x.val)

end TauCeti.Toric.Fan

open CategoryTheory QPainleve.BlowupTower TauCeti.AlgebraicGeometry
open LineBundleClass (pullback)

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} {n : ℕ}
  (b : Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray) (k : Fin n)
  (hop : hull ℝ {i (-(s k).primitiveGenerator)} ∈ Φ.cones) (hΦ : Φ.IsRegular)
  (hc : Φ.IsComplete) [Φ.algebraicRealization.IsProjectiveOver ℂ]

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "hv" => Ray.primitiveGenerator_ne_zero (s k)
local notation "hp" => Ray.hull_primitiveGenerator_mem (s k)
local notation "Ψ" => Φ.mutationFan b hv hp hop
local notation "r" => Φ.mutationFanRayEquiv b hv hp hop
local notation "t" => Φ.mutationFanCenterRays b s k hop
local notation "hΨ" => Iff.mpr (Φ.isRegular_mutationFan_iff b hv hp hop) hΦ
local notation "nΦ" => Nonempty.intro (Ray.toCone Φ (s k))
local notation "nΨ" => Nonempty.intro (Ray.toCone (Ψ) (r (s k)))

variable {X Y X' Y' : Scheme} [X.Over S] [X'.Over S] [IsIntegral X] [IsIntegral X']
  [X.IsProjectiveOver ℂ] [X'.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (X ↘ S)] [SmoothOfRelativeDimension 2 (X' ↘ S)]
  {D : X.IdealSheafData} {D' : X'.IdealSheafData} {m l : ℕ}
  {T : QPainleve.BlowupTower X m Y} {T' : QPainleve.BlowupTower X' l Y'}
  (c d : Fin n → ℂˣ)
  (hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T)
  (hT' : IsNodalBoundaryTower D' (X' ↘ S) (𝟙 X') T')

local notation "coords₀" => LinearEquiv.symm (internalBlowupPicardMarking (h₀ := nΦ) b s c hΦ)
local notation "coords₁" => LinearEquiv.symm (internalBlowupPicardMarking (h₀ := nΨ) b (t) d hΨ)

/-- When the nodal contractions have corresponding contracted rays, the
center-independent mutation isometry is the full pullback in their fixed markings.
The auxiliary-coordinate identity is the one supplied by
`exists_iso_ordered_nodal_mutation`. -/
theorem contractedPicardMarkingOfRaySet_symm_pullback_mutation
    [pΨ : @Scheme.IsProjectiveOver ℂ _ (Fan.algebraicRealization Ψ)
      (Fan.algebraicRealizationOver Ψ)]
    (u : (internalBlowupTower (h₀ := nΦ) b s c).1 ≅ Y)
    (v : (internalBlowupTower (h₀ := nΨ) b (t) d).1 ≅ Y')
    (hu : u.hom ≫ T.toBase ≫ (X ↘ S) =
      (internalBlowupTower (h₀ := nΦ) b s c).2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap)
    (hv' : v.hom ≫ T'.toBase ≫ (X' ↘ S) =
      (internalBlowupTower (h₀ := nΨ) b (t) d).2.toTower.toBase ≫
        (Ψ).algebraicRealizationStructureMap)
    (hD : (D.comap (u.hom ≫ T.toBase)).support =
      (internalBlowupTower (h₀ := nΦ) b s c).2.boundaryι.ker.support)
    (hD' : (D'.comap (v.hom ≫ T'.toBase)).support =
      (internalBlowupTower (h₀ := nΨ) b (t) d).2.boundaryι.ker.support)
    (R : Set Φ.Ray)
    (hR : R = contractedRaySet (h₀ := nΦ) hΦ b s c hT u hD)
    (hR' : r '' R = contractedRaySet (h₀ := nΨ) hΨ b (t) d hT' v hD')
    (g : X ≅ X') (L : LineBundleClass X')
    (hmark : coords₀ (Additive.ofMul (pullback (u.hom ≫ T.toBase) (pullback g.hom L))) =
      mutationPicardEquiv b s k hop hΦ
        (coords₁ (Additive.ofMul (pullback (v.hom ≫ T'.toBase) L)))) :
    let μ := contractedPicardMarkingOfRaySet (h₀ := nΦ) hΦ b s c hT u hu hD R hR
    let ν := contractedPicardMarkingOfRaySet (h₀ := nΨ) hΨ b (t) d hT' v hv' hD' (r '' R) hR'
    μ.symm (Additive.ofMul (pullback g.hom L)) =
      mutationContractedPicardIsometry b s k hop hΦ hc (pΨ := pΨ) R
        (ν.symm (Additive.ofMul L)) := by
  let : Nonempty Φ.cones := nΦ
  let : Nonempty (Ψ).cones := nΨ
  apply Subtype.ext
  rw [coe_mutationContractedPicardIsometry_apply,
    coe_contractedPicardMarkingOfRaySet_symm_apply,
    coe_contractedPicardMarkingOfRaySet_symm_apply]
  exact hmark

end TauCeti.Toric.Fan
