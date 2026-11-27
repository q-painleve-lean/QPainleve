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

variable (k₀ : Type) [Field k₀] [IsAlgClosed k₀]

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
local notation "I" => mutationPicardEquiv k₀ b s k hop hΦ
local notation "Rays[" h "," s "," R "]" =>
  Submodule.span ℤ ((fun ρ ↦ markedBoundaryMap k₀ h s (Pi.single ρ 1)) '' R)

omit [Fintype ι] in
open Classical in
omit [IsAlgClosed k₀] in
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
  Eq.mpr (congrArg (SmoothOfRelativeDimension 2) (Fan.finiteFanScheme_over k₀ Ξ))
    (Eq.mp (congrArg
      (fun n ↦ SmoothOfRelativeDimension n (Fan.finiteFanSchemeToSpec k₀ Ξ)) rankTwo)
      (Fan.smoothOfRelativeDimension_finiteFanSchemeToSpec Ξ k₀ h))
local notation "B[" Ξ "," h "," p "]" =>
  LinearMap.BilinForm.prod
    (@intersectionBilinForm k₀ _ _ (Fan.finiteFanScheme k₀ Ξ)
      (Fan.finiteFanSchemeOver k₀ Ξ) p _ (smooth Ξ h))
    (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (ι → ℤ)))

variable (hc : Φ.IsComplete) [pΦ : (Φ.finiteFanScheme k₀).IsProjectiveOver k₀]

local notation "B₀" => B[Φ,hΦ,pΦ]
local notation "B₁[" p "]" => B[Ψ,hΨ,p]
local notation "E[" p "]" => mutationPicardIsometry b k₀ hΦ s k hop hc (hTarget := p)

open Classical in
/-- The center-independent Picard isometry for a mutation of contracted toric
presentations. Its domain is the orthogonal complement of the sheared contracted ray
span, and its codomain is the orthogonal complement of the original span. -/
def mutationContractedPicardIsometry
    [pΨ : @Scheme.IsProjectiveOver k₀ _ (Fan.finiteFanScheme k₀ Ψ)
      (Fan.finiteFanSchemeOver k₀ Ψ)] (R : Set Φ.Ray) :
    letI : Nonempty Φ.cones := nΦ
    letI : Nonempty (Ψ).cones := nΨ
    ((B₁[pΨ]).restrict ((B₁[pΨ]).orthogonal (Rays[hΨ,t,r '' R]))).IsometryEquiv
      ((B₀).restrict ((B₀).orthogonal (Rays[hΦ,s,R]))) := by
  letI : Nonempty Φ.cones := nΦ
  letI : Nonempty (Ψ).cones := nΨ
  have h : (E[pΨ]).toLinearEquiv = I :=
    mutationPicardIsometry_toLinearEquiv b k₀ hΦ s k hop hc (hTarget := pΨ)
  have hspan : (Rays[hΨ,t,r '' R]).map (E[pΨ]).toLinearMap = Rays[hΦ,s,R] :=
    (congrArg (fun (f : _ ≃ₗ[ℤ] _) ↦ (Rays[hΨ,t,r '' R]).map f.toLinearMap) h).trans
      (map_span_markedBoundaryMap_mutationPicardEquiv k₀ b s k hop hΦ R)
  exact (E[pΨ]).ofSubmodules _ _ (((E[pΨ]).map_orthogonal _).trans (congrArg (B₀).orthogonal hspan))

open Classical in
/-- On ambient Picard coordinates, the contracted isometry applies the ordered mutation
formula. -/
@[simp]
theorem coe_mutationContractedPicardIsometry_apply
    [pΨ : @Scheme.IsProjectiveOver k₀ _ (Fan.finiteFanScheme k₀ Ψ)
      (Fan.finiteFanSchemeOver k₀ Ψ)] (R : Set Φ.Ray)
    (x : let : Nonempty (Ψ).cones := nΨ; (B₁[pΨ]).orthogonal (Rays[hΨ,t,r '' R])) :
    let : Nonempty Φ.cones := nΦ
    ((mutationContractedPicardIsometry k₀ b s k hop hΦ hc (pΨ := pΨ) R x).val) = I x.val := by
  let : Nonempty Φ.cones := nΦ
  let : Nonempty (Ψ).cones := nΨ
  exact (LinearMap.BilinForm.IsometryEquiv.coe_ofSubmodules_apply (E[pΨ]) _ x).trans
    (mutationPicardIsometry_apply b k₀ hΦ s k hop hc (hTarget := pΨ) x.val)

end TauCeti.Toric.Fan

open CategoryTheory QPainleve.BlowupTower TauCeti.AlgebraicGeometry
open LineBundleClass (pullback)

namespace TauCeti.Toric.Fan

variable (k₀ : Type) [Field k₀] [IsAlgClosed k₀]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} {n : ℕ}
  (b : Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray) (k : Fin n)
  (hop : hull ℝ {i (-(s k).primitiveGenerator)} ∈ Φ.cones) (hΦ : Φ.IsRegular)
  (hc : Φ.IsComplete) [(Φ.finiteFanScheme k₀).IsProjectiveOver k₀]

local notation "S" => Spec (CommRingCat.of k₀)
local notation "hv" => Ray.primitiveGenerator_ne_zero (s k)
local notation "hp" => Ray.hull_primitiveGenerator_mem (s k)
local notation "Ψ" => Φ.mutationFan b hv hp hop
local notation "r" => Φ.mutationFanRayEquiv b hv hp hop
local notation "t" => Φ.mutationFanCenterRays b s k hop
local notation "hΨ" => Iff.mpr (Φ.isRegular_mutationFan_iff b hv hp hop) hΦ
local notation "nΦ" => Nonempty.intro (Ray.toCone Φ (s k))
local notation "nΨ" => Nonempty.intro (Ray.toCone (Ψ) (r (s k)))

variable {X Y X' Y' : Scheme} [X.Over (Spec (.of k₀))] [X'.Over (Spec (.of k₀))]
  [IsIntegral X] [IsIntegral X']
  [X.IsProjectiveOver k₀] [X'.IsProjectiveOver k₀]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k₀))]
  [SmoothOfRelativeDimension 2 (X' ↘ Spec (.of k₀))]
  {D : X.IdealSheafData} {D' : X'.IdealSheafData} {m l : ℕ}
  {T : QPainleve.BlowupTower X m Y} {T' : QPainleve.BlowupTower X' l Y'}
  (c d : Fin n → k₀ˣ)
  (hT : IsNodalBoundaryTower D (X ↘ Spec (.of k₀)) (𝟙 X) T)
  (hT' : IsNodalBoundaryTower D' (X' ↘ Spec (.of k₀)) (𝟙 X') T')

local notation "coords₀" => LinearEquiv.symm (internalBlowupPicardMarking k₀ (h₀ := nΦ) b s c hΦ)
local notation "coords₁" => LinearEquiv.symm (internalBlowupPicardMarking k₀ (h₀ := nΨ) b (t) d hΨ)

/-- When the nodal contractions have corresponding contracted rays, the
center-independent mutation isometry is the full pullback in their fixed markings.
The auxiliary-coordinate identity is the one supplied by
`exists_iso_ordered_nodal_mutation`. -/
theorem contractedPicardMarkingOfRaySet_symm_pullback_mutation
    [pΨ : @Scheme.IsProjectiveOver k₀ _ (Fan.finiteFanScheme k₀ Ψ)
      (Fan.finiteFanSchemeOver k₀ Ψ)]
    (u : (internalBlowupTower k₀ (h₀ := nΦ) b s c).1 ≅ Y)
    (v : (internalBlowupTower k₀ (h₀ := nΨ) b (t) d).1 ≅ Y')
    (hu : u.hom ≫ T.toBase ≫ (X ↘ S) =
      (internalBlowupTower k₀ (h₀ := nΦ) b s c).2.toTower.toBase ≫ (Φ.finiteFanSchemeToSpec k₀))
    (hv' : v.hom ≫ T'.toBase ≫ (X' ↘ S) =
      (internalBlowupTower k₀ (h₀ := nΨ) b (t) d).2.toTower.toBase ≫
        (Fan.finiteFanSchemeToSpec k₀ (Ψ)))
    (hD : (D.comap (u.hom ≫ T.toBase)).support =
      (internalBlowupTower k₀ (h₀ := nΦ) b s c).2.boundaryι.ker.support)
    (hD' : (D'.comap (v.hom ≫ T'.toBase)).support =
      (internalBlowupTower k₀ (h₀ := nΨ) b (t) d).2.boundaryι.ker.support)
    (R : Set Φ.Ray)
    (hR : R = contractedRaySet k₀ (h₀ := nΦ) hΦ b s c hT u hD)
    (hR' : r '' R = contractedRaySet k₀ (h₀ := nΨ) hΨ b (t) d hT' v hD')
    (g : X ≅ X') (L : LineBundleClass X')
    (hmark : coords₀ (Additive.ofMul (pullback (u.hom ≫ T.toBase) (pullback g.hom L))) =
      mutationPicardEquiv k₀ b s k hop hΦ
        (coords₁ (Additive.ofMul (pullback (v.hom ≫ T'.toBase) L)))) :
    let μ := contractedPicardMarkingOfRaySet k₀ (h₀ := nΦ) hΦ b s c hT u hu hD R hR
    let ν := contractedPicardMarkingOfRaySet k₀ (h₀ := nΨ) hΨ b (t) d hT' v hv' hD' (r '' R) hR'
    μ.symm (Additive.ofMul (pullback g.hom L)) =
      mutationContractedPicardIsometry k₀ b s k hop hΦ hc (pΨ := pΨ) R
        (ν.symm (Additive.ofMul L)) := by
  let : Nonempty Φ.cones := nΦ
  let : Nonempty (Ψ).cones := nΨ
  intro μ ν
  apply Subtype.ext
  dsimp only [μ, ν]
  rw [coe_mutationContractedPicardIsometry_apply,
    coe_contractedPicardMarkingOfRaySet_symm_apply k₀ hΦ b s c hT u hu hD R hR,
    coe_contractedPicardMarkingOfRaySet_symm_apply k₀ hΨ b t d hT' v hv' hD' (r '' R) hR']
  exact hmark

end TauCeti.Toric.Fan
