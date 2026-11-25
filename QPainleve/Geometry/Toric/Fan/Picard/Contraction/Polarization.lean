/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.LineBundle.Ample
public import QPainleve.Geometry.Toric.Fan.Picard.Contraction.Boundary

import QPainleve.AlgebraicGeometry.Chow.Ample
import QPainleve.Geometry.Toric.Fan.Picard.Contraction.Surviving

/-!
# Detecting surviving toric rays with a polarization

The pullback of an ample class on the contracted surface has degree zero on each
contracted boundary ray and positive degree on each strict transform of a boundary
prime of the contracted surface. The test is an integer intersection calculation
in the toric and exceptional Picard coordinates of the pullback.
-/

public section

open Additive AlgebraicGeometry CategoryTheory QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] (hΦ : Φ.IsRegular)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Z" => Φ.algebraicRealization
local notation "F[" ι "]" => LinearMap.BilinForm.prod (Chow.intersectionBilinForm ℂ Z)
  (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (ι → ℤ)))

variable [Φ.algebraicRealization.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ S)]

variable (b : Module.Basis (Fin 2) ℤ N) {r : ℕ} (s : Fin r → Φ.Ray)
  {X Y : Scheme} [X.Over S] [X.IsProjectiveOver ℂ] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ S)] {D : X.IdealSheafData}
  {l : ℕ} {T : BlowupTower X l Y}
  (c : Fin r → ℂˣ) (hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T)
  (e : (internalBlowupTower b s c).1 ≅ Y)
  (he : e.hom ≫ T.toBase ≫ (X ↘ S) =
    (internalBlowupTower b s c).2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap)
  (hD : (D.comap (e.hom ≫ T.toBase)).support =
    (internalBlowupTower b s c).2.boundaryι.ker.support)

local notation "p" => (e.hom ≫ T.toBase)
local notation "hU" => isClosedPointTower_internalBlowupTower b s c
local notation "cl" ρ:arg => markedBoundaryMap hΦ s (Pi.single ρ 1)

include hT he hD in
/-- A strict ray survives a nodal contraction exactly when it has positive intersection
with the pullback of an ample class. The pairing is in the ordered toric Picard marking. -/
theorem markedBoundaryMap_single_pairing_pullback_pos_iff
    {H : LineBundleClass X} (hH : H.IsAmple) (ρ : Φ.Ray) :
    (0 < F[Fin r] (cl ρ) ((internalBlowupPicardMarking b s c hΦ).symm
      (Additive.ofMul (pullback p H)))) ↔
    p (internalBlowupBoundaryPrimeEquiv hΦ b s c ρ).val ∈ D.boundaryPrimes := by
  let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  let : IsNoetherian Z := isNoetherian_of_finiteType (Z ↘ S)
  let := (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let : IsNormalScheme X := IsNormalScheme.of_uniqueFactorizationMonoid_stalk
  let : IsModification p := isModification_orderedContraction hΦ b s c hT e
  let μ := contractedPicardMarking ℂ hT.isClosedPointTower hU e he
  let a := μ.symm (Additive.ofMul H)
  have ha : (internalBlowupPicardMarking b s c hΦ).symm (Additive.ofMul (pullback p H)) =
      a.val := by
    apply (internalBlowupPicardMarking b s c hΦ).injective
    rw [LinearEquiv.apply_symm_apply, internalBlowupPicardMarking_apply]
    exact (picardHom_contractedPicardMarking_symm ℂ hT.isClosedPointTower hU e he _).symm
  rw [ha]
  constructor
  · intro hpos
    by_contra hnot
    have hmem := (markedBoundaryMap_single_mem_markedExceptionalSpan_iff
      hΦ b s c hT e he hD ρ).mpr hnot
    have hzero := (LinearMap.BilinForm.mem_orthogonal_iff.mp a.property) (cl ρ) hmem
    exact (ne_of_gt hpos) hzero
  · rw [← mem_range_contractedBoundaryRayEmbedding_iff hΦ b s c p hD]
    rintro ⟨x, rfl⟩
    let ρ' := contractedBoundaryRayEmbedding hΦ b s c p hD x
    let z : CodimensionOnePoint X := ⟨x.val, (mem_boundaryPrimes.mp x.property).2⟩
    let v := μ.symm (Additive.ofMul (primeDivisorClass z))
    have hv : v = Submodule.projectionOnto _ _
        (isCompl_orthogonal_markedExceptionalSpan ℂ hT.isClosedPointTower hU e he) (cl ρ') :=
      contractedPicardMarking_symm_boundaryPrime hΦ b s c hT e he hD x
    have hdiff : cl ρ' - v.val ∈ markedExceptionalSpan ℂ hU T e := by
      rw [hv, Submodule.coe_projectionOnto_apply]
      exact Submodule.sub_projection_mem _ (cl ρ')
    have hzero := LinearMap.BilinForm.mem_orthogonal_iff.mp a.property _ hdiff
    have hpair : F[Fin r] (cl ρ') a.val = F[Fin r] v.val a.val := by
      simpa only [map_sub, LinearMap.sub_apply, sub_eq_zero] using hzero
    have hdeg := Chow.classIntersectionNumber_primeDivisorClass_pos_of_isAmple ℂ
      (topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)) hH z
    rw [hpair]
    have h := μ.symm.map_app (Additive.ofMul H) (Additive.ofMul (primeDivisorClass z))
    rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply] at h
    rw [h]
    simpa only [Chow.intersectionBilinForm_apply, toMul_ofMul,
      Chow.classIntersectionNumber_comm] using hdeg

end TauCeti.Toric.Fan
