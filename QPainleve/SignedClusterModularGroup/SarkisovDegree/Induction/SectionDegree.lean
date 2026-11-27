/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Logarithmic.PlaneDegree
public import QPainleve.Geometry.Toric.Fan.Picard.Hirzebruch
public import QPainleve.Geometry.Toric.Fan.ProjectiveSpace.Boundary

import QPainleve.AlgebraicGeometry.Scheme.LocalDimension
import QPainleve.Geometry.Toric.Fan.Boundary.Component
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective

/-!
# The positive section in a marked Hirzebruch-to-plane resolution

The positive invariant section has degree equal to the fiber coefficient of
the marked line class. The sum of the base orders along its successive strict
transforms differs from this degree by zero or one. This is the section estimate
used to decrease the Hirzebruch index before taking the final link to a smaller
Sarkisov degree. The intersection computation uses the total exceptional
classes as in [Lutz, Proposition 8.7][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=70
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Module
open TauCeti.AlgebraicGeometry TauCeti.SymmetricAlgebra TauCeti.Toric
open LineBundleClass Scheme.IdealSheafData Chow

namespace QPainleve.BlowupTower.IsClosedPointTower

variable (k₀ : Type) [Field k₀] [IsAlgClosed k₀]

attribute [local instance] MvPolynomial.gradedAlgebra

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (e : ℕ) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (e : ℤ) • b 0 - b 1])
  {Y : Scheme} {n : ℕ} {T : BlowupTower (Φ.finiteFanScheme k₀) n Y}
  (hT : IsClosedPointTower (Φ.finiteFanScheme k₀) T)

local notation "S" => Spec (CommRingCat.of k₀)
local notation "X" => Fan.finiteFanScheme k₀ Φ
local notation "f" => (X ↘ S)
local notation "P" => Proj (homogeneousSubmodule k₀ (Fin 3 → k₀))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle k₀ (Fin 3 → k₀) 1)
local notation "coords" => Pi.basisFun k₀ (Fin 3)
local notation "plane[" b "," h "]" => Fan.projectiveSpace b h
local notation "planeIso[" b "," h "]" =>
  (Fan.projectivePlaneIso k₀ b h ≪≫ Module.Basis.polynomialProjIso coords)
local notation "D[" Ψ "," h "]" => Fan.toricBoundaryIdeal k₀ Ψ (Fan.IsComplete.nonempty_cones h)
local notation "C" => Φ.rayDivisorIdeal k₀ hΦ (r 2)
local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)

/-- The total base order on the successive strict transforms of the positive
invariant section lies between the fiber coefficient minus one and the fiber
coefficient. The pole decompositions are for the specified ruling projection
and the specified target plane morphism on the same resolution. -/
theorem section_order_sum_of_hirzebruch_plane
    (d : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)
    (g : Y ⟶ P) (hg : g ≫ P ↘ S = T.toBase ≫ f) (hbir : Scheme.BirationalOver g (𝟙 P))
    (D : Y.IdealSheafData) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 f :=
      rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΦ
    letI : Smooth f := SmoothOfRelativeDimension.smooth 2 f
    let : IsNoetherian X := isNoetherian_of_finiteType f
    let : Y.Over S := ⟨T.toBase ≫ f⟩
    letI : Smooth (Y ↘ S) := (hT.smoothOfRelativeDimension f).smooth
    letI : g.IsOver S := ⟨hg⟩
    D[Φ,hc].comap T.toBase = D * hT.ramificationIdealSheafToBase k₀ →
    (D[plane[d,hi], Fan.isComplete_projectiveSpace d hi].comap (planeIso[d,hi]).inv).comap g =
      D * ramificationIdealSheaf k₀ g →
    let v := (T.picardMarking hT f).symm (Additive.ofMul (pullback g H))
    let a := (Φ.hirzebruchPicardBasis k₀ b e hΦ r hr).repr v.1 0
    a - 1 ≤ ∑ j ∈ hT.strictTransformCenterIndices C, -v.2 j ∧
      (∑ j ∈ hT.strictTransformCenterIndices C, -v.2 j) ≤ a := by
  intro hcones hsmooth hnoeth hOver hpole hplane v a
  let := hcones
  let := hsmooth
  let : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  let := hnoeth
  let := hOver
  let : (X).IsProjectiveOver k₀ :=
    Φ.isProjectiveOver_finiteFanScheme_of_isComplete k₀ hΦ hc b
  let : IsRegular (C).subscheme := Φ.isRegular_rayBoundary k₀ hΦ (r 2)
  have hdim : topologicalKrullDim (C).subscheme = 1 := by
    rw [Φ.rayDivisorIdeal_def k₀ hΦ (r 2)]
    exact QPainleve.topologicalKrullDim_vanishingIdeal_subscheme k₀
      (topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)) _
  have htriangle := Fan.projectivePlaneIso_comap_coordinateTriangle k₀ d hi
    (Fan.isComplete_projectiveSpace d hi).nonempty_cones
  simp only [← htriangle, ← comap_comp, Iso.trans_inv, Category.assoc,
    Iso.inv_hom_id, Category.comp_id] at hplane
  have hsupport := congrArg Scheme.IdealSheafData.support hplane
  rw [support_mul] at hsupport
  have hbounds := hT.section_order_sum_of_triangle
    (Φ.isEffectiveCartier_rayDivisorIdeal k₀ hΦ (r 2))
    hdim
    (Fan.boundaryIdeal_le_rayBoundaryIdeal k₀ (r 2) hΦ) g hg hbir hpole
    (le_sup_left.trans_eq hsupport.symm)
  let := Φ.uniqueFactorizationMonoid_stalk_finiteFanScheme (R := k₀) hΦ
  let basis := Φ.hirzebruchPicardBasis k₀ b e hΦ r hr
  let pairing := intersectionBilinForm k₀ X
  let sectionClass :=
    Additive.ofMul (mk (Φ.isEffectiveCartier_rayDivisorIdeal k₀ hΦ (r 2)).toInvertibleSheaf)⁻¹
  have hclass : sectionClass =
      Additive.ofMul (primeDivisorClass (Φ.rayBoundaryChartPoint (R := k₀) hΦ (r 2))) := by
    dsimp only [sectionClass]
    rw [primeDivisorClass_def, mk_toInvertibleSheaf_congr _ _ (Φ.rayDivisorIdeal_def k₀ hΦ (r 2))]
  obtain ⟨h₀, h₁⟩ := Φ.hirzebruch_opposite_section_coordinates k₀ b e hΦ r hr
  rw [← hclass] at h₀ h₁
  have hexpand : sectionClass = (e : ℤ) • basis 0 + basis 1 := by
    simpa only [basis, Fin.sum_univ_two, h₀, h₁, one_smul] using (basis.sum_repr sectionClass).symm
  have h := congrArg (pairing v.1) hexpand
  rw [map_add, map_zsmul] at h
  obtain ⟨hF, hS⟩ := Φ.hirzebruchPicardBasis_intersection_repr k₀ b e hΦ r hr hc v.1
  -- The fiber contribution cancels the negative section's self-intersection term.
  have hdeg : pairing v.1 sectionClass = basis.repr v.1 0 := by
    rw [h, hF, hS, Int.zsmul_eq_mul]
    ring
  have hdegree : classIntersectionNumber k₀ X v.1.toMul sectionClass.toMul = a :=
    (intersectionBilinForm_apply k₀ X v.1 sectionClass).symm.trans hdeg
  simp only [v, sectionClass, toMul_ofMul] at hdegree
  dsimp only at hbounds
  rwa [hdegree] at hbounds

end QPainleve.BlowupTower.IsClosedPointTower
