/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Basic
public import QPainleve.Geometry.Toric.Fan.Mutation.Pullback

import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order

/-!
# Boundary valuations of toric mutations

The pivot fiber misses the generic point of every toric boundary divisor. On the
complement of that fiber, the elementary transformation sends these generic points
to the corresponding points of the sheared fan, and therefore transports the boundary
orders of all rational functions. This is the boundary transport used in the
tropicalization of Gross, Hacking and Keel, *Birational geometry of cluster algebras*,
(1.4) and the proof of Theorem 5.6.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory AddMonoidAlgebra Multiplicative
open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  (Φ : Fan i) (b : Module.Basis (Fin 2) ℤ N) {v : N} (c : ℂˣ)
  (hv : v ≠ 0) (hpos : PointedCone.hull ℝ {i v} ∈ Φ.cones)
  (hneg : PointedCone.hull ℝ {i (-v)} ∈ Φ.cones)

local notation "Ψ" => mutationFan Φ b hv hpos hneg
local notation "h₀" => detCharacter_nonneg_or_nonpos Φ b hv hpos hneg
local notation "h₁" => mutationDetCharacter_nonneg_or_nonpos Φ b hv hpos hneg
local notation "U₀" => mutationComplement Φ b h₀ (c : ℂ)
local notation "U₁" => mutationComplement Ψ b h₁ (c : ℂ)
local notation "E" => mutationComplementIso Φ b (c : ℂ) hv hpos hneg

/-- The generic point of every boundary ray is outside the pivot fiber. -/
theorem rayBoundaryPoint_mem_mutationComplement (hΦ : Φ.IsRegular) (ρ : Φ.Ray) :
    (Φ.rayBoundaryPoint hΦ ρ).val ∈ U₀ := by
  classical
  let σ := ρ.toCone
  let hσ := Φ.isToricCone σ.property
  let hreg := (isRegular_iff.mp hΦ) _ σ.property
  let r := ρ.toToricRay Φ σ le_rfl
  let x := (hreg.rayPoint Φ.lattice hσ r).val
  obtain ⟨side, hs⟩ := Φ.exists_mutationChartCharacter_mem_dualSemigroup b hv hpos hneg σ
  let S := dualSemigroup Φ.lattice σ.val
  let e := toMultiplicativeAlgEquiv ℂ ℂ S
  let q : S := ⟨mutationChartCharacter b (v := v) side, hs⟩
  let f := Φ.mutationChartBinomial side (c : ℂ) q
  have hq : ofAdd q ≠ ofAdd (0 : S) := fun he ↦
    mutationChartCharacter_ne_zero b hv side (congrArg (fun t ↦ (t.toAdd : S).val) he)
  have hcoeff : (e f).coeff (ofAdd (0 : S)) = cond side (c : ℂ) 1 := by
    simp only [f, mutationChartBinomial, e, map_add, toMultiplicativeAlgEquiv_single,
      MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.coeff_single,
      Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne hq.symm, add_zero]
  have hf : e f ∉ x.asIdeal := by
    intro h
    rw [IsRegularCone.rayPoint_asIdeal] at h
    have hz := coeff_eq_zero_of_mem_rayIdeal Φ.lattice hσ hreg r h 0 (by simp)
    rw [hcoeff] at hz
    cases side <;> simp [c.ne_zero] at hz
  let j := Spec.map (CommRingCat.ofHom e.toRingEquiv.toRingHom)
  have hj : j ≫ Φ.additiveAffineToricChartι σ = Φ.affineToricChartι σ := by
    rw [additiveAffineToricChartι_def, ← Category.assoc, ← Spec.map_comp]
    rw [← CommRingCat.ofHom_comp, AlgEquiv.symm_toRingEquiv,
      RingEquiv.toRingHom_comp_symm_toRingHom,
      CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  have hopen : j ⁻¹ᵁ (Φ.additiveAffineToricChartι σ ⁻¹ᵁ U₀) = PrimeSpectrum.basicOpen (e f) := by
    rw [Φ.additiveAffineToricChartι_preimage_mutationComplement b σ side hs (c : ℂ) h₀,
      SpecMap_preimage_basicOpen]
    rfl
  have hm : x ∈ j ⁻¹ᵁ (Φ.additiveAffineToricChartι σ ⁻¹ᵁ U₀) := by
    rw [hopen]
    exact hf
  rw [Φ.coe_rayBoundaryPoint hΦ ρ, ← hj, Scheme.Hom.comp_apply]
  exact hm

/-- On the fiber complements, the mutation isomorphism sends the boundary generic
point of a ray to the boundary generic point of its integral shear. -/
theorem mutationComplementIso_hom_rayBoundaryPoint (hΦ : Φ.IsRegular) (ρ : Φ.Ray) :
    ((E).hom ≫ (U₁).ι)
        ⟨(Φ.rayBoundaryPoint hΦ ρ).val, Φ.rayBoundaryPoint_mem_mutationComplement
          b c hv hpos hneg hΦ ρ⟩ =
      ((Ψ).rayBoundaryPoint ((Φ.isRegular_mutationFan_iff b hv hpos hneg).mpr hΦ)
        (Φ.mutationFanRayEquiv b hv hpos hneg ρ)).val := by
  let σ := ρ.toCone
  let τ := Φ.mutationFanRayEquiv b hv hpos hneg ρ
  let hΨ := (Φ.isRegular_mutationFan_iff b hv hpos hneg).mpr hΦ
  let x : (U₀).toScheme := ⟨_, Φ.rayBoundaryPoint_mem_mutationComplement b c hv hpos hneg hΦ ρ⟩
  let g := (E).hom ≫ (U₁).ι
  obtain ⟨side, hs⟩ := Φ.exists_mutationChartCharacter_mem_dualSemigroup b hv hpos hneg σ
  let j := Φ.mutationComplementChartι b σ side hs (c : ℂ) h₀
  have hmem : x ∈ Set.range j := by
    rw [Φ.range_mutationComplementChartι, Φ.range_additiveAffineToricChartι]
    exact (Φ.rayBoundaryPoint_mem_range_affineToricChartι_iff hΦ ρ σ).mpr le_rfl
  have hchart : g x ∈ Set.range ((Ψ).affineToricChartι τ.toCone) := by
    obtain ⟨y, hy⟩ := hmem
    rw [← hy, ← Scheme.Hom.comp_apply, ← (Ψ).range_additiveAffineToricChartι,
      mutationFanRayEquiv_toCone]
    dsimp only [j, g]
    rw [Φ.mutationComplementChartι_comp_mutationComplementIso_hom_assoc,
      mutationComplementChartι_comp_ι]
    exact ⟨_, by rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]⟩
  have htorus : g x ∉ Set.range ((Ψ).denseTorusι ⟨τ.toCone⟩) := by
    intro h
    have ht' : x ∈ g ⁻¹' Set.range ((Ψ).denseTorusι ⟨τ.toCone⟩) := h
    rw [Φ.mutationComplementIso_preimage_range_denseTorusι b (c : ℂ) hv hpos hneg
      ⟨σ⟩ ⟨τ.toCone⟩] at ht'
    exact Φ.rayBoundaryPoint_notMem_range_denseTorusι hΦ ρ ht'
  have hx : Order.coheight (g x) = 1 :=
    (coheight_eq_of_isOpenImmersion g).trans (by
      rw [← coheight_eq_of_isOpenImmersion (U₀).ι (x := x)]
      exact (Φ.rayBoundaryPoint hΦ ρ).property)
  exact congrArg Subtype.val (CodimensionOnePoint.eq_of_specializes
    (y := (Ψ).rayBoundaryPoint hΨ τ) (x := ⟨g x, hx⟩)
    ((Ψ).rayBoundaryPoint_specializes_of_mem_rayChart hΨ τ hchart htorus)).symm

/-- Pullback by toric mutation preserves the order of every rational function
at corresponding boundary rays. -/
theorem ord_rayBoundaryPoint_mutationComplementPullback (hΦ : Φ.IsRegular) (ρ : Φ.Ray) :
    letI : Nonempty Φ.cones := ⟨⟨_, hpos⟩⟩
    letI : Nonempty (Ψ).cones := ⟨Φ.mutationFanConeEquiv b hv hpos hneg ⟨_, hpos⟩⟩
    ∀ f : (Ψ).algebraicRealization.functionField,
      Φ.algebraicRealization.ord (Φ.mutationComplementPullback b (c : ℂ) hv hpos hneg f)
          (Φ.rayBoundaryPoint hΦ ρ).val =
        (Ψ).algebraicRealization.ord f
          ((Ψ).rayBoundaryPoint ((Φ.isRegular_mutationFan_iff b hv hpos hneg).mpr hΦ)
            (Φ.mutationFanRayEquiv b hv hpos hneg ρ)).val := by
  let : Nonempty Φ.cones := ⟨⟨_, hpos⟩⟩
  let : Nonempty (Ψ).cones := ⟨Φ.mutationFanConeEquiv b hv hpos hneg ⟨_, hpos⟩⟩
  let := isIntegral_mutationComplement_source Φ b (c : ℂ) hv hpos hneg
  let := isIntegral_mutationComplement_target Φ b (c : ℂ) hv hpos hneg
  intro f
  let x : (U₀).toScheme := ⟨_, Φ.rayBoundaryPoint_mem_mutationComplement b c hv hpos hneg hΦ ρ⟩
  have hx : (U₀).ι x = (Φ.rayBoundaryPoint hΦ ρ).val := rfl
  have he := ConcreteCategory.congr_hom
    (Φ.mutationComplementPullback_comp_functionFieldMap b (c : ℂ) hv hpos hneg) f
  rw [CommRingCat.comp_apply] at he
  rw [← hx, ← Scheme.ord_functionFieldMap (U₀).ι, he, Scheme.ord_functionFieldMap,
    Φ.mutationComplementIso_hom_rayBoundaryPoint b c hv hpos hneg hΦ ρ]

end TauCeti.Toric.Fan
