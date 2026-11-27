/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import QPainleve.Geometry.Toric.BaseChange.FanMap

import TauCeti.RingTheory.Spectrum.Prime.Topology

/-!
# Density of the zero-cone chart

The zero-cone chart of a nonempty fan is the dense torus. Injectivity of the pullback
on characters implies dominance of the induced toric morphism.
-/

public section

open AlgebraicGeometry CategoryTheory AddMonoidAlgebra

namespace TauCeti.Toric

/-- A coefficient-one monomial on the zero-cone chart is a unit. -/
theorem isUnit_single_bot {R N V : Type*} [CommSemiring R] [AddCommGroup N] [AddCommGroup V]
    [Module ℝ V] {i : N →+ V} (hi : IsIntegralLattice i) (m : dualSemigroup hi ⊥) :
    IsUnit (single m (1 : R)) := by
  refine IsUnit.of_mul_eq_one (single ⟨-(m : N →+ ℤ), by simp⟩ 1) ?_
  rw [single_mul_single, mul_one]
  change single _ (1 : R) = single 0 (1 : R)
  exact congrArg (fun a ↦ single a (1 : R)) (Subtype.ext (add_neg_cancel (m : N →+ ℤ)))

universe u

variable (R : Type u) [CommRing R]
  {N N' : Type u} {V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'}
  {σ : PointedCone ℝ V} {τ : PointedCone ℝ V'}

/-- An affine chart morphism is dominant if its pullback on dual semigroups is injective. -/
theorem isDominant_affineChartMap (hi : IsIntegralLattice i) (hi' : IsIntegralLattice i')
    (f : N →+ N') (g : V →ₗ[ℝ] V') (hfg : ∀ n, g (i n) = i' (f n))
    (hmaps : Set.MapsTo g σ τ) (hf : Function.Injective (dualSemigroupMap hi hi' f g hfg hmaps)) :
    IsDominant (affineChartMap R hi hi' f g hfg hmaps) := by
  rw [affineChartMap_def]
  exact ⟨RingHom.denseRange_comap_of_injective _ (mapDomain_injective hf)⟩

/-- The map of affine toric charts induced by a face inclusion is dominant. -/
theorem isDominant_faceAffineChartMap (hi : IsIntegralLattice i)
    {σ τ : PointedCone ℝ V} (h : σ.IsFaceOf τ) :
    IsDominant (faceAffineChartMap R hi h) := by
  rw [faceAffineChartMap_eq_affineChartMap]
  refine isDominant_affineChartMap R hi hi _ _ _ _ fun _ _ hm ↦ Subtype.ext ?_
  simpa using congrArg Subtype.val hm

/-- The zero-cone chart of a nonempty fan is dense in the toric scheme. -/
instance Fan.isDominant_affineChartι_bot (Φ : Fan i)
    (hbot : (⊥ : PointedCone ℝ V) ∈ Φ.cones) : IsDominant (Φ.affineChartι R ⟨⊥, hbot⟩) := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨σ, y, rfl⟩ := Φ.exists_affineChartι_apply_eq R x
  have hface := (Φ.isToricCone σ.property).salient.bot_isFaceOf
  have hdense := (isDominant_faceAffineChartMap R Φ.lattice hface).denseRange
  have hclosure := (Φ.affineChartι R σ).continuous.range_subset_closure_image_dense hdense
  have hcomp : ⇑(faceAffineChartMap R Φ.lattice hface ≫ Φ.affineChartι R σ) =
      ⇑(Φ.affineChartι R σ) ∘ ⇑(faceAffineChartMap R Φ.lattice hface) :=
    funext (Scheme.Hom.comp_apply _ _)
  rw [← Set.range_comp, ← hcomp,
    Fan.faceAffineChartMap_comp_affineChartι R (τ := ⟨⊥, hbot⟩) (σ := σ) hface] at hclosure
  exact hclosure ⟨y, rfl⟩

/-- A morphism from a nonempty fan is dominant if pullback is injective on the character
lattice of the target. -/
theorem FanHom.isDominant_finiteFanSchemeHom_of_injective_dualMap {Φ : Fan i} {Ψ : Fan i'}
    (f : FanHom Φ Ψ) (hΦ : Nonempty Φ.cones)
    (hf : Function.Injective fun m : N' →+ ℤ ↦ m.comp f.latticeMap) :
    IsDominant (f.finiteFanSchemeHom R) := by
  have hbot : (⊥ : PointedCone ℝ V) ∈ Φ.cones := Φ.bot_mem hΦ.some.property
  have hbot' : (⊥ : PointedCone ℝ V') ∈ Ψ.cones :=
    Ψ.bot_mem (f.leastCone_mem hΦ.some.property)
  have hmaps : Set.MapsTo f.realMap ((⊥ : PointedCone ℝ V) : Set V)
      ((⊥ : PointedCone ℝ V') : Set V') := by simp [Set.MapsTo]
  have hchart : IsDominant
      (affineChartMap R Φ.lattice Ψ.lattice f.latticeMap f.realMap f.map_lattice hmaps) := by
    refine isDominant_affineChartMap R _ _ _ _ _ _ fun _ _ hm ↦ Subtype.ext (hf ?_)
    simpa only [coe_dualSemigroupMap] using congrArg Subtype.val hm
  have : IsDominant (Φ.affineChartι R ⟨⊥, hbot⟩ ≫ f.finiteFanSchemeHom R) := by
    rw [affineChartι_comp_finiteFanSchemeHom R f ⟨⊥, hbot⟩ ⟨⊥, hbot'⟩ hmaps]
    infer_instance
  exact IsDominant.of_comp (Φ.affineChartι R ⟨⊥, hbot⟩) _

end TauCeti.Toric
