/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.FaceLocalization
public import QPainleve.Geometry.Toric.Fan.Subdivision.Basic
public import TauCeti.Geometry.Toric.Algebraic.Fan.DenseTorus

import TauCeti.Geometry.Toric.Algebraic.Fan.SubfanScheme
import TauCeti.RingTheory.Spectrum.Prime.Topology

/-!
# Density of the torus in a toric scheme

The inclusion of a face induces an injective map of affine toric coordinate rings, so
the corresponding open immersion is dominant. Applying this to the zero face in each
chart shows that Tau Ceti's torus inclusion is dense in any nonempty fan realization.
`FanHom.denseTorusι_comp_algebraicMap` reduces dominance of a toric morphism to the
map on dense tori, where injectivity on characters suffices.
The common-cone chart comparison identifies the inverse image of the torus under a subdivision.
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative

namespace TauCeti.Toric.Fan

universe u

variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- The torus inclusion in the scheme of a nonempty fan is dominant. -/
instance isDominant_denseTorusι (Φ : Fan i) (hΦ : Nonempty Φ.cones) :
    IsDominant (Φ.denseTorusι hΦ) := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨σ, y, rfl⟩ := Φ.exists_affineToricChartι_apply_eq x
  let hface := (Φ.isToricCone σ.property).salient.bot_isFaceOf
  have hdense := (isDominant_faceAffineToricSchemeMap Φ.lattice hface).denseRange
  have hclosure := (Φ.affineToricChartι σ).continuous.range_subset_closure_image_dense hdense
  have hcomp : ⇑(faceAffineToricSchemeMap Φ.lattice hface ≫ Φ.affineToricChartι σ) =
      ⇑(Φ.affineToricChartι σ) ∘ ⇑(faceAffineToricSchemeMap Φ.lattice hface) :=
    funext (Scheme.Hom.comp_apply _ _)
  rw [← Set.range_comp, ← hcomp, ← Φ.denseTorusι_face σ] at hclosure
  exact hclosure ⟨y, rfl⟩

/-- The subfan consisting of the zero cone has image the dense torus. -/
theorem range_subfanInclusion_algebraicMap_of_eq_singleton_bot
    (A : Fan i) (hA : Nonempty A.cones) {T : Set (PointedCone ℝ V)}
    (hT : T ⊆ A.cones) (hface : ∀ ⦃σ τ⦄, σ ∈ T → τ.IsFaceOf σ → τ ∈ T)
    (heq : T = {⊥}) :
    Set.range (A.subfanInclusion T hT hface).algebraicMap = Set.range (A.denseTorusι hA) := by
  have hbot : (⊥ : PointedCone ℝ V) ∈ T := heq.symm ▸ Set.mem_singleton _
  rw [A.range_subfanInclusion_algebraicMap T hT hface,
    A.denseTorusι_eq_affineToricChartι hA (hT hbot)]
  refine le_antisymm (iSup_le fun σ ↦ ?_) (le_iSup_of_le ⟨⊥, ?_⟩ le_rfl)
  · have hσ : σ.val ∈ T := by simpa only [subfan_cones] using σ.property
    exact le_of_eq (congrArg (fun τ : A.cones ↦ Set.range (A.affineToricChartι τ))
      (Subtype.ext (Set.mem_singleton_iff.mp (heq ▸ hσ))))
  · simpa only [subfan_cones] using hbot

end TauCeti.Toric.Fan

namespace TauCeti.Toric.FanHom

variable {N N' : Type u} {V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}

/-- A toric morphism out of a nonempty fan is dominant if pullback is injective on
the character lattice of the target. -/
theorem isDominant_algebraicMap_of_injective_dualMap (f : FanHom Φ Ψ) (hΦ : Nonempty Φ.cones)
    (hf : Function.Injective fun m : N' →+ ℤ ↦ m.comp f.latticeMap) :
    IsDominant f.algebraicMap := by
  let hbot : Set.MapsTo f.realMap (⊥ : PointedCone ℝ V) (⊥ : PointedCone ℝ V') :=
    by simp [Set.MapsTo]
  let d := dualSemigroupMap Φ.lattice Ψ.lattice f.latticeMap f.realMap f.map_lattice hbot
  let q := affineToricSchemeMap Φ.lattice Ψ.lattice f.latticeMap f.realMap f.map_lattice hbot
  have hq : IsDominant q := by
    dsimp only [q]
    rw [affineToricSchemeMap_def]
    refine ⟨RingHom.denseRange_comap_of_injective _ ?_⟩
    have he : affineCoordinateRingMap Φ.lattice Ψ.lattice f.latticeMap f.realMap
        f.map_lattice hbot = MonoidAlgebra.mapDomainAlgHom ℂ ℂ d.toMultiplicative := by
      apply MonoidAlgebra.algHom_ext
      · intro m
        rw [← ofAdd_toAdd m, affineCoordinateRingMap_single]
        simp [d]
      · ext
    rw [he]
    apply MonoidAlgebra.mapDomain_injective
    intro m n hmn
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    apply hf
    simpa only [AddMonoidHom.coe_toMultiplicative, Function.comp_apply, toAdd_ofAdd,
      coe_dualSemigroupMap, d] using
      congrArg (fun x : Multiplicative (dualSemigroup Φ.lattice ⊥) ↦
        (x.toAdd : N →+ ℤ)) hmn
  have : IsDominant (Φ.denseTorusι hΦ ≫ f.algebraicMap) := by
    rw [f.denseTorusι_comp_algebraicMap hΦ]
    exact inferInstanceAs (IsDominant (q ≫ Ψ.denseTorusι _))
  exact IsDominant.of_comp (Φ.denseTorusι hΦ) _

end TauCeti.Toric.FanHom

namespace TauCeti.Toric.Fan.IsSubdivision

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i} (h : Φ.IsSubdivision Ψ)
  (hΦ : Nonempty Φ.cones) (hΨ : Nonempty Ψ.cones)

/-- A subdivision pulls back the open dense torus to the open dense torus. -/
theorem preimage_range_denseTorusι :
    h.toFanHom.algebraicMap ⁻¹' Set.range (Ψ.denseTorusι hΨ) =
      Set.range (Φ.denseTorusι hΦ) := by
  have hbΦ : (⊥ : PointedCone ℝ V) ∈ Φ.cones := let ⟨σ⟩ := hΦ; Φ.bot_mem σ.property
  have hbΨ : (⊥ : PointedCone ℝ V) ∈ Ψ.cones := let ⟨σ⟩ := hΨ; Ψ.bot_mem σ.property
  rw [Φ.denseTorusι_eq_affineToricChartι hΦ hbΦ, Ψ.denseTorusι_eq_affineToricChartι hΨ hbΨ]
  exact h.preimage_range_affineToricChartι hbΦ hbΨ

end TauCeti.Toric.Fan.IsSubdivision
