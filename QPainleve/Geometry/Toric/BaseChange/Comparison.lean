/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.BaseChange.Boundary
public import QPainleve.Geometry.Toric.BaseChange.FanMap
public import QPainleve.Geometry.Toric.Fan.Boundary.Basic
public import TauCeti.Geometry.Toric.Algebraic.BaseChange.Complex

/-!
# Comparing the two toric scheme constructions

The change from multiplicative to additive notation for the chart exponents
commutes with pullback along a fan morphism and identifies the reduced boundaries.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.Toric.FanHom

variable {N N' V V' : Type} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}

/-- The comparison with the complex toric scheme is natural in the fan. -/
@[reassoc]
theorem finiteFanSchemeComplexIso_inv_comp_finiteFanSchemeHom (f : FanHom Φ Ψ) :
    Φ.finiteFanSchemeComplexIso.inv ≫ f.finiteFanSchemeHom ℂ =
      f.algebraicMap ≫ Ψ.finiteFanSchemeComplexIso.inv := by
  apply Φ.algebraicRealization_hom_ext
  intro σ
  let τ : Ψ.cones := ⟨f.leastCone σ.property, f.leastCone_mem σ.property⟩
  have hm : Set.MapsTo f.realMap (σ.val : Set V) (τ.val : Set V') :=
    fun x hx ↦ f.map_le_leastCone σ.property ⟨x, hx, rfl⟩
  rw [Fan.affineToricChartι_finiteFanSchemeComplexIso_inv_assoc,
    f.affineChartι_comp_finiteFanSchemeHom ℂ σ τ hm, ← Category.assoc _ f.algebraicMap,
    f.affineToricChartι_comp_algebraicMap_of_mapsTo σ τ hm, Category.assoc,
    Fan.affineToricChartι_finiteFanSchemeComplexIso_inv]
  simp only [← Category.assoc, affineToricSchemeIsoAddMonoidAlgebraSpec_hom_left,
    affineChartMap_def, affineToricSchemeMap_def, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply CommRingCat.hom_ext
  let eσ := AddMonoidAlgebra.toMultiplicativeAlgEquiv ℂ ℂ (dualSemigroup Φ.lattice σ.val)
  let eτ := AddMonoidAlgebra.toMultiplicativeAlgEquiv ℂ ℂ (dualSemigroup Ψ.lattice τ.val)
  have h :
      eσ.toAlgHom.comp
          (AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ
            (dualSemigroupMap Φ.lattice Ψ.lattice f.latticeMap f.realMap f.map_lattice hm)) =
        (affineCoordinateRingMap Φ.lattice Ψ.lattice f.latticeMap f.realMap f.map_lattice hm).comp
          eτ.toAlgHom := by
    apply AddMonoidAlgebra.algHom_ext
    · intro m
      simp only [AlgHom.coe_comp, AlgEquiv.coe_toAlgHom, Function.comp_apply, eσ, eτ,
        AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single,
        AddMonoidAlgebra.toMultiplicativeAlgEquiv_single,
        affineCoordinateRingMap_single]
    · exact Subsingleton.elim _ _
  exact congrArg AlgHom.toRingHom h

end TauCeti.Toric.FanHom

open AlgebraicGeometry CategoryTheory Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i)

/-- The comparison identifies the vanishing ideals of the two reduced boundaries. -/
theorem comap_boundaryIdeal_finiteFanSchemeComplexIso_hom (h₀ : Nonempty Φ.cones) :
    (Φ.boundaryIdeal h₀).comap Φ.finiteFanSchemeComplexIso.hom = Φ.toricBoundaryIdeal ℂ h₀ := by
  let σ : Φ.cones := ⟨⊥, Φ.bot_mem h₀.some.property⟩
  have htorus : Set.range (Φ.denseTorusι h₀) =
      Set.range (Φ.affineToricChartι σ) := by
    rw [Φ.denseTorusι_eq_affineToricChartι h₀ σ.property]
  have hrange : Φ.finiteFanSchemeComplexIso.hom ⁻¹' Set.range (Φ.denseTorusι h₀) =
      Set.range (Φ.affineChartι ℂ σ) := by
    rw [htorus]
    ext x
    change Φ.finiteFanSchemeComplexIso.hom x ∈ Set.range (Φ.affineToricChartι σ) ↔
      x ∈ Set.range (Φ.affineChartι ℂ σ)
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨(affineToricSchemeIsoAddMonoidAlgebraSpec Φ.lattice σ).hom.left y, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Φ.affineToricChartι_finiteFanSchemeComplexIso_inv,
        Scheme.Hom.comp_apply, hy, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
      rfl
    · rintro ⟨y, rfl⟩
      refine ⟨(affineToricSchemeIsoAddMonoidAlgebraSpec Φ.lattice σ).inv.left y, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Φ.affineChartι_finiteFanSchemeComplexIso_hom,
        Scheme.Hom.comp_apply]
  rw [Φ.boundaryIdeal_def, Φ.toricBoundaryIdeal_def ℂ h₀, comap_vanishingIdeal_of_isOpenImmersion]
  congr 1
  apply SetLike.coe_injective
  exact Set.preimage_compl.trans (congrArg Set.compl hrange)

end TauCeti.Toric.Fan
