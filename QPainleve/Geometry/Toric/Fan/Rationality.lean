/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import QPainleve.Geometry.Toric.Fan.Adjacency
public import QPainleve.Geometry.Toric.BaseChange.FunctionField

import QPainleve.Geometry.Toric.Fan.Ray
import TauCeti.Geometry.Toric.Algebraic.Fan.AffineSpace.Scheme

/-!
# Rationality from an affine space chart

The cone on an integral basis has a polynomial coordinate ring over the coefficient
domain. Its affine chart is an affine space and is dense in the fan scheme.
-/

public section

open AlgebraicGeometry CategoryTheory Module

namespace TauCeti.Toric.Fan

universe u

variable (R : Type u) [CommRing R] [IsDomain R]
  {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i)

/-- A toric scheme with a cone spanned by an integral basis is rational over its base. -/
theorem isRationalOver_of_hull_basis_mem {ι : Type u} [Finite ι]
    (b : Basis ι ℤ N) (h : PointedCone.hull ℝ (Set.range fun j ↦ i (b j)) ∈ Φ.cones) :
    Scheme.IsRationalOver (Φ.finiteFanSchemeToSpec R) := by
  let := Fintype.ofFinite ι
  have hcone : projectiveSpaceCone b i {none}ᶜ ∈ Φ.cones := by
    rwa [projectiveSpaceCone_compl_none]
  let σ : Φ.cones := ⟨projectiveSpaceCone b i {none}ᶜ, hcone⟩
  let : Nonempty Φ.cones := ⟨σ⟩
  let e : affineChartRing R Φ.lattice σ.val ≃ₐ[R] MvPolynomial ι R :=
    AddMonoidAlgebra.domCongr R R (affineSpaceDualSemigroupEquiv b Φ.lattice)
  let g := (AffineSpace.SpecIso ι (.of R)).hom ≫
    (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op).hom
  let j := Φ.affineChartι R σ
  let f := g ≫ j
  have : IsOpenImmersion f := inferInstanceAs (IsOpenImmersion (g ≫ j))
  have : IsDominant f := isDominant_of_isOpenImmersion f
  refine ⟨ι, (f.birationalOver _ _ ?_).symm⟩
  change (g ≫ j) ≫ Φ.finiteFanSchemeToSpec R = _
  rw [Category.assoc, show j = Φ.affineChartι R σ from rfl,
    Φ.affineChartι_finiteFanSchemeToSpec R σ]
  change ((AffineSpace.SpecIso ι (.of R)).hom ≫
      Spec.map (CommRingCat.ofHom e.toRingHom)) ≫
      Spec.algebraMap R (affineChartRing R Φ.lattice σ.val) = _
  rw [Category.assoc, Spec.algebraMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have he : e.toRingHom.comp (algebraMap R (affineChartRing R Φ.lattice σ.val)) =
      algebraMap R (MvPolynomial ι R) := e.toAlgHom.comp_algebraMap
  rw [he]
  change (AffineSpace.SpecIso ι (.of R)).hom ≫
      Spec.map (CommRingCat.ofHom MvPolynomial.C) = _
  rw [← AffineSpace.SpecIso_inv_over (n := ι) (.of R), Iso.hom_inv_id_assoc]

/-- A regular rank-two fan with two distinct rays in a common cone realizes
a rational surface. -/
theorem isRationalOver_of_ray_ne_of_le (hΦ : Φ.IsRegular) (hN : Module.finrank ℤ N = 2)
    {ρ τ : Φ.Ray} {σ : Φ.cones} (hne : ρ ≠ τ) (hρ : ρ.toCone ≤ σ) (hτ : τ.toCone ≤ σ) :
    Scheme.IsRationalOver (Φ.finiteFanSchemeToSpec R) := by
  obtain ⟨b, hb₀, hb₁⟩ := Fan.exists_basis_of_ray_ne_of_le
    (Fan.isRegular_iff.mp hΦ _ σ.property) hN hne hρ hτ
  have hcone := Φ.cone_eq_sup_of_ray_ne_of_le hΦ hN hne hρ hτ
  let b' := b.reindex (Equiv.ulift.symm : Fin 2 ≃ ULift.{u} (Fin 2))
  apply Φ.isRationalOver_of_hull_basis_mem R b'
  rw [show Set.range (fun j : ULift.{u} (Fin 2) ↦ i (b' j)) =
      Set.range (fun j : Fin 2 ↦ i (b j)) by
    simp only [b', Basis.reindex_apply, Equiv.symm_symm]
    exact Equiv.ulift.surjective.range_comp (fun j : Fin 2 ↦ i (b j))]
  have hpair : Set.range (fun j : Fin 2 ↦ i (b j)) = {i (b 0)} ∪ {i (b 1)} := by
    ext x
    simp [Fin.exists_fin_succ, eq_comm, or_comm]
  rw [Ray.toCone_eq_hull_primitiveGenerator, Ray.toCone_eq_hull_primitiveGenerator,
    ← hb₀, ← hb₁, ← Submodule.span_union, ← hpair] at hcone
  have hσ : σ.val = PointedCone.hull ℝ (Set.range fun j : Fin 2 ↦ i (b j)) := hcone
  rw [← hσ]
  exact σ.property

/-- A complete regular rank-two fan realizes a rational surface. -/
theorem isRationalOver_of_isComplete (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (b : Basis (Fin 2) ℤ N) :
    Scheme.IsRationalOver (Φ.finiteFanSchemeToSpec R) := by
  have : Nontrivial N := b.equivFun.toEquiv.nontrivial
  obtain ⟨ρ⟩ := Φ.nonempty_ray_of_isComplete hc
  obtain ⟨τ, ⟨hdet, σ, hr, ht⟩, -⟩ := (exists_unique_ray_neighbor_on_each_side b hΦ hc ρ).1
  have hne : ρ ≠ τ := by
    intro h
    rw [← h, b.detDualEquiv_self] at hdet
    exact zero_ne_one hdet
  exact Φ.isRationalOver_of_ray_ne_of_le R hΦ
    ((finrank_eq_card_basis b).trans (Fintype.card_fin 2)) hne hr ht

end TauCeti.Toric.Fan
