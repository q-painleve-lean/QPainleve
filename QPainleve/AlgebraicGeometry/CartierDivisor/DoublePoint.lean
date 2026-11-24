/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import QPainleve.AlgebraicGeometry.CartierDivisor.ZeroDivisor
public import TauCeti.AlgebraicGeometry.IdealSheaf.Stalk
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
import QPainleve.AlgebraicGeometry.CartierDivisor.LocalEquation
import QPainleve.AlgebraicGeometry.LineBundle.Frame

/-!
# Double points in linear systems

The dimension of the local ring modulo the square of its maximal ideal bounds
the number of linear conditions for a section to vanish to order two at a
point. On an integral regular scheme, a nonzero such section cuts out an
effective Cartier divisor that is singular at that point.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- If the section space has larger dimension than the first infinitesimal
neighbourhood of a point, a nonzero section vanishes to order at least two there. -/
theorem exists_two_le_stalkOrder_zeroIdeal_of_finrank_lt (L : InvertibleSheaf X) (x : X)
    [Module.Finite k (X.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ 2)]
    (h : Module.finrank k (X.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ 2) <
      Module.finrank k Γ(L.obj, ⊤)) :
    ∃ s : Γ(L.obj, ⊤), s ≠ 0 ∧ 2 ≤ (L.zeroIdeal s).stalkOrder x := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  obtain ⟨b, hb⟩ := L.obj.exists_mem_nonvanishingLocus_of_isAffineOpen hV hxV
  obtain ⟨U, hU, hxU, hle⟩ := exists_isAffineOpen_mem_and_subset hb
  have hUV : U ≤ V := hle.trans (L.obj.nonvanishingLocus_le b)
  let a := L.obj.presheaf.map (homOfLE hUV).op b
  have ha : U ≤ L.obj.nonvanishingLocus a := L.obj.le_nonvanishingLocus_map _ _ hle
  let R := X.presheaf.stalk x
  let m := IsLocalRing.maximalIdeal R
  let : Algebra k Γ(X, U) :=
    ((X.baseRingToStructurePresheaf k).app (.op U)).hom.toAlgebra
  let : Algebra Γ(X, U) R := (X.presheaf.germ U x hxU).hom.toAlgebra
  let : IsScalarTower k Γ(X, U) (X.presheaf.stalk x) :=
    X.isScalarTower_base_section_stalk k ⟨x, hxU⟩
  let : Module k Γ(L.obj, U) := sectionsBaseModule k L.obj U
  let : IsScalarTower k Γ(X, U) Γ(L.obj, U) :=
    IsScalarTower.of_compHom _ _ _
  let germ : Γ(X, U) →ₐ[k] R :=
    { (X.presheaf.germ U x hxU).hom with
      commutes' := fun c ↦ (IsScalarTower.algebraMap_apply k Γ(X, U) R c).symm }
  let F := ((L.obj.sectionFrame a ha).symm.restrictScalars k).toLinearMap
  let restr : Γ(L.obj, ⊤) →ₗ[k] Γ(L.obj, U) :=
    { toFun := L.obj.presheaf.map U.leTop.op
      map_add' := map_add _
      map_smul' := fun c s ↦ by
        rw [base_smul_globalSections_eq_baseRingToStructurePresheaf_smul]
        exact presheaf_map_baseRingToStructurePresheaf_smul k L.obj U.leTop c s }
  let q := (Ideal.Quotient.mkₐ k (m ^ 2)).toLinearMap.comp
    (germ.toLinearMap.comp (F.comp restr))
  have hq : ¬ Function.Injective q :=
    fun hinj ↦ (not_le_of_gt h) (LinearMap.finrank_le_finrank_of_injective hinj)
  rw [← LinearMap.ker_eq_bot] at hq
  obtain ⟨s, hqs, hs⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hq
  rw [LinearMap.mem_ker] at hqs
  have hq_apply : q s = Ideal.Quotient.mk (m ^ 2)
      ((X.presheaf.germ U x hxU).hom
        ((L.obj.sectionFrame a ha).symm (L.obj.presheaf.map U.leTop.op s))) := rfl
  refine ⟨s, hs, ((L.zeroIdeal s).natCast_le_stalkOrder_iff x 2).mpr ?_⟩
  rw [(L.zeroIdeal s).stalkIdeal_eq_map ⟨U, hU⟩ x hxU,
    L.zeroIdeal_ideal_eq_span_singleton s ⟨U, hU⟩ a ha, Ideal.map_span,
    Set.image_singleton, Ideal.span_singleton_le_iff_mem]
  rw [hq_apply, sectionFrame_symm_apply] at hqs
  exact Ideal.Quotient.eq_zero_iff_mem.mp hqs

end TauCeti.AlgebraicGeometry.InvertibleSheaf
