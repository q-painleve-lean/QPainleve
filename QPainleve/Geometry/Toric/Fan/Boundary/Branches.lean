/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Automorphism
public import QPainleve.Geometry.Toric.Fan.Boundary.Normalization

import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import QPainleve.Geometry.Toric.Fan.Boundary.Intersection
import QPainleve.Geometry.Toric.Fan.Boundary.Node
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced

/-!
# Ray-preserving automorphisms of toric boundary branches

An automorphism fixing the ray divisors of a complete regular toric surface fixes
each node as the intersection of two ray divisors. Over a node, the normalized ray
component distinguishes its branch.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

universe u

variable (k : Type u) [Field k] {N : Type u} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones]

local notation "X" => Φ.finiteFanScheme k
local notation "D" => Φ.toricBoundaryIdeal k h₀
local notation "C" => Scheme.IdealSheafData.subscheme D
local notation "base" => Spec (CommRingCat.of k)
local notation "I" => Scheme.singularLocus k C
local notation "ν" => Scheme.IdealSheafData.blowupToBase I
local notation "W" => Scheme.IdealSheafData.blowup I
local notation "j" => Scheme.branchSchemeToBlowup k C

omit h₀ in
private theorem fixes_distinguishedSection_of_comap_rayBoundaryIdeal_eq
    (hΦ : Φ.IsRegular) (hdim : Module.finrank ℤ N = 2)
    (e : X ≅ X) (he : ∀ ρ, (Φ.rayDivisorIdeal k hΦ ρ).comap e.hom = Φ.rayDivisorIdeal k hΦ ρ)
    (σ : Φ.cones) (hσ : Nat.card (ToricRay σ.val) = 2) (p : base) :
    e.hom (Φ.distinguishedSection (R := k) σ p) = Φ.distinguishedSection (R := k) σ p := by
  obtain ⟨r, t, hrt, -⟩ := Nat.card_eq_two_iff.mp hσ
  let ρ := (Φ.rayEquiv σ).symm r
  let τ := (Φ.rayEquiv σ).symm t
  have hne : ρ.val ≠ τ.val := fun h ↦ hrt ((Φ.rayEquiv σ).symm.injective (Subtype.ext h))
  have hker : (Φ.distinguishedSection (R := k) σ).ker.comap e.hom =
      (Φ.distinguishedSection (R := k) σ).ker := by
    rw [← Φ.sup_rayBoundaryIdeal_eq_ker_distinguishedPoint k hΦ hdim hne σ ρ.property τ.property,
      comap_sup, he, he]
  let f := Φ.distinguishedSection (R := k) σ
  have : IsClosedImmersion f := Φ.isClosedImmersion_distinguishedSection (R := k) σ
  have hs : (f.ker.support : Set X) = {f p} := by
    rw [Scheme.Hom.support_ker, f.isClosedEmbedding.isClosed_range.closure_eq,
      Set.range_eq_singleton (fun q ↦ congrArg f (Subsingleton.elim q p))]
  have hp : e.hom (f p) ∈ ({f p} : Set X) := by
    have h := congrArg (fun J : Scheme.IdealSheafData X ↦ (J.support : Set X)) hker
    rw [support_comap, Closeds.coe_preimage, hs] at h
    exact (Set.ext_iff.mp h (f p)).mpr (Set.mem_singleton _)
  exact Set.mem_singleton_iff.mp hp

variable [PrestableFamily ((Φ.toricBoundaryIdeal k h₀).subscheme ↘ Spec (.of k))]
  (hΦ : Φ.IsRegular) (e : Φ.finiteFanScheme k ≅ Φ.finiteFanScheme k)
  (d : (Φ.toricBoundaryIdeal k h₀).subscheme ≅ (Φ.toricBoundaryIdeal k h₀).subscheme)
  [d.hom.IsOver (Spec (.of k))]
  (hd : d.hom ≫ (Φ.toricBoundaryIdeal k h₀).subschemeι =
    (Φ.toricBoundaryIdeal k h₀).subschemeι ≫ e.hom)
  (he : ∀ ρ, (Φ.rayDivisorIdeal k hΦ ρ).comap e.hom = Φ.rayDivisorIdeal k hΦ ρ)

local notation "l" => Iso.hom (d.singularLocusBlowupIso (R := k))

include hd he in
private theorem mapsTo_normalizedRay_of_comap_rayBoundaryIdeal_eq (ρ : Φ.Ray) :
    Set.MapsTo l (Φ.boundaryNormalizationComponentEquiv k hΦ ρ : Set W)
      (Φ.boundaryNormalizationComponentEquiv k hΦ ρ : Set W) := by
  let v := Φ.boundaryNormalizationComponentEquiv k hΦ ρ
  let x := (genericPoints.ofComponent v : W)
  let p := (Φ.rayBoundaryChartPoint (R := k) hΦ ρ).val
  have hx : (D).subschemeι (ν x) = p := by
    refine IsGenericPoint.eq (S := closure {p}) ?_ isGenericPoint_closure
    rw [IsGenericPoint,
      ← (C).range_blowupComponent_comp (k := k) v (D).subschemeι (D).subschemeι.isClosedMap,
      ← ρ.boundaryNormalizationComponentIso_hom_boundaryComponentι_assoc k,
      ρ.boundaryComponentι_subschemeι k, Scheme.Hom.comp_base, TopCat.coe_comp,
      (ρ.boundaryNormalizationComponentIso k hΦ).hom.surjective.range_comp,
      range_subschemeι, Φ.coe_support_rayDivisorIdeal k]
  have hcomm : l ≫ ν ≫ (D).subschemeι = ν ≫ (D).subschemeι ≫ e.hom := by
    rw [Iso.singularLocusBlowupIso_hom_blowupToBase_assoc, hd]
  have hfix : l x = x := by
    have hp : ν (l x) = ν x := by
      apply (D).subschemeι.injective
      have h := congrArg (fun f : W ⟶ X ↦ f x) hcomm
      simp only [Scheme.Hom.comp_apply, hx] at h ⊢
      exact h.trans ((Φ.comap_rayDivisorIdeal_eq_iff k hΦ e ρ).mp (he ρ))
    have hy := (C).blowupComponentGeneric_mem_isoLocus (k := k) v
    exact (ν).injOn_preimage_isoLocus (Set.mem_preimage.mpr (hp.symm ▸ hy)) hy hp
  rw [← (genericPoints.isGenericPoint_ofComponent v).def]
  have hxmap : Set.MapsTo l ({x} : Set W) {x} := Set.mapsTo_singleton.mpr (by simp [hfix])
  exact hxmap.closure (l).continuous

include hd he in
private theorem branchSchemeIso_apply_eq_self_of_comap_rayBoundaryIdeal_eq
    (hc : Φ.IsComplete) (hdim : Module.finrank ℤ N = 2) (q : Scheme.branchScheme k C) :
    (d.branchSchemeIso (R := k)).hom q = q := by
  let x := j q
  let z := ν x
  have hnodal := PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := C ↘ base)
  have hz : z ∈ (I).support := by
    have h := congrArg (fun f : Scheme.branchScheme k C ⟶ C ↦ f q)
      ((C).branchSchemeToSingularLocus_subschemeι k)
    simp only [Scheme.Hom.comp_apply] at h
    rw [← SetLike.mem_coe]
    simpa only [z, x, ← h] using
      (I).range_subschemeι.le (Set.mem_range_self ((C).branchSchemeToSingularLocus k q))
  have hznode :
      (D).IsNodeOfReducedBoundary (Φ.finiteFanSchemeToSpec k) ((D).subschemeι z) := by
    have hred : IsReduced C := hnodal.isReduced
    apply (D).isNodeOfReducedBoundary_iff_of_isReduced _ _ |>.mpr
    refine ⟨z, rfl, ?_⟩
    rw [← Φ.finiteFanScheme_over k, ← over_eq_subschemeι_comp]
    exact ((C ↘ base).isNodeAt_iff_notMem_smoothLocus hnodal z).mpr
      (((C).mem_support_singularLocus_iff_notMem_smoothLocus z).mp hz)
  obtain ⟨σ, ⟨hσ, hpoint⟩, -⟩ :=
    (Φ.isNodeOfReducedBoundary_iff_existsUnique_twoRayCone k hΦ hc hdim).mp hznode
  have hfix : d.hom z = z := by
    apply (D).subschemeι.injective
    rw [← Scheme.Hom.comp_apply, hd, Scheme.Hom.comp_apply, ← hpoint]
    exact fixes_distinguishedSection_of_comap_rayBoundaryIdeal_eq k hΦ hdim e he σ hσ _
  obtain ⟨ρ, hρ⟩ := (Φ.boundaryNormalizationComponentEquiv k hΦ).surjective
    (irreducibleComponentOf x)
  have hx : x ∈ (Φ.boundaryNormalizationComponentEquiv k hΦ ρ : Set W) :=
    hρ.symm ▸ mem_irreducibleComponentOf x
  have hxl := mapsTo_normalizedRay_of_comap_rayBoundaryIdeal_eq k hΦ e d hd he ρ hx
  have hl : l x = x := by
    apply ρ.injOn_blowupToBase_boundaryNormalizationComponent k hΦ hxl hx
    rw [← Scheme.Hom.comp_apply, Iso.singularLocusBlowupIso_hom_blowupToBase,
      Scheme.Hom.comp_apply]
    exact hfix
  have : IsClosedImmersion (j) := MorphismProperty.of_isPullback ((C).isPullback_branchScheme k)
    inferInstance
  apply (j).isClosedEmbedding.injective
  rw [← Scheme.Hom.comp_apply, Iso.branchSchemeIso_hom_branchSchemeToBlowup, Scheme.Hom.comp_apply]
  exact hl

variable [IsAlgClosed k] in
include hd he in
/-- An isomorphism of a complete regular toric surface fixing each ray divisor acts
as the identity on the branch scheme of the reduced boundary. -/
theorem branchSchemeIso_eq_refl_of_comap_rayBoundaryIdeal_eq
    (hc : Φ.IsComplete) (hdim : Module.finrank ℤ N = 2) :
    d.branchSchemeIso (R := k) = Iso.refl (Scheme.branchScheme k C) :=
  (d.branchSchemeIso_eq_refl_iff PrestableFamily.atWorstNodalOfRelativeDimensionOne).mpr
    (branchSchemeIso_apply_eq_self_of_comap_rayBoundaryIdeal_eq k hΦ e d hd he hc hdim)

end TauCeti.Toric.Fan
