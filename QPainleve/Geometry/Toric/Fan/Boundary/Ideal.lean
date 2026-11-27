/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import QPainleve.Geometry.Toric.BaseChange.Boundary
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.Over
public import TauCeti.AlgebraicGeometry.IdealSheaf.Stalk
public import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme

import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Stalk
import QPainleve.Geometry.Toric.BaseChange.FiniteType
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Factorial
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal

/-!
# Ideal sheaves of toric boundary divisors

A ray divisor is the reduced closure of its codimension-one point in the fan scheme.
On a chart containing the ray it is cut out by the ray ideal. On the other charts
its ideal is the unit ideal. The ray divisor is regular and is proper over the coefficient
field when the fan scheme is proper. This is the scheme-theoretic chart description of
the invariant divisors in Fulton, *Introduction to Toric Varieties*, §3.1.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Multiplicative
open AlgebraicGeometry.Scheme.IdealSheafData
open TauCeti.AlgebraicGeometry (isRegularLocalRing_stalk_iff_of_isOpenImmersion
  isRegularLocalRing_stalk_of_smooth)

namespace TauCeti.Toric.Fan

universe u

variable (k : Type u) [Field k] {N : Type u} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (hΦ : Φ.IsRegular) (ρ : Φ.Ray)

/-- A ray divisor in a proper toric scheme is proper over the coefficient field. -/
instance isProper_rayDivisor [IsProper (Φ.finiteFanSchemeToSpec k)] :
    IsProper ((Φ.rayDivisorIdeal k hΦ ρ).subscheme ↘ Spec (.of k)) := by
  rw [over_eq_subschemeι_comp, Φ.finiteFanScheme_over k]
  infer_instance

local notation "D" => Φ.rayDivisorIdeal k hΦ ρ

private theorem isRegularLocalRing_stalk_rayBoundary (x : (D).subscheme) :
    IsRegularLocalRing ((D).subscheme.presheaf.stalk x) := by
  obtain ⟨σ, y, hy⟩ := Φ.exists_affineChartι_apply_eq k ((D).subschemeι x)
  let j := Φ.affineChartι k σ
  have hyD : y ∈ (((D).comap j).support : Set (affineChart k Φ.lattice σ.val)) := by
    rw [support_comap, Closeds.coe_preimage, Set.mem_preimage, hy, ← (D).range_subschemeι]
    exact Set.mem_range_self x
  have hρ : ρ.toCone ≤ σ := by
    by_contra h
    rw [Φ.comap_rayDivisorIdeal_eq_top k hΦ ρ σ h, support_top] at hyD
    exact hyD
  let hσ := Φ.isToricCone σ.property
  let I := rayChartIdeal Φ.lattice hσ (ρ.toToricRay Φ σ hρ) k
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have : IsClosedImmersion q := IsClosedImmersion.spec_of_surjective
    _ Ideal.Quotient.mk_surjective
  have hker : q.ker = (D).comap j := by
    rw [Φ.comap_rayDivisorIdeal_eq_ofIdealTop k hΦ ρ σ hρ, Scheme.Hom.ker_Spec_map]
    simp [I]
  let g := IsClosedImmersion.lift (D).subschemeι (q ≫ j) (by
    rw [ker_subschemeι, Scheme.Hom.ker_comp, hker]
    exact le_map_comap _ _)
  have hg : g ≫ (D).subschemeι = q ≫ j := IsClosedImmersion.lift_fac _ _ _
  have hpb := isPullback_of_isClosedImmersion q (D).subschemeι g j hg.symm
    (by rw [ker_subschemeι, hker])
  have : IsOpenImmersion g := MorphismProperty.of_isPullback hpb inferInstance
  have hyq : y ∈ Set.range q := by rwa [← hker, q.support_ker,
    q.isClosedEmbedding.isClosed_range.closure_eq] at hyD
  obtain ⟨z, hz⟩ := hyq
  have hx : g z = x := (D).subschemeι.isClosedEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, hg, Scheme.Hom.comp_apply, hz, hy])
  have := ((isRegular_iff.mp hΦ) σ.val σ.property).isRegularRing_quotient_rayChartIdeal
    Φ.lattice hσ (ρ.toToricRay Φ σ hρ) k
  exact hx ▸ (isRegularLocalRing_stalk_iff_of_isOpenImmersion g z).mpr inferInstance

/-- The reduced component belonging to a ray of a regular fan is a regular scheme. -/
theorem isRegular_rayBoundary (Φ : Fan i) (hΦ : Φ.IsRegular) (ρ : Φ.Ray) :
    TauCeti.AlgebraicGeometry.IsRegular (Φ.rayDivisorIdeal k hΦ ρ).subscheme := by
  have := LocallyOfFiniteType.isLocallyNoetherian (Φ.rayDivisorIdeal k hΦ ρ).subschemeι
  exact ⟨isRegularLocalRing_stalk_rayBoundary k hΦ ρ⟩

local notation "p[" σ "]" =>
  Fan.distinguishedSection (R := k) _ σ (IsLocalRing.closedPoint k : Spec (CommRingCat.of k))

/-- A distinguished point lies on a ray divisor precisely when the ray is a face
of its cone. -/
theorem distinguishedPoint_mem_support_rayBoundaryIdeal_iff
    (σ : Φ.cones) (ρ : Φ.Ray) :
    p[σ] ∈ (Φ.rayDivisorIdeal k hΦ ρ).support ↔ ρ.toCone ≤ σ := by
  classical
  let j := Φ.affineChartι k σ
  let d := facePointAlgebraHom Φ.lattice (⊤ : σ.val.Face) k
  let x : affineChart k Φ.lattice σ.val :=
    PrimeSpectrum.comap d.toRingHom (IsLocalRing.closedPoint k)
  let z : Spec (CommRingCat.of k) := IsLocalRing.closedPoint k
  have hd : p[σ] = j x :=
    congrArg (fun f : Spec (CommRingCat.of k) ⟶ (Φ.finiteFanScheme k) ↦ f z)
      (Φ.distinguishedSection_def (R := k) σ)
  have hx : x ∈ ((Φ.rayDivisorIdeal k hΦ ρ).comap j).support ↔
      j x ∈ (Φ.rayDivisorIdeal k hΦ ρ).support := by
    rw [← SetLike.mem_coe, support_comap, Closeds.coe_preimage]
    rfl
  rw [hd, ← hx]
  by_cases h : ρ.toCone ≤ σ
  · rw [iff_true_intro h, Φ.comap_rayDivisorIdeal_eq_ofIdealTop k hΦ _ σ h]
    rw [← SetLike.mem_coe, coe_support_ofIdealTop, Spec_zeroLocus]
    let y : PrimeSpectrum (affineChartRing k Φ.lattice σ.val) := x
    -- Affine membership here is membership of the contracted prime in the zero locus.
    change (y ∈ PrimeSpectrum.zeroLocus _) ↔ True
    rw [iff_true, PrimeSpectrum.mem_zeroLocus, ← Ideal.coe_comap,
      Ideal.comap_map_of_bijective _ (ConcreteCategory.bijective_of_isIso (C := CommRingCat) _),
      SetLike.coe_subset_coe]
    -- At the distinguished point the contracted prime comes from the zero ideal of the field.
    change _ ≤ (PrimeSpectrum.comap d.toRingHom (IsLocalRing.closedPoint k)).asIdeal
    have hz : (IsLocalRing.closedPoint k).asIdeal = ⊥ := IsLocalRing.maximalIdeal_eq_bot
    rw [PrimeSpectrum.comap_asIdeal, hz, ← RingHom.ker_eq_comap_bot]
    apply (rayChartIdeal_le_iff _ _ _ k _).mpr
    intro m hm
    rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe]
    exact facePointAlgebraHom_top_single_eq_zero_of_pos k _ _ _ _ _ hm
  · rw [iff_false_intro h, Φ.comap_rayDivisorIdeal_eq_top k hΦ ρ σ h, support_top]
    exact Iff.rfl

open Classical in
/-- The multiplicity of a ray divisor at a distinguished point is one for a ray
of the center cone and zero for any other ray. -/
theorem stalkOrder_rayBoundaryIdeal_distinguishedPoint
    (σ : Φ.cones) (ρ : Φ.Ray) :
    (Φ.rayDivisorIdeal k hΦ ρ).stalkOrder p[σ] = if ρ.toCone ≤ σ then 1 else 0 := by
  let p := p[σ]
  let J := Φ.rayDivisorIdeal k hΦ ρ
  have : SmoothOfRelativeDimension (Module.finrank ℤ N) (Φ.finiteFanSchemeToSpec k) :=
    Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k hΦ
  have : Smooth (Φ.finiteFanSchemeToSpec k) :=
    SmoothOfRelativeDimension.smooth (Module.finrank ℤ N) _
  let : IsRegularLocalRing ((Φ.finiteFanScheme k).presheaf.stalk p) :=
    isRegularLocalRing_stalk_of_smooth (Φ.finiteFanSchemeToSpec k) p
  let : TauCeti.AlgebraicGeometry.IsRegular J.subscheme := Φ.isRegular_rayBoundary k hΦ ρ
  have hm := Φ.distinguishedPoint_mem_support_rayBoundaryIdeal_iff k hΦ σ ρ
  split_ifs with h
  · have hp : p ∈ (J.support : Set (Φ.finiteFanScheme k)) := hm.mpr h
    rw [← J.range_subschemeι] at hp
    obtain ⟨x, hx⟩ := hp
    have : IsRegularLocalRing ((Φ.finiteFanScheme k).presheaf.stalk (J.subschemeι x)) :=
      hx.symm ▸ inferInstanceAs (IsRegularLocalRing ((Φ.finiteFanScheme k).presheaf.stalk p))
    have hD := Φ.isEffectiveCartier_rayDivisorIdeal k hΦ ρ
    have horder := (hD.stalkOrder_eq_one_iff_isRegularLocalRing x).mpr inferInstance
    exact (congrArg J.stalkOrder hx).symm.trans horder
  · exact (J.stalkOrder_eq_zero_iff p).mpr (h ∘ hm.mp)

end TauCeti.Toric.Fan
