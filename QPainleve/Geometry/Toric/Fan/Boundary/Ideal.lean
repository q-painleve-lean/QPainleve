/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import QPainleve.Geometry.Toric.Fan.Boundary.Basic
public import QPainleve.Geometry.Toric.Fan.Point
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.Over
public import TauCeti.AlgebraicGeometry.IdealSheaf.Stalk
public import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme

import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Stalk
import QPainleve.Geometry.Toric.Fan.Picard.Basic
import QPainleve.Geometry.Toric.Fan.Smooth
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Factorial
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal

/-!
# Ideal sheaves of toric boundary divisors

A ray divisor is the reduced closure of its codimension-one point in the fan scheme.
On a chart containing the ray it is cut out by the ray ideal. On the other charts
its ideal is the unit ideal. The ray divisor is regular, and it is proper over `ℂ` when
the fan scheme is proper. This is the scheme-theoretic chart description of
the invariant divisors in Fulton, *Introduction to Toric Varieties*, §3.1.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Multiplicative
open AlgebraicGeometry.Scheme.IdealSheafData
open TauCeti.AlgebraicGeometry (isRegularLocalRing_stalk_iff_of_isOpenImmersion
  isRegularLocalRing_stalk_of_smooth)

namespace TauCeti.Toric.Fan

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i) (hΦ : Φ.IsRegular)

/-- The reduced closure of the codimension-one point belonging to a ray. -/
def rayBoundaryIdeal (ρ : Φ.Ray) : Φ.algebraicRealization.IdealSheafData :=
  vanishingIdeal ⟨closure {((Φ.rayBoundaryPoint hΦ ρ).val)}, isClosed_closure⟩

/-- The ray ideal sheaf is the vanishing ideal of the closure of the ray point. -/
theorem rayBoundaryIdeal_def (ρ : Φ.Ray) :
    Φ.rayBoundaryIdeal hΦ ρ = vanishingIdeal
      ⟨closure {((Φ.rayBoundaryPoint hΦ ρ).val)}, isClosed_closure⟩ :=
  (rfl)

/-- The reduced ray divisor is integral. -/
instance isIntegral_rayBoundary (ρ : Φ.Ray) :
    IsIntegral (Φ.rayBoundaryIdeal hΦ ρ).subscheme := by
  rw [Φ.rayBoundaryIdeal_def]
  infer_instance

/-- A ray divisor in a proper toric variety is proper over `ℂ`. -/
instance isProper_rayBoundary {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
    {i : N →+ V} {Φ : Fan i} (hΦ : Φ.IsRegular) (ρ : Φ.Ray)
    [IsProper (Φ.algebraicRealization ↘ Spec (.of ℂ))] :
    IsProper ((Φ.rayBoundaryIdeal hΦ ρ).subscheme ↘ Spec (.of ℂ)) := by
  rw [over_eq_subschemeι_comp]
  infer_instance

/-- The boundary ideal of a ray in a regular fan defines an effective Cartier divisor. -/
theorem isEffectiveCartier_rayBoundaryIdeal (ρ : Φ.Ray) :
    (Φ.rayBoundaryIdeal hΦ ρ).IsEffectiveCartier := by
  have : Nonempty Φ.cones := ⟨ρ.toCone⟩
  have := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  rw [rayBoundaryIdeal_def]
  exact isEffectiveCartier_vanishingIdeal_closure_singleton (Φ.rayBoundaryPoint hΦ ρ).property

/-- When the reduced toric boundary is effective Cartier, its ideal is the
product of the prime ray ideals. -/
theorem boundaryIdeal_eq_prod_rayBoundaryIdeal [Nonempty Φ.cones] [Fintype Φ.Ray]
    (hD : (Φ.boundaryIdeal inferInstance).IsEffectiveCartier) :
    Φ.boundaryIdeal inferInstance = ∏ ρ : Φ.Ray, Φ.rayBoundaryIdeal hΦ ρ := by
  let X := Φ.algebraicRealization
  let D := Φ.boundaryIdeal inferInstance
  have : IsReduced D.subscheme := by
    dsimp only [D]
    rw [boundaryIdeal_def]
    infer_instance
  have := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  let p := (⟨Φ.rayBoundaryPoint hΦ, Φ.rayBoundaryPoint_injective hΦ⟩ :
    Φ.Ray ↪ TauCeti.AlgebraicGeometry.CodimensionOnePoint X)
  let T := Finset.univ.map p
  have hT (x : TauCeti.AlgebraicGeometry.CodimensionOnePoint X) :
      x ∈ T ↔ (x : X) ∈ D.support := by
    -- Express support as a set to use the description by the torus complement.
    change x ∈ T ↔ (x : X) ∈ ((Φ.boundaryIdeal inferInstance).support : Set X)
    rw [support_boundaryIdeal]
    simpa only [T, p, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk,
      Set.mem_compl_iff, Set.mem_range, Set.mem_ofPred_eq] using
      Set.ext_iff.mp (Φ.range_rayBoundaryPoint hΦ inferInstance) x
  simpa only [T, Finset.prod_map, p, Function.Embedding.coeFn_mk, ← rayBoundaryIdeal_def] using
    hD.eq_prod_vanishingIdeal_of_isReduced T hT

/-- The support of the ray divisor is the closure of its generic point. -/
@[simp]
theorem coe_support_rayBoundaryIdeal (ρ : Φ.Ray) :
    ((Φ.rayBoundaryIdeal hΦ ρ).support : Set Φ.algebraicRealization) =
      closure {((Φ.rayBoundaryPoint hΦ ρ).val)} := by
  rw [rayBoundaryIdeal, coe_support_vanishingIdeal]
  rfl

/-- An automorphism preserves a ray divisor exactly when it fixes its generic point. -/
theorem comap_rayBoundaryIdeal_eq_iff (e : Φ.algebraicRealization ≅ Φ.algebraicRealization)
    (ρ : Φ.Ray) :
    (Φ.rayBoundaryIdeal hΦ ρ).comap e.hom = Φ.rayBoundaryIdeal hΦ ρ ↔
      e.hom (Φ.rayBoundaryPoint hΦ ρ).val = (Φ.rayBoundaryPoint hΦ ρ).val := by
  let x := (Φ.rayBoundaryPoint hΦ ρ).val
  constructor
  · intro he
    have h := congrArg (fun J : Φ.algebraicRealization.IdealSheafData ↦
      (J.support : Set Φ.algebraicRealization)) he
    rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
      Φ.coe_support_rayBoundaryIdeal] at h
    have himage := congrArg (Set.image e.hom) h
    rw [Set.image_preimage_eq _ (fun y ↦ ⟨e.inv y, by simp [← Scheme.Hom.comp_apply]⟩)] at himage
    have h' := (isGenericPoint_closure (x := x)).image e.hom.continuous
    rw [← himage, closure_closure] at h'
    exact h'.eq isGenericPoint_closure
  · intro he
    simpa only [x, he, Φ.rayBoundaryIdeal_def] using
      Scheme.IdealSheafData.comap_vanishingIdeal_closure_singleton_apply e.hom x

/-- On a chart not containing the ray, the boundary ideal is the unit ideal. -/
@[simp]
theorem comap_rayBoundaryIdeal_eq_top (ρ : Φ.Ray) (σ : Φ.cones) (h : ¬ ρ.toCone ≤ σ) :
    (Φ.rayBoundaryIdeal hΦ ρ).comap (Φ.affineToricChartι σ) = ⊤ :=
  comap_vanishingIdeal_closure_singleton_eq_top_of_notMem_range _
    (mt (Φ.rayBoundaryPoint_mem_range_affineToricChartι_iff hΦ ρ σ).mp h)

/-- On a chart containing a ray, the reduced boundary ideal is the ideal sheaf of
the prime generated by monomials positive on that ray. -/
theorem comap_rayBoundaryIdeal_eq_ofIdealTop (ρ : Φ.Ray) (σ : Φ.cones) (h : ρ.toCone ≤ σ) :
    (Φ.rayBoundaryIdeal hΦ ρ).comap (Φ.affineToricChartι σ) =
      ofIdealTop ((rayIdeal Φ.lattice (Φ.isToricCone σ.property) (ρ.toToricRay Φ σ h)).map
        (Scheme.ΓSpecIso (.of (affineCoordinateRing Φ.lattice σ.val))).inv.hom) := by
  let r := ρ.toToricRay Φ σ h
  have hr : Ray.ofToricRay Φ σ r = ρ := by
    simpa only [r, rayEquiv_apply, rayEquiv_symm_apply] using
      congrArg Subtype.val ((Φ.rayEquiv σ).symm_apply_apply ⟨ρ, h⟩)
  let hreg := isRegular_iff.1 hΦ _ σ.property
  let p : PrimeSpectrum (affineCoordinateRing Φ.lattice σ.val) :=
    (hreg.rayPoint Φ.lattice (Φ.isToricCone σ.property) r).val
  let x : Φ.affineToricChart σ := p
  have hp : (Φ.rayBoundaryPoint hΦ ρ).val = Φ.affineToricChartι σ x := by
    rw [← hr, Φ.rayBoundaryPoint_ofToricRay]
  have hl : (Φ.rayBoundaryIdeal hΦ ρ).comap (Φ.affineToricChartι σ) =
      vanishingIdeal ⟨closure {x}, isClosed_closure⟩ := by
    simpa only [rayBoundaryIdeal, hp] using
      comap_vanishingIdeal_closure_singleton_apply (Φ.affineToricChartι σ) x
  rw [hl, ← equivOfIsAffine_symm_apply]
  refine equivOfIsAffine.injective (Eq.trans ?_ (OrderRingIso.apply_symm_apply _ _).symm)
  -- The order-ring isomorphism computes the ideal using top sections.
  change equivOfIsAffine (vanishingIdeal ⟨closure {x}, isClosed_closure⟩) = _
  rw [equivOfIsAffine_apply, vanishingIdeal_ideal, IsAffineOpen.fromSpec_top,
    Scheme.isoSpec_Spec_inv]
  let f := (Scheme.ΓSpecIso (.of (affineCoordinateRing Φ.lattice σ.val))).inv.hom
  -- Read the map of affine schemes as the contraction of primes.
  change PrimeSpectrum.vanishingIdeal (PrimeSpectrum.comap f ⁻¹' closure {p}) =
    (rayIdeal Φ.lattice (Φ.isToricCone σ.property) r).map f
  rw [PrimeSpectrum.closure_singleton, PrimeSpectrum.preimage_comap_zeroLocus,
    ← PrimeSpectrum.zeroLocus_span, ← Ideal.map, PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical,
    hreg.rayPoint_asIdeal]
  have := hreg.isPrime_rayIdeal Φ.lattice (Φ.isToricCone σ.property) r
  exact (Ideal.map_isPrime_of_equiv (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv).radical

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (hΦ : Φ.IsRegular) (ρ : Φ.Ray)

local notation "D" => Φ.rayBoundaryIdeal hΦ ρ

private theorem isRegularLocalRing_stalk_rayBoundary (x : (D).subscheme) :
    IsRegularLocalRing ((D).subscheme.presheaf.stalk x) := by
  obtain ⟨σ, y, hy⟩ := Φ.exists_affineToricChartι_apply_eq ((D).subschemeι x)
  let j := Φ.affineToricChartι σ
  have hyD : y ∈ (((D).comap j).support : Set (Φ.affineToricChart σ)) := by
    rw [support_comap, Closeds.coe_preimage, Set.mem_preimage, hy, ← (D).range_subschemeι]
    exact Set.mem_range_self x
  have hρ : ρ.toCone ≤ σ := by
    by_contra h
    rw [Φ.comap_rayBoundaryIdeal_eq_top hΦ ρ σ h, support_top] at hyD
    exact hyD
  let hσ := Φ.isToricCone σ.property
  let I := rayIdeal Φ.lattice hσ (ρ.toToricRay Φ σ hρ)
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have : IsClosedImmersion q := IsClosedImmersion.spec_of_surjective
    _ Ideal.Quotient.mk_surjective
  have hker : q.ker = (D).comap j := by
    rw [Φ.comap_rayBoundaryIdeal_eq_ofIdealTop hΦ ρ σ hρ, Scheme.Hom.ker_Spec_map]
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
  have := ((isRegular_iff.mp hΦ) σ.val σ.property).isRegularRing_quotient_rayIdeal
    Φ.lattice (ρ.toToricRay Φ σ hρ)
  exact hx ▸ (isRegularLocalRing_stalk_iff_of_isOpenImmersion g z).mpr inferInstance

/-- The reduced component belonging to a ray of a regular fan is a regular scheme. -/
theorem isRegular_rayBoundary (Φ : Fan i) (hΦ : Φ.IsRegular) (ρ : Φ.Ray) :
    TauCeti.AlgebraicGeometry.IsRegular (Φ.rayBoundaryIdeal hΦ ρ).subscheme := by
  have := LocallyOfFiniteType.isLocallyNoetherian (Φ.rayBoundaryIdeal hΦ ρ).subschemeι
  exact ⟨isRegularLocalRing_stalk_rayBoundary hΦ ρ⟩

local notation "p[" σ "]" =>
  Fan.distinguishedPointHom _ σ (IsLocalRing.closedPoint ℂ : Spec (CommRingCat.of ℂ))

/-- A distinguished point lies on a ray divisor precisely when the ray is a face
of its cone. -/
theorem distinguishedPoint_mem_support_rayBoundaryIdeal_iff
    (σ : Φ.cones) (ρ : Φ.Ray) :
    p[σ] ∈ (Φ.rayBoundaryIdeal hΦ ρ).support ↔ ρ.toCone ≤ σ := by
  classical
  let j := Φ.affineToricChartι σ
  let d := distinguishedPoint Φ.lattice (⊤ : σ.val.Face)
  let x : Φ.affineToricChart σ := PrimeSpectrum.comap d.toRingHom (IsLocalRing.closedPoint ℂ)
  let z : Spec (CommRingCat.of ℂ) := IsLocalRing.closedPoint ℂ
  have hd : p[σ] = j x :=
    congrArg (fun f : Spec (CommRingCat.of ℂ) ⟶ Φ.algebraicRealization ↦ f z)
      (Φ.distinguishedPointHom_def σ)
  have hx : x ∈ ((Φ.rayBoundaryIdeal hΦ ρ).comap j).support ↔
      j x ∈ (Φ.rayBoundaryIdeal hΦ ρ).support := by
    rw [← SetLike.mem_coe, support_comap, Closeds.coe_preimage]
    rfl
  rw [hd, ← hx]
  by_cases h : ρ.toCone ≤ σ
  · rw [iff_true_intro h, Φ.comap_rayBoundaryIdeal_eq_ofIdealTop hΦ _ σ h]
    rw [← SetLike.mem_coe, coe_support_ofIdealTop, Spec_zeroLocus]
    let y : PrimeSpectrum (affineCoordinateRing Φ.lattice σ.val) := x
    -- Affine membership here is membership of the contracted prime in the zero locus.
    change (y ∈ PrimeSpectrum.zeroLocus _) ↔ True
    rw [iff_true, PrimeSpectrum.mem_zeroLocus, ← Ideal.coe_comap,
      Ideal.comap_map_of_bijective _ (ConcreteCategory.bijective_of_isIso (C := CommRingCat) _),
      SetLike.coe_subset_coe]
    -- At the distinguished point the contracted prime comes from the zero ideal of the field.
    change _ ≤ (PrimeSpectrum.comap d.toRingHom (IsLocalRing.closedPoint ℂ)).asIdeal
    have hz : (IsLocalRing.closedPoint ℂ).asIdeal = ⊥ := IsLocalRing.maximalIdeal_eq_bot
    rw [PrimeSpectrum.comap_asIdeal, hz, ← RingHom.ker_eq_comap_bot]
    apply (rayIdeal_le_iff _ _ _ _).mpr
    intro m hm
    rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, MonoidAlgebra.of_apply]
    exact distinguishedPoint_top_single_eq_zero_of_pos _ _ _ _ hm
  · rw [iff_false_intro h, Φ.comap_rayBoundaryIdeal_eq_top hΦ ρ σ h, support_top]
    exact Iff.rfl

open Classical in
/-- The multiplicity of a ray divisor at a distinguished point is one for a ray
of the center cone and zero for any other ray. -/
theorem stalkOrder_rayBoundaryIdeal_distinguishedPoint
    (σ : Φ.cones) (ρ : Φ.Ray) :
    (Φ.rayBoundaryIdeal hΦ ρ).stalkOrder p[σ] = if ρ.toCone ≤ σ then 1 else 0 := by
  let p := p[σ]
  let J := Φ.rayBoundaryIdeal hΦ ρ
  let : Smooth Φ.algebraicRealizationStructureMap :=
    Φ.smooth_algebraicRealizationStructureMap hΦ
  let : IsRegularLocalRing (Φ.algebraicRealization.presheaf.stalk p) :=
    isRegularLocalRing_stalk_of_smooth Φ.algebraicRealizationStructureMap p
  let : TauCeti.AlgebraicGeometry.IsRegular J.subscheme := Φ.isRegular_rayBoundary hΦ ρ
  have hm := Φ.distinguishedPoint_mem_support_rayBoundaryIdeal_iff hΦ σ ρ
  split_ifs with h
  · have hp : p ∈ (J.support : Set Φ.algebraicRealization) := hm.mpr h
    rw [← J.range_subschemeι] at hp
    obtain ⟨x, hx⟩ := hp
    have : IsRegularLocalRing (Φ.algebraicRealization.presheaf.stalk (J.subschemeι x)) :=
      hx.symm ▸ inferInstanceAs (IsRegularLocalRing (Φ.algebraicRealization.presheaf.stalk p))
    have hD := Φ.isEffectiveCartier_rayBoundaryIdeal hΦ ρ
    have horder := (hD.stalkOrder_eq_one_iff_isRegularLocalRing x).mpr inferInstance
    exact (congrArg J.stalkOrder hx).symm.trans horder
  · exact (J.stalkOrder_eq_zero_iff p).mpr (h ∘ hm.mp)

end TauCeti.Toric.Fan
