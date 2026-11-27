/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import QPainleve.Geometry.Toric.BaseChange.FunctionField
public import QPainleve.Geometry.Toric.BaseChange.Point
public import QPainleve.Geometry.Toric.Fan.Boundary.RayGenericPoint
public import TauCeti.AlgebraicGeometry.Blowup.StrictTransform
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Factorial
public import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal

import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Reduced
import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Stalk
import QPainleve.Geometry.Toric.BaseChange.Subfan
import QPainleve.Geometry.Toric.Cone.Regularity
import QPainleve.Geometry.Toric.BaseChange.Fan

/-!
# Boundary ideals of toric schemes

The toric boundary is the reduced complement of the zero-cone chart.
For a regular fan over a Noetherian domain its ray divisors are the reduced
closures of the corresponding codimension-one points.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Multiplicative
open AlgebraicGeometry.Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

universe u

variable (R : Type u) [CommRing R] {N : Type u} {V : Type*} [AddCommGroup N]
  [AddCommGroup V] [Module ℝ V] {i : N →+ V} (Φ : Fan i)

/-- The reduced closed complement of the zero-cone chart. -/
def toricBoundaryIdeal (h₀ : Nonempty Φ.cones) : (Φ.finiteFanScheme R).IdealSheafData :=
  let σ : Φ.cones := ⟨⊥, Φ.bot_mem h₀.some.property⟩
  vanishingIdeal ⟨(Set.range (Φ.affineChartι R σ))ᶜ,
    (Φ.affineChartι R σ).isOpenEmbedding.isOpen_range.isClosed_compl⟩

/-- The boundary ideal is the vanishing ideal of the complement of the zero-cone chart. -/
theorem toricBoundaryIdeal_def (h₀ : Nonempty Φ.cones) :
    let σ : Φ.cones := ⟨⊥, Φ.bot_mem h₀.some.property⟩
    Φ.toricBoundaryIdeal R h₀ = vanishingIdeal ⟨(Set.range (Φ.affineChartι R σ))ᶜ,
      (Φ.affineChartι R σ).isOpenEmbedding.isOpen_range.isClosed_compl⟩ :=
  (rfl)

/-- The support of the boundary is the complement of the dense torus. -/
@[simp]
theorem support_toricBoundaryIdeal (h₀ : Nonempty Φ.cones) :
    ((Φ.toricBoundaryIdeal R h₀).support : Set (Φ.finiteFanScheme R)) =
      (Set.range (Φ.affineChartι R ⟨⊥, Φ.bot_mem h₀.some.property⟩))ᶜ := by
  rw [toricBoundaryIdeal, coe_support_vanishingIdeal]
  rfl

/-- The reduced toric boundary is a reduced closed subscheme. -/
instance isReduced_toricBoundary (h₀ : Nonempty Φ.cones) :
    IsReduced (Φ.toricBoundaryIdeal R h₀).subscheme := by
  rw [toricBoundaryIdeal]
  dsimp only
  infer_instance

variable [IsDomain R] [IsNoetherianRing R] (hΦ : Φ.IsRegular)

/-- The reduced closure of the codimension-one point belonging to a ray. -/
def rayDivisorIdeal (ρ : Φ.Ray) : (Φ.finiteFanScheme R).IdealSheafData :=
  vanishingIdeal ⟨closure {((Φ.rayBoundaryChartPoint (R := R) hΦ ρ).val)}, isClosed_closure⟩

/-- The ray ideal sheaf is the vanishing ideal of the closure of the ray point. -/
theorem rayDivisorIdeal_def (ρ : Φ.Ray) :
    Φ.rayDivisorIdeal R hΦ ρ = vanishingIdeal
      ⟨closure {((Φ.rayBoundaryChartPoint (R := R) hΦ ρ).val)}, isClosed_closure⟩ :=
  (rfl)

/-- The reduced ray divisor is integral. -/
instance isIntegral_rayDivisor (ρ : Φ.Ray) :
    IsIntegral (Φ.rayDivisorIdeal R hΦ ρ).subscheme := by
  rw [Φ.rayDivisorIdeal_def R]
  infer_instance

/-- The boundary ideal of a ray in a regular fan defines an effective Cartier divisor. -/
theorem isEffectiveCartier_rayDivisorIdeal [UniqueFactorizationMonoid R] (ρ : Φ.Ray) :
    (Φ.rayDivisorIdeal R hΦ ρ).IsEffectiveCartier := by
  have : Nonempty Φ.cones := ⟨ρ.toCone⟩
  have := Φ.uniqueFactorizationMonoid_stalk_finiteFanScheme (R := R) hΦ
  rw [rayDivisorIdeal_def]
  exact isEffectiveCartier_vanishingIdeal_closure_singleton
    (Φ.rayBoundaryChartPoint (R := R) hΦ ρ).property

/-- When the reduced toric boundary is effective Cartier, its ideal is the
product of the prime ray ideals. -/
theorem toricBoundaryIdeal_eq_prod_rayDivisorIdeal [UniqueFactorizationMonoid R]
    [Nonempty Φ.cones] [Fintype Φ.Ray]
    (hD : (Φ.toricBoundaryIdeal R inferInstance).IsEffectiveCartier) :
    Φ.toricBoundaryIdeal R inferInstance = ∏ ρ : Φ.Ray, Φ.rayDivisorIdeal R hΦ ρ := by
  let X := (Φ.finiteFanScheme R)
  let D := Φ.toricBoundaryIdeal R inferInstance
  have := Φ.uniqueFactorizationMonoid_stalk_finiteFanScheme (R := R) hΦ
  let p := (⟨Φ.rayBoundaryChartPoint (R := R) hΦ, Φ.rayBoundaryChartPoint_injective (R := R) hΦ⟩ :
    Φ.Ray ↪ TauCeti.AlgebraicGeometry.CodimensionOnePoint X)
  let T := Finset.univ.map p
  have hT (x : TauCeti.AlgebraicGeometry.CodimensionOnePoint X) :
      x ∈ T ↔ (x : X) ∈ D.support := by
    -- Express support as a set to use the description by the torus complement.
    change x ∈ T ↔ (x : X) ∈ ((Φ.toricBoundaryIdeal R inferInstance).support : Set X)
    rw [support_toricBoundaryIdeal R Φ]
    simpa only [T, p, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk,
      Set.mem_compl_iff, Set.mem_range, Set.mem_ofPred_eq] using
      Set.ext_iff.mp (Φ.range_rayBoundaryChartPoint (R := R) hΦ
        (Φ.bot_mem (inferInstance : Nonempty Φ.cones).some.property)) x
  simpa only [T, Finset.prod_map, p, Function.Embedding.coeFn_mk, ← rayDivisorIdeal_def R] using
    hD.eq_prod_vanishingIdeal_of_isReduced T hT

/-- The support of the ray divisor is the closure of its generic point. -/
@[simp]
theorem coe_support_rayDivisorIdeal (ρ : Φ.Ray) :
    ((Φ.rayDivisorIdeal R hΦ ρ).support : Set (Φ.finiteFanScheme R)) =
      closure {((Φ.rayBoundaryChartPoint (R := R) hΦ ρ).val)} := by
  rw [rayDivisorIdeal, coe_support_vanishingIdeal]
  rfl

/-- The support of the reduced toric boundary is the union of the ray closures. -/
theorem support_toricBoundaryIdeal_eq_iUnion_closure (h₀ : Nonempty Φ.cones) :
    ((Φ.toricBoundaryIdeal R h₀).support : Set (Φ.finiteFanScheme R)) =
      ⋃ ρ : Φ.Ray, closure {(Φ.rayBoundaryChartPoint (R := R) hΦ ρ).val} := by
  let hbot := Φ.bot_mem h₀.some.property
  rw [support_toricBoundaryIdeal]
  refine Set.Subset.antisymm (fun x hx ↦ ?_) (Set.iUnion_subset fun ρ ↦ ?_)
  · obtain ⟨ρ, hρ⟩ := Φ.exists_rayBoundaryChartPoint_specializes (R := R) hΦ hbot hx
    exact Set.mem_iUnion.mpr ⟨ρ, specializes_iff_mem_closure.mp hρ⟩
  · exact closure_minimal
      (Set.singleton_subset_iff.mpr (Φ.rayBoundaryChartPoint_notMem_zeroChart (R := R) hΦ ρ hbot))
      (Φ.affineChartι R ⟨⊥, hbot⟩).isOpenEmbedding.isOpen_range.isClosed_compl

/-- An automorphism preserves a ray divisor exactly when it fixes its generic point. -/
theorem comap_rayDivisorIdeal_eq_iff (e : (Φ.finiteFanScheme R) ≅ (Φ.finiteFanScheme R))
    (ρ : Φ.Ray) :
    (Φ.rayDivisorIdeal R hΦ ρ).comap e.hom = Φ.rayDivisorIdeal R hΦ ρ ↔
      e.hom (Φ.rayBoundaryChartPoint (R := R) hΦ ρ).val =
        (Φ.rayBoundaryChartPoint (R := R) hΦ ρ).val := by
  let x := (Φ.rayBoundaryChartPoint (R := R) hΦ ρ).val
  constructor
  · intro he
    have h := congrArg (fun J : (Φ.finiteFanScheme R).IdealSheafData ↦
      (J.support : Set (Φ.finiteFanScheme R))) he
    rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
      Φ.coe_support_rayDivisorIdeal R hΦ] at h
    have himage := congrArg (Set.image e.hom) h
    rw [Set.image_preimage_eq _ (fun y ↦ ⟨e.inv y, by simp [← Scheme.Hom.comp_apply]⟩)] at himage
    have h' := (isGenericPoint_closure (x := x)).image e.hom.continuous
    rw [← himage, closure_closure] at h'
    exact h'.eq isGenericPoint_closure
  · intro he
    simpa only [x, he, Φ.rayDivisorIdeal_def R] using
      Scheme.IdealSheafData.comap_vanishingIdeal_closure_singleton_apply e.hom x

/-- On a chart not containing the ray, the boundary ideal is the unit ideal. -/
@[simp]
theorem comap_rayDivisorIdeal_eq_top (ρ : Φ.Ray) (σ : Φ.cones) (h : ¬ ρ.toCone ≤ σ) :
    (Φ.rayDivisorIdeal R hΦ ρ).comap (Φ.affineChartι R σ) = ⊤ :=
  comap_vanishingIdeal_closure_singleton_eq_top_of_notMem_range _
    (mt (Φ.rayBoundaryChartPoint_mem_range_affineChartι_iff (R := R) hΦ ρ σ).mp h)

/-- On a chart containing a ray, the reduced boundary ideal is the ideal sheaf of
the prime generated by monomials positive on that ray. -/
theorem comap_rayDivisorIdeal_eq_ofIdealTop (ρ : Φ.Ray) (σ : Φ.cones) (h : ρ.toCone ≤ σ) :
    (Φ.rayDivisorIdeal R hΦ ρ).comap (Φ.affineChartι R σ) =
      ofIdealTop ((rayChartIdeal Φ.lattice (Φ.isToricCone σ.property) (ρ.toToricRay Φ σ h) R).map
        (Scheme.ΓSpecIso (.of (affineChartRing R Φ.lattice σ.val))).inv.hom) := by
  let r := ρ.toToricRay Φ σ h
  have hr : Ray.ofToricRay Φ σ r = ρ := by
    simpa only [r, rayEquiv_apply, rayEquiv_symm_apply] using
      congrArg Subtype.val ((Φ.rayEquiv σ).symm_apply_apply ⟨ρ, h⟩)
  let hreg := isRegular_iff.1 hΦ _ σ.property
  let p : PrimeSpectrum (affineChartRing R Φ.lattice σ.val) :=
    (hreg.rayChartPoint Φ.lattice (Φ.isToricCone σ.property) r R).val
  let x : affineChart R Φ.lattice σ.val := p
  have hp : (Φ.rayBoundaryChartPoint (R := R) hΦ ρ).val = Φ.affineChartι R σ x := by
    rw [← hr, Φ.rayBoundaryChartPoint_ofToricRay (R := R)]
  have hl : (Φ.rayDivisorIdeal R hΦ ρ).comap (Φ.affineChartι R σ) =
      vanishingIdeal ⟨closure {x}, isClosed_closure⟩ := by
    simpa only [rayDivisorIdeal, hp] using
      comap_vanishingIdeal_closure_singleton_apply (Φ.affineChartι R σ) x
  rw [hl, ← equivOfIsAffine_symm_apply]
  refine equivOfIsAffine.injective (Eq.trans ?_ (OrderRingIso.apply_symm_apply _ _).symm)
  -- The order-ring isomorphism computes the ideal using top sections.
  change equivOfIsAffine (vanishingIdeal ⟨closure {x}, isClosed_closure⟩) = _
  rw [equivOfIsAffine_apply, vanishingIdeal_ideal, IsAffineOpen.fromSpec_top,
    Scheme.isoSpec_Spec_inv]
  let f := (Scheme.ΓSpecIso (.of (affineChartRing R Φ.lattice σ.val))).inv.hom
  -- Read the map of affine schemes as the contraction of primes.
  change PrimeSpectrum.vanishingIdeal (PrimeSpectrum.comap f ⁻¹' closure {p}) =
    (rayChartIdeal Φ.lattice (Φ.isToricCone σ.property) r R).map f
  rw [PrimeSpectrum.closure_singleton, PrimeSpectrum.preimage_comap_zeroLocus,
    ← PrimeSpectrum.zeroLocus_span, ← Ideal.map, PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical,
    hreg.rayChartPoint_asIdeal]
  have := isPrime_rayChartIdeal Φ.lattice (Φ.isToricCone σ.property) r R
  exact (Ideal.map_isPrime_of_equiv (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv).radical

end TauCeti.Toric.Fan

namespace TauCeti.Toric

open _root_.AddMonoidAlgebra

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V}

/-- A monomial of positive order on a ray vanishes at the distinguished section. -/
theorem facePointAlgebraHom_top_single_eq_zero_of_pos (R : Type*) [CommRing R]
    (hi : IsIntegralLattice i) (hσ : IsToricCone i σ) (ρ : ToricRay σ)
    (m : dualSemigroup hi σ) (r : R) (hm : 0 < m.val (primitiveGenerator hi hσ ρ)) :
    facePointAlgebraHom hi (⊤ : σ.Face) R (single m r) = 0 := by
  rw [facePointAlgebraHom_single]
  refine ite_eq_right fun h ↦ ?_
  have hzero := h (i (primitiveGenerator hi hσ ρ))
    (ρ.val.isFaceOf.le (primitiveGenerator_mem hi hσ ρ))
  rw [hi.realCharacter_apply] at hzero
  exact hm.ne' (Int.cast_eq_zero.mp hzero)

/-- In a full-rank regular cone the ray ideals cut out the distinguished section. -/
theorem iSup_rayChartIdeal_eq_ker_facePointAlgebraHom (R : Type*) [CommRing R]
    (hi : IsIntegralLattice i) (hσ : IsToricCone i σ) (hreg : IsRegularCone i σ)
    (hfull : Nat.card (ToricRay σ) = Module.finrank ℤ N) :
    (⨆ r : ToricRay σ, rayChartIdeal hi hσ r R) =
      RingHom.ker (facePointAlgebraHom hi (⊤ : σ.Face) R).toRingHom := by
  classical
  let J := ⨆ r : ToricRay σ, rayChartIdeal hi hσ r R
  let d := facePointAlgebraHom hi (⊤ : σ.Face) R
  let q := Ideal.Quotient.mkₐ R J
  have heval (r : ToricRay σ) (m : dualSemigroup hi σ)
      (hm : 0 < m.val (primitiveGenerator hi hσ r)) : d (single m 1) = 0 :=
    facePointAlgebraHom_top_single_eq_zero_of_pos R hi hσ r m 1 hm
  have hcomp : q = (Algebra.ofId R _).comp d := by
    apply AddMonoidAlgebra.algHom_ext
    · intro m
      by_cases hm : m = 0
      · subst m
        change q 1 = ((Algebra.ofId R _).comp d) 1
        simp
      · obtain ⟨r, hr⟩ := exists_pos_primitiveGenerator_of_ne_zero hi hσ hreg hfull hm
        have hmJ : single m (1 : R) ∈ J :=
          le_iSup (fun r ↦ rayChartIdeal hi hσ r R) r
            ((single_mem_rayChartIdeal_iff hi hσ r R m 1).mpr (Or.inr hr))
        rw [AlgHom.comp_apply, heval r m hr, map_zero]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hmJ
    · exact Subsingleton.elim _ _
  refine le_antisymm (iSup_le fun r ↦ (rayChartIdeal_le_iff hi hσ r R _).mpr ?_) ?_
  · intro m hm
    exact heval r m hm
  · intro x hx
    have hx' : d x = 0 := hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q x = 0
    rw [hcomp, AlgHom.comp_apply, hx', map_zero]

namespace Fan.IsSubdivision

universe u

variable (R : Type u) [CommRing R] {N : Type u} {V : Type*} [AddCommGroup N]
  [AddCommGroup V] [Module ℝ V] {i : N →+ V} {Φ Ψ : Fan i}
  (h : Φ.IsSubdivision Ψ) (hΦ : Nonempty Φ.cones) (hΨ : Nonempty Ψ.cones)

/-- Taking the reduced inverse image of the toric boundary gives the subdividing fan's boundary. -/
theorem radical_comap_toricBoundaryIdeal :
    ((Ψ.toricBoundaryIdeal R hΨ).comap (h.toFanHom.finiteFanSchemeHom R)).radical =
      Φ.toricBoundaryIdeal R hΦ := by
  rw [← vanishingIdeal_support]
  conv_rhs => rw [toricBoundaryIdeal]
  congr 1
  apply SetLike.coe_injective
  rw [support_comap, Closeds.coe_preimage, Ψ.support_toricBoundaryIdeal R,
    Set.preimage_compl, h.preimage_range_affineChartι R
      (Φ.bot_mem hΦ.some.property) (Ψ.bot_mem hΨ.some.property)]
  rfl

variable [IsDomain R] [IsNoetherianRing R]

/-- The generic point of a surviving ray maps to the original ray point. -/
theorem finiteFanSchemeHom_rayBoundaryChartPoint_liftRay
    (hregΦ : Φ.IsRegular) (hregΨ : Ψ.IsRegular) (ρ : Ψ.Ray) :
    h.toFanHom.finiteFanSchemeHom R (Φ.rayBoundaryChartPoint (R := R) hregΦ (h.liftRay ρ)).val =
      (Ψ.rayBoundaryChartPoint (R := R) hregΨ ρ).val := by
  have hchart : Φ.affineChartι R (h.liftRay ρ).toCone ≫ h.toFanHom.finiteFanSchemeHom R =
      Ψ.affineChartι R ρ.toCone :=
    h.affineChartι_comp_finiteFanSchemeHom R (h.ray_mem ρ) ρ.toCone.property
  rw [Fan.coe_rayBoundaryChartPoint, ← Scheme.Hom.comp_apply, hchart,
    Fan.coe_rayBoundaryChartPoint, h.liftRay_toToricRay]
  rfl

/-- A surviving ray whose generic point lies outside the blowup center defines the
strict transform of its original ray divisor. -/
theorem comap_ker_blowupMap_rayDivisorIdeal (hregΦ : Φ.IsRegular) (hregΨ : Ψ.IsRegular)
    {I : (Ψ.finiteFanScheme R).IdealSheafData} (e : Φ.finiteFanScheme R ≅ I.blowup)
    (he : e.hom ≫ I.blowupToBase = h.toFanHom.finiteFanSchemeHom R) (ρ : Ψ.Ray)
    (hρ : (Ψ.rayBoundaryChartPoint (R := R) hregΨ ρ).val ∉ I.support) :
    (I.blowupMap (Ψ.rayDivisorIdeal R hregΨ ρ).subschemeι).ker.comap e.hom =
      Φ.rayDivisorIdeal R hregΦ (h.liftRay ρ) := by
  let x := (Φ.rayBoundaryChartPoint (R := R) hregΦ (h.liftRay ρ)).val
  have hx : I.blowupToBase (e.hom x) = (Ψ.rayBoundaryChartPoint (R := R) hregΨ ρ).val := by
    rw [← Scheme.Hom.comp_apply, he]
    exact h.finiteFanSchemeHom_rayBoundaryChartPoint_liftRay R hregΦ hregΨ ρ
  have houtside : e.hom x ∉ ((I.comap I.blowupToBase).support : Set I.blowup) := by
    rwa [support_comap, Closeds.coe_preimage, Set.mem_preimage, hx]
  rw [Ψ.rayDivisorIdeal_def R, ← hx, I.ker_blowupMap_vanishingIdeal_closure_singleton _ houtside,
    comap_vanishingIdeal_closure_singleton_apply, Φ.rayDivisorIdeal_def R]

end Fan.IsSubdivision

end TauCeti.Toric
