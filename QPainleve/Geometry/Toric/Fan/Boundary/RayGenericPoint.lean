/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.RayIdeal
public import QPainleve.Geometry.Toric.Fan.Ray
public import TauCeti.AlgebraicGeometry.Scheme.CodimensionOnePoint
public import TauCeti.Geometry.Toric.Algebraic.BaseChange.Fan

import QPainleve.Geometry.Toric.RegularChart
import QPainleve.Geometry.Toric.BaseChange.DenseTorus

/-!
# Boundary points of regular toric schemes

The ray primes in the affine charts give codimension-one points of the fan scheme
over a Noetherian domain. Their closures cover the complement of the zero-cone chart.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory AddMonoidAlgebra Multiplicative
open TauCeti.AlgebraicGeometry (CodimensionOnePoint)

namespace TauCeti.Toric

universe u

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V}
  (hi : IsIntegralLattice i) (hσ : IsToricCone i σ) (hreg : IsRegularCone i σ)
  (ρ : ToricRay σ) (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]

/-- The generic point of the ray divisor in the chart of a regular cone. -/
noncomputable def IsRegularCone.rayChartPoint :
    CodimensionOnePoint (Spec (.of (affineChartRing R hi σ))) :=
  let x : PrimeSpectrum (affineChartRing R hi σ) :=
    ⟨rayChartIdeal hi hσ ρ R, isPrime_rayChartIdeal hi hσ ρ R⟩
  ⟨x, (idealHeight_eq_coheight (.of (affineChartRing R hi σ)) x).symm.trans
    (hreg.height_rayChartIdeal hi hσ ρ R)⟩

/-- The ray point is determined by the ideal of monomials positive on the ray. -/
@[simp]
theorem IsRegularCone.rayChartPoint_asIdeal :
    (hreg.rayChartPoint hi hσ ρ R).val.asIdeal = rayChartIdeal hi hσ ρ R :=
  (rfl)

namespace Fan

variable {N R : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} [CommRing R] [IsDomain R] [IsNoetherianRing R] (Φ : Fan i)

/-- The generic point of a ray divisor on a regular toric scheme over a Noetherian domain. -/
noncomputable def rayBoundaryChartPoint (hΦ : Φ.IsRegular) (ρ : Φ.Ray) :
    CodimensionOnePoint (Φ.finiteFanScheme R) :=
  CodimensionOnePoint.mapOfIsOpenImmersion (Φ.affineChartι R ρ.toCone)
    ((isRegular_iff.mp hΦ _ ρ.toCone.property).rayChartPoint Φ.lattice
      (Φ.isToricCone ρ.toCone.property) (Ray.toToricRay Φ ρ ρ.toCone le_rfl) R)

/-- The ray boundary point is the image of its prime in the chart of the ray. -/
@[simp]
theorem coe_rayBoundaryChartPoint (hΦ : Φ.IsRegular) (ρ : Φ.Ray) :
    (Φ.rayBoundaryChartPoint (R := R) hΦ ρ).val =
      Φ.affineChartι R ρ.toCone
        ((isRegular_iff.mp hΦ _ ρ.toCone.property).rayChartPoint Φ.lattice
          (Φ.isToricCone ρ.toCone.property) (Ray.toToricRay Φ ρ ρ.toCone le_rfl) R).val := by
  rw [rayBoundaryChartPoint, CodimensionOnePoint.coe_mapOfIsOpenImmersion]

/-- In any chart containing a fan ray, the ray boundary point is given by the ray prime. -/
theorem rayBoundaryChartPoint_ofToricRay (hΦ : Φ.IsRegular) (σ : Φ.cones) (ρ : ToricRay σ.val) :
    (Φ.rayBoundaryChartPoint (R := R) hΦ (Ray.ofToricRay Φ σ ρ)).val =
      Φ.affineChartι R σ
        ((isRegular_iff.mp hΦ _ σ.property).rayChartPoint Φ.lattice
          (Φ.isToricCone σ.property) ρ R).val := by
  let τ := (Ray.ofToricRay Φ σ ρ).toCone
  let r := Ray.toToricRay Φ (Ray.ofToricRay Φ σ ρ) τ le_rfl
  let hτ := Φ.isToricCone τ.property
  let hσ := Φ.isToricCone σ.property
  let hτreg := (isRegular_iff.mp hΦ) _ τ.property
  let hσreg := (isRegular_iff.mp hΦ) _ σ.property
  let hface := Φ.isFaceOf_of_le σ.property τ.property (Ray.toCone_ofToricRay_le Φ σ ρ)
  let f := faceAffineChartMap R Φ.lattice hface
  have : IsOpenImmersion f := hσ.rational.isOpenImmersion_faceAffineChartMap R Φ.lattice hface
  let q := hτreg.rayChartPoint Φ.lattice hτ r R
  let p := hσreg.rayChartPoint Φ.lattice hσ ρ R
  have hv : primitiveGenerator Φ.lattice hσ ρ = primitiveGenerator Φ.lattice hτ r := by
    simpa only [Ray.primitiveGenerator_def] using (Ray.primitiveGenerator_ofToricRay σ ρ).symm
  have hsub : p.val.asIdeal ≤ (f q.val).asIdeal := by
    rw [hσreg.rayChartPoint_asIdeal, rayChartIdeal_eq_span, Ideal.span_le]
    rintro _ ⟨m, hm, rfl⟩
    rw [show f = Spec.map (CommRingCat.ofHom (faceAffineChartRingMap R Φ.lattice hface).toRingHom)
      from faceAffineChartMap_def R Φ.lattice hface]
    change faceAffineChartRingMap R Φ.lattice hface (single m 1) ∈ q.val.asIdeal
    rw [hτreg.rayChartPoint_asIdeal, faceAffineChartRingMap_single, single_mem_rayChartIdeal_iff]
    exact Or.inr (hv ▸ hm)
  have hqheight : (f q.val).asIdeal.height = 1 :=
    (idealHeight_eq_coheight (.of (affineChartRing R Φ.lattice σ.val)) _).trans
      ((coheight_eq_of_isOpenImmersion f).trans q.property)
  have hpheight : p.val.asIdeal.height = 1 :=
    (idealHeight_eq_coheight (.of (affineChartRing R Φ.lattice σ.val)) _).trans p.property
  have := p.val.isPrime
  have : p.val.asIdeal.FiniteHeight := p.val.asIdeal.finiteHeight_iff.mpr (by rw [hpheight]; simp)
  have heq : f q.val = p.val := PrimeSpectrum.ext <|
    (Ideal.eq_of_le_of_height_le p.val.asIdeal hsub (by rw [hqheight, hpheight])).symm
  rw [coe_rayBoundaryChartPoint,
    ← Φ.faceAffineChartMap_comp_affineChartι R (τ := τ) (σ := σ) hface,
    Scheme.Hom.comp_apply, heq]

/-- The ray boundary point lies outside the chart of the zero cone. -/
theorem rayBoundaryChartPoint_notMem_zeroChart (hΦ : Φ.IsRegular) (ρ : Φ.Ray)
    (hbot : (⊥ : PointedCone ℝ V) ∈ Φ.cones) :
    (Φ.rayBoundaryChartPoint (R := R) hΦ ρ).val ∉
      Set.range (Φ.affineChartι R ⟨⊥, hbot⟩) := by
  let σ := ρ.toCone
  let r := Ray.toToricRay Φ ρ σ le_rfl
  let hσ := Φ.isToricCone σ.property
  let hreg := (isRegular_iff.mp hΦ) _ σ.property
  let hface := hσ.salient.bot_isFaceOf
  let p := hreg.rayChartPoint Φ.lattice hσ r R
  rintro ⟨y, hy⟩
  rw [← Φ.faceAffineChartMap_comp_affineChartι R (τ := ⟨⊥, hbot⟩) (σ := σ) hface,
    Scheme.Hom.comp_apply, coe_rayBoundaryChartPoint] at hy
  have hp : faceAffineChartMap R Φ.lattice hface y = p.val :=
    (Φ.affineChartι R σ).isOpenEmbedding.injective hy
  obtain ⟨l, b, hb⟩ := hreg.exists_basis_sum
  let m := dualSemigroupCoord Φ.lattice hσ hb (Sum.inl r)
  have hm : single m 1 ∈ p.val.asIdeal := by
    rw [IsRegularCone.rayChartPoint_asIdeal,
      rayChartIdeal_eq_span_rayCoordinate Φ.lattice hσ r R hb]
    exact Ideal.mem_span_singleton_self _
  rw [← hp, faceAffineChartMap_def, Spec.map_apply] at hm
  let q : PrimeSpectrum (affineChartRing R Φ.lattice ⊥) := y
  have := q.isPrime
  have hm' : faceAffineChartRingMap R Φ.lattice hface (single m 1) ∈ q.asIdeal := hm
  apply q.asIdeal.notMem_of_isUnit _ hm'
  rw [faceAffineChartRingMap_single]
  exact isUnit_single_bot Φ.lattice _

/-- Every point off the zero-cone chart is a specialization of a ray point. -/
theorem exists_rayBoundaryChartPoint_specializes (hΦ : Φ.IsRegular)
    (hbot : (⊥ : PointedCone ℝ V) ∈ Φ.cones) {x : Φ.finiteFanScheme R}
    (hx : x ∉ Set.range (Φ.affineChartι R ⟨⊥, hbot⟩)) :
    ∃ ρ : Φ.Ray, (Φ.rayBoundaryChartPoint (R := R) hΦ ρ).val ⤳ x := by
  obtain ⟨σ, y, hy⟩ := Φ.exists_affineChartι_apply_eq R x
  let hσ := Φ.isToricCone σ.property
  let hreg := (isRegular_iff.mp hΦ) _ σ.property
  let hface := hσ.salient.bot_isFaceOf
  have hy' : y ∉ Set.range (faceAffineChartMap R Φ.lattice hface) := by
    rintro ⟨a, rfl⟩
    exact hx ⟨a, by
      rw [← Φ.faceAffineChartMap_comp_affineChartι R (τ := ⟨⊥, hbot⟩) (σ := σ) hface,
        Scheme.Hom.comp_apply, hy]⟩
  obtain ⟨m, hm⟩ :=
    hσ.rational.exists_isLocalization_away_faceAffineChartRingMap R Φ.lattice hface
  let := (faceAffineChartRingMap R Φ.lattice hface).toRingHom.toAlgebra
  let := hm
  have hrange : Set.range (faceAffineChartMap R Φ.lattice hface) =
      (PrimeSpectrum.basicOpen (single m (1 : R)) :
        Set (PrimeSpectrum (affineChartRing R Φ.lattice σ.val))) := by
    rw [faceAffineChartMap_def]
    exact PrimeSpectrum.localization_away_comap_range (affineChartRing R Φ.lattice ⊥) _
  rw [hrange] at hy'
  let p : PrimeSpectrum (affineChartRing R Φ.lattice σ.val) := y
  have : p.asIdeal.IsPrime := p.isPrime
  have hmem : single m (1 : R) ∈ p.asIdeal := Classical.not_not.mp hy'
  obtain ⟨ρ, hρ⟩ := exists_rayChartIdeal_le_of_single_mem Φ.lattice hσ R hreg p.asIdeal m hmem
  refine ⟨Ray.ofToricRay Φ σ ρ, ?_⟩
  rw [rayBoundaryChartPoint_ofToricRay, ← hy]
  apply Specializes.map _ (Φ.affineChartι R σ).continuous
  let q := (hreg.rayChartPoint Φ.lattice hσ ρ R).val
  exact (PrimeSpectrum.le_iff_specializes q y).mp ((PrimeSpectrum.asIdeal_le_asIdeal q y).mp
    ((hreg.rayChartPoint_asIdeal Φ.lattice hσ ρ R).symm ▸ hρ))

/-- The complement of the zero chart is the union of the closures of the ray points. -/
theorem compl_range_zeroChart_eq_iUnion_closure (hΦ : Φ.IsRegular)
    (hbot : (⊥ : PointedCone ℝ V) ∈ Φ.cones) :
    (Set.range (Φ.affineChartι R ⟨⊥, hbot⟩))ᶜ =
      ⋃ ρ : Φ.Ray, closure {(Φ.rayBoundaryChartPoint (R := R) hΦ ρ).val} := by
  refine Set.Subset.antisymm (fun x hx ↦ ?_) (Set.iUnion_subset fun ρ ↦ ?_)
  · obtain ⟨ρ, hρ⟩ := Φ.exists_rayBoundaryChartPoint_specializes hΦ hbot hx
    exact Set.mem_iUnion.mpr ⟨ρ, specializes_iff_mem_closure.mp hρ⟩
  · exact closure_minimal
      (Set.singleton_subset_iff.mpr (Φ.rayBoundaryChartPoint_notMem_zeroChart hΦ ρ hbot))
      (Φ.affineChartι R ⟨⊥, hbot⟩).isOpenEmbedding.isOpen_range.isClosed_compl

/-- The ray points are all the codimension-one points outside the zero-cone chart. -/
theorem range_rayBoundaryChartPoint (hΦ : Φ.IsRegular)
    (hbot : (⊥ : PointedCone ℝ V) ∈ Φ.cones) :
    Set.range (Φ.rayBoundaryChartPoint (R := R) hΦ) =
      {x | x.val ∉ Set.range (Φ.affineChartι R ⟨⊥, hbot⟩)} := by
  ext x
  constructor
  · rintro ⟨ρ, rfl⟩
    exact Φ.rayBoundaryChartPoint_notMem_zeroChart hΦ ρ hbot
  · intro hx
    obtain ⟨ρ, hρ⟩ := Φ.exists_rayBoundaryChartPoint_specializes hΦ hbot hx
    exact ⟨ρ, CodimensionOnePoint.eq_of_specializes hρ⟩

/-- A cone chart contains the point of a ray precisely when the cone contains that ray. -/
theorem rayBoundaryChartPoint_mem_range_affineChartι_iff (hΦ : Φ.IsRegular)
    (ρ : Φ.Ray) (σ : Φ.cones) :
    (Φ.rayBoundaryChartPoint (R := R) hΦ ρ).val ∈ Set.range (Φ.affineChartι R σ) ↔
      ρ.toCone ≤ σ := by
  constructor
  · rintro ⟨y, hy⟩
    rw [coe_rayBoundaryChartPoint] at hy
    obtain ⟨z, hz, -⟩ := (Φ.affineChartι_apply_eq_affineChartι_apply_iff R _ _).mp hy
    let τ := σ ⊓ ρ.toCone
    have hτ : τ.val.IsFaceOf ρ.toCone.val := Φ.inf_isFaceOf_right σ.property ρ.toCone.property
    rw [ρ.toCone_eq_hull_primitiveGenerator] at hτ
    rcases hτ.eq_bot_or_eq_of_hull_singleton (i ρ.primitiveGenerator) with hbot | hfull
    · have hmem : (Φ.rayBoundaryChartPoint (R := R) hΦ ρ).val ∈
          Set.range (Φ.affineChartι R τ) := by
        exact ⟨z, by rw [← Φ.faceAffineChartMap_comp_affineChartι R
          (Φ.inf_isFaceOf_left σ.property ρ.toCone.property), Scheme.Hom.comp_apply, hz, hy,
          coe_rayBoundaryChartPoint]⟩
      have hz' : τ = ⟨⊥, Φ.bot_mem σ.property⟩ := Subtype.ext hbot
      exact (Φ.rayBoundaryChartPoint_notMem_zeroChart hΦ ρ _ (hz' ▸ hmem)).elim
    · have heq : τ = ρ.toCone := Subtype.ext
        (hfull.trans ρ.toCone_eq_hull_primitiveGenerator.symm)
      exact heq ▸ inf_le_left (a := σ) (b := ρ.toCone)
  · intro h
    let r := ρ.toToricRay Φ σ h
    have hr : Ray.ofToricRay Φ σ r = ρ := by
      simpa only [r, rayEquiv_apply, rayEquiv_symm_apply] using
        congrArg Subtype.val ((Φ.rayEquiv σ).symm_apply_apply ⟨ρ, h⟩)
    exact ⟨_, (Φ.rayBoundaryChartPoint_ofToricRay (R := R) hΦ σ r).symm.trans
      (congrArg (fun s : Φ.Ray ↦ (Φ.rayBoundaryChartPoint (R := R) hΦ s).val) hr)⟩

/-- Distinct rays give distinct codimension-one points. -/
theorem rayBoundaryChartPoint_injective (hΦ : Φ.IsRegular) :
    Function.Injective (Φ.rayBoundaryChartPoint (R := R) hΦ) := by
  intro ρ τ h
  apply Subtype.ext
  apply le_antisymm
  · apply (Φ.rayBoundaryChartPoint_mem_range_affineChartι_iff (R := R) hΦ ρ τ.toCone).mp
    rw [h, coe_rayBoundaryChartPoint]
    exact Set.mem_range_self _
  · apply (Φ.rayBoundaryChartPoint_mem_range_affineChartι_iff (R := R) hΦ τ ρ.toCone).mp
    rw [← h, coe_rayBoundaryChartPoint]
    exact Set.mem_range_self _

end Fan

end TauCeti.Toric
