/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import QPainleve.Geometry.Toric.Fan.Boundary.Basic
public import QPainleve.Geometry.Toric.Fan.Boundary.Ray.Orbit
public import QPainleve.Geometry.Toric.Fan.Separated
public import TauCeti.Algebra.Polynomial.Laurent.Basic
public import TauCeti.AlgebraicGeometry.Curves.Prestable
public import TauCeti.AlgebraicGeometry.Curves.SingularLocus.Basic
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.Over
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import QPainleve.Algebra.MonoidAlgebra.Smooth
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.Algebra.Bialgebra.MonoidAlgebra.Equiv
import TauCeti.AlgebraicGeometry.Curves.SingularLocus.Smooth
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Section
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.OfIdealTop
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import TauCeti.AlgebraicGeometry.Pullback.Carrier
import TauCeti.AlgebraicGeometry.Scheme.SpecOver

/-!
# Binomial centers on toric boundary rays

In a rank-two fan, the boundary in a ray's affine chart is the one-dimensional torus.
A primitive character annihilating the ray gives a Laurent coordinate on this torus.
For a nonzero complex parameter `c`, the equation `1 + c * z^m = 0` cuts out a single
reduced point. Its ideal in the ray chart includes the ray ideal and the binomial equation.

This uses the affine orbit description in Fulton, *Introduction to Toric Varieties*, §3.1,
for the smooth boundary centers of Gross, Hacking and Keel, *Moduli of surfaces with an
anti-canonical cycle*, Definition 1.2. The scheme structure comes from Tau Ceti's
`AddSubmonoid.faceRestriction` and `ker_laurentEval_neg_inv`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative LaurentPolynomial TopologicalSpace

namespace TauCeti.Toric.Fan.Ray

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (ρ : Φ.Ray)

local notation "S" => dualSemigroup Φ.lattice ρ.toCone.val
local notation "R" => affineCoordinateRing Φ.lattice ρ.toCone.val
local notation "v" => ρ.primitiveGenerator

private theorem isRegularCone_toCone : IsRegularCone i ρ.toCone.val := by
  rw [ρ.toCone_eq_hull_primitiveGenerator]
  exact isRegularCone_hull_singleton Φ.lattice ρ.primitiveGenerator_isPrimitive

variable {m : N →+ ℤ}

local notation "χ" => MonoidAlgebra.of ℂ (Multiplicative S)

local notation "chartEquiv" => (AddMonoidAlgebra.toMultiplicativeAlgEquiv ℂ ℂ S)
local notation "orbitEval(" hdim ", " hm ", " hprim ")" =>
  (AlgHom.comp (orbitCoordinateMap ρ ℂ hdim hm hprim)
    (AlgEquiv.toAlgHom (AlgEquiv.symm chartEquiv)))
local notation "centerEval(" hdim ", " hm ", " hprim ", " c ")" =>
  (AlgHom.comp (binomialCenterEval ρ ℂ hdim hm hprim c)
    (AlgEquiv.toAlgHom (AlgEquiv.symm chartEquiv)))

private theorem map_rayChartIdeal (r : ToricRay ρ.toCone.val) :
    (rayChartIdeal Φ.lattice (Φ.isToricCone ρ.toCone.property) r ℂ).map (chartEquiv).toRingEquiv =
      rayIdeal Φ.lattice (Φ.isToricCone ρ.toCone.property) r := by
  apply le_antisymm
  · rw [rayChartIdeal_eq_span, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    change (chartEquiv) (AddMonoidAlgebra.single a (1 : ℂ)) ∈
      rayIdeal Φ.lattice (Φ.isToricCone ρ.toCone.property) r
    simpa only [AddMonoidAlgebra.toMultiplicativeAlgEquiv_single, MonoidAlgebra.of_apply] using
      monomial_mem_rayIdeal Φ.lattice (Φ.isToricCone ρ.toCone.property) r a ha
  · rw [rayIdeal_le_iff]
    intro a ha
    have hmem : AddMonoidAlgebra.single a (1 : ℂ) ∈
        rayChartIdeal Φ.lattice (Φ.isToricCone ρ.toCone.property) r ℂ :=
      (single_mem_rayChartIdeal_iff _ _ _ _ _ _).mpr (Or.inr ha)
    simpa only [RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv,
      AddMonoidAlgebra.toMultiplicativeAlgEquiv_single, MonoidAlgebra.of_apply] using
      Ideal.mem_map_of_mem (chartEquiv).toRingEquiv hmem

private theorem ker_binomialCenterEval_chart (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : ℂˣ) :
    RingHom.ker (centerEval(hdim, hm, hprim, c)) =
      rayIdeal Φ.lattice (Φ.isToricCone ρ.toCone.property)
        (Ray.toToricRay Φ ρ ρ.toCone le_rfl) ⊔
      Ideal.span {1 + algebraMap ℂ R (c : ℂ) * χ (ofAdd (ρ.chartCharacter hm))} := by
  change Ideal.comap (chartEquiv).toRingEquiv.symm
    (RingHom.ker (ρ.binomialCenterEval ℂ hdim hm hprim c)) = _
  rw [Ideal.comap_symm, ker_binomialCenterEval, Ideal.map_sup, map_rayChartIdeal,
    Ideal.map_span, Set.image_singleton]
  simp [MonoidAlgebra.of_apply]

/-- The boundary point with parameter `c`, included into the entire fan scheme. -/
def binomialCenter (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : ℂˣ) :
    Spec (.of ℂ) ⟶ Φ.algebraicRealization :=
  Spec.map (CommRingCat.ofHom (centerEval(hdim, hm, hprim, c)).toRingHom) ≫
    Φ.affineToricChartι ρ.toCone

/-- The center is the point of the ray chart defined by the binomial evaluation map. -/
theorem binomialCenter_def (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : ℂˣ) :
    ρ.binomialCenter hdim hm hprim c =
      Spec.map (CommRingCat.ofHom (centerEval(hdim, hm, hprim, c)).toRingHom) ≫
        Φ.affineToricChartι ρ.toCone := (rfl)

/-- Negating the primitive orbit character inverts the center parameter. The resulting
sections coincide as morphisms from the coefficient field. -/
theorem binomialCenter_neg_inv (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hs : Function.Surjective m) (c : ℂˣ) :
    ρ.binomialCenter hdim (m := -m) (by simp [hm])
        (neg_involutive.surjective.comp hs) c⁻¹ =
      ρ.binomialCenter hdim hm hs c := by
  have h : ρ.binomialCenterEval ℂ hdim (m := -m) (by simp [hm])
      (neg_involutive.surjective.comp hs) c⁻¹ = ρ.binomialCenterEval ℂ hdim hm hs c :=
    ρ.binomialCenterEval_neg_inv ℂ hdim hm hs c
  simp only [binomialCenter, h]

/-- A binomial center is a section of the structural morphism. -/
@[reassoc, simp]
theorem binomialCenter_comp_structureMap (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : ℂˣ) :
    ρ.binomialCenter hdim hm hprim c ≫ Φ.algebraicRealizationStructureMap = 𝟙 _ := by
  rw [binomialCenter, Category.assoc, Φ.affineToricChartι_comp_algebraicRealizationStructureMap,
    ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext a
  exact (centerEval(hdim, hm, hprim, c)).commutes a

/-- A binomial center is a reduced closed complex point of the fan scheme. -/
instance isClosedImmersion_binomialCenter (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : ℂˣ) :
    IsClosedImmersion (ρ.binomialCenter hdim hm hprim c) :=
  isClosedImmersion_of_comp_eq_id _ _ (ρ.binomialCenter_comp_structureMap hdim hm hprim c)

open Scheme.IdealSheafData in
/-- The ideal sheaf of the ambient center restricts to the binomial and ray equations. -/
theorem comap_ker_binomialCenter_rayChart (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : ℂˣ) :
    (ρ.binomialCenter hdim hm hprim c).ker.comap (Φ.affineToricChartι ρ.toCone) =
      ofIdealTop ((
        rayIdeal Φ.lattice (Φ.isToricCone ρ.toCone.property)
          (Ray.toToricRay Φ ρ ρ.toCone le_rfl) ⊔
        Ideal.span {1 + algebraMap ℂ R (c : ℂ) * χ (ofAdd (ρ.chartCharacter hm))}).map
          (Scheme.ΓSpecIso (.of R)).inv.hom) := by
  let j := Φ.affineToricChartι ρ.toCone
  let t := Spec.map (CommRingCat.ofHom (centerEval(hdim, hm, hprim, c)).toRingHom)
  let s := ρ.binomialCenter hdim hm hprim c
  have hcomp : t ≫ j = s := rfl
  have hrange : Set.range s ⊆ Set.range j := by
    rw [← hcomp, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact Set.range_comp_subset_range _ _
  have H : IsPullback t (𝟙 _) j s := by
    rw [IsOpenImmersion.lift_uniq j s hrange t hcomp]
    exact IsOpenImmersion.isPullback_lift_id s j hrange
  rw [← ker_eq_comap_of_isPullback_of_isOpenImmersion j H]
  exact (Scheme.Hom.ker_Spec_map _).trans (congrArg
    (fun I : Ideal R ↦ ofIdealTop (I.map (Scheme.ΓSpecIso (.of R)).inv.hom))
    (ker_binomialCenterEval_chart ρ hdim hm hprim c))

/-- Two parameters give the same center on a fixed ray exactly when they are equal. -/
theorem binomialCenter_injective (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) :
    Function.Injective (ρ.binomialCenter hdim hm hprim) := by
  intro c d h
  rw [binomialCenter, binomialCenter, cancel_mono, Spec.map_injective.eq_iff] at h
  have heq := congrArg (fun g : CommRingCat.of R ⟶ CommRingCat.of ℂ ↦
    g (χ (ofAdd (ρ.chartCharacter hm)))) h
  have heval : centerEval(hdim, hm, hprim, c) (χ (ofAdd (ρ.chartCharacter hm))) =
      centerEval(hdim, hm, hprim, d) (χ (ofAdd (ρ.chartCharacter hm))) := heq
  simp only [MonoidAlgebra.of_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AddMonoidAlgebra.toMultiplicativeAlgEquiv_symm_single, toAdd_ofAdd,
    binomialCenterEval_character, neg_inj] at heval
  exact inv_injective (Units.ext heval)

private theorem exists_rayChartEquation :
    ∃ q : S, (q : N →+ ℤ) v = 1 ∧
      rayIdeal Φ.lattice (Φ.isToricCone ρ.toCone.property)
          (Ray.toToricRay Φ ρ ρ.toCone le_rfl) = Ideal.span {χ (ofAdd q)} := by
  let r := Ray.toToricRay Φ ρ ρ.toCone le_rfl
  let hσ := Φ.isToricCone ρ.toCone.property
  obtain ⟨l, b, hb⟩ := (isRegularCone_toCone ρ).exists_basis_sum
  let q := dualSemigroupCoord Φ.lattice hσ hb (Sum.inl r)
  refine ⟨q, ?_, rayIdeal_eq_span _ _ hb r⟩
  rw [Ray.primitiveGenerator_def, ← (hb r).eq_primitiveGenerator Φ.lattice hσ]
  simp [q]

private theorem inf_ker_eq_bot_of_rayChartEquation (q : S) (hq : (q : N →+ ℤ) v = 1) :
    ρ.toCone.val ⊓ PointedCone.ofSubmodule (LinearMap.ker (Φ.lattice.realCharacter q)) = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨hx, hxker⟩ := hx
  rw [ρ.toCone_eq_hull_primitiveGenerator] at hx
  obtain ⟨r, _, rfl⟩ := PointedCone.mem_hull_singleton.mp hx
  have hzero := LinearMap.mem_ker.mp hxker
  rw [map_smul, smul_eq_mul, Φ.lattice.realCharacter_apply, hq, Int.cast_one, mul_one] at hzero
  simp [hzero]

private theorem preimage_compl_range_denseTorusι :
    Φ.affineToricChartι ρ.toCone ⁻¹' (Set.range (Φ.denseTorusι ⟨ρ.toCone⟩))ᶜ =
      PrimeSpectrum.zeroLocus (rayIdeal Φ.lattice (Φ.isToricCone ρ.toCone.property)
        (Ray.toToricRay Φ ρ ρ.toCone le_rfl) : Set R) := by
  let j := Φ.affineToricChartι ρ.toCone
  obtain ⟨q, hq, heq⟩ := exists_rayChartEquation ρ
  let P (τ : PointedCone ℝ V) := ∀ h : τ.IsFaceOf ρ.toCone.val,
    Set.range (faceAffineToricSchemeMap Φ.lattice h) =
      (PrimeSpectrum.basicOpen (MonoidAlgebra.single (ofAdd q) (1 : ℂ)) : Set (PrimeSpectrum R))
  have hP : P (ρ.toCone.val ⊓
      PointedCone.ofSubmodule (LinearMap.ker (Φ.lattice.realCharacter q))) :=
    fun _ ↦ range_faceAffineToricSchemeMap Φ.lattice (Φ.isToricCone ρ.toCone.property).fg q
  rw [inf_ker_eq_bot_of_rayChartEquation ρ q hq] at hP
  have hrange := hP (Φ.isToricCone ρ.toCone.property).salient.bot_isFaceOf
  rw [Φ.denseTorusι_face ρ.toCone, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.preimage_compl, j.isOpenEmbedding.injective.preimage_image, hrange, heq,
    PrimeSpectrum.zeroLocus_span]
  rw [MonoidAlgebra.of_apply, PrimeSpectrum.basicOpen_eq_zeroLocus_compl]
  exact compl_compl _

/-- The affine ray orbit, parametrized by the primitive character, embeds as the closed
boundary in the affine ray chart. -/
def orbitToRayChart (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) :
    Spec (.of (LaurentPolynomial ℂ)) ⟶ Φ.affineToricChart ρ.toCone :=
  Spec.map (CommRingCat.ofHom (orbitEval(hdim, hm, hprim)).toRingHom)

/-- The ray orbit immersion is induced by restriction to Laurent coordinates. -/
theorem orbitToRayChart_def (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) :
    ρ.orbitToRayChart hdim hm hprim =
      Spec.map (CommRingCat.ofHom (orbitEval(hdim, hm, hprim)).toRingHom) :=
  (rfl)

private theorem ker_orbitCoordinateMap_chart (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) :
    RingHom.ker (orbitEval(hdim, hm, hprim)) =
      rayIdeal Φ.lattice (Φ.isToricCone ρ.toCone.property)
        (Ray.toToricRay Φ ρ ρ.toCone le_rfl) := by
  change Ideal.comap (chartEquiv).toRingEquiv.symm
    (RingHom.ker (ρ.orbitCoordinateMap ℂ hdim hm hprim)) = _
  rw [Ideal.comap_symm, ker_orbitCoordinateMap, map_rayChartIdeal]

open Scheme.IdealSheafData in
/-- The ray orbit immersion has the ideal sheaf of the ray ideal in its chart. -/
theorem ker_orbitToRayChart (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) :
    (ρ.orbitToRayChart hdim hm hprim).ker =
      ofIdealTop ((rayIdeal Φ.lattice (Φ.isToricCone ρ.toCone.property)
        (Ray.toToricRay Φ ρ ρ.toCone le_rfl)).map (Scheme.ΓSpecIso (.of R)).inv.hom) := by
  rw [orbitToRayChart_def, Scheme.Hom.ker_Spec_map, CommRingCat.hom_ofHom,
    AlgHom.toRingHom_eq_coe, ← AlgHom.ker_coe, ker_orbitCoordinateMap_chart]

/-- The orbit is a closed subscheme of the ray chart. -/
instance isClosedImmersion_orbitToRayChart (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) :
    IsClosedImmersion (ρ.orbitToRayChart hdim hm hprim) :=
  IsClosedImmersion.spec_of_surjective _ ((ρ.orbitCoordinateMap_surjective ℂ hdim hm hprim).comp
    (chartEquiv).symm.surjective)

private theorem range_orbitToRayChart (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) :
    Set.range (ρ.orbitToRayChart hdim hm hprim) =
      Φ.affineToricChartι ρ.toCone ⁻¹' (Set.range (Φ.denseTorusι ⟨ρ.toCone⟩))ᶜ := by
  rw [orbitToRayChart, preimage_compl_range_denseTorusι]
  have hsurj : Function.Surjective (orbitEval(hdim, hm, hprim)).toRingHom :=
    (ρ.orbitCoordinateMap_surjective ℂ hdim hm hprim).comp (chartEquiv).symm.surjective
  exact (range_comap_of_surjective _ _ hsurj).trans
    (congrArg (fun I : Ideal R ↦ PrimeSpectrum.zeroLocus (I : Set R))
      (ker_orbitCoordinateMap_chart ρ hdim hm hprim))

open Scheme.IdealSheafData in
private theorem boundaryIdeal_comap_rayChart (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) :
    (Φ.boundaryIdeal ⟨ρ.toCone⟩).comap (Φ.affineToricChartι ρ.toCone) =
      (ρ.orbitToRayChart hdim hm hprim).ker := by
  let f := ρ.orbitToRayChart hdim hm hprim
  rw [boundaryIdeal_def, comap_vanishingIdeal_of_isOpenImmersion]
  have hclosed := (Φ.denseTorusι ⟨ρ.toCone⟩).isOpenEmbedding.isOpen_range.isClosed_compl.preimage
    (Φ.affineToricChartι ρ.toCone).continuous
  have hZ : (⟨Φ.affineToricChartι ρ.toCone ⁻¹'
      (Set.range (Φ.denseTorusι ⟨ρ.toCone⟩))ᶜ, hclosed⟩ : Closeds (Φ.affineToricChart ρ.toCone)) =
      f.ker.support := by
    ext1
    rw [f.support_ker, f.isClosedEmbedding.isClosed_range.closure_eq, range_orbitToRayChart]
    rfl
  exact (congrArg vanishingIdeal hZ).trans f.ker_eq_vanishingIdeal_support.symm

private theorem boundaryIdeal_le_ker_orbit_comp (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) :
    Φ.boundaryIdeal ⟨ρ.toCone⟩ ≤
      (ρ.orbitToRayChart hdim hm hprim ≫ Φ.affineToricChartι ρ.toCone).ker := by
  rw [boundaryIdeal_def]
  apply Scheme.IdealSheafData.vanishingIdeal_le_ker_of_range_subset
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, range_orbitToRayChart]
  exact Set.image_preimage_subset _ _

/-- The orbit is a chart of the reduced boundary, obtained by restricting the affine ray chart. -/
def orbitToBoundary (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) :
    Spec (.of (LaurentPolynomial ℂ)) ⟶ (Φ.boundaryIdeal ⟨ρ.toCone⟩).subscheme :=
  IsClosedImmersion.lift (Φ.boundaryIdeal ⟨ρ.toCone⟩).subschemeι
    (ρ.orbitToRayChart hdim hm hprim ≫ Φ.affineToricChartι ρ.toCone)
    (by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      exact boundaryIdeal_le_ker_orbit_comp ρ hdim hm hprim)

/-- The ray orbit in the boundary has its original inclusion into the fan scheme. -/
@[reassoc, simp]
theorem orbitToBoundary_comp_subschemeι (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) :
    ρ.orbitToBoundary hdim hm hprim ≫ (Φ.boundaryIdeal ⟨ρ.toCone⟩).subschemeι =
      ρ.orbitToRayChart hdim hm hprim ≫ Φ.affineToricChartι ρ.toCone :=
  IsClosedImmersion.lift_fac _ _ _

/-- The toric structure map on the ray orbit is the structure map of the Laurent ring. -/
theorem orbitToBoundary_comp_algebraicRealizationStructureMap
    (hdim : Module.finrank ℤ N = 2) (hm : m v = 0) (hprim : Function.Surjective m) :
    ρ.orbitToBoundary hdim hm hprim ≫ (Φ.boundaryIdeal ⟨ρ.toCone⟩).subschemeι ≫
        Φ.algebraicRealizationStructureMap =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (LaurentPolynomial ℂ))) := by
  rw [orbitToBoundary_comp_subschemeι_assoc,
    Φ.affineToricChartι_comp_algebraicRealizationStructureMap, orbitToRayChart_def, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact (orbitEval(hdim, hm, hprim)).commutes a

/-- The affine ray orbit is the scheme-theoretic restriction of the boundary to the ray chart. -/
theorem isPullback_orbitToBoundary (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) :
    IsPullback (ρ.orbitToRayChart hdim hm hprim) (ρ.orbitToBoundary hdim hm hprim)
      (Φ.affineToricChartι ρ.toCone) (Φ.boundaryIdeal ⟨ρ.toCone⟩).subschemeι := by
  apply isPullback_of_isClosedImmersion
  · exact (ρ.orbitToBoundary_comp_subschemeι hdim hm hprim).symm
  · rw [Scheme.IdealSheafData.ker_subschemeι]
    exact boundaryIdeal_comap_rayChart ρ hdim hm hprim

/-- The ray orbit is an open subscheme of the reduced boundary. -/
instance isOpenImmersion_orbitToBoundary (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) :
    IsOpenImmersion (ρ.orbitToBoundary hdim hm hprim) :=
  MorphismProperty.of_isPullback (ρ.isPullback_orbitToBoundary hdim hm hprim)
    (Φ.isOpenImmersion_affineToricChartι ρ.toCone)

/-- The binomial point as a complex point of the reduced boundary. -/
def binomialCenterOnBoundary (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : ℂˣ) :
    Spec (.of ℂ) ⟶ (Φ.boundaryIdeal ⟨ρ.toCone⟩).subscheme :=
  Spec.map (CommRingCat.ofHom (laurentEval ((-1 : ℂˣ) * c⁻¹)).toRingHom) ≫
    ρ.orbitToBoundary hdim hm hprim

/-- On the ray orbit, a binomial center is Laurent evaluation at `-c⁻¹`. -/
theorem binomialCenterOnBoundary_def (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : ℂˣ) :
    ρ.binomialCenterOnBoundary hdim hm hprim c =
      Spec.map (CommRingCat.ofHom (laurentEval ((-1 : ℂˣ) * c⁻¹)).toRingHom) ≫
        ρ.orbitToBoundary hdim hm hprim :=
  (rfl)

/-- Including the binomial point from the boundary gives the same point of the fan scheme. -/
@[reassoc, simp]
theorem binomialCenterOnBoundary_comp_subschemeι (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : ℂˣ) :
    ρ.binomialCenterOnBoundary hdim hm hprim c ≫ (Φ.boundaryIdeal ⟨ρ.toCone⟩).subschemeι =
      ρ.binomialCenter hdim hm hprim c := by
  rw [binomialCenterOnBoundary, Category.assoc, orbitToBoundary_comp_subschemeι, ← Category.assoc,
    orbitToRayChart, ← Spec.map_comp, binomialCenter, binomialCenterEval_def]
  rfl

/-- Negating the orbit character and inverting the parameter leaves the section of the
reduced boundary unchanged. -/
theorem binomialCenterOnBoundary_neg_inv (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hs : Function.Surjective m) (c : ℂˣ) :
    ρ.binomialCenterOnBoundary hdim (m := -m) (by simp [hm])
        (neg_involutive.surjective.comp hs) c⁻¹ =
      ρ.binomialCenterOnBoundary hdim hm hs c := by
  apply (cancel_mono (Φ.boundaryIdeal ⟨ρ.toCone⟩).subschemeι).mp
  exact (ρ.binomialCenterOnBoundary_comp_subschemeι (m := -m) hdim (by simp [hm])
    (neg_involutive.surjective.comp hs) c⁻¹).trans
    ((ρ.binomialCenter_neg_inv hdim hm hs c).trans
      (ρ.binomialCenterOnBoundary_comp_subschemeι hdim hm hs c).symm)

/-- The binomial point is a reduced closed point of the boundary. -/
instance isClosedImmersion_binomialCenterOnBoundary (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : ℂˣ) :
    IsClosedImmersion (ρ.binomialCenterOnBoundary hdim hm hprim c) := by
  have : IsClosedImmersion (ρ.binomialCenterOnBoundary hdim hm hprim c ≫
      (Φ.boundaryIdeal ⟨ρ.toCone⟩).subschemeι) := by
    rw [binomialCenterOnBoundary_comp_subschemeι]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (Φ.boundaryIdeal ⟨ρ.toCone⟩).subschemeι

/-- Every complex section of the reduced boundary in a ray chart is the binomial
point for some nonzero parameter in the prescribed primitive character. -/
theorem exists_binomialCenterOnBoundary_eq_of_mem_rayChart
    (hdim : Module.finrank ℤ N = 2) (hm : m v = 0) (hprim : Function.Surjective m)
    (p : Spec (.of ℂ) ⟶ (Φ.boundaryIdeal ⟨ρ.toCone⟩).subscheme)
    (hp : p ≫ (Φ.boundaryIdeal ⟨ρ.toCone⟩).subschemeι ≫ Φ.algebraicRealizationStructureMap = 𝟙 _)
    (hx : (Φ.boundaryIdeal ⟨ρ.toCone⟩).subschemeι (p (IsLocalRing.closedPoint ℂ)) ∈
      Set.range (Φ.affineToricChartι ρ.toCone)) :
    ∃ c : ℂˣ, ρ.binomialCenterOnBoundary hdim hm hprim c = p := by
  let o := ρ.orbitToBoundary hdim hm hprim
  have hmem : Set.range p ⊆ Set.range o := by
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x (IsLocalRing.closedPoint ℂ),
      Scheme.Pullback.range_snd_of_isPullback (ρ.isPullback_orbitToBoundary hdim hm hprim)]
    exact hx
  let l := IsOpenImmersion.lift o p hmem
  have hl : l ≫ o = p := IsOpenImmersion.lift_fac _ _ _
  have hbase : l ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (LaurentPolynomial ℂ))) = 𝟙 _ := by
    rw [← ρ.orbitToBoundary_comp_algebraicRealizationStructureMap hdim hm hprim,
      ← Category.assoc l o, hl, hp]
  have hl' : l ≫ Spec.algebraMap ℂ (LaurentPolynomial ℂ) = Spec.algebraMap ℂ ℂ := by
    simpa only [Spec.algebraMap, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
      using hbase
  obtain ⟨f, hf⟩ := TauCeti.AlgebraicGeometry.exists_algHom_SpecMap_eq l hl'
  obtain ⟨u, rfl⟩ := laurentEvalEquiv.surjective f
  refine ⟨(-u)⁻¹, ?_⟩
  rw [binomialCenterOnBoundary_def, ← hl, ← hf, laurentEvalEquiv_apply]
  simp [o]

/-- The ray chart of the reduced boundary is a smooth relative curve over `ℂ`. -/
theorem smoothOfRelativeDimension_orbitToBoundary (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) :
    SmoothOfRelativeDimension 1
      (ρ.orbitToBoundary hdim hm hprim ≫ (Φ.boundaryIdeal ⟨ρ.toCone⟩).subschemeι ≫
        Φ.algebraicRealizationStructureMap) := by
  rw [orbitToBoundary_comp_algebraicRealizationStructureMap,
    HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)
    (Q := RingHom.Locally (@RingHom.IsStandardSmoothOfRelativeDimension 1)),
    CommRingCat.hom_ofHom]
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := 1)]
  have hSmooth := AddMonoidAlgebra.isStandardSmoothOfRelativeDimension_finsupp_int ℂ (Fin 1)
  rw [Nat.card_fin] at hSmooth
  let e : (Fin 1 →₀ ℤ) ≃+ ℤ := Finsupp.uniqueAddEquiv 0
  have hLaurent : Algebra.IsStandardSmoothOfRelativeDimension 1 ℂ (LaurentPolynomial ℂ) :=
    Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv 1
      (AddMonoidAlgebra.domCongr ℂ ℂ e)
  exact hLaurent

/-- The binomial point on the boundary lies in the open ray orbit. -/
theorem range_binomialCenterOnBoundary_subset_range_orbitToBoundary
    (hdim : Module.finrank ℤ N = 2) (hm : m v = 0) (hprim : Function.Surjective m) (c : ℂˣ) :
    Set.range (ρ.binomialCenterOnBoundary hdim hm hprim c) ⊆
      Set.range (ρ.orbitToBoundary hdim hm hprim) := by
  rw [binomialCenterOnBoundary, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  exact Set.image_subset_range _ _

section SingularLocus

open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

variable [Nonempty Φ.cones]

local notation "base" => Spec (CommRingCat.of ℂ)
local notation "C" => Scheme.IdealSheafData.subscheme (Φ.boundaryIdeal inferInstance)
local notation "I" => Scheme.singularLocus ℂ C

variable [PrestableFamily ((Φ.boundaryIdeal inferInstance).subscheme ↘ Spec (.of ℂ))]

/-- A binomial center is away from the nodes, so its Cartier ideal restricts to
the unit ideal on the singular locus. -/
theorem comap_ker_binomialCenterOnBoundary_singularLocus
    (hdim : Module.finrank ℤ N = 2) (hm : m v = 0) (hprim : Function.Surjective m) (c : ℂˣ) :
    (ρ.binomialCenterOnBoundary hdim hm hprim c).ker.comap (I).subschemeι = ⊤ := by
  let t := ρ.orbitToBoundary hdim hm hprim
  let f := C ↘ base
  let p := ρ.binomialCenterOnBoundary hdim hm hprim c
  have hsm := ρ.smoothOfRelativeDimension_orbitToBoundary hdim hm hprim
  have : SmoothOfRelativeDimension 1 (t ≫ f) := by
    simpa only [t, f, over_eq_subschemeι_comp, Φ.algebraicRealization_over] using hsm
  have : Smooth (t ≫ f) := SmoothOfRelativeDimension.smooth 1 _
  have hdisj : Set.range p ⊆ f.smoothLocus := by
    refine (ρ.range_binomialCenterOnBoundary_subset_range_orbitToBoundary hdim hm hprim c).trans ?_
    rintro _ ⟨y, rfl⟩
    apply (t.mem_preimage).mp
    rw [t.preimage_smoothLocus_eq f, (t ≫ f).smoothLocus_eq_top]
    exact TopologicalSpace.Opens.mem_top y
  rw [comap_eq_top_iff, ← TopologicalSpace.Opens.coe_eq_univ, Scheme.Hom.coe_preimage,
    TopologicalSpace.Closeds.coe_compl, Scheme.Hom.support_ker,
    p.isClosedEmbedding.isClosed_range.closure_eq, Set.eq_univ_iff_forall]
  intro x hx
  have hs : (I).subschemeι x ∈ (I).support := (I).range_subschemeι.le (Set.mem_range_self x)
  exact ((C).mem_support_singularLocus_iff_notMem_smoothLocus _).mp hs (hdisj hx)

end SingularLocus

/-- The binomial point is an effective Cartier divisor on the reduced toric boundary. -/
theorem isEffectiveCartier_ker_binomialCenterOnBoundary (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : ℂˣ) :
    (ρ.binomialCenterOnBoundary hdim hm hprim c).ker.IsEffectiveCartier := by
  let D := Φ.boundaryIdeal ⟨ρ.toCone⟩
  let f := D.subschemeι ≫ Φ.algebraicRealizationStructureMap
  let j := ρ.orbitToBoundary hdim hm hprim
  let U := j.opensRange
  let s := ρ.binomialCenterOnBoundary hdim hm hprim c
  have hs : s ≫ f = 𝟙 _ := by
    dsimp only [s, f, D]
    rw [← Category.assoc, binomialCenterOnBoundary_comp_subschemeι,
      binomialCenter_comp_structureMap]
  have hU : Set.range s ⊆ U := by
    simpa only [U, Scheme.Hom.coe_opensRange] using
      ρ.range_binomialCenterOnBoundary_subset_range_orbitToBoundary hdim hm hprim c
  let e := IsOpenImmersion.isoOfRangeEq j U.ι U.range_ι.symm
  have he : e.hom ≫ U.ι = j :=
    IsOpenImmersion.isoOfRangeEq_hom_fac j U.ι U.range_ι.symm
  have : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension.{0} 1) :=
    @MorphismProperty.IsStableUnderBaseChange.respectsIso _ _ _
      (smoothOfRelativeDimension_isStableUnderBaseChange 1)
  have : SmoothOfRelativeDimension 1 (U.ι ≫ f) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1) e.hom,
      ← Category.assoc, he]
    exact smoothOfRelativeDimension_orbitToBoundary ρ hdim hm hprim
  exact Scheme.Hom.isEffectiveCartier_ker_of_comp_eq_id s hs U hU

/-- The ideal of the boundary center is the residue-field ideal of its closed point. -/
theorem exists_closedPoint_ker_binomialCenterOnBoundary (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : ℂˣ) :
    ∃ p : (Φ.boundaryIdeal ⟨ρ.toCone⟩).subscheme, IsClosed ({p} : Set _) ∧
      (ρ.binomialCenterOnBoundary hdim hm hprim c).ker = (Scheme.fromSpecResidueField _ p).ker := by
  let s := ρ.binomialCenterOnBoundary hdim hm hprim c
  let p := s (IsLocalRing.closedPoint ℂ)
  refine ⟨p, ?_, s.ker_eq_ker_fromSpecResidueField⟩
  have hrange : Set.range s = {p} :=
    Set.range_eq_singleton fun z ↦ congrArg s (Subsingleton.elim z _)
  rw [← hrange]
  exact s.isClosedEmbedding.isClosed_range

/-- Two binomial centers can coincide only if their rays agree. Distinct ray charts
intersect in the dense torus, whereas these centers lie on the boundary. -/
theorem eq_of_binomialCenter_eq {τ : Φ.Ray} {m' : N →+ ℤ} (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : ℂˣ)
    (hm' : m' τ.primitiveGenerator = 0) (hprim' : Function.Surjective m') (d : ℂˣ)
    (h : ρ.binomialCenter hdim hm hprim c = τ.binomialCenter hdim hm' hprim' d) : ρ = τ := by
  let pt : Spec (.of ℂ) := IsLocalRing.closedPoint ℂ
  let p := ρ.binomialCenter hdim hm hprim c pt
  let σ := ρ.toCone ⊓ τ.toCone
  have hpρ : p ∈ Set.range (Φ.affineToricChartι ρ.toCone) := by
    dsimp only [p]
    rw [binomialCenter_def, Scheme.Hom.comp_apply]
    exact Set.mem_range_self _
  have hpτ : p ∈ Set.range (Φ.affineToricChartι τ.toCone) := by
    dsimp only [p]
    rw [h, binomialCenter_def, Scheme.Hom.comp_apply]
    exact Set.mem_range_self _
  have hp : p ∈ Set.range (Φ.affineToricChartι σ) := by
    rw [← Φ.range_affineToricChartι_inter_range_affineToricChartι]
    exact ⟨hpρ, hpτ⟩
  have hD : p ∈ ((Φ.boundaryIdeal ⟨ρ.toCone⟩).support : Set Φ.algebraicRealization) := by
    dsimp only [p]
    rw [← (Φ.boundaryIdeal ⟨ρ.toCone⟩).range_subschemeι,
      ← binomialCenterOnBoundary_comp_subschemeι, Scheme.Hom.comp_apply]
    exact Set.mem_range_self _
  have hσ : σ.val ≠ ⊥ := by
    intro hbot
    have heq : σ = ⟨⊥, Φ.bot_mem ρ.toCone.property⟩ := Subtype.ext hbot
    rw [heq, ← Φ.denseTorusι_eq_affineToricChartι ⟨ρ.toCone⟩ _] at hp
    exact (Φ.support_boundaryIdeal ⟨ρ.toCone⟩ ▸ hD) hp
  have hρ : σ.val.IsFaceOf ρ.toCone.val :=
    Φ.isFaceOf_of_le ρ.toCone.property σ.property inf_le_left
  have hτ : σ.val.IsFaceOf τ.toCone.val :=
    Φ.isFaceOf_of_le τ.toCone.property σ.property inf_le_right
  rw [ρ.toCone_eq_hull_primitiveGenerator] at hρ
  rw [τ.toCone_eq_hull_primitiveGenerator] at hτ
  apply Subtype.ext
  apply Subtype.ext
  exact ((hρ.eq_bot_or_eq_of_hull_singleton _).resolve_left hσ |>.trans
    ρ.toCone_eq_hull_primitiveGenerator.symm).symm.trans
    ((hτ.eq_bot_or_eq_of_hull_singleton _).resolve_left hσ |>.trans
      τ.toCone_eq_hull_primitiveGenerator.symm)

end TauCeti.Toric.Fan.Ray
