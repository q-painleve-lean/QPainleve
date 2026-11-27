/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Ray.Orbit
public import TauCeti.AlgebraicGeometry.IdealSheaf.OfIdealTop
public import TauCeti.Geometry.Toric.Algebraic.BaseChange.Fan

import QPainleve.Geometry.Toric.Cone.Regularity

/-!
# The closed orbit and binomial sections of an affine ray chart

The Laurent coordinate on a ray restricts the affine chart to the closed orbit cut out by
the ray ideal over the coefficient ring. Evaluating that coordinate at `-c⁻¹` gives
the section defined by the binomial with unit parameter `c`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory LaurentPolynomial AddMonoidAlgebra

namespace TauCeti.Toric.Fan.Ray

universe u
variable {N k : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  [CommRing k] {i : N →+ V} {Φ : Fan i} (ρ : Φ.Ray) {m : N →+ ℤ}
  (hdim : Module.finrank ℤ N = 2) (hm : m ρ.primitiveGenerator = 0) (hp : Function.Surjective m)

/-- The ray orbit as a closed subscheme of its affine toric chart. -/
def orbitToRayChart : Spec (.of (LaurentPolynomial k)) ⟶
    affineChart k Φ.lattice ρ.toCone.val :=
  Spec.map (CommRingCat.ofHom (ρ.orbitCoordinateMap k hdim hm hp).toRingHom)

/-- Restriction to the orbit induces the affine ray orbit morphism. -/
theorem orbitToRayChart_def :
    orbitToRayChart (k := k) ρ hdim hm hp =
      Spec.map (CommRingCat.ofHom (ρ.orbitCoordinateMap k hdim hm hp).toRingHom) :=
  (rfl)

/-- The coordinate restriction is surjective, so the ray orbit is a closed subscheme. -/
instance isClosedImmersion_orbitToRayChart :
    IsClosedImmersion (orbitToRayChart (k := k) ρ hdim hm hp) :=
  IsClosedImmersion.spec_of_surjective _ (ρ.orbitCoordinateMap_surjective k hdim hm hp)

/-- The affine ray orbit is defined by the ray ideal. -/
theorem ker_orbitToRayChart :
    (orbitToRayChart (k := k) ρ hdim hm hp).ker =
      Scheme.IdealSheafData.ofIdealTop
        ((rayChartIdeal Φ.lattice (Φ.isToricCone ρ.toCone.property)
          (ρ.toToricRay Φ ρ.toCone le_rfl) k).map
            (Scheme.ΓSpecIso (.of (affineChartRing k Φ.lattice ρ.toCone.val))).inv.hom) := by
  rw [orbitToRayChart_def, Scheme.Hom.ker_Spec_map, CommRingCat.hom_ofHom,
    AlgHom.toRingHom_eq_coe, ← AlgHom.ker_coe, ρ.ker_orbitCoordinateMap]

local notation "S" => dualSemigroup Φ.lattice ρ.toCone.val
local notation "R" => affineChartRing k Φ.lattice ρ.toCone.val
local notation "v" => ρ.primitiveGenerator

private theorem isRegularCone_toCone : IsRegularCone i ρ.toCone.val := by
  rw [ρ.toCone_eq_hull_primitiveGenerator]
  exact isRegularCone_hull_singleton Φ.lattice ρ.primitiveGenerator_isPrimitive

private theorem exists_rayChartEquation :
    ∃ q : S, (q : N →+ ℤ) v = 1 ∧
      rayChartIdeal Φ.lattice (Φ.isToricCone ρ.toCone.property)
          (Ray.toToricRay Φ ρ ρ.toCone le_rfl) k = Ideal.span {single q 1} := by
  let r := Ray.toToricRay Φ ρ ρ.toCone le_rfl
  let hσ := Φ.isToricCone ρ.toCone.property
  obtain ⟨l, b, hb⟩ := (isRegularCone_toCone ρ).exists_basis_sum
  let q := dualSemigroupCoord Φ.lattice hσ hb (Sum.inl r)
  refine ⟨q, ?_, rayChartIdeal_eq_span_rayCoordinate Φ.lattice hσ r k hb⟩
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

private theorem preimage_compl_range_zeroChart :
    Φ.affineChartι k ρ.toCone ⁻¹' (Set.range (Φ.affineChartι k ⟨⊥, Φ.bot_mem ρ.toCone.property⟩))ᶜ =
      PrimeSpectrum.zeroLocus (rayChartIdeal Φ.lattice (Φ.isToricCone ρ.toCone.property)
        (Ray.toToricRay Φ ρ ρ.toCone le_rfl) k : Set R) := by
  let j := Φ.affineChartι k ρ.toCone
  obtain ⟨q, hq, heq⟩ := exists_rayChartEquation (k := k) ρ
  let P (τ : PointedCone ℝ V) := ∀ h : τ.IsFaceOf ρ.toCone.val,
    Set.range (faceAffineChartMap k Φ.lattice h) =
      (PrimeSpectrum.basicOpen (single q (1 : k)) : Set (PrimeSpectrum R))
  have hP : P (ρ.toCone.val ⊓
      PointedCone.ofSubmodule (LinearMap.ker (Φ.lattice.realCharacter q))) :=
    fun _ ↦ range_faceAffineChartMap k Φ.lattice (Φ.isToricCone ρ.toCone.property).fg q
  rw [inf_ker_eq_bot_of_rayChartEquation ρ q hq] at hP
  have hrange := hP (Φ.isToricCone ρ.toCone.property).salient.bot_isFaceOf
  rw [← Φ.faceAffineChartMap_comp_affineChartι k
      (τ := ⟨⊥, Φ.bot_mem ρ.toCone.property⟩) (σ := ρ.toCone)
      (Φ.isToricCone ρ.toCone.property).salient.bot_isFaceOf,
    Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.preimage_compl, j.isOpenEmbedding.injective.preimage_image, hrange, heq,
    PrimeSpectrum.zeroLocus_span]
  rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl]
  exact compl_compl _

/-- The closed ray orbit is the complement of the zero-cone chart on the ray chart. -/
theorem range_orbitToRayChart :
    Set.range (ρ.orbitToRayChart (k := k) hdim hm hp) =
      Φ.affineChartι k ρ.toCone ⁻¹'
        (Set.range (Φ.affineChartι k ⟨⊥, Φ.bot_mem ρ.toCone.property⟩))ᶜ := by
  rw [orbitToRayChart, preimage_compl_range_zeroChart]
  exact (range_comap_of_surjective _ _ (ρ.orbitCoordinateMap_surjective k
    hdim hm hp)).trans (congrArg (fun I : Ideal R ↦ PrimeSpectrum.zeroLocus (I : Set R))
      (ρ.ker_orbitCoordinateMap k hdim hm hp))

/-- The binomial section of the affine ray chart, induced by evaluating its Laurent coordinate. -/
def binomialCenterToRayChart (c : kˣ) : Spec (.of k) ⟶ affineChart k Φ.lattice ρ.toCone.val :=
  Spec.map (CommRingCat.ofHom (ρ.binomialCenterEval k hdim hm hp c).toRingHom)

/-- The affine binomial section is induced by the binomial evaluation on the chart ring. -/
theorem binomialCenterToRayChart_def (c : kˣ) :
    ρ.binomialCenterToRayChart hdim hm hp c =
      Spec.map (CommRingCat.ofHom (ρ.binomialCenterEval k hdim hm hp c).toRingHom) :=
  (rfl)

/-- In the affine ray chart, the binomial section factors through the ray orbit. -/
theorem binomialCenterToRayChart_eq_comp (c : kˣ) :
    ρ.binomialCenterToRayChart hdim hm hp c =
      Spec.map (CommRingCat.ofHom (laurentEval ((-1 : kˣ) * c⁻¹)).toRingHom) ≫
        ρ.orbitToRayChart (k := k) hdim hm hp := by
  rw [binomialCenterToRayChart, orbitToRayChart_def, ← Spec.map_comp, binomialCenterEval_def]
  rfl

/-- Reversing the primitive orbit character inverts the binomial parameter. -/
theorem binomialCenterToRayChart_neg_inv (c : kˣ) :
    ρ.binomialCenterToRayChart hdim (m := -m) (by simp [hm])
        (neg_involutive.surjective.comp hp) c⁻¹ =
      ρ.binomialCenterToRayChart hdim hm hp c := by
  have h := ρ.binomialCenterEval_neg_inv k hdim hm hp c
  simp only [binomialCenterToRayChart, h]

/-- A binomial section in a given Laurent coordinate determines its parameter. -/
theorem binomialCenterToRayChart_injective :
    Function.Injective (ρ.binomialCenterToRayChart (k := k) hdim hm hp) := by
  intro c d h
  simp only [binomialCenterToRayChart, Spec.map_injective.eq_iff] at h
  have he := congrArg (fun g : CommRingCat.of (affineChartRing k Φ.lattice ρ.toCone.val) ⟶
    CommRingCat.of k ↦ g (AddMonoidAlgebra.single (ρ.chartCharacter hm) 1)) h
  change ρ.binomialCenterEval k hdim hm hp c (AddMonoidAlgebra.single (ρ.chartCharacter hm) 1) =
    ρ.binomialCenterEval k hdim hm hp d (AddMonoidAlgebra.single (ρ.chartCharacter hm) 1) at he
  simp only [ρ.binomialCenterEval_character, neg_inj] at he
  exact inv_injective (Units.ext he)

end TauCeti.Toric.Fan.Ray
