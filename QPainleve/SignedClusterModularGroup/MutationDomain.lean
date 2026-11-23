/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.CharacterTorus.Noncollision
public import QPainleve.Geometry.Toric.Fan.Charge
public import QPainleve.Geometry.Toric.Fan.Mutation
public import QPainleve.SignedClusterModularGroup.CenterMutation

/-!
# Center parameters for an elementary toric mutation

The elementary transformation moves the pivot center to the opposite ray. The two
configurations have distinct centers on each ray exactly when the original centers do
and none on the opposite ray has parameter inverse to the pivot parameter. This is a
dense open of the center torus over a field. The center map and the elementary transformation
follow Gross, Hacking and Keel, *Birational geometry of cluster algebras*, §3.1.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative PointedCone
open QPainleve CharacterTorus Cluster

namespace TauCeti.Toric.Fan

universe u

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {l : N →+ V} {Φ : Fan l} (b : Module.Basis (Fin 2) ℤ N)
  {ι : Type u} [Fintype ι] [DecidableEq ι] (s : ι → Φ.Ray) (p : ι)
  (hOpposite : hull ℝ {l (-(s p).primitiveGenerator)} ∈ Φ.cones)

local notation "A" => (ι → ℤ)
local notation "ω" => b.detDualEquiv.toLinearMap
local notation "E" => chargeExchangeMatrix ω (rayChargeMap s)
local notation "s′" => Φ.mutationFanCenterRays b s p hOpposite

variable (k : Type u) [CommRing k]

/-- The center open where both the original and mutated configurations have distinct
centers on each ray. -/
def mutationCenterOpen : (scheme k A).Opens :=
  distinctCentersOpen k s ⊓ (centerMutation k E p).hom ⁻¹ᵁ distinctCentersOpen k s′

/-- The mutation center open is the intersection of the original distinct-center open with
the pullback of the distinct-center open for the mutated rays. -/
theorem mutationCenterOpen_def :
    mutationCenterOpen b s p hOpposite k =
      distinctCentersOpen k s ⊓ (centerMutation k E p).hom ⁻¹ᵁ distinctCentersOpen k s′ := (rfl)

variable {k} in
private theorem mutatedCenter_ne_iff_of_ne (c : Multiplicative A →* kˣ) {i j : ι}
    (hi : i ≠ p) (hj : j ≠ p) (h : s i = s j) :
    let c' := c.comp (chargeMutationEquiv E p).toAddEquiv.toAddMonoidHom.toMultiplicative
    c' (ofAdd (Pi.single i 1)) ≠ c' (ofAdd (Pi.single j 1)) ↔
      c (ofAdd (Pi.single i 1)) ≠ c (ofAdd (Pi.single j 1)) := by
  have hω : (ω : LinearMap.BilinForm ℤ N).IsAlt := fun v ↦ b.detDualEquiv_self v
  have hE : E i p = E j p := by simp [h]
  dsimp only
  rw [centerMutation_character_apply_of_ne ω (rayChargeMap s) p k hω c hi,
    centerMutation_character_apply_of_ne ω (rayChargeMap s) p k hω c hj, hE]
  exact not_congr (mul_left_inj _)

variable {k} in
private theorem mutatedCenter_ne_pivot_iff (c : Multiplicative A →* kˣ) {j : ι}
    (hj : j ≠ p) (h : (s j).primitiveGenerator = -(s p).primitiveGenerator) :
    let c' := c.comp (chargeMutationEquiv E p).toAddEquiv.toAddMonoidHom.toMultiplicative
    c' (ofAdd (Pi.single j 1)) ≠ c' (ofAdd (Pi.single p 1)) ↔
      c (ofAdd (Pi.single j 1)) * c (ofAdd (Pi.single p 1)) ≠ 1 := by
  have hω : (ω : LinearMap.BilinForm ℤ N).IsAlt := fun v ↦ b.detDualEquiv_self v
  have hE : E j p = 0 := by
    rw [chargeExchangeMatrix_apply, rayChargeMap_single, rayChargeMap_single, h,
      map_neg, LinearMap.neg_apply]
    exact neg_eq_zero.mpr (b.detDualEquiv_self _)
  dsimp only
  rw [centerMutation_character_apply_of_ne ω (rayChargeMap s) p k hω c hj,
    centerMutation_character_apply_self, hE]
  simpa using not_congr (eq_inv_iff_mul_eq_one
    (a := c (ofAdd (Pi.single j 1))) (b := c (ofAdd (Pi.single p 1))))

omit [Fintype ι] in
private theorem mutationFanCenterRays_eq_pivot_iff {j : ι} (hj : j ≠ p) :
    s′ j = s′ p ↔ (s j).primitiveGenerator = -(s p).primitiveGenerator := by
  rw [mutationFanCenterRays_of_ne _ _ _ _ _ hj, mutationFanCenterRays_self]
  constructor
  · intro h
    have hr := (Φ.mutationFanRayEquiv b _ _ hOpposite).injective h
    exact (congrArg Ray.primitiveGenerator hr).trans
      (Ray.primitiveGenerator_ofPrimitiveGenerator ..)
  · intro h
    apply congrArg (Φ.mutationFanRayEquiv b _ _ hOpposite)
    apply Subtype.ext
    apply Subtype.ext
    rw [(s j).toCone_eq_hull_primitiveGenerator, h]
    exact (Ray.ofPrimitiveGenerator_toCone ..).symm

section Field

variable (K : Type u) [Field K]

/-- A rational center belongs to the mutation open exactly when the original centers are
distinct on each ray and no opposite-ray parameter is the inverse of the pivot parameter. -/
@[simp]
theorem point_mem_mutationCenterOpen_iff (c : Multiplicative A →* Kˣ) (x : Spec (.of K)) :
    ((pointsEquiv K A).symm c).val x ∈ mutationCenterOpen b s p hOpposite K ↔
      (∀ i j : ι, i ≠ j → s i = s j →
        c (ofAdd (Pi.single i 1)) ≠ c (ofAdd (Pi.single j 1))) ∧
      (∀ j : ι, (s j).primitiveGenerator = -(s p).primitiveGenerator →
        c (ofAdd (Pi.single j 1)) * c (ofAdd (Pi.single p 1)) ≠ 1) := by
  have hp : (s p).primitiveGenerator ≠ -(s p).primitiveGenerator := by
    intro h
    have he : (1 : ℤ) = -1 := (s p).isPrimitiveGenerator.isPrimitive.zsmul_left_injective
      (by simpa using h)
    omega
  rw [mutationCenterOpen_def, TopologicalSpace.Opens.mem_inf, Scheme.Hom.mem_preimage,
    ← Scheme.Hom.comp_apply, pointsEquiv_symm_comp_centerMutation_hom,
    point_mem_distinctCentersOpen_iff, point_mem_distinctCentersOpen_iff]
  refine and_congr_right fun hs ↦ ⟨?_, ?_⟩
  · intro h j hj
    have hjp : j ≠ p := fun he ↦ hp (he ▸ hj)
    refine (mutatedCenter_ne_pivot_iff b s p c hjp hj).mp (h j p hjp ?_)
    exact (mutationFanCenterRays_eq_pivot_iff b s p hOpposite hjp).mpr hj
  · intro h i j hij hr
    by_cases hi : i = p
    · subst i
      have hj := hij.symm
      have hneg := (mutationFanCenterRays_eq_pivot_iff b s p hOpposite hj).mp hr.symm
      exact ((mutatedCenter_ne_pivot_iff b s p c hj hneg).mpr (h j hneg)).symm
    · by_cases hj : j = p
      · subst j
        have hneg := (mutationFanCenterRays_eq_pivot_iff b s p hOpposite hi).mp hr
        exact (mutatedCenter_ne_pivot_iff b s p c hi hneg).mpr (h i hneg)
      · rw [mutationFanCenterRays_of_ne _ _ _ _ _ hi,
          mutationFanCenterRays_of_ne _ _ _ _ _ hj] at hr
        have he := (Φ.mutationFanRayEquiv b _ _ hOpposite).injective hr
        exact (mutatedCenter_ne_iff_of_ne b s p c hi hj he).mpr (hs i j hij he)

/-- The elementary transformation's center conditions define a nonempty open. -/
theorem nonempty_mutationCenterOpen :
    (mutationCenterOpen b s p hOpposite K : Set (scheme K A)).Nonempty := by
  let : HasUniqueDiv A := hasUniqueDiv_of_free_int
  let : IrreducibleSpace (scheme K A) :=
    inferInstanceAs (IrreducibleSpace (PrimeSpectrum (AddMonoidAlgebra K A)))
  let m := (centerMutation K E p).hom
  let U := m ⁻¹ᵁ distinctCentersOpen K s′
  have hU : (U : Set (scheme K A)).Nonempty :=
    (nonempty_distinctCentersOpen s′).preimage m.homeomorph.surjective
  rw [mutationCenterOpen_def, TopologicalSpace.Opens.coe_inf]
  exact nonempty_preirreducible_inter (distinctCentersOpen K s).isOpen U.isOpen
    (nonempty_distinctCentersOpen s) hU

/-- Over a separably closed field, the noncollision conditions can be met by a center
character with values in that field. -/
theorem exists_point_mem_mutationCenterOpen [IsSepClosed K] :
    ∃ c : Multiplicative A →* Kˣ,
      ((pointsEquiv K A).symm c).val default ∈ mutationCenterOpen b s p hOpposite K :=
  (denseRange_centerPoints K ι).exists_mem_open (mutationCenterOpen b s p hOpposite K).isOpen
    (nonempty_mutationCenterOpen b s p hOpposite K)

end Field

end TauCeti.Toric.Fan
