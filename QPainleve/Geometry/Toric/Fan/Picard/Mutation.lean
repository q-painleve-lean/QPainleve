/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Mutation
public import QPainleve.Geometry.Toric.Fan.Picard.BoundaryQuotient

import Mathlib.LinearAlgebra.Reflection

/-!
# The Picard change of marking for toric mutation

The elementary transformation of a ruling, as in Gross, Hacking and Keel,
*Birational geometry of cluster algebras*, §1 and Lemma 3.2, replaces the exceptional
class at the selected center by the fiber class minus that exceptional class. The two
opposite section classes also change. The resulting map on divisor and exceptional
coefficients identifies the two submodules of principal relations, and hence gives an
integral linear equivalence on the full marked Picard groups.
-/

public noncomputable section

open LinearMap PointedCone
open TauCeti.AlgebraicGeometry (LineBundleClass)

namespace TauCeti.Toric.Fan

variable {N : Type} {V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

local notation "Pic" Ψ:arg => Additive (LineBundleClass (Fan.algebraicRealization Ψ))
local notation "mark" Ψ:arg => (Pic Ψ × (ι → ℤ))
local notation "coeffs" Ψ:arg => ((Fan.Ray Ψ → ℤ) × (ι → ℤ))

variable (b : Module.Basis (Fin 2) ℤ N)

/-- The ray coefficients of the positive part of the ruling character divisor. -/
private def fiberCoeffs (ρ₀ ρ : Φ.Ray) : ℤ :=
  max (b.det ![ρ.primitiveGenerator, ρ₀.primitiveGenerator]) 0

/-- The fiber class used in the Picard change of marking, expressed as the class of the
positive part of the character divisor with ray orders `det(u, v)` for the pivot ray
generator `v`. -/
def mutationFiberClass (ρ₀ : Φ.Ray) (hΦ : Φ.IsRegular) : Pic Φ :=
  letI : Nonempty Φ.cones := ⟨ρ₀.toCone⟩
  Φ.rayDivisorToPicard hΦ (fiberCoeffs b ρ₀)

/-- Compute the fiber class in the toric divisor presentation. -/
theorem mutationFiberClass_eq (ρ₀ : Φ.Ray) (hΦ : Φ.IsRegular) :
    letI : Nonempty Φ.cones := ⟨ρ₀.toCone⟩
    mutationFiberClass b ρ₀ hΦ =
      Φ.rayDivisorToPicard hΦ
        (fun ρ ↦ max (b.det ![ρ.primitiveGenerator, ρ₀.primitiveGenerator]) 0) :=
  (rfl)

variable (s : ι → Φ.Ray) (k : ι)

local notation "v" => Ray.primitiveGenerator (s k)

variable (hOpposite : hull ℝ {i (-(s k).primitiveGenerator)} ∈ Φ.cones)

local notation "q" => Ray.ofPrimitiveGenerator
  (IsPrimitive.neg (IsPrimitiveGenerator.isPrimitive (Ray.isPrimitiveGenerator (s k)))) hOpposite
local notation "hv" => IsPrimitiveGenerator.ne_zero (Ray.isPrimitiveGenerator (s k))
local notation "hpos" => Ray.hull_primitiveGenerator_mem (s k)
local notation "Φ'" => Fan.mutationFan Φ b hv hpos hOpposite
local notation "r" => Fan.mutationFanRayEquiv Φ b hv hpos hOpposite
local notation "Fp" => fiberCoeffs b (s k)

private theorem fiberCoeffs_pivot : Fp (s k) = 0 := by
  simp [fiberCoeffs, ← Module.Basis.detDualEquiv_apply, Module.Basis.detDualEquiv_self]

private theorem fiberCoeffs_opposite : Fp q = 0 := by
  simp [fiberCoeffs, ← Module.Basis.detDualEquiv_apply, Module.Basis.detDualEquiv_self]

variable [DecidableEq ι]

local notation "E" => (Pi.single k (1 : ℤ))

/-- Lift the generator formulas to the free divisor and exceptional coefficients. The
change of coordinates adds the opposite ray coefficient to the selected exceptional
coefficient, reflects, and then subtracts the pivot ray coefficient. -/
private def mutationCoefficients : coeffs Φ' ≃ₗ[ℤ] coeffs Φ :=
  let reindex := LinearEquiv.funCongrLeft ℤ ℤ r
  let axis := LinearEquiv.refl ℤ (ι → ℤ)
  let insert := LinearMap.single ℤ (fun _ : ι ↦ ℤ) k
  let f := (LinearMap.proj k : (ι → ℤ) →ₗ[ℤ] ℤ).comp (LinearMap.snd ℤ (Φ.Ray → ℤ) (ι → ℤ))
  let reflection := Module.reflection (x := (-Fp, 2 • E)) (f := f) (by simp [f])
  (reindex.skewProd axis (insert.comp ((LinearMap.proj q).comp reindex.toLinearMap))).trans
    (reflection.trans ((LinearEquiv.refl ℤ (Φ.Ray → ℤ)).skewProd axis
      (-(insert.comp (LinearMap.proj (s k))))))

private theorem mutationCoefficients_apply (a : (Φ').Ray → ℤ) (e : ι → ℤ) :
    mutationCoefficients b s k hOpposite (a, e) =
      (a ∘ r + (e k + a (r q)) • Fp, e - (2 * e k + a (r (s k)) + a (r q)) • E) := by
  simp only [mutationCoefficients, LinearEquiv.trans_apply, LinearEquiv.skewProd_apply,
    LinearEquiv.refl_apply, LinearMap.comp_apply, LinearMap.proj_apply, LinearEquiv.coe_coe,
    LinearMap.single_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
    Module.reflection_apply, LinearMap.snd_apply, LinearMap.neg_apply, Prod.smul_mk]
  refine Prod.ext ?_ ?_
  · funext ρ
    simp [Pi.single_eq_same]
  · funext j
    by_cases hj : j = k
    · simp [hj, fiberCoeffs_pivot]
      ring
    · simp [hj]

/-- The quotient of the free ray and exceptional coordinates giving the marked Picard group. -/
private def markedPicardProjection (Ψ : Fan i) [Nonempty Ψ.cones] (hΨ : Ψ.IsRegular) :
    coeffs Ψ →ₗ[ℤ] mark Ψ :=
  (Ψ.rayDivisorToPicard hΨ).toIntLinearMap.prodMap (LinearMap.id : (ι → ℤ) →ₗ[ℤ] (ι → ℤ))

omit [DecidableEq ι] in
private theorem markedPicardProjection_surjective (Ψ : Fan i) [Nonempty Ψ.cones]
    (hΨ : Ψ.IsRegular) :
    Function.Surjective (markedPicardProjection (ι := ι) Ψ hΨ) :=
  (Ψ.rayDivisorToPicard_surjective hΨ).prodMap Function.surjective_id

omit [DecidableEq ι] in
private theorem mem_ker_markedPicardProjection (Ψ : Fan i) [Nonempty Ψ.cones]
    (hΨ : Ψ.IsRegular) (z : coeffs Ψ) :
    z ∈ ker (markedPicardProjection Ψ hΨ) ↔
      ∃ m : N →+ ℤ, z = (Ψ.characterToRayDivisor m, 0) := by
  rcases z with ⟨a, e⟩
  simp only [markedPicardProjection, LinearMap.ker_prodMap, Submodule.mem_prod,
    LinearMap.mem_ker, AddMonoidHom.coe_toIntLinearMap, LinearMap.id_apply, Prod.mk.injEq,
    Ψ.exact_characterToRayDivisor_rayDivisorToPicard hΨ a, Set.mem_range]
  exact ⟨fun ⟨⟨m, hm⟩, he⟩ ↦ ⟨m, hm.symm, he⟩,
    fun ⟨m, hm, he⟩ ↦ ⟨⟨m, hm.symm⟩, he⟩⟩

private theorem mutationCoefficients_character (m : N →+ ℤ) :
    mutationCoefficients b s k hOpposite ((Φ').characterToRayDivisor m, 0) =
      (Φ.characterToRayDivisor m, 0) := by
  have hq : Ray.primitiveGenerator q = -v := Ray.primitiveGenerator_ofPrimitiveGenerator _ _
  have hr (ρ : Φ.Ray) :
      (Φ').characterToRayDivisor m (r ρ) =
        Φ.characterToRayDivisor m ρ + Fp ρ * m v := by
    simp [fiberCoeffs]
  rw [mutationCoefficients_apply]
  have hpos' : (Φ').characterToRayDivisor m (r (s k)) = m v := by
    simp [hr, fiberCoeffs_pivot]
  have hneg' : (Φ').characterToRayDivisor m (r q) = -m v := by
    simp [hr, hq, fiberCoeffs_opposite]
  refine Prod.ext ?_ ?_
  · funext ρ
    simp only [Pi.add_apply, Function.comp_apply, hr ρ, Pi.zero_apply,
      zero_add, hneg', Pi.smul_apply]
    simp only [zsmul_eq_mul, Int.cast_id]
    ring
  · simp [hpos', hneg']

variable (hΦ : Φ.IsRegular)

local notation "hΦ'" => Iff.mpr (Φ.isRegular_mutationFan_iff b hv hpos hOpposite) hΦ

private theorem map_ker_mutationCoefficients :
    letI : Nonempty Φ.cones := ⟨(s k).toCone⟩
    letI : Nonempty (Φ').cones := ⟨(r (s k)).toCone⟩
    (ker (markedPicardProjection (ι := ι) Φ' hΦ')).map
      (mutationCoefficients b s k hOpposite).toLinearMap =
        ker (markedPicardProjection Φ hΦ) := by
  let : Nonempty Φ.cones := ⟨(s k).toCone⟩
  let : Nonempty (Φ').cones := ⟨(r (s k)).toCone⟩
  ext z
  rw [Submodule.mem_map, mem_ker_markedPicardProjection]
  constructor
  · rintro ⟨z', hz', rfl⟩
    obtain ⟨m, rfl⟩ := (mem_ker_markedPicardProjection _ _ _).mp hz'
    exact ⟨m, mutationCoefficients_character b s k hOpposite m⟩
  · rintro ⟨m, rfl⟩
    exact ⟨_, (mem_ker_markedPicardProjection _ _ _).mpr ⟨m, rfl⟩,
      mutationCoefficients_character b s k hOpposite m⟩

/-- The integral change of marking from the mutated toric Picard group and its exceptional
coordinates to the original ones. The formula allows multiple center labels on the same ray. -/
def mutationPicardEquiv : mark Φ' ≃ₗ[ℤ] mark Φ :=
  letI : Nonempty Φ.cones := ⟨(s k).toCone⟩
  letI : Nonempty (Φ').cones := ⟨(r (s k)).toCone⟩
  ((markedPicardProjection Φ' hΦ').quotKerEquivOfSurjective
    (markedPicardProjection_surjective Φ' hΦ')).symm.trans
      ((Submodule.Quotient.equiv _ _ (mutationCoefficients b s k hOpposite)
        (map_ker_mutationCoefficients b s k hOpposite hΦ)).trans
          ((markedPicardProjection Φ hΦ).quotKerEquivOfSurjective
            (markedPicardProjection_surjective Φ hΦ)))

/-- Evaluate the Picard change of marking on any ray divisor and family of exceptional
coefficients. The correction is supported on the fiber class and the selected exceptional
class. -/
theorem mutationPicardEquiv_apply_rayDivisor (a : (Φ').Ray → ℤ) (e : ι → ℤ) :
    letI : Nonempty Φ.cones := ⟨(s k).toCone⟩
    letI : Nonempty (Φ').cones := ⟨(r (s k)).toCone⟩
    mutationPicardEquiv b s k hOpposite hΦ ((Φ').rayDivisorToPicard hΦ' a, e) =
      (Φ.rayDivisorToPicard hΦ (a ∘ r) + (e k + a (r q)) • mutationFiberClass b (s k) hΦ,
        e - (2 * e k + a (r (s k)) + a (r q)) • E) := by
  let : Nonempty Φ.cones := ⟨(s k).toCone⟩
  let : Nonempty (Φ').cones := ⟨(r (s k)).toCone⟩
  -- Write the input as the image of the quotient representative `(a, e)`.
  change mutationPicardEquiv b s k hOpposite hΦ (markedPicardProjection Φ' hΦ' (a, e)) = _
  simp only [mutationPicardEquiv, LinearEquiv.trans_apply,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.Quotient.equiv_apply,
    Submodule.mapQ_apply, LinearMap.quotKerEquivOfSurjective_apply_mk, LinearEquiv.coe_coe,
    mutationCoefficients_apply]
  simp only [markedPicardProjection, LinearMap.prodMap_apply, AddMonoidHom.coe_toIntLinearMap,
    LinearMap.id_apply, mutationFiberClass, map_add, map_zsmul]

/-- The selected exceptional class maps to the fiber class minus the original exceptional class. -/
@[simp]
theorem mutationPicardEquiv_exceptional_pivot :
    mutationPicardEquiv b s k hOpposite hΦ (0, E) =
      (mutationFiberClass b (s k) hΦ, -E) := by
  let : Nonempty Φ.cones := ⟨(s k).toCone⟩
  let : Nonempty (Φ').cones := ⟨(r (s k)).toCone⟩
  simpa [sub_eq_add_neg, two_smul] using
    mutationPicardEquiv_apply_rayDivisor b s k hOpposite hΦ 0 E

/-- The exceptional class at every other label is unchanged in the marked coordinates. -/
@[simp]
theorem mutationPicardEquiv_exceptional_of_ne {j : ι} (hj : j ≠ k) :
    mutationPicardEquiv b s k hOpposite hΦ (0, Pi.single j 1) = (0, Pi.single j 1) := by
  let : Nonempty Φ.cones := ⟨(s k).toCone⟩
  let : Nonempty (Φ').cones := ⟨(r (s k)).toCone⟩
  simpa [Pi.single_apply, Ne.symm hj] using
    mutationPicardEquiv_apply_rayDivisor b s k hOpposite hΦ 0 (Pi.single j 1)

/-- The toric boundary generators change only at the two rays on the mutation line.
At the pivot one subtracts the selected exceptional class, and at the opposite ray
one adds the fiber class minus the selected exceptional class. -/
theorem mutationPicardEquiv_toric_single [DecidableEq Φ.Ray] (ρ : Φ.Ray) :
    letI : Nonempty Φ.cones := ⟨(s k).toCone⟩
    letI : Nonempty (Φ').cones := ⟨(r (s k)).toCone⟩
    letI : DecidableEq (Φ').Ray := Equiv.decidableEq (Equiv.symm r)
    mutationPicardEquiv b s k hOpposite hΦ ((Φ').rayDivisorToPicard hΦ' (Pi.single (r ρ) 1), 0) =
      (Φ.rayDivisorToPicard hΦ (Pi.single ρ 1) +
        (if q = ρ then mutationFiberClass b (s k) hΦ else 0),
        -((if s k = ρ then E else 0) + (if q = ρ then E else 0))) := by
  let : Nonempty Φ.cones := ⟨(s k).toCone⟩
  let : Nonempty (Φ').cones := ⟨(r (s k)).toCone⟩
  let : DecidableEq (Φ').Ray := Equiv.decidableEq (Equiv.symm r)
  have hs : Pi.single (r ρ) (1 : ℤ) ∘ r = Pi.single ρ 1 := by
    simpa only [Equiv.symm_apply_apply] using Pi.single_comp_equiv r (r ρ) (1 : ℤ)
  have ha (τ : Φ.Ray) :
      (Pi.single (r ρ) 1 : (Φ').Ray → ℤ) (r τ) = (Pi.single ρ 1 : Φ.Ray → ℤ) τ := by
    simpa only [Function.comp_apply] using congrFun hs τ
  rw [mutationPicardEquiv_apply_rayDivisor, hs, ha, ha]
  simp only [Pi.single_apply]
  split_ifs <;> simp [two_smul]

/-- The strict-transform boundary classes are carried to the corresponding boundary classes
under the ray bijection, including the rays gaining or losing the selected center. -/
theorem mutationPicardEquiv_markedBoundaryMap (a : (Φ').Ray → ℤ) :
    letI : Nonempty Φ.cones := ⟨(s k).toCone⟩
    letI : Nonempty (Φ').cones := ⟨(r (s k)).toCone⟩
    mutationPicardEquiv b s k hOpposite hΦ
        (markedBoundaryMap hΦ' (Φ.mutationFanCenterRays b s k hOpposite) a) =
      markedBoundaryMap hΦ s (a ∘ r) := by
  let : Nonempty Φ.cones := ⟨(s k).toCone⟩
  let : Nonempty (Φ').cones := ⟨(r (s k)).toCone⟩
  rw [markedBoundaryMap_apply, mutationPicardEquiv_apply_rayDivisor, markedBoundaryMap_apply]
  simp only [mutationFanCenterRays_self, neg_add_cancel, zero_smul, add_zero]
  refine Prod.ext rfl ?_
  funext j
  by_cases hj : j = k
  · subst j
    simp [mutationFanCenterRays_self, Pi.single_eq_same, zsmul_eq_mul]
    ring
  · simp [mutationFanCenterRays_of_ne Φ b s k hOpposite hj, hj]

/-- The values on the toric prime classes and the total exceptional classes determine the
Picard change of marking. This lets a geometric pullback be compared on these generators. -/
theorem eq_mutationPicardEquiv_of_eq_on_generators [Finite ι] [DecidableEq (Φ').Ray]
    (f : mark Φ' →ₗ[ℤ] mark Φ) :
    letI : Nonempty (Φ').cones := ⟨(r (s k)).toCone⟩
    (∀ ρ : (Φ').Ray, f ((Φ').rayDivisorToPicard hΦ' (Pi.single ρ 1), 0) =
      mutationPicardEquiv b s k hOpposite hΦ ((Φ').rayDivisorToPicard hΦ' (Pi.single ρ 1), 0)) →
    (∀ j : ι, f (0, Pi.single j 1) = mutationPicardEquiv b s k hOpposite hΦ (0, Pi.single j 1)) →
    f = (mutationPicardEquiv b s k hOpposite hΦ).toLinearMap := by
  let : Nonempty (Φ').cones := ⟨(r (s k)).toCone⟩
  let g := (mutationPicardEquiv b s k hOpposite hΦ).toLinearMap
  intro htoric hex
  apply LinearMap.prod_ext
  · let π := ((Φ').rayDivisorToPicard hΦ').toIntLinearMap
    have hπ : Function.Surjective π := (Φ').rayDivisorToPicard_surjective hΦ'
    have hcomp : (f.comp (LinearMap.inl ℤ _ _)).comp π =
        (g.comp (LinearMap.inl ℤ _ _)).comp π := by
      apply (Pi.basisFun ℤ (Φ').Ray).ext
      intro ρ
      simpa [π, g, Pi.basisFun_apply] using htoric ρ
    exact (LinearMap.cancel_right hπ).mp hcomp
  · apply (Pi.basisFun ℤ ι).ext
    intro j
    simpa [Pi.basisFun_apply] using hex j

end TauCeti.Toric.Fan
