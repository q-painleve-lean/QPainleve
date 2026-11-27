/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Ray.Ideal
public import QPainleve.Geometry.Toric.Fan.Ray
public import TauCeti.Algebra.Polynomial.Laurent.Basic
import QPainleve.Algebra.Polynomial.Laurent

/-!
# Laurent coordinates on ray orbits

In a rank-two fan, an annihilating primitive character gives a Laurent coordinate on
the ray orbit. Over a commutative ring, evaluation at the root of a binomial with a unit
coefficient defines a section of the orbit over the base.
-/

public noncomputable section

open LaurentPolynomial _root_.AddMonoidAlgebra

namespace TauCeti.Toric.Fan.Ray

variable {N : Type*} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (ρ : Φ.Ray)
  (k : Type*)

local notation "S" => dualSemigroup Φ.lattice ρ.toCone.val
local notation "R" => affineChartRing k Φ.lattice ρ.toCone.val
local notation "v" => ρ.primitiveGenerator
local notation "ray" => Ray.toToricRay Φ ρ ρ.toCone le_rfl
local notation "hσ" => Φ.isToricCone ρ.toCone.property
local notation "F" => rayCharacterFace Φ.lattice hσ ray

variable {m : N →+ ℤ}

/-- A character pairing to zero with a ray's primitive generator is regular on its affine chart. -/
def chartCharacter (hm : m v = 0) : S :=
  ⟨m, (mem_rayDualSemigroup_iff ρ m).2 hm.ge⟩

/-- The regular character has the stated exponent in the ambient character lattice. -/
@[simp]
theorem coe_chartCharacter (hm : m v = 0) : (ρ.chartCharacter hm : N →+ ℤ) = m := (rfl)

private def rayDualFaceHom (hm : m v = 0) : ℤ →+ F where
  toFun n := ⟨ρ.chartCharacter (show (n • m) v = 0 by simp [hm]), by simp [hm]⟩
  map_zero' := by ext x; simp [chartCharacter]
  map_add' a b := by ext x; simp [chartCharacter, add_zsmul]

private theorem bijective_rayDualFaceHom (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) :
    Function.Bijective (rayDualFaceHom ρ hm) := by
  constructor
  · intro a b hab
    obtain ⟨x, hx⟩ := hprim 1
    simpa [rayDualFaceHom, hx] using congrArg (fun f : F ↦
      (f.val : N →+ ℤ) x) hab
  · intro a
    obtain ⟨n, hn⟩ := ρ.exists_zsmul_eq_of_apply_primitiveGenerator_eq_zero hdim hm hprim
      (by simpa only [mem_rayCharacterFace, ← Ray.primitiveGenerator_def] using a.property)
    exact ⟨n, Subtype.ext (Subtype.ext hn)⟩

private def rayDualFaceEquiv (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) : ℤ ≃+ F :=
  AddEquiv.ofBijective (rayDualFaceHom ρ hm) (bijective_rayDualFaceHom ρ hdim hm hprim)

section Orbit

variable [CommSemiring k]

/-- Restriction from the affine ray chart to its boundary torus, in the Laurent coordinate
given by the primitive character `m`. -/
def orbitCoordinateMap (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) : R →ₐ[k] LaurentPolynomial k :=
  (AddMonoidAlgebra.domCongr k k (rayDualFaceEquiv ρ hdim hm hprim).symm).toAlgHom.comp
    ((F).faceRestriction (addSaturated_rayCharacterFace Φ.lattice hσ ray) k)

/-- Every Laurent polynomial on the ray orbit extends to the ray chart. -/
theorem orbitCoordinateMap_surjective (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) :
    Function.Surjective (ρ.orbitCoordinateMap k hdim hm hprim) := by
  unfold orbitCoordinateMap
  exact (AddMonoidAlgebra.domCongr k k (rayDualFaceEquiv ρ hdim hm hprim).symm).surjective.comp
    ((F).faceRestriction_surjective (addSaturated_rayCharacterFace Φ.lattice hσ ray))

/-- Restriction to the orbit kills precisely the ray ideal. -/
@[simp]
theorem ker_orbitCoordinateMap (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) :
    RingHom.ker (ρ.orbitCoordinateMap k hdim hm hprim) =
      rayChartIdeal Φ.lattice (Φ.isToricCone ρ.toCone.property)
        (Ray.toToricRay Φ ρ ρ.toCone le_rfl) k := by
  rw [rayChartIdeal_def, ← AddSubmonoid.ker_faceRestriction
    (hF := addSaturated_rayCharacterFace Φ.lattice hσ ray)]
  ext a
  simp [orbitCoordinateMap, RingHom.mem_ker]

/-- A multiple of the primitive character restricts to the corresponding Laurent monomial. -/
@[simp]
theorem orbitCoordinateMap_zsmul_chartCharacter (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (n : ℤ) :
    ρ.orbitCoordinateMap k hdim hm hprim
      (single (ρ.chartCharacter (m := n • m) (by simp [hm])) 1) = T n := by
  let a := rayDualFaceHom ρ hm n
  have ha : a.val = ρ.chartCharacter (m := n • m) (by simp [hm]) := (rfl)
  simp only [orbitCoordinateMap, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  rw [← ha, AddSubmonoid.faceRestriction_single_mem, AddMonoidAlgebra.domCongr_single]
  congr 1
  exact (rayDualFaceEquiv ρ hdim hm hprim).symm_apply_apply n

/-- The primitive annihilating character becomes the Laurent variable on restriction. -/
@[simp]
theorem orbitCoordinateMap_character (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) :
    ρ.orbitCoordinateMap k hdim hm hprim
      (single (ρ.chartCharacter hm) 1) = T 1 := by
  simpa only [one_zsmul] using ρ.orbitCoordinateMap_zsmul_chartCharacter k hdim hm hprim 1

end Orbit

variable [CommRing k]

/-- Evaluation on the ray chart at the boundary center with Laurent coordinate `-c⁻¹`. -/
def binomialCenterEval (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : kˣ) : R →ₐ[k] k :=
  (laurentEval ((-1 : kˣ) * c⁻¹)).comp (ρ.orbitCoordinateMap k hdim hm hprim)

/-- Binomial evaluation is Laurent evaluation after restricting to the ray orbit. -/
theorem binomialCenterEval_def (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : kˣ) :
    ρ.binomialCenterEval k hdim hm hprim c =
      (laurentEval ((-1 : kˣ) * c⁻¹)).comp (ρ.orbitCoordinateMap k hdim hm hprim) :=
  (rfl)

/-- Monomials of positive degree along the ray vanish at a binomial center. -/
theorem binomialCenterEval_single_eq_zero (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : kˣ) (a : S) (r : k)
    (ha : (a : N →+ ℤ) v ≠ 0) :
    ρ.binomialCenterEval k hdim hm hprim c (single a r) = 0 := by
  have hn : a ∉ F := by simpa only [mem_rayCharacterFace, ← Ray.primitiveGenerator_def] using ha
  simp [binomialCenterEval, orbitCoordinateMap, AddSubmonoid.faceRestriction_single_of_notMem, hn]

/-- A monomial of exponent `n • m` evaluates to the corresponding Laurent power. -/
theorem binomialCenterEval_single_zsmul (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : kˣ) (n : ℤ) (r : k) :
    ρ.binomialCenterEval k hdim hm hprim c
      (single (ρ.chartCharacter (m := n • m) (by simp [hm])) r) =
      r * (((-1 : kˣ) * c⁻¹) ^ n : kˣ) := by
  have hs : r • single (ρ.chartCharacter (m := n • m) (by simp [hm])) (1 : k) =
      single (ρ.chartCharacter (m := n • m) (by simp [hm])) r := by
    rw [smul_single', mul_one]
  rw [← hs, map_smul, binomialCenterEval_def, AlgHom.comp_apply,
    orbitCoordinateMap_zsmul_chartCharacter, laurentEval_T, smul_eq_mul]

/-- The primitive character evaluates at the unique root of the boundary binomial. -/
@[simp]
theorem binomialCenterEval_character (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : kˣ) :
    ρ.binomialCenterEval k hdim hm hprim c
      (single (ρ.chartCharacter hm) 1) = -(↑c⁻¹ : k) := by
  simpa only [one_zsmul, zpow_one, one_mul, Units.val_mul, Units.val_neg,
    Units.val_one, neg_one_mul] using
    ρ.binomialCenterEval_single_zsmul k hdim hm hprim c 1 1

/-- The center ideal on the ray chart is generated by the ray ideal and the binomial. -/
theorem ker_binomialCenterEval (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : kˣ) :
    RingHom.ker (ρ.binomialCenterEval k hdim hm hprim c) =
      rayChartIdeal Φ.lattice (Φ.isToricCone ρ.toCone.property)
        (Ray.toToricRay Φ ρ ρ.toCone le_rfl) k ⊔
      Ideal.span {1 + algebraMap k R (c : k) * single (ρ.chartCharacter hm) 1} := by
  let f := ρ.orbitCoordinateMap k hdim hm hprim
  let J : Ideal R :=
    Ideal.span {1 + algebraMap k R (c : k) * single (ρ.chartCharacter hm) 1}
  have hJ : Ideal.map f J = RingHom.ker (laurentEval ((-1 : kˣ) * c⁻¹)) := by
    dsimp only [J]
    rw [Ideal.map_span, Set.image_singleton, ker_laurentEval_neg_inv]
    have hf : f (single (ρ.chartCharacter hm) 1) = T 1 :=
      ρ.orbitCoordinateMap_character k hdim hm hprim
    rw [map_add, map_one, map_mul, f.commutes, hf, ← C_eq_algebraMap]
  calc
    _ = Ideal.comap f (RingHom.ker (laurentEval ((-1 : kˣ) * c⁻¹))) := by
      ext x
      rfl
    _ = J ⊔ RingHom.ker f := by
      rw [← hJ, Ideal.comap_map_of_surjective _ (ρ.orbitCoordinateMap_surjective k hdim hm hprim),
        RingHom.ker_eq_comap_bot]
    _ = _ := by
      dsimp only [f, J]
      rw [ρ.ker_orbitCoordinateMap, sup_comm]

/-- A character strictly positive on the ray vanishes at every binomial center on that ray. -/
theorem binomialCenterEval_monomial_of_pos
    (hdim : Module.finrank ℤ N = 2) (hmρ : m ρ.primitiveGenerator = 0)
    (hsurj : Function.Surjective m) (c : kˣ)
    (a : dualSemigroup Φ.lattice ρ.toCone.val)
    (ha : 0 < (a : N →+ ℤ) ρ.primitiveGenerator) :
    ρ.binomialCenterEval k hdim hmρ hsurj c (single a 1) = 0 :=
  ρ.binomialCenterEval_single_eq_zero k hdim hmρ hsurj c a 1 ha.ne'

/-- Negating the orbit character inverts the binomial parameter. -/
theorem binomialCenterEval_neg_inv (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hs : Function.Surjective m) (c : kˣ) :
    ρ.binomialCenterEval k hdim (m := -m) (by simp [hm])
        (neg_involutive.surjective.comp hs) c⁻¹ =
      ρ.binomialCenterEval k hdim hm hs c := by
  suffices h : ∀ hs' : Function.Surjective (-m),
      ρ.binomialCenterEval k hdim (m := -m) (by simp [hm]) hs' c⁻¹ =
        ρ.binomialCenterEval k hdim hm hs c from h (neg_involutive.surjective.comp hs)
  intro hs'
  refine AddMonoidAlgebra.algHom_ext (fun a ↦ ?_) (Subsingleton.elim _ _)
  by_cases ha : (a : N →+ ℤ) v = 0
  · obtain ⟨n, hn⟩ := ρ.exists_zsmul_eq_of_apply_primitiveGenerator_eq_zero hdim hm hs ha
    have h₁ : ρ.chartCharacter (m := n • m) (by simp [hm]) = a := Subtype.ext hn
    have h₂ : ρ.chartCharacter (m := (-n) • (-m)) (by simp [hm]) = a :=
      Subtype.ext (by simpa using hn)
    rw [← h₂, binomialCenterEval_single_zsmul, h₂, ← h₁, binomialCenterEval_single_zsmul]
    simp [zpow_neg, ← inv_zpow, mul_comm]
  · rw [binomialCenterEval_single_eq_zero ρ k _ _ _ _ _ _ ha,
      binomialCenterEval_single_eq_zero ρ k _ _ _ _ _ _ ha]

end TauCeti.Toric.Fan.Ray
