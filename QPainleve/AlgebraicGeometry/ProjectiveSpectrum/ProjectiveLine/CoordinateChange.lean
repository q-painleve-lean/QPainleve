/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.LinearAction

import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.CoordinateMap

/-!
# Ordered pairs of rational points on the projective line

A projective linear change of coordinates sends an ordered pair of distinct rational
points to the two coordinate points.
This lets one prescribe the two fibers in a boundary of a ruled surface.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial

universe u

namespace TauCeti.AlgebraicGeometry.projectiveLine

variable {k : Type u} [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "P" => projectiveLine k
local notation "V" => (Fin 2 → k)
local notation "p[" i "," a "]" => polynomialPoint k (RingHom.id k) i a
local notation "χ[" i "," a "]" => pointCoordinates k (RingHom.id k) i a

private def coordinateFunctional (i : Fin 2) (a : k) : V →ₗ[k] k where
  toFun v := χ[i,a] (SymmetricAlgebra.ι k V v)
  map_add' _ _ := by simp
  map_smul' r v := by
    rw [RingHom.id_apply, map_smul, smul_eq_mul, Algebra.smul_def, map_mul,
      pointCoordinates_algebraMap, RingHom.id_apply]

private theorem coordinateFunctional_apply (i : Fin 2) (a : k) (v : V) :
    coordinateFunctional i a v = χ[i,a] (SymmetricAlgebra.ι k V v) := (rfl)

@[simp]
private theorem coordinateFunctional_basis_self (i : Fin 2) (a : k) :
    coordinateFunctional i a (Pi.single i 1) = 1 := by
  fin_cases i <;> simp [coordinateFunctional_apply, ι_eq_smul_coord_add_smul_coord k 0]

@[simp]
private theorem coordinateFunctional_basis_rev (i : Fin 2) (a : k) :
    coordinateFunctional i a (Pi.single i.rev 1) = a := by
  fin_cases i
  · simpa [coordinateFunctional_apply, ι_eq_smul_coord_add_smul_coord k 0, Fin.rev]
      using pointCoordinates_coord_rev k (RingHom.id k) 0 a
  · simpa [coordinateFunctional_apply, ι_eq_smul_coord_add_smul_coord k 0, Fin.rev]
      using pointCoordinates_coord_rev k (RingHom.id k) 1 a

private theorem separating_vector {i j : Fin 2} {a c : k} (hne : p[i,a] ≠ p[j,c]) :
    ∃ v : V, coordinateFunctional i a v = 1 ∧ coordinateFunctional j c v = 0 := by
  let w := (Pi.single j.rev 1 : V) - c • Pi.single j 1
  have hw : coordinateFunctional j c w = 0 := by simp [w]
  have h : coordinateFunctional i a w ≠ 0 := by
    intro hz
    by_cases hij : i = j
    · subst j
      have hac : a = c := sub_eq_zero.mp (by simpa [w] using hz)
      exact hne (by rw [hac])
    · have hij' : i.rev = j := by fin_cases i <;> fin_cases j <;> simp_all
      subst j
      have hac : c * a = 1 := (sub_eq_zero.mp (by simpa [w] using hz)).symm
      have ha : a ≠ 0 := by
        intro haz
        simp [haz] at hac
      let a' := Units.mk0 a ha
      have hinv : (↑a'⁻¹ : k) = c := by
        apply (mul_right_cancel₀ ha)
        exact (Units.inv_mul a').trans hac.symm
      exact hne ((polynomialPoint_rev (RingHom.id k) i a').trans (by rw [hinv]))
  refine ⟨(coordinateFunctional i a w)⁻¹ • w, ?_, ?_⟩
  · simp [h]
  · simp [hw]

private theorem polynomialPoint_comp_symmetricAlgebraMapIso {i j : Fin 2} {a : k}
    (e : V ≃ₗ[k] V) (h : (coordinateFunctional i a).comp e.toLinearMap =
      coordinateFunctional j 0) :
    p[i,a] ≫ (Proj.symmetricAlgebraMapIso k e).hom = p[j,0] := by
  rw [Proj.symmetricAlgebraMapIso_hom, polynomialPoint_eq_fromGlobalSections,
    Proj.fromOfGlobalSections_map, polynomialPoint_eq_fromGlobalSections]
  congr 1
  rw [RingHom.comp_assoc]
  apply congrArg ((Scheme.ΓSpecIso (.of k)).inv.hom.comp)
  apply SymmetricAlgebra.ringHom_ext
  · ext r
    simp
  · intro v
    rw [RingHom.comp_apply, GradedRingHom.coe_toRingHom, SymmetricAlgebra.gradedMap_apply,
      SymmetricAlgebra.map_apply_ι]
    simpa only [LinearMap.comp_apply, coordinateFunctional_apply] using LinearMap.congr_fun h v

/-- A projective linear automorphism of the projective line sends two specified
distinct rational points to the two coordinate points, in the given order. -/
theorem exists_linearEquiv_comp_eq_coordinatePoints {p q : S ⟶ P}
    (hp : p ≫ (P ↘ S) = 𝟙 S) (hq : q ≫ (P ↘ S) = 𝟙 S) (hpq : p ≠ q) :
    ∃ e : V ≃ₗ[k] V,
      p ≫ (Proj.symmetricAlgebraMapIso k e).hom = p[0,0] ∧
      q ≫ (Proj.symmetricAlgebraMapIso k e).hom = p[1,0] := by
  obtain ⟨i, a, rfl⟩ := exists_eq_polynomialPoint p hp
  obtain ⟨j, c, rfl⟩ := exists_eq_polynomialPoint q hq
  obtain ⟨v, hv, hv'⟩ := separating_vector hpq
  obtain ⟨w, hw', hw⟩ := separating_vector hpq.symm
  let b := Pi.basisFun k (Fin 2)
  let F : V →ₗ[k] V := LinearMap.pi ![coordinateFunctional i a, coordinateFunctional j c]
  let G : V →ₗ[k] V := b.constr k ![v, w]
  have hFG : F.comp G = LinearMap.id := by
    apply b.ext
    intro l
    rw [LinearMap.comp_apply, Module.Basis.constr_basis, LinearMap.id_apply]
    ext t
    fin_cases l <;> fin_cases t <;> simp [b, F, hv, hv', hw, hw', Pi.basisFun_apply]
  have hleft : Function.LeftInverse F G := fun x ↦ LinearMap.congr_fun hFG x
  have hG := hleft.injective
  let e := LinearEquiv.ofBijective G ⟨hG,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hG⟩
  have he : e.toLinearMap = G := rfl
  refine ⟨e, polynomialPoint_comp_symmetricAlgebraMapIso e ?_,
    polynomialPoint_comp_symmetricAlgebraMapIso e ?_⟩
  · apply b.ext
    have hG (l : Fin 2) : G (b l) = ![v, w] l := b.constr_basis k _ _
    simp only [he, LinearMap.comp_apply, hG]
    rw [Fin.forall_fin_two]
    have h₀ := coordinateFunctional_basis_self (k := k) 0 0
    have h₁ := coordinateFunctional_basis_rev (k := k) 0 0
    simp only [b, Pi.basisFun_apply] at h₀ h₁ ⊢
    exact ⟨hv.trans h₀.symm, hw.trans h₁.symm⟩
  · apply b.ext
    have hG (l : Fin 2) : G (b l) = ![v, w] l := b.constr_basis k _ _
    simp only [he, LinearMap.comp_apply, hG]
    rw [Fin.forall_fin_two]
    have h₀ := coordinateFunctional_basis_rev (k := k) 1 0
    have h₁ := coordinateFunctional_basis_self (k := k) 1 0
    simp only [b, Pi.basisFun_apply] at h₀ h₁ ⊢
    exact ⟨hv'.trans h₀.symm, hw'.trans h₁.symm⟩

end TauCeti.AlgebraicGeometry.projectiveLine
