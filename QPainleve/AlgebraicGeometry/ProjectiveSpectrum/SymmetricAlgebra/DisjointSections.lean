/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality

import Mathlib.RingTheory.Ideal.Quotient.Operations
import TauCeti.LinearAlgebra.SymmetricAlgebra.Semilinear
import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Maps

/-!
# Disjoint line quotients on an affine projective bundle

Two line quotients with disjoint images in the projective spectrum are jointly
surjective. Over a maximal ideal where joint surjectivity fails, the two
quotients give proportional nonzero linear forms and hence the same point.
-/

public section

open AlgebraicGeometry TauCeti.SymmetricAlgebra

namespace SymmetricAlgebra

universe u

variable {R M L₁ L₂ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup L₁] [Module R L₁] [AddCommGroup L₂] [Module R L₂]

private noncomputable def quotientPointMap (p : Ideal R) (e : L₁ ≃ₗ[R] R) :
    homogeneousSubmodule R L₁ →+*ᵍ homogeneousSubmodule (R ⧸ p) (R ⧸ p) :=
  let f : L₁ →ₛₗ[Ideal.Quotient.mk p] R ⧸ p :=
    (Ideal.Quotient.mk p).toSemilinearMap.comp e.toLinearMap
  ⟨mapₛₗ f, mapₛₗ_mem_homogeneousSubmodule f⟩

private theorem irrelevant_le_map_quotientPointMap (p : Ideal R) (e : L₁ ≃ₗ[R] R) :
    HomogeneousIdeal.irrelevant (homogeneousSubmodule (R ⧸ p) (R ⧸ p)) ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule R L₁)).map (quotientPointMap p e) := by
  refine HomogeneousIdeal.irrelevant_le_map_of_surjective _ ?_
  have h := Ideal.Quotient.mk_surjective (I := p)
  let f : L₁ →ₛₗ[Ideal.Quotient.mk p] R ⧸ p :=
    (Ideal.Quotient.mk p).toSemilinearMap.comp e.toLinearMap
  -- Surjectivity can be checked on the scalars and the symmetric algebra generators.
  intro x
  induction x using SymmetricAlgebra.induction with
  | algebraMap a =>
    obtain ⟨r, rfl⟩ := h a
    exact ⟨algebraMap R _ r, mapₛₗ_algebraMap f r⟩
  | ι a =>
    obtain ⟨r, rfl⟩ := h a
    exact ⟨ι R L₁ (e.symm r), by
      dsimp only [quotientPointMap, GradedRingHom.coe_mk]
      rw [mapₛₗ_ι]
      simp⟩
  | mul _ _ hx hy =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    exact ⟨x * y, map_mul _ _ _⟩
  | add _ _ hx hy =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    exact ⟨x + y, map_add _ _ _⟩

private noncomputable def zeroPoint (K : Type u) [Field K] :
    ProjectiveSpectrum (homogeneousSubmodule K K) :=
  ⟨⊥, by rw [HomogeneousIdeal.toIdeal_bot]; exact Ideal.isPrime_bot, fun h ↦ by
    have hz : ι K K (1 : K) = 0 :=
      (Ideal.mem_bot (R := SymmetricAlgebra K K)).mp <|
        h (HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.one_pos (ι_mem_homogeneousSubmodule K K 1))
    exact one_ne_zero (ι_injective K K (hz.trans (map_zero _).symm))⟩

/-- The projective morphism associated to a surjective linear map is defined
on the entire target projective spectrum of the induced graded ring map. -/
theorem irrelevant_le_map_gradedMap_of_surjective (q : M →ₗ[R] L₁)
    (hq : Function.Surjective q) :
    HomogeneousIdeal.irrelevant (homogeneousSubmodule R L₁) ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule R M)).map (gradedMap R q) :=
  HomogeneousIdeal.irrelevant_le_map_of_surjective _ fun x ↦ by
    simpa only [gradedMap_apply] using map_surjective R q hq x

private theorem exists_same_projectivePoint_of_proportional_quotients
    (p : Ideal R) [p.IsMaximal] (e₁ : L₁ ≃ₗ[R] R) (e₂ : L₂ ≃ₗ[R] R)
    (q₁ : M →ₗ[R] L₁) (q₂ : M →ₗ[R] L₂)
    (hq₁ : Function.Surjective q₁) (hq₂ : Function.Surjective q₂)
    (a : R ⧸ p) (ha : a ≠ 0)
    (h : ∀ m, Ideal.Quotient.mk p (e₂ (q₂ m)) = a * Ideal.Quotient.mk p (e₁ (q₁ m))) :
    ∃ x₁ x₂, ProjectiveSpectrum.comapFun (gradedMap R q₁)
      (irrelevant_le_map_gradedMap_of_surjective q₁ hq₁) x₁ =
      ProjectiveSpectrum.comapFun (gradedMap R q₂)
        (irrelevant_le_map_gradedMap_of_surjective q₂ hq₂) x₂ := by
  let K := R ⧸ p
  let : Field K := Ideal.Quotient.field p
  let scale : K →ₗ[K] K := a • LinearMap.id
  have hscale : Function.Injective (map K scale) :=
    map_injective scale fun x y hxy ↦ mul_left_cancel₀ ha hxy
  refine ⟨ProjectiveSpectrum.comapFun (quotientPointMap p e₁)
      (irrelevant_le_map_quotientPointMap p e₁) (zeroPoint K),
    ProjectiveSpectrum.comapFun (quotientPointMap p e₂)
      (irrelevant_le_map_quotientPointMap p e₂) (zeroPoint K), ?_⟩
  have hcomp :
      (quotientPointMap p e₂).toRingHom.comp (gradedMap R q₂).toRingHom =
        (map K scale).toRingHom.comp
          ((quotientPointMap p e₁).toRingHom.comp (gradedMap R q₁).toRingHom) := by
    -- The ring maps coincide on scalars and degree-one generators.
    ext r
    · simp [quotientPointMap, K]
    · simp [quotientPointMap, K, scale, map_apply_ι, h, smul_eq_mul]
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.toIdeal_injective
  ext x
  simp only [ProjectiveSpectrum.comapFun_asHomogeneousIdeal, HomogeneousIdeal.toIdeal_comap,
    zeroPoint, HomogeneousIdeal.toIdeal_bot, Ideal.mem_comap, Ideal.mem_bot]
  have hx := RingHom.congr_fun hcomp x
  rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply] at hx
  simp only [GradedRingHom.coe_toRingHom] at hx
  rw [hx]
  exact (map_eq_zero_iff (map K scale) hscale).symm

/-- Surjective maps onto two free rank-one modules are jointly surjective if
the lines they define in the projective spectrum have disjoint images. -/
theorem surjective_prod_of_disjoint_projectiveSpectrum
    (e₁ : L₁ ≃ₗ[R] R) (e₂ : L₂ ≃ₗ[R] R)
    (q₁ : M →ₗ[R] L₁) (q₂ : M →ₗ[R] L₂)
    (hq₁ : Function.Surjective q₁) (hq₂ : Function.Surjective q₂)
    (hd : Disjoint (Set.range (ProjectiveSpectrum.comapFun (gradedMap R q₁)
      (irrelevant_le_map_gradedMap_of_surjective q₁ hq₁)))
      (Set.range (ProjectiveSpectrum.comapFun (gradedMap R q₂)
        (irrelevant_le_map_gradedMap_of_surjective q₂ hq₂)))) :
    Function.Surjective (q₁.prod q₂) := by
  let f₁ := e₁.toLinearMap.comp q₁
  let f₂ := e₂.toLinearMap.comp q₂
  let I : Ideal R := LinearMap.range (f₂.comp f₁.ker.subtype)
  obtain ⟨v, hv : f₁ v = 1⟩ := e₁.surjective.comp hq₁ 1
  have hI : I = ⊤ := by
    by_contra hI
    obtain ⟨p, hp, hIp⟩ := I.exists_le_maximal hI
    let := hp
    let a := Ideal.Quotient.mk p (f₂ v)
    have hrel (m : M) : Ideal.Quotient.mk p (f₂ m) = a * Ideal.Quotient.mk p (f₁ m) := by
      have hz : m - f₁ m • v ∈ f₁.ker := by simp [LinearMap.mem_ker, hv]
      have hm := Ideal.Quotient.eq_zero_iff_mem.mpr
        (hIp (show f₂ (m - f₁ m • v) ∈ I from ⟨⟨_, hz⟩, rfl⟩))
      simp only [map_sub, map_smul, smul_eq_mul, map_mul, sub_eq_zero] at hm
      exact hm.trans (mul_comm _ _)
    have ha : a ≠ 0 := by
      obtain ⟨m, hm⟩ := e₂.surjective.comp hq₂ 1
      intro ha
      have he := hrel m
      rw [show f₂ m = 1 from hm, map_one, ha, zero_mul] at he
      exact one_ne_zero he
    obtain ⟨x₁, x₂, hx⟩ :=
      exists_same_projectivePoint_of_proportional_quotients p e₁ e₂ q₁ q₂ hq₁ hq₂ a ha hrel
    exact Set.disjoint_left.mp hd (Set.mem_range_self x₁) ⟨x₂, hx.symm⟩
  rintro ⟨x, y⟩
  obtain ⟨w, hw : f₂ (w : M) = e₂ y - f₂ (e₁ x • v)⟩ :=
    show e₂ y - f₂ (e₁ x • v) ∈ I by rw [hI]; exact Submodule.mem_top
  refine ⟨e₁ x • v + w, Prod.ext (e₁.injective ?_) (e₂.injective ?_)⟩
  · have hz : f₁ (w : M) = 0 := w.property
    have hval : f₁ (e₁ x • v + w) = e₁ x := by simp [hv, hz]
    exact hval
  · have hval : f₂ (e₁ x • v + w) = e₂ y := by rw [map_add, hw, add_sub_cancel]
    exact hval

end SymmetricAlgebra
