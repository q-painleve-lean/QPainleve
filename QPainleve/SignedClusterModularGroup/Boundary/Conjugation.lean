/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.LinearAlgebra.BilinearForm.Conjugation
public import QPainleve.LinearAlgebra.BilinearForm.Isometry
public import QPainleve.SignedClusterModularGroup.Boundary.Isometry

/-!
# Conjugating boundary isometries

A Picard isometry which identifies two cyclic boundary families by a signed
shift conjugates their rotation groups and their signed isometry groups. In
the signed groups the sign is preserved, including when the two boundary
families have length one or two.
-/

public section

namespace QPainleve

open LinearMap (BilinForm)

variable {L₀ L₁ : Type*} [AddCommGroup L₀] [AddCommGroup L₁] {n : ℕ}
  {B₀ : BilinForm ℤ L₀} {B₁ : BilinForm ℤ L₁} {d₀ : ZMod n → L₀} {d₁ : ZMod n → L₁}

local notation "transport[" I "]" =>
  MulEquiv.prodCongr (BilinForm.IsometryEquiv.isometryGroupCongr I) (MulEquiv.refl ℤˣ)

namespace SignedBoundaryIsometryGroup

private theorem isometryGroupCongr_mem (I : B₁.IsometryEquiv B₀)
    {ε : ℤˣ} {a : ZMod n} (hI : ∀ j, I (d₁ j) = d₀ (ε • j + a))
    {g : B₀.isometryGroup × ℤˣ} (hg : g ∈ signedBoundaryIsometryGroup B₀ d₀) :
    (I.symm.isometryGroupCongr g.1, g.2) ∈ signedBoundaryIsometryGroup B₁ d₁ := by
  obtain ⟨k, hk⟩ := (mem_signedBoundaryIsometryGroup_iff B₀ d₀).mp hg
  refine (mem_signedBoundaryIsometryGroup_iff B₁ d₁).mpr
    ⟨ε⁻¹ • (g.2 • a + k - a), fun j ↦ ?_⟩
  rw [BilinForm.IsometryEquiv.isometryGroupCongr_apply_apply, I.symm_symm, hI, hk]
  have hshift : g.2 • (ε • j + a) + k =
      ε • (g.2 • j + ε⁻¹ • (g.2 • a + k - a)) + a := by
    simp only [smul_add, ← mul_smul, mul_inv_cancel, one_smul, mul_comm g.2 ε]
    abel
  rw [hshift, ← hI, I.symm_apply_apply]

private theorem map_eq_of_signed_shift (I : B₁.IsometryEquiv B₀)
    {ε : ℤˣ} {a : ZMod n} (hI : ∀ j, I (d₁ j) = d₀ (ε • j + a)) :
    (signedBoundaryIsometryGroup B₀ d₀).map
      transport[I.symm].toMonoidHom =
      signedBoundaryIsometryGroup B₁ d₁ := by
  have hInv (j : ZMod n) : I.symm (d₀ j) = d₁ (ε⁻¹ • j + -(ε⁻¹ • a)) := by
    have hshift : ε • (ε⁻¹ • j + -(ε⁻¹ • a)) + a = j := by
      simp [smul_add, ← mul_smul]
    exact (congrArg (fun j ↦ I.symm (d₀ j)) hshift.symm).trans (by rw [← hI, I.symm_apply_apply])
  have hright (g : B₁.isometryGroup × ℤˣ) :
      transport[I.symm] (transport[I] g) = g := by
    apply Prod.ext
    · apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      exact (by
        simp :
        (I.symm.isometryGroupCongr (I.isometryGroupCongr g.1)).val x = g.1.val x)
    · rfl
  ext g
  rw [Subgroup.mem_map_equiv]
  have hg : transport[I.symm].symm g = transport[I] g :=
    (MulEquiv.symm_apply_eq _).mpr (hright g).symm
  rw [hg]
  refine ⟨fun h ↦ ?_, fun h ↦ isometryGroupCongr_mem I.symm hInv h⟩
  have h' : transport[I.symm] (transport[I] g) ∈ signedBoundaryIsometryGroup B₁ d₁ :=
    isometryGroupCongr_mem I hI h
  exact hright g ▸ h'

/-- A Picard pullback which matches two boundary families by a signed shift
identifies their signed boundary isometry groups by conjugation. -/
def congr (I : B₁.IsometryEquiv B₀)
    {ε : ℤˣ} {a : ZMod n} (hI : ∀ j, I (d₁ j) = d₀ (ε • j + a)) :
    signedBoundaryIsometryGroup B₀ d₀ ≃* signedBoundaryIsometryGroup B₁ d₁ :=
  TauCeti.Subgroup.congrOfMapEq transport[I.symm]
    (map_eq_of_signed_shift I hI)

@[simp]
theorem coe_congr (I : B₁.IsometryEquiv B₀)
    {ε : ℤˣ} {a : ZMod n} (hI : ∀ j, I (d₁ j) = d₀ (ε • j + a))
    (g : signedBoundaryIsometryGroup B₀ d₀) :
    ((congr I hI g : signedBoundaryIsometryGroup B₁ d₁) : B₁.isometryGroup × ℤˣ) =
      (I.symm.isometryGroupCongr g.val.1, g.val.2) := by
  rw [congr]
  exact TauCeti.Subgroup.coe_congrOfMapEq_apply transport[I.symm] (map_eq_of_signed_shift I hI) g

end SignedBoundaryIsometryGroup

private theorem map_boundaryRotationGroup_congr (I : B₁.IsometryEquiv B₀)
    {ε : ℤˣ} {a : ZMod n} (hI : ∀ j, I (d₁ j) = d₀ (ε • j + a)) :
    (boundaryRotationGroup B₀ d₀).map I.symm.isometryGroupCongr.toMonoidHom =
      boundaryRotationGroup B₁ d₁ := by
  ext g'
  obtain ⟨g, rfl⟩ := I.symm.isometryGroupCongr.surjective g'
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have h (g : B₀.isometryGroup × ℤˣ) :
      transport[I.symm] g ∈ signedBoundaryIsometryGroup B₁ d₁ ↔
        g ∈ signedBoundaryIsometryGroup B₀ d₀ := by
    rw [← SignedBoundaryIsometryGroup.map_eq_of_signed_shift I hI, Subgroup.mem_map_equiv,
      MulEquiv.symm_apply_apply]
  have hm := h (g, 1)
  -- The product equivalence carries a pair of sign one to a pair of sign one.
  change (I.symm.isometryGroupCongr g, 1) ∈ signedBoundaryIsometryGroup B₁ d₁ ↔
    (g, 1) ∈ signedBoundaryIsometryGroup B₀ d₀ at hm
  rw [mem_boundaryRotationGroup_iff, mem_boundaryRotationGroup_iff]
  simpa only [mem_signedBoundaryIsometryGroup_iff, one_smul] using hm.symm

/-- Conjugation by the inverse of a Picard pullback identifies the rotation
groups in the source and target markings. The pullback can match the boundary
indices with either orientation. -/
def boundaryRotationGroupCongr (I : B₁.IsometryEquiv B₀)
    {ε : ℤˣ} {a : ZMod n} (hI : ∀ j, I (d₁ j) = d₀ (ε • j + a)) :
    boundaryRotationGroup B₀ d₀ ≃* boundaryRotationGroup B₁ d₁ :=
  TauCeti.Subgroup.congrOfMapEq I.symm.isometryGroupCongr (map_boundaryRotationGroup_congr I hI)

/-- The underlying isometry of a transported rotation is its conjugate by the change of marking. -/
@[simp]
theorem coe_boundaryRotationGroupCongr (I : B₁.IsometryEquiv B₀)
    {ε : ℤˣ} {a : ZMod n} (hI : ∀ j, I (d₁ j) = d₀ (ε • j + a))
    (g : boundaryRotationGroup B₀ d₀) :
    (boundaryRotationGroupCongr I hI g : B₁.isometryGroup) = I.symm.isometryGroupCongr g.val :=
  TauCeti.Subgroup.coe_congrOfMapEq_apply I.symm.isometryGroupCongr
    (map_boundaryRotationGroup_congr I hI) g

namespace SignedBoundaryIsometryGroup

/-- Conjugation on signed boundary isometries restricts to the same conjugation on rotations. -/
@[simp]
theorem congr_rotationInclusion (I : B₁.IsometryEquiv B₀)
    {ε : ℤˣ} {a : ZMod n} (hI : ∀ j, I (d₁ j) = d₀ (ε • j + a))
    (g : boundaryRotationGroup B₀ d₀) :
    congr I hI (rotationInclusion B₀ d₀ g) =
      rotationInclusion B₁ d₁ (boundaryRotationGroupCongr I hI g) := by
  apply Subtype.ext
  simp only [coe_congr, coe_rotationInclusion, coe_boundaryRotationGroupCongr]

end SignedBoundaryIsometryGroup

end QPainleve
