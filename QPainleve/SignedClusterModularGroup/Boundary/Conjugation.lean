/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.LinearAlgebra.BilinearForm.Conjugation
public import QPainleve.SignedClusterModularGroup.Boundary.Isometry

/-!
# Conjugating boundary rotations

A Picard isometry which identifies two cyclic boundary families by a signed
shift conjugates their rotation groups. Reversing the indexing reverses the
shift of each rotation, including when the two boundary families have length
one or two.
-/

public section

namespace QPainleve

open LinearMap (BilinForm)

variable {L₀ L₁ : Type*} [AddCommGroup L₀] [AddCommGroup L₁] {n : ℕ}
  {B₀ : BilinForm ℤ L₀} {B₁ : BilinForm ℤ L₁} {d₀ : ZMod n → L₀} {d₁ : ZMod n → L₁}

private theorem map_boundaryRotationGroup_congr (I : B₁.IsometryEquiv B₀)
    {ε : ℤˣ} {a : ZMod n} (hI : ∀ j, I (d₁ j) = d₀ (ε • j + a)) :
    (boundaryRotationGroup B₀ d₀).map I.symm.isometryGroupCongr.toMonoidHom =
      boundaryRotationGroup B₁ d₁ := by
  ext g'
  obtain ⟨g, rfl⟩ := I.symm.isometryGroupCongr.surjective g'
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply,
    mem_boundaryRotationGroup_iff, mem_boundaryRotationGroup_iff]
  have hInv : I.symm.symm = I := rfl
  simp only [BilinForm.IsometryEquiv.isometryGroupCongr_apply_apply,
    hInv, hI]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨ε⁻¹ • k, fun j ↦ I.injective (calc
      I (I.symm (g.val (d₀ (ε • j + a)))) = g.val (d₀ (ε • j + a)) :=
        I.apply_symm_apply _
      _ = d₀ (ε • j + a + k) := hk _
      _ = I (d₁ (j + ε⁻¹ • k)) := by
        rw [hI]
        simp [smul_add, ← mul_smul, add_right_comm])⟩
  · rintro ⟨k, hk⟩
    refine ⟨ε • k, fun j ↦ ?_⟩
    let t := ε⁻¹ • (j - a)
    have ht : ε • t + a = j := by simp [t, ← mul_smul]
    have ht' : ε • (t + k) + a = j + ε • k := by
      rw [smul_add, add_right_comm, ht]
    simpa only [BilinForm.IsometryEquiv.apply_symm_apply, hI, ht, ht']
      using congrArg I (hk t)

/-- Conjugation by the inverse of a Picard pullback identifies the rotation
groups in the source and target markings. The pullback can match the boundary
indices with either orientation. -/
def boundaryRotationGroupCongr (I : B₁.IsometryEquiv B₀)
    {ε : ℤˣ} {a : ZMod n} (hI : ∀ j, I (d₁ j) = d₀ (ε • j + a)) :
    boundaryRotationGroup B₀ d₀ ≃* boundaryRotationGroup B₁ d₁ :=
  TauCeti.Subgroup.congrOfMapEq I.symm.isometryGroupCongr (map_boundaryRotationGroup_congr I hI)

@[simp]
theorem boundaryRotationGroupCongr_apply_apply (I : B₁.IsometryEquiv B₀)
    {ε : ℤˣ} {a : ZMod n} (hI : ∀ j, I (d₁ j) = d₀ (ε • j + a))
    (g : boundaryRotationGroup B₀ d₀) (x : L₁) :
    (boundaryRotationGroupCongr I hI g).val.val x = I.symm (g.val.val (I x)) := by
  have h := TauCeti.Subgroup.coe_congrOfMapEq_apply I.symm.isometryGroupCongr
    (map_boundaryRotationGroup_congr I hI) g
  exact (congrArg (fun u : B₁.isometryGroup ↦ u.val x) h).trans
    (BilinForm.IsometryEquiv.isometryGroupCongr_apply_apply I.symm g.val x)

end QPainleve
