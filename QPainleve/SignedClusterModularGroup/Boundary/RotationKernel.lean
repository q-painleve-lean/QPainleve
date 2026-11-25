/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import QPainleve.SignedClusterModularGroup.Boundary.Restriction
public import QPainleve.SignedClusterModularGroup.BoundaryCycle

import QPainleve.LinearAlgebra.BilinearForm.QuotientDual
import QPainleve.SignedClusterModularGroup.Faithfulness
import TauCeti.LinearAlgebra.SesquilinearForm.TorsionFree

/-!
# Boundary rotations invisible on the signed orthogonal lattice

An isometry in the kernel of the signed restriction has positive sign. Its rotation
is the degree moment of a torsion class in the quotient by the boundary span.
This embeds the kernel into that torsion group, making the signed restriction
faithful when the boundary span is saturated.

The construction uses `BoundaryCycle.degreeMoment_injective_on_torsion`.
-/

public section

open LinearMap Submodule

namespace QPainleve.SignedBoundaryIsometryGroup

variable {L : Type*} [AddCommGroup L]
  {B : LinearMap.BilinForm ℤ L} [LinearMap.IsPerfPair B] {n : ℕ} [NeZero n] {D : ZMod n → L}
  (hSymm : B.IsSymm)
  (hGram : ∀ i j, B (D i) (D j) =
    (-2 : ℤ) * (if i = j then 1 else 0) +
      (if j = i + 1 then 1 else 0) + (if j = i - 1 then 1 else 0))
  (hprim : TauCeti.IsPrimitive (∑ i, D i))

local notation "M" => span ℤ (Set.range D)
local notation "K" => B.orthogonal M
local notation "δ" => ∑ i, D i
local notation "S" => MonoidHom.ker (signedOrthogonalRestriction B D)
local notation "T" => AddCommGroup.torsion (L ⧸ M)
local notation "iso[" g "]" => Subtype.val (toIsometry B D (Subtype.val (g : S)))

include hSymm hGram hprim in
private theorem kernel_sign_eq_one (g : S) : sign B D g.val = 1 := by
  let : Module.IsTorsionFree ℤ L :=
    (IsPerfPair.nondegenerate ‹LinearMap.IsPerfPair B›).1.isTorsionFree
  let : HasUniqueDiv L := HasUniqueDiv.of_isTorsionFree ℤ L
  have hδ : δ ∈ K := by
    refine mem_orthogonalBilin_span.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact (hSymm.eq _ _).trans (BoundaryCycle.pairing_sum hGram i)
  exact MonoidHom.mem_ker.mp (ker_signedOrthogonalRestriction_le_ker_sign hδ hprim.ne_zero
    g.property)

include hSymm hGram hprim in
private theorem exists_kernel_rotation (g : S) :
    ∃ k : ZMod n, ∀ i, iso[g] (D i) = D (i + k) := by
  obtain ⟨k, hk⟩ := (mem_signedBoundaryIsometryGroup_iff B D).mp g.val.property
  refine ⟨k, ?_⟩
  simpa only [← sign_apply, kernel_sign_eq_one hSymm hGram hprim g, one_smul, toIsometry_apply]
    using hk

include hSymm hGram hprim in
private theorem kernel_fixes_orthogonal (g : S) (x : K) : iso[g] x = x := by
  have hx := congrArg (fun e : (B.restrict K).isometryGroup ↦ (e.val x : L))
    (MonoidHom.mem_ker.mp g.property)
  simpa only [coe_signedOrthogonalRestriction_apply, kernel_sign_eq_one hSymm hGram hprim g,
    one_smul, Subgroup.coe_one, FunLike.coe_one_eq_id, id_eq] using hx

omit [LinearMap.IsPerfPair B] in
include hGram in
private theorem degreeMoment_sub_eq_rotation (g : B.isometryGroup) {f : L} (hf : B f δ = 1)
    (k : ZMod n) (hk : ∀ i, g.val (D i) = D (i + k)) :
    BoundaryCycle.degreeMoment hGram (Submodule.Quotient.mk (g.val f - f)) = k := by
  have hpres := BilinForm.mem_isometryGroup_iff.mp g.property
  have hshift (i : ZMod n) : B (g.val f) (D (i + k)) = B f (D i) := by
    rw [← hk, hpres]
  have hsum : ∑ i, (B f (D i) : ZMod n) = 1 := by
    rw [← Int.cast_sum, ← BilinForm.sum_right, hf, Int.cast_one]
  rw [← mkQ_apply, map_sub, map_sub, mkQ_apply, mkQ_apply]
  simp only [BoundaryCycle.degreeMoment_mk]
  rw [← Equiv.sum_comp (Equiv.addRight k) (fun i ↦ i * (B (g.val f) (D i) : ZMod n))]
  simp only [Equiv.coe_addRight, hshift, add_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, hsum, mul_one, add_sub_cancel_left]

variable [Module.Finite ℤ L]

include hSymm hGram hprim in
private theorem quotient_sub_mem_torsion (g : S) (f : L) :
    (Submodule.Quotient.mk (iso[g] f - f) : L ⧸ M) ∈ T := by
  rw [← Submodule.torsion_int, Submodule.mem_toAddSubgroup,
    ← B.mem_flip_orthogonal_orthogonal_iff_quotient_mem_torsion]
  refine BilinForm.mem_orthogonal_iff.mpr fun x hx ↦ ?_
  have h := (BilinForm.mem_isometryGroup_iff.mp (toIsometry B D g.val).property) f x
  rw [kernel_fixes_orthogonal hSymm hGram hprim g ⟨x, hx⟩] at h
  simpa only [BilinForm.flip_apply, BilinForm.sub_left, sub_eq_zero] using h

include hSymm hGram hprim in
/-- A rotation acting trivially under the signed restriction maps to a torsion class of
the boundary quotient. The image is represented by `g f - f` for a vector `f` of
total boundary degree one. -/
noncomputable def restrictionKernelToBoundaryTorsion (f : L) (hf : B f δ = 1) :
    S →* Multiplicative T where
  toFun g := Multiplicative.ofAdd
    ⟨Submodule.Quotient.mk (iso[g] f - f), quotient_sub_mem_torsion hSymm hGram hprim g f⟩
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    simp
  map_mul' g h := by
    let : Module.IsTorsionFree ℤ L :=
      (IsPerfPair.nondegenerate ‹LinearMap.IsPerfPair B›).1.isTorsionFree
    let : HasUniqueDiv L := HasUniqueDiv.of_isTorsionFree ℤ L
    apply Multiplicative.toAdd.injective
    apply BoundaryCycle.degreeMoment_injective_on_torsion hGram hprim
    obtain ⟨k, hk⟩ := exists_kernel_rotation hSymm hGram hprim g
    obtain ⟨l, hl⟩ := exists_kernel_rotation hSymm hGram hprim h
    have hkl (i : ZMod n) : iso[g * h] (D i) = D (i + (k + l)) := by
      simp only [Subgroup.coe_mul, map_mul, mul_apply_eq_comp, hl, hk]
      congr 1
      abel
    simp only [toAdd_mul, toAdd_ofAdd, AddMonoidHom.comp_apply,
      AddSubgroup.coe_subtype, AddSubgroup.coe_add]
    -- Read the quotient moment through its additive-homomorphism coercion.
    change BoundaryCycle.degreeMoment hGram (Submodule.Quotient.mk (iso[g * h] f - f)) =
      BoundaryCycle.degreeMoment hGram
        (Submodule.Quotient.mk (iso[g] f - f) + Submodule.Quotient.mk (iso[h] f - f))
    simpa only [map_add,
      degreeMoment_sub_eq_rotation hGram (g := toIsometry B D g.val) hf k hk,
      degreeMoment_sub_eq_rotation hGram (g := toIsometry B D h.val) hf l hl]
      using degreeMoment_sub_eq_rotation hGram (g := toIsometry B D (g * h).val) hf (k + l) hkl

/-- The degree moment of the torsion class recovers the pullback rotation. -/
theorem degreeMoment_restrictionKernelToBoundaryTorsion (f : L) (hf : B f δ = 1)
    (g : S) (k : ZMod n) (hk : ∀ i, iso[g] (D i) = D (i + k)) :
    BoundaryCycle.degreeMoment hGram
      ((restrictionKernelToBoundaryTorsion hSymm hGram hprim f hf g).toAdd : L ⧸ M) = k :=
  degreeMoment_sub_eq_rotation hGram (toIsometry B D g.val) hf k hk

/-- The embedding is independent of the degree-one class used to compute it. -/
theorem restrictionKernelToBoundaryTorsion_eq {f f' : L} (hf : B f δ = 1) (hf' : B f' δ = 1) :
    restrictionKernelToBoundaryTorsion hSymm hGram hprim f hf =
      restrictionKernelToBoundaryTorsion hSymm hGram hprim f' hf' := by
  let : Module.IsTorsionFree ℤ L :=
    (IsPerfPair.nondegenerate ‹LinearMap.IsPerfPair B›).1.isTorsionFree
  let : HasUniqueDiv L := HasUniqueDiv.of_isTorsionFree ℤ L
  ext g : 1
  apply Multiplicative.toAdd.injective
  apply BoundaryCycle.degreeMoment_injective_on_torsion hGram hprim
  obtain ⟨k, hk⟩ := exists_kernel_rotation hSymm hGram hprim g
  exact (degreeMoment_restrictionKernelToBoundaryTorsion hSymm hGram hprim f hf g k hk).trans
    (degreeMoment_restrictionKernelToBoundaryTorsion hSymm hGram hprim f' hf' g k hk).symm

/-- The signed restriction kernel embeds into the torsion of the boundary quotient. -/
theorem restrictionKernelToBoundaryTorsion_injective (f : L) (hf : B f δ = 1) :
    Function.Injective (restrictionKernelToBoundaryTorsion hSymm hGram hprim f hf) := by
  let hB := IsPerfPair.nondegenerate ‹LinearMap.IsPerfPair B›
  let : Module.IsTorsionFree ℤ L := hB.1.isTorsionFree
  let : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
  intro g h he
  obtain ⟨k, hk⟩ := exists_kernel_rotation hSymm hGram hprim g
  obtain ⟨l, hl⟩ := exists_kernel_rotation hSymm hGram hprim h
  have hkl : k = l := by
    rw [← degreeMoment_restrictionKernelToBoundaryTorsion hSymm hGram hprim f hf g k hk, he,
      degreeMoment_restrictionKernelToBoundaryTorsion hSymm hGram hprim f hf h l hl]
  have hIso := boundary_isometry_ext (B := B) hSymm hB.1
    (BoundaryCycle.span_sup_orthogonal_rat hGram hSymm hB)
    (g := B.isometryGroupEquivIsometryEquiv (toIsometry B D g.val))
    (h := B.isometryGroupEquivIsometryEquiv (toIsometry B D h.val))
    (fun i ↦ by
      simpa only [BilinForm.coe_isometryGroupEquivIsometryEquiv] using
        (hk i).trans (hkl ▸ hl i).symm)
    (fun x hx ↦ by
      simpa only [BilinForm.coe_isometryGroupEquivIsometryEquiv] using
        (kernel_fixes_orthogonal hSymm hGram hprim g ⟨x, hx⟩).trans
          (kernel_fixes_orthogonal hSymm hGram hprim h ⟨x, hx⟩).symm)
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · simpa only [toIsometry_apply] using B.isometryGroupEquivIsometryEquiv.injective hIso
  · simpa only [sign_apply] using (kernel_sign_eq_one hSymm hGram hprim g).trans
      (kernel_sign_eq_one hSymm hGram hprim h).symm

include hSymm hGram hprim in
/-- The order of the signed restriction kernel divides the boundary saturation index. -/
theorem card_ker_signedOrthogonalRestriction_dvd :
    Nat.card S ∣ Nat.card T := by
  obtain ⟨ℓ, hℓ⟩ := TauCeti.isPrimitive_def.mp hprim
  let f := B.toPerfPair.symm ℓ
  have hf : B f δ = 1 := by simpa [f] using hℓ
  have hd : Nat.card S ∣ Nat.card (Multiplicative T) := Subgroup.card_dvd_of_injective
    (restrictionKernelToBoundaryTorsion hSymm hGram hprim f hf)
    (restrictionKernelToBoundaryTorsion_injective hSymm hGram hprim f hf)
  simpa only [Nat.card_congr Multiplicative.toAdd] using hd

end QPainleve.SignedBoundaryIsometryGroup
