/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Boundary.Restriction

import QPainleve.SignedClusterModularGroup.BoundaryCycle
import QPainleve.SignedClusterModularGroup.Faithfulness
import TauCeti.LinearAlgebra.SesquilinearForm.TorsionFree

/-!
# Faithful signed restriction for a one-component boundary

For a single nonzero isotropic boundary class, the signed action on its orthogonal
lattice determines the whole signed isometry. The action on the boundary class itself
recovers the sign, and boundary isometry extensionality then recovers the isometry.
-/

public section

namespace QPainleve.SignedBoundaryIsometryGroup

open QPainleve

variable {L : Type*} [AddCommGroup L] [Module ℤ L] [Module.Free ℤ L] [Module.Finite ℤ L]
  {B : LinearMap.BilinForm ℤ L} {D : ZMod 1 → L}

/-- For a single nonzero isotropic boundary class, the sign-adjusted restriction to its
orthogonal lattice determines a signed boundary isometry. -/
theorem signedOrthogonalRestriction_injective_of_one_component
    (hSymm : B.IsSymm) (hB : B.Nondegenerate) (hD : D 0 ≠ 0) (hself : B (D 0) (D 0) = 0) :
    Function.Injective (signedOrthogonalRestriction B D) := by
  have hGram (i j : ZMod 1) :
      B (D i) (D j) = (-2 : ℤ) * (if i = j then 1 else 0) +
        (if j = i + 1 then 1 else 0) + (if j = i - 1 then 1 else 0) := by
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    have hone : (1 : ZMod 1) = 0 := Subsingleton.elim _ _
    simp only [hone, add_zero, sub_zero, hself]
    norm_num
  have hδ : (∑ i, D i) ∈ B.orthogonal (Submodule.span ℤ (Set.range D)) := by
    refine Submodule.mem_orthogonalBilin_span.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact (hSymm.eq _ _).trans (BoundaryCycle.pairing_sum hGram i)
  have hδ₀ : (∑ i, D i) ≠ 0 := by
    rw [Fintype.sum_unique]
    exact fun h ↦ hD ((congrArg D (Subsingleton.elim 0 default)).trans h)
  have hfix (g : signedBoundaryIsometryGroup B D) (i : ZMod 1) :
      (toIsometry B D g).val (D i) = D i := by
    obtain ⟨p, hp⟩ := exists_indexPerm B D g
    exact (hp i).trans (congrArg D (Subsingleton.elim (p i) i))
  intro g h he
  let : Module.IsTorsionFree ℤ L := hB.1.isTorsionFree
  let : HasUniqueDiv L := HasUniqueDiv.of_isTorsionFree ℤ L
  have hsign := sign_eq_of_signedOrthogonalRestriction_eq hδ hδ₀ he
  apply Subtype.ext
  refine Prod.ext ?_ (by simpa only [sign_apply] using hsign)
  apply B.isometryGroupEquivIsometryEquiv.injective
  refine boundary_isometry_ext hSymm hB.1 (BoundaryCycle.span_sup_orthogonal_rat hGram hSymm hB)
    (fun i ↦ ?_) (fun x hx ↦ ?_)
  · simpa only [LinearMap.BilinForm.coe_isometryGroupEquivIsometryEquiv, toIsometry_apply]
      using (hfix g i).trans (hfix h i).symm
  · have heval := congrArg (fun a ↦ (a.val ⟨x, hx⟩ : L)) he
    simp only [coe_signedOrthogonalRestriction_apply, hsign] at heval
    simpa only [LinearMap.BilinForm.coe_isometryGroupEquivIsometryEquiv, toIsometry_apply]
      using smul_left_cancel (sign B D h) heval

end QPainleve.SignedBoundaryIsometryGroup
