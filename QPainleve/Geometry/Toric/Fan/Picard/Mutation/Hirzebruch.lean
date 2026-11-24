/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Hirzebruch
public import QPainleve.Geometry.Toric.Fan.Picard.Mutation.Basic

/-!
# The mutation fiber class in Hirzebruch coordinates

The positive character divisor used for mutation along the chosen section
represents the first Hirzebruch Picard basis vector, the ruling fiber class.
-/

public section

open Module

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

/-- When mutating at the chosen section of a Hirzebruch fan, the mutation fiber
class is the fiber vector of the Hirzebruch Picard basis. -/
theorem mutationFiberClass_eq_hirzebruchPicardBasis_zero (b : Basis (Fin 2) ℤ N)
    (e : ℤ) (hΦ : Φ.IsRegular) (r : Fin 4 ≃ Φ.Ray)
    (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1]) :
    letI : Nonempty Φ.cones := ⟨(r 0).toCone⟩
    mutationFiberClass b (r 0) hΦ = Φ.hirzebruchPicardBasis b e hΦ r hr 0 := by
  classical
  let : Nonempty Φ.cones := ⟨(r 0).toCone⟩
  let m := (b.detDualEquiv (b 0)).toAddMonoidHom
  let a : Φ.Ray → ℤ := fun ρ ↦ max (b.det ![ρ.primitiveGenerator, (r 0).primitiveGenerator]) 0
  have hm (ρ : Φ.Ray) : m ρ.primitiveGenerator =
      -b.det ![ρ.primitiveGenerator, (r 0).primitiveGenerator] := by
    have h₀ : (r 0).primitiveGenerator = b 0 := congrFun hr 0
    rw [h₀, ← b.detDualEquiv_apply, b.detDualEquiv_swap ρ.primitiveGenerator (b 0), neg_neg]
    rfl
  have hadd : a + Φ.characterToRayDivisor m = Pi.single (r 1) 1 := by
    apply r.surjective.injective_comp_right
    funext j
    simp only [Function.comp_apply, Pi.add_apply, characterToRayDivisor_apply, hm, a,
      Pi.single_apply, Equiv.apply_eq_iff_eq]
    have h₀ : (r 0).primitiveGenerator = b 0 := congrFun hr 0
    rw [h₀, ← b.detDualEquiv_apply, b.detDualEquiv_swap _ (b 0)]
    have hj := congrFun hr j
    rw [hj]
    fin_cases j <;> norm_num [b.detDualEquiv_self, b.detDualEquiv_apply_basis_zero_one,
      -Basis.detDualEquiv_apply]
  have hpri := (Φ.exact_characterToRayDivisor_rayDivisorToPicard hΦ _).mpr ⟨m, rfl⟩
  rw [mutationFiberClass_eq, hirzebruchPicardBasis_apply_zero, ← hadd, map_add, hpri, add_zero]

end TauCeti.Toric.Fan
