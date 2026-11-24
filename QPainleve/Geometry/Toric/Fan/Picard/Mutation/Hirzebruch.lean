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

open Module PointedCone

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

section

variable (ρ : Φ.Ray) (b : Basis (Fin 2) ℤ N)
  (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones)

local notation "Ψ" =>
  Φ.mutationFan b ρ.primitiveGenerator_ne_zero ρ.hull_primitiveGenerator_mem hOpp
local notation "rayEquiv" =>
  Φ.mutationFanRayEquiv b ρ.primitiveGenerator_ne_zero ρ.hull_primitiveGenerator_mem hOpp
local notation "hΨ[" h "]" => Iff.mpr (Φ.isRegular_mutationFan_iff b ρ.primitiveGenerator_ne_zero
  ρ.hull_primitiveGenerator_mem hOpp) h

/-- After mutation at either Hirzebruch section, the mutation fiber classes on the
original and mutated fans are the first vectors of their respective Hirzebruch Picard bases. -/
theorem Ray.mutationFiberClasses_eq_hirzebruchPicardBasis_zero
    [Nonempty Φ.cones] [Nonempty (Ψ).cones] (e : ℤ) (hΦ : Φ.IsRegular)
    (r : Fin 4 ≃ Φ.Ray)
    (hr : (fun l ↦ (r l).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])
    (onSection : Bool) (hρ : ρ = r (if onSection then 0 else 2))
    (d : Basis (Fin 2) ℤ N) (hd₀ : d 0 = b 0)
    (hd₁ : d 1 = b 1 - (if onSection then 0 else b 0))
    (hr' : (fun l ↦ ((r.trans rayEquiv) l).primitiveGenerator) =
      ![d 0, d 1, -d 0, (if onSection then e + 1 else e - 1) • d 0 - d 1]) :
    mutationFiberClass b ρ hΦ = hirzebruchPicardBasis b e hΦ r hr 0 ∧
    mutationFiberClass b (rayEquiv ρ) hΨ[hΦ] =
      hirzebruchPicardBasis d (if onSection then e + 1 else e - 1) hΨ[hΦ]
        (r.trans rayEquiv) hr' 0 := by
  cases onSection
  · have hρ₂ : ρ = r 2 := hρ
    have hρ₂' : rayEquiv ρ = (r.trans rayEquiv) 2 := congrArg rayEquiv hρ₂
    rw [hρ₂', hirzebruchPicardBasis_apply_zero, hirzebruchPicardBasis_apply_zero]
    exact ⟨hρ₂.symm ▸ mutationFiberClass_of_opposite_section b hΦ r e 0 (by simpa using hr),
      mutationFiberClass_of_opposite_section b hΨ[hΦ] (r.trans rayEquiv) (e - 1) 1
        (by simpa only [hd₀, hd₁, Bool.false_eq_true, ite_false, one_zsmul] using hr')⟩
  · have hρ₀ : ρ = r 0 := hρ
    have hρ₀' : rayEquiv ρ = (r.trans rayEquiv) 0 := congrArg rayEquiv hρ₀
    have hd₁' : d 1 = b 1 := by simpa only [ite_true, sub_zero] using hd₁
    have hdb : d = b := by
      apply DFunLike.ext
      intro l
      fin_cases l
      · exact hd₀
      · exact hd₁'
    subst d
    exact ⟨hρ₀.symm ▸ mutationFiberClass_eq_hirzebruchPicardBasis_zero b e hΦ r hr,
      hρ₀'.symm ▸
        mutationFiberClass_eq_hirzebruchPicardBasis_zero b (e + 1) hΨ[hΦ] (r.trans rayEquiv) hr'⟩

end

end TauCeti.Toric.Fan
