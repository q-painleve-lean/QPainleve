/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
import QPainleve.AlgebraicGeometry.IdealSheaf.Integral
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Stalk
import TauCeti.AlgebraicGeometry.IdealSheaf.Stalk

/-!
# Integral effective Cartier divisors

The generic point of an integral effective Cartier divisor is a codimension-one point
of the ambient scheme.
The codimension calculation applies Mathlib's
`Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors` to the maximal ideal
of the ambient stalk at that point.
-/

public section

open CategoryTheory Order TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme}

/-- The generic point of an integral effective Cartier divisor has codimension one in the
ambient locally Noetherian scheme. -/
theorem IsEffectiveCartier.coheight_subschemeι_genericPoint [IsLocallyNoetherian X]
    {I : X.IdealSheafData} [IsIntegral I.subscheme] (hI : I.IsEffectiveCartier) :
    coheight (I.subschemeι (genericPoint I.subscheme)) = 1 := by
  let η := genericPoint I.subscheme
  let x := I.subschemeι η
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (Opens.mem_top x)
  obtain ⟨a, ha, hspan⟩ := hI.exists_map_germ_eq_span_singleton ⟨U, hU⟩ hxU
  have hker : RingHom.ker (I.subschemeι.stalkMap η).hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    IsLocalRing.ker_eq_maximalIdeal (K := I.subscheme.functionField) _
      (I.subschemeι.stalkMap_surjective η)
  rw [I.subschemeι.ker_stalkMap_of_isClosedImmersion, I.ker_subschemeι,
    I.stalkIdeal_eq_map ⟨U, hU⟩ x hxU, hspan] at hker
  have hnonunit : ¬ IsUnit a := by
    intro hu
    exact Ideal.IsMaximal.ne_top (inferInstance :
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).IsMaximal)
      (hker ▸ Ideal.span_singleton_eq_top.mpr hu)
  have hheight := Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (isRegular_iff_mem_nonZeroDivisors.mp (isLeftRegular_iff_isRegular.mp ha)) hnonunit
  have hdim :
      ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).height : WithBot ℕ∞) = 1 := by
    exact_mod_cast hker ▸ hheight
  rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ringKrullDim_stalk_eq_coheight] at hdim
  exact_mod_cast hdim

/-- The generic point is the unique codimension-one point of the ambient scheme on an
integral effective Cartier divisor. -/
theorem IsEffectiveCartier.mem_support_iff_eq_subschemeι_genericPoint [IsLocallyNoetherian X]
    {I : X.IdealSheafData} [IsIntegral I.subscheme] (hI : I.IsEffectiveCartier)
    {x : X} (hx : coheight x = 1) :
    x ∈ I.support ↔ x = I.subschemeι (genericPoint I.subscheme) := by
  let η := I.subschemeι (genericPoint I.subscheme)
  have hη := hI.coheight_subschemeι_genericPoint
  rw [← SetLike.mem_coe, I.support_eq_closure_subschemeι_genericPoint,
    ← specializes_iff_mem_closure]
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ specializes_refl _⟩
  by_contra hne
  have hlt : x < η := ⟨h, fun hs ↦ hne (hs.antisymm h).eq⟩
  have hle := coheight_add_one_le hlt
  rw [hx, hη] at hle
  norm_num at hle

end AlgebraicGeometry.Scheme.IdealSheafData
