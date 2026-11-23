/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Factorial
public import TauCeti.AlgebraicGeometry.IdealSheaf.Stalk
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Stalk
import TauCeti.AlgebraicGeometry.Morphisms.Dominant

/-!
# Support of effective Cartier divisors

The stalk ideal of an effective Cartier divisor detects its prime components. At
codimension one, membership in its support is equivalent to having nonzero Weil coefficient.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

variable {X : Scheme.{u}} {I : X.IdealSheafData}

/-- The ideal of an effective Cartier divisor is nonzero at every stalk. -/
theorem stalkIdeal_ne_bot (hI : I.IsEffectiveCartier) (x : X) : I.stalkIdeal x ≠ ⊥ := by
  obtain ⟨U, hU, hx, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (TopologicalSpace.Opens.mem_top x)
  obtain ⟨a, ha, hspan⟩ := hI.exists_map_germ_eq_span_singleton ⟨U, hU⟩ hx
  rw [I.stalkIdeal_eq_map ⟨U, hU⟩ x hx, hspan]
  exact fun h ↦ ha.isLeftRegular.ne_zero (Ideal.span_singleton_eq_bot.mp h)

variable [IsIntegral X]

/-- The generic point is outside the support of an effective Cartier divisor. -/
theorem genericPoint_notMem_support (hI : I.IsEffectiveCartier) : genericPoint X ∉ I.support := by
  rw [I.mem_support_iff_stalkIdeal_ne_top, not_not]
  let : Field X.functionField := inferInstance
  exact (eq_bot_or_eq_top (I.stalkIdeal (genericPoint X))).resolve_left
    (hI.stalkIdeal_ne_bot (genericPoint X))

/-- The pullback of an effective Cartier divisor along a dominant morphism of integral
schemes is effective Cartier. -/
theorem comap_of_isDominant {Y : Scheme.{u}} (hI : I.IsEffectiveCartier) (f : Y ⟶ X)
    [IsIntegral Y] [IsDominant f] : (I.comap f).IsEffectiveCartier :=
  hI.comap_of_isIntegral f (f.genericPoint_eq_of_isDominant.symm ▸ hI.genericPoint_notMem_support)

open TauCeti.AlgebraicGeometry in
/-- At a codimension-one point, the Weil coefficient of an effective Cartier divisor
vanishes exactly where its ideal is the unit ideal. -/
theorem coeff_toWeilDivisor_eq_zero_iff [IsNoetherian X] (hI : I.IsEffectiveCartier)
    (x : CodimensionOnePoint X) :
    WeilDivisor.coeff hI.toCartierDivisor.toWeilDivisor x = 0 ↔ (x : X) ∉ I.support := by
  obtain ⟨U, hxU, a, ha, hUa⟩ := (isEffectiveCartier_iff I).mp hI (x : X)
  have : Nonempty U.val := ⟨⟨x, hxU⟩⟩
  have ha0 : a ≠ 0 := ha.isLeftRegular.ne_zero
  rw [hI.toCartierDivisor.coeff_toWeilDivisor_eq_ord x hxU _
      (hI.toCartierDivisor_restrict U ha0 hUa).symm,
    Units.val_mk0, ← X.algebraMap_germ_eq_germToFunctionField hxU a]
  have hb : (X.presheaf.germ U.val x hxU).hom a ≠ 0 :=
    (map_ne_zero_iff _ (germ_injective_of_isIntegral X x hxU)).mpr ha0
  rw [Scheme.ord_algebraMap_stalk_eq_zero_iff x.property specializes_rfl hb,
    I.mem_support_iff_stalkIdeal_ne_top, not_not, I.stalkIdeal_eq_map U x hxU, hUa,
    Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_top]
  simp [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
