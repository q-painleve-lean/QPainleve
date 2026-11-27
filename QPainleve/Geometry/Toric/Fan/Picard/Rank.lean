/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.FiniteFanScheme
public import QPainleve.Geometry.Toric.Fan.Equiv

import Mathlib.LinearAlgebra.Dimension.RankNullity
import TauCeti.LinearAlgebra.Dual.Basis

/-!
# The Picard rank of a complete regular fan

The divisor sequence of Cox, Little and Schenck, *Toric Varieties*, Theorem 4.1.3,
computes Picard rank from the number of rays and the lattice rank. Completeness
ensures that a character whose divisor vanishes is zero.
-/

public section

open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

universe u

variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

/-- On a complete fan, the coefficients of a character's divisor determine the character. -/
theorem characterToRayDivisor_injective (hc : Φ.IsComplete) :
    Function.Injective Φ.characterToRayDivisor := by
  apply (injective_iff_map_eq_zero _).mpr
  intro m hm
  apply Φ.character_eq_zero_of_nonneg_primitiveGenerator hc
  intro ρ
  exact le_of_eq (by simpa using (congrFun hm ρ).symm)

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [UniqueFactorizationMonoid R] in
/-- For a complete regular fan, Picard rank plus lattice rank is the number of rays. -/
theorem finrank_picard_add_finrank_eq_natCard_ray (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) :
    Module.finrank ℤ (Additive (LineBundleClass (Φ.finiteFanScheme R))) +
      Module.finrank ℤ N = Nat.card Φ.Ray := by
  let := hc.nonempty_cones
  let := Φ.lattice.free
  let := Fintype.ofFinite Φ.Ray
  let f := Φ.characterToRayDivisor.toIntLinearMap
  let g := (Φ.rayChartDivisorToPicard R hΦ).toIntLinearMap
  have hf : Function.Injective f := characterToRayDivisor_injective hc
  have hg : Function.Surjective g := Φ.rayChartDivisorToPicard_surjective R hΦ
  have hex : Function.Exact f g := Φ.exact_characterToRayDivisor_rayChartDivisorToPicard R hΦ
  have h := g.ker.finrank_quotient_add_finrank
  rw [(g.quotKerEquivOfSurjective hg).finrank_eq, LinearMap.exact_iff.mp hex,
    ← (LinearEquiv.ofInjective f hf).finrank_eq,
    (addMonoidHomLequivInt (A := N) (B := ℤ) ℤ).finrank_eq,
    TauCeti.Module.dual_finrank_eq] at h
  simpa [Nat.card_eq_fintype_card] using h

end TauCeti.Toric.Fan

namespace TauCeti.Toric.FanEquiv

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}

/-- Fan equivalences from a complete fan are determined by their action on rays. -/
theorem eq_of_rayEquiv_eq (hc : Φ.IsComplete) {f g : FanEquiv Φ Ψ}
    (h : f.rayEquiv = g.rayEquiv) : f = g := by
  apply FanEquiv.ext
  have := Ψ.lattice.free
  let b := Module.Free.chooseBasis ℤ N'
  apply AddEquiv.ext
  intro x
  apply b.ext_elem_iff.mpr
  intro j
  let m := (b.coord j).toAddMonoidHom
  have hm : m.comp f.latticeEquiv.toAddMonoidHom = m.comp g.latticeEquiv.toAddMonoidHom := by
    apply Φ.characterToRayDivisor_injective hc
    funext ρ
    simp only [Fan.characterToRayDivisor_apply, AddMonoidHom.comp_apply,
      AddEquiv.coe_toAddMonoidHom, ← primitiveGenerator_rayEquiv, h]
  exact DFunLike.congr_fun hm x

end TauCeti.Toric.FanEquiv
