/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.FiniteFanScheme
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.Boundary
public import QPainleve.Geometry.Toric.Fan.Subdivision

import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Residual
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.Geometry.Toric.Fan.Boundary.Subdivision
import QPainleve.Geometry.Toric.BaseChange.FiniteType
import QPainleve.Geometry.Toric.Fan.Boundary.Ideal
import TauCeti.AlgebraicGeometry.RationalPoint.Basic
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension

/-!
# Total transforms of ray classes under toric point blowups

A surviving ray in a toric point blowup represents the strict transform of the
original boundary curve. The total transform includes the exceptional class
exactly when that curve contains the center.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module PointedCone TopologicalSpace
open Scheme.IdealSheafData TauCeti.AlgebraicGeometry LineBundleClass

namespace TauCeti.Toric.Fan

universe u

variable (k : Type u) [Field k] {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} {Φ Ψ : Fan i}

local notation "X[" Δ "]" => Fan.finiteFanScheme k Δ
local notation "p[" σ "]" =>
  Fan.distinguishedSection (R := k) _ σ (IsLocalRing.closedPoint k)

local notation "D[" h "," ρ "]" => Fan.rayDivisorIdeal k _ h ρ
local notation "R[" h "," ρ "]" => Fan.rayChartDivisorToPicard k _ h (Pi.single ρ 1)

private theorem pullback_rayChartDivisorToPicard_single_of_closedPoint
    [Nonempty Φ.cones] [Nonempty Ψ.cones] (s : Ψ.IsSubdivision Φ)
    (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (hN : finrank ℤ N = 2)
    {p : X[Φ]} (hp : IsClosed ({p} : Set X[Φ])) (ρ : Φ.Ray)
    {I : (X[Φ]).IdealSheafData} (hI : I = vanishingIdeal ⟨closure {p}, isClosed_closure⟩)
    (e : X[Ψ] ≅ I.blowup) (he : e.hom ≫ I.blowupToBase = (s.toFanHom.finiteFanSchemeHom k)) :
    let pull := (pullbackHom (s.toFanHom.finiteFanSchemeHom k)).toAdditive.toIntLinearMap
    pull R[hΦ, ρ] = R[hΨ, s.liftRay ρ] + (D[hΦ, ρ].stalkOrder p).toNat •
      Additive.ofMul (pullback e.hom I.blowupExceptionalClass) := by
  classical
  subst I
  let f := Φ.finiteFanSchemeToSpec k
  let : SmoothOfRelativeDimension 2 f :=
    hN ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k hΦ
  let : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  let : IsNoetherian X[Φ] := isNoetherian_of_finiteType f
  let : IsRegularLocalRing (X[Φ].presheaf.stalk p) := isRegularLocalRing_stalk_of_smooth f p
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq f 2).mp inferInstance).2 p hp
  have hcodim := coheight_eq_of_isClosed_of_smoothOfRelativeDimension (n := 2) f hp
  have hout : (Φ.rayBoundaryChartPoint (R := k) hΦ ρ).val ∉
      ((vanishingIdeal ⟨closure {p}, isClosed_closure⟩).support : Set X[Φ]) := by
    rw [coe_support_vanishingIdeal, Closeds.coe_mk, hp.closure_eq, Set.mem_singleton_iff]
    intro heq
    have hh := (Φ.rayBoundaryChartPoint (R := k) hΦ ρ).property
    rw [heq, hcodim] at hh
    exact (by decide : (2 : ℕ∞) ≠ 1) hh
  have hstrict := s.comap_ker_blowupMap_rayDivisorIdeal k hΨ hΦ e he ρ hout
  have hD := Φ.isEffectiveCartier_rayDivisorIdeal k hΦ ρ
  have hS := hD.strictTransform_pointBlowup hp hdim
  have hclass := congrArg (pullback e.hom)
    (hD.toLineBundleClass_strictTransform_pointBlowup hp hdim)
  rw [pullback_mul, pullback_comp] at hclass
  -- The strict transform API writes the center with an explicit Set.singleton.
  erw [he] at hclass
  simp only [pullback_pow, pullback_inv] at hclass
  rw [IsEffectiveCartier.pullback_mk_toInvertibleSheaf _ (hS.comap e.hom),
    mk_toInvertibleSheaf_congr _ (Ψ.isEffectiveCartier_rayDivisorIdeal k hΨ _) hstrict] at hclass
  let := Φ.uniqueFactorizationMonoid_stalk_finiteFanScheme (R := k) hΦ
  let := Ψ.uniqueFactorizationMonoid_stalk_finiteFanScheme (R := k) hΨ
  simp only [rayChartDivisorToPicard_single, one_smul, primeDivisorClass_def,
    ← Φ.rayDivisorIdeal_def k hΦ, ← Ψ.rayDivisorIdeal_def k hΨ]
  apply Additive.toMul.injective
  simp only [AddMonoidHom.coe_toIntLinearMap,
    MonoidHom.toAdditive_apply_apply, pullbackHom_apply, toMul_ofMul, toMul_add, toMul_nsmul]
  rw [pullback_inv, hclass, inv_pow]
  erw [inv_mul_cancel_right]

open Classical in
/-- For a subdivision realized by blowing up a distinguished point of a regular
toric surface, the total transform of a ray class is the lifted ray class plus
the exceptional class if the ray belongs to the center cone. -/
theorem IsSubdivision.pullback_rayDivisorToPicard_single_of_pointBlowup
    (s : Ψ.IsSubdivision Φ) (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)
    (hN : finrank ℤ N = 2) (σ : Φ.cones) (ρ : Φ.Ray)
    (e : X[Ψ] ≅ (Φ.distinguishedSection (R := k) σ).ker.blowup)
    (he : e.hom ≫ (Φ.distinguishedSection (R := k) σ).ker.blowupToBase =
      s.toFanHom.finiteFanSchemeHom k) :
    letI : Nonempty Φ.cones := ⟨σ⟩
    letI : Nonempty Ψ.cones := s.nonempty_cones_of_nonempty ⟨σ⟩
    let pull := (pullbackHom (s.toFanHom.finiteFanSchemeHom k)).toAdditive.toIntLinearMap
    pull R[hΦ, ρ] = R[hΨ, s.liftRay ρ] + (if ρ.toCone ≤ σ then (1 : ℤ) else 0) •
      Additive.ofMul (pullback e.hom
        (Φ.distinguishedSection (R := k) σ).ker.blowupExceptionalClass) := by
  let : Nonempty Φ.cones := ⟨σ⟩
  let : Nonempty Ψ.cones := s.nonempty_cones_of_nonempty ⟨σ⟩
  dsimp only
  have hI := (Φ.distinguishedSection (R := k) σ).ker_eq_ker_fromSpecResidueField.trans
    (X[Φ].ker_fromSpecResidueField_eq_vanishingIdeal p[σ])
  have h := pullback_rayChartDivisorToPicard_single_of_closedPoint k s hΦ hΨ hN
    (isClosed_singleton_of_section (Φ.distinguishedSection_comp_finiteFanSchemeToSpec σ)) ρ hI e he
  dsimp only at h
  rw [Φ.stalkOrder_rayBoundaryIdeal_distinguishedPoint k hΦ] at h
  split_ifs at h ⊢ <;> simpa only [ENat.toNat_one, ENat.toNat_zero, one_nsmul, zero_nsmul,
    one_zsmul, zero_zsmul] using h

end TauCeti.Toric.Fan
