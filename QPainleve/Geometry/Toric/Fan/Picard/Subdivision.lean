/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.InternalBlowup
public import QPainleve.Geometry.Toric.Fan.Subdivision.Basic

import QPainleve.AlgebraicGeometry.Morphisms.Modification.Birational
import QPainleve.AlgebraicGeometry.Morphisms.Modification.IsoLocus
import QPainleve.Geometry.Toric.Fan.Subdivision.FunctionField
import QPainleve.Geometry.Toric.Fan.Subdivision.InternalBlowup

/-!
# Picard pullback along a subdivision of an ordered toric model

Refining the fan pulls back the toric part of the marking along the toric projection
and retains the coefficient of each total internal exceptional class. This compares
the full marked Picard groups across the nodal subdivisions used to change toric
presentations. The models are those of Gross, Hacking and Keel,
[*Moduli of surfaces with an anti-canonical cycle*, Definition 1.2][GHK].

[GHK]: https://arxiv.org/abs/1211.6367
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower TauCeti.AlgebraicGeometry
open LineBundleClass

namespace TauCeti.Toric.Fan.IsSubdivision

universe u

section BaseRing

variable (R : Type u) [CommRing R] {N : Type u} {V : Type*} [AddCommGroup N]
  [AddCommGroup V] [Module ℝ V] {i : N →+ V} {Φ Ψ : Fan i}

/-- Pullback in the coordinates of an ordered internal blowup model. A fan subdivision
pulls back the toric class and keeps every total exceptional coefficient. -/
noncomputable def internalBlowupPicardPullback (h : Φ.IsSubdivision Ψ) {n : ℕ} :
    Additive (LineBundleClass (Ψ.finiteFanScheme R)) × (Fin n → ℤ) →ₗ[ℤ]
      Additive (LineBundleClass (Φ.finiteFanScheme R)) × (Fin n → ℤ) :=
  ((pullbackHom (h.toFanHom.finiteFanSchemeHom R)).toAdditive.toIntLinearMap).prodMap LinearMap.id

/-- Coordinate formula for pullback along a fan subdivision of an ordered internal model. -/
@[simp]
theorem internalBlowupPicardPullback_apply (h : Φ.IsSubdivision Ψ) {n : ℕ}
    (x : Additive (LineBundleClass (Ψ.finiteFanScheme R)) × (Fin n → ℤ)) :
    h.internalBlowupPicardPullback R x =
      (Additive.ofMul (pullback (h.toFanHom.finiteFanSchemeHom R) x.1.toMul), x.2) := by
  simp only [internalBlowupPicardPullback, LinearMap.prodMap_apply, AddMonoidHom.coe_toIntLinearMap,
    MonoidHom.coe_toAdditive, Function.comp_apply, pullbackHom_apply, LinearMap.id_apply]

end BaseRing

variable (k : Type u) [Field k] [PerfectField k] {N V : Type u} [AddCommGroup N]
  [AddCommGroup V] [Module ℝ V] {i : N →+ V} {Φ Ψ : Fan i}

variable [Nonempty Φ.cones] [Nonempty Ψ.cones]
  (h : Φ.IsSubdivision Ψ) (b : Module.Basis (Fin 2) ℤ N) {n : ℕ}
  (ρ : Fin n → Ψ.Ray) (c : Fin n → kˣ)

local notation "A" => internalBlowupTower k b ρ c
local notation "A'" => internalBlowupTower k b (h.liftRay ∘ ρ) c
local notation "π" => QPainleve.BlowupTower.toBase (WithBoundary.toTower (Sigma.snd (A)))
local notation "π'" => QPainleve.BlowupTower.toBase (WithBoundary.toTower (Sigma.snd (A')))
local notation "f" => h.toFanHom.finiteFanSchemeHom k

/-- The projection between ordered internal models over a fan subdivision pulls back
the toric class and keeps every exceptional coefficient. The centers may repeat,
so the exceptional classes in this formula are total transforms. -/
theorem pullback_internalBlowupPicardMarking (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)
    (g : (A').1 ⟶ (A).1) (hg : g ≫ π = π' ≫ f)
    (L : LineBundleClass (Ψ.finiteFanScheme k)) (m : Fin n → ℤ) :
    pullback g (internalBlowupPicardMarking k b ρ c hΨ (Additive.ofMul L, m)).toMul =
      (internalBlowupPicardMarking k b (h.liftRay ∘ ρ) c hΦ
        (Additive.ofMul (pullback f L), m)).toMul := by
  have := isIntegral_internalBlowupTower k b (h.liftRay ∘ ρ) c hΦ
  have : IsModification π := isModification_internalBlowupTower_toBase k b ρ c hΨ
  have : IsModification π' := isModification_internalBlowupTower_toBase k b (h.liftRay ∘ ρ) c hΦ
  obtain ⟨q, hq, -, hE⟩ := h.exists_isPullback_internalBlowupTower k b ρ c
  have : IsDominant (g ≫ π) := hg.symm ▸ inferInstanceAs (IsDominant (π' ≫ f))
  have : IsDominant (q ≫ π) := hq.w.symm ▸ inferInstanceAs (IsDominant (π' ≫ f))
  have := IsModification.isDominant_of_comp g π
  have := IsModification.isDominant_of_comp q π
  have he : g = q := (π).eq_of_comp_eq_of_isModification (hg.trans hq.w.symm)
  rw [he, internalBlowupPicardMarking_apply, internalBlowupPicardMarking_apply]
  exact pullback_picardHom hq.w hE (Additive.ofMul L) m

end TauCeti.Toric.Fan.IsSubdivision
