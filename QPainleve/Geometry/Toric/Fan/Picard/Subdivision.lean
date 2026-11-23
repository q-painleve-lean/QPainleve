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

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i} [Nonempty Φ.cones] [Nonempty Ψ.cones]
  (h : Φ.IsSubdivision Ψ) (b : Module.Basis (Fin 2) ℤ N) {n : ℕ}
  (ρ : Fin n → Ψ.Ray) (c : Fin n → ℂˣ)

local notation "A" => internalBlowupTower b ρ c
local notation "A'" => internalBlowupTower b (h.liftRay ∘ ρ) c
local notation "π" => QPainleve.BlowupTower.toBase (WithBoundary.toTower (Sigma.snd (A)))
local notation "π'" => QPainleve.BlowupTower.toBase (WithBoundary.toTower (Sigma.snd (A')))
local notation "f" => h.toFanHom.algebraicMap

/-- The projection between ordered internal models over a fan subdivision pulls back
the toric class and keeps every exceptional coefficient. The centers may repeat,
so the exceptional classes in this formula are total transforms. -/
theorem pullback_internalBlowupPicardMarking (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)
    (g : (A').1 ⟶ (A).1) (hg : g ≫ π = π' ≫ f)
    (L : LineBundleClass Ψ.algebraicRealization) (m : Fin n → ℤ) :
    pullback g (internalBlowupPicardMarking b ρ c hΨ (Additive.ofMul L, m)).toMul =
      (internalBlowupPicardMarking b (h.liftRay ∘ ρ) c hΦ
        (Additive.ofMul (pullback f L), m)).toMul := by
  have := isIntegral_internalBlowupTower b (h.liftRay ∘ ρ) c hΦ
  have : IsModification π := isModification_internalBlowupTower_toBase b ρ c hΨ
  have : IsModification π' := isModification_internalBlowupTower_toBase b (h.liftRay ∘ ρ) c hΦ
  obtain ⟨q, hq, -, hE⟩ := h.exists_isPullback_internalBlowupTower b ρ c
  have : IsDominant (g ≫ π) := hg.symm ▸ inferInstanceAs (IsDominant (π' ≫ f))
  have : IsDominant (q ≫ π) := hq.w.symm ▸ inferInstanceAs (IsDominant (π' ≫ f))
  have := IsModification.isDominant_of_comp g π
  have := IsModification.isDominant_of_comp q π
  have he : g = q := (π).eq_of_comp_eq_of_isModification (hg.trans hq.w.symm)
  rw [he, internalBlowupPicardMarking_apply, internalBlowupPicardMarking_apply]
  exact pullback_picardHom hq.w hE (Additive.ofMul L) m

end TauCeti.Toric.Fan.IsSubdivision
