/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.TorusAction.Comparison

import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic
import QPainleve.AlgebraicGeometry.RationalMap.FunctionField

/-!
# Orientation reversal of contracted toric evaluation

Exchanging the two basis vectors and inverting the center character leaves each
ordered blowup center unchanged. Consequently the fixed-center evaluation on a
specified contraction changes by regular inversion in the independent X torus.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable (k : Type) [Field k] [IsAlgClosed k]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]
  {m : ℕ} (b : Module.Basis (Fin 2) ℤ N) (s : Fin m → Φ.Ray)
  (c : Multiplicative (Fin m → ℤ) →* kˣ)

local notation "center" a:arg => (fun j : Fin m ↦ a (ofAdd (Pi.single j 1)))
local notation "bᵣ" => b.reindex (Equiv.swap 0 1)
local notation "T" => internalBlowupTower k b s (center c)
local notation "Tᵣ" => internalBlowupTower k bᵣ s (center (c⁻¹))
local notation "Xtor" => QPainleve.CharacterTorus.scheme k (Fin m →₀ ℤ)
local notation "invX" =>
  QPainleve.CharacterTorus.map k (AddEquiv.toAddMonoidHom (AddEquiv.neg (Fin m →₀ ℤ)))

variable {X : Scheme} [IsIntegral X] (hΦ : Φ.IsRegular)
  (p : (internalBlowupTower k b s (fun j : Fin m ↦ c (ofAdd (Pi.single j 1)))).1 ⟶ X)
  [IsModification p]
  (q : (internalBlowupTower k (b.reindex (Equiv.swap 0 1)) s
    (fun j : Fin m ↦ c⁻¹ (ofAdd (Pi.single j 1)))).1 ⟶ X)
  [IsModification q]

/-- The same contraction, read with the opposite toric lattice orientation and
inverse center character, evaluates to the reciprocals of the original X coordinates.
The comparison applies with repeated centers and with any charge rank. -/
theorem contractedXEvaluation_reindex_swap
    (hq : let h : Tᵣ = T := internalBlowupTower_reindex_swap k b s (center c)
      eqToHom (congrArg Sigma.fst h) ≫ p = q) :
    contractedXEvaluation k bᵣ s c⁻¹ hΦ q =
      (contractedXEvaluation k b s c hΦ p).compHom invX := by
  let := isIntegral_internalBlowupTower k bᵣ s (center (c⁻¹)) hΦ
  let := isIntegral_internalBlowupTower k b s (center c) hΦ
  let := isModification_internalBlowupTower_toBase k bᵣ s (center (c⁻¹)) hΦ
  let := isModification_internalBlowupTower_toBase k b s (center c) hΦ
  have transfer (U V : Σ Y, WithBoundary (Φ.toricBoundaryIdeal k inferInstance).subschemeι m Y)
      (h : U = V) (f : V.1 ⟶ X) (g : U.1 ⟶ X)
      [IsIntegral U.1] [IsIntegral V.1] [IsDominant f] [IsDominant g]
      [IsDominant U.2.toTower.toBase] [IsDominant V.2.toTower.toBase]
      (hfg : eqToHom (congrArg Sigma.fst h) ≫ f = g)
      (v : X ⤏ Xtor)
      (hv : f.toRationalMap.comp v =
        V.2.toTower.toBase.toRationalMap.comp (Φ.xEvaluation k b s c)) :
      g.toRationalMap.comp v =
        U.2.toTower.toBase.toRationalMap.comp (Φ.xEvaluation k b s c) := by
    subst V
    have he : f = g := by simpa only [eqToHom_refl, Category.id_comp] using hfg
    subst g
    exact hv
  have h : Tᵣ = T := internalBlowupTower_reindex_swap k b s (center c)
  have he := transfer Tᵣ T h p q hq _ (comp_contractedXEvaluation k b s c hΦ p)
  apply Scheme.RationalMap.comp_left_injective q.toRationalMap
  calc
    _ = Tᵣ.2.toTower.toBase.toRationalMap.comp (Φ.xEvaluation k bᵣ s c⁻¹) :=
      comp_contractedXEvaluation k bᵣ s c⁻¹ hΦ q
    _ = _ := by
      simpa only [xEvaluation_reindex_swap, Scheme.RationalMap.comp_compHom] using
        congrArg (·.compHom invX) he.symm

end TauCeti.Toric.Fan
