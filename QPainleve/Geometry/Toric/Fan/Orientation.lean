/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.ChargeKernel.Basic
public import QPainleve.Geometry.Toric.Fan.CyclicOrder
public import QPainleve.Geometry.Toric.Fan.Evaluation
public import QPainleve.Geometry.Toric.Fan.InternalBlowup

import QPainleve.Algebra.MvPolynomial.Laurent.FiniteType
import QPainleve.AlgebraicGeometry.RationalMap.Affine

/-!
# Reversing the orientation of a toric presentation

Swapping the lattice basis reverses the order of the incident rays at each toric
node. Inverting the center parameters identifies the ordered blowup models and
the marked Picard classes. On the independent cluster X torus the same change
of presentation inverts every coordinate.

The X inversion is the signed generator of Bershtein, Gavrylenko and Marshakov,
[*Cluster integrable systems, q-Painlevé equations and their quantization*, §3.1]
(https://arxiv.org/abs/1711.02063).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module Multiplicative
open QPainleve.BlowupTower QPainleve.Cluster TauCeti.LaurentRing
open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {l : N →+ V} {Φ : Fan l} (b : Basis (Fin 2) ℤ N)

local notation "bᵣ" => b.reindex (Equiv.swap 0 1)

/-- Reversing the lattice orientation reverses the cyclic numbering by `j ↦ -j`.
The initial ray and the cones at which successive rays meet are preserved. -/
theorem cyclicRayNumbering_neg (u : ZMod (Nat.card Φ.Ray) ≃ Φ.Ray)
    (hu : ∀ j, b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ) (j : ZMod (Nat.card Φ.Ray)) :
    (bᵣ).detDualEquiv (u (-j)).primitiveGenerator (u (-(j + 1))).primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, (u (-j)).toCone ≤ σ ∧ (u (-(j + 1))).toCone ≤ σ := by
  have h : -(j + 1) + 1 = -j := by simp [neg_add_rev, add_assoc]
  obtain ⟨hdet, σ, h₁, h₂⟩ := hu (-(j + 1))
  rw [h] at hdet h₂
  refine ⟨?_, σ, h₂, h₁⟩
  simpa only [Basis.detDualEquiv_reindex_swap, LinearMap.neg_apply,
    ← Basis.detDualEquiv_swap b (u (-(j + 1))).primitiveGenerator] using hdet

section OrderedBlowups

variable [h₀ : Nonempty Φ.cones] {n : ℕ} (s : Fin n → Φ.Ray) (c : Fin n → ℂˣ)

open LineBundleClass in
/-- Identifying the blowup models for opposite orientations sends the strict
boundary identically to itself, preserves the projection to the fan, and pulls
back every marked Picard class to the class with the same coordinates. -/
theorem internalBlowupTower_reindex_swap_iso (hΦ : Φ.IsRegular) :
    let A := internalBlowupTower b s c
    let B := internalBlowupTower (b.reindex (Equiv.swap 0 1)) s c⁻¹
    let e := eqToIso (congrArg Sigma.fst (internalBlowupTower_reindex_swap b s c).symm)
    e.hom ≫ B.2.toTower.toBase = A.2.toTower.toBase ∧
      A.2.boundaryι ≫ e.hom = B.2.boundaryι ∧
      ∀ a, pullback e.hom
        (internalBlowupPicardMarking (b.reindex (Equiv.swap 0 1)) s c⁻¹ hΦ a).toMul =
          (internalBlowupPicardMarking b s c hΦ a).toMul := by
  dsimp only
  simp only [internalBlowupPicardMarking_apply]
  have compare (A B : Σ Y, WithBoundary (Φ.boundaryIdeal h₀).subschemeι n Y) (h : A = B) :
      let e := eqToIso (congrArg Sigma.fst h)
      e.hom ≫ B.2.toTower.toBase = A.2.toTower.toBase ∧
        A.2.boundaryι ≫ e.hom = B.2.boundaryι ∧
        ∀ a, pullback e.hom (B.2.toTower.picardHom a).toMul =
          (A.2.toTower.picardHom a).toMul := by
    subst B
    simp
  exact compare _ _ (internalBlowupTower_reindex_swap b s c).symm

end OrderedBlowups

variable {ι : Type} [DecidableEq ι] (s : ι → Φ.Ray)

/-- Orientation reversal negates the exchange matrix without changing the ray charges. -/
@[simp]
theorem chargeExchangeMatrix_reindex_swap [Fintype ι] :
    chargeExchangeMatrix (bᵣ).detDualEquiv.toLinearMap (rayChargeMap s) =
      -chargeExchangeMatrix b.detDualEquiv.toLinearMap (rayChargeMap s) := by
  ext j k
  simp [chargeExchangeMatrix_apply]

variable [Nonempty Φ.cones]

/-- Each determinant character becomes its reciprocal when the basis orientation is
reversed. This comparison uses the same function field of the fan. -/
theorem character_detDualEquiv_reindex_swap (v : N) :
    Φ.character (ofAdd ((bᵣ).detDualEquiv v).toAddMonoidHom) =
      (Φ.character (ofAdd (b.detDualEquiv v).toAddMonoidHom))⁻¹ := by
  have h : ((bᵣ).detDualEquiv v).toAddMonoidHom = -(b.detDualEquiv v).toAddMonoidHom := by
    ext x
    simp
  rw [h, ofAdd_neg, map_inv]

variable (c : Multiplicative (ι → ℤ) →* ℂˣ)

local notation "L" => LaurentRing ℂ ι
local notation "invX" => AddMonoidAlgebra.domCongr ℂ ℂ (AddEquiv.neg (ι →₀ ℤ))

/-- Reversing the basis and inverting the center character has the effect of
inverting all independent X coordinates before evaluating. -/
theorem xEval_reindex_swap :
    Φ.xEval bᵣ s c⁻¹ = (Φ.xEval b s c).comp (invX).toAlgHom := by
  apply LaurentRing.algHom_ext
  intro j
  have hinv :
      Φ.xEval b s c (↑((unitX j : Lˣ)⁻¹) : L) =
        (Φ.xEval b s c (X j))⁻¹ := by
    let f : L →* Φ.algebraicRealization.functionField := Φ.xEval b s c
    simpa only [Units.val_inv_eq_inv_val, Units.coe_map, val_unitX, f,
      AlgHom.coe_toMonoidHom] using (Units.coe_map_inv f (unitX j)).symm
  have hX : (invX) (X j) = (↑((unitX j : Lˣ)⁻¹) : L) := by
    rw [X_def, AddMonoidAlgebra.domCongr_single, AddEquiv.neg_apply, ← Finsupp.single_neg,
      val_inv_unitX]
  rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, hX, hinv, xEval_X, xEval_X]
  simp only [character_detDualEquiv_reindex_swap, MonoidHom.inv_apply,
    Units.val_inv_eq_inv_val, map_inv₀, mul_inv_rev, mul_comm]

/-- Fixed-center X evaluation in the reversed toric presentation equals evaluation
in the original presentation followed by regular inversion on the X torus. -/
theorem xEvaluation_reindex_swap [Finite ι] :
    Φ.xEvaluation bᵣ s c⁻¹ =
      (Φ.xEvaluation b s c).compHom
        (Spec.map (CommRingCat.ofHom (invX).toAlgHom.toRingHom)) := by
  have h (b' : Basis (Fin 2) ℤ N) (c' : Multiplicative (ι → ℤ) →* ℂˣ) :
      Φ.xEvaluation b' s c' = Scheme.RationalMap.ofAffineAlgHom (Φ.xEval b' s c') := by
    apply Scheme.RationalMap.eq_of_fromFunctionField_eq
    simp
  rw [h, h, Scheme.RationalMap.ofAffineAlgHom_compHom, xEval_reindex_swap]

end TauCeti.Toric.Fan
