/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Center
public import QPainleve.Geometry.Toric.Fan.Ruling.Basic

/-!
# Binomial centers in ruling fibers

A boundary center defined by a binomial in the ruling character maps to the corresponding
point of the projective line. This identifies the fiber that passes through the center of
an elementary transformation, as in Gross, Hacking and Keel,
*Birational geometry of cluster algebras*, §3.1.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative
open TauCeti.AlgebraicGeometry (projectiveLine)

namespace TauCeti.Toric.Fan.Ray

variable (K : Type) [Field K] {N V : Type} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} {Φ : Fan i} {m : N →+ ℤ}
  (h : ∀ σ : Φ.cones, (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter m x) ∨
    ∀ x ∈ σ.val, Φ.lattice.realCharacter m x ≤ 0)

/-- The binomial boundary center is in the ruling fiber at the affine coordinate
`-c⁻¹`. The equality holds for the section of the coefficient field. -/
theorem binomialCenter_comp_characterRuling (ρ : Φ.Ray)
    (hdim : Module.finrank ℤ N = 2)
    (hm : m ρ.primitiveGenerator = 0) (hprim : Function.Surjective m) (c : Kˣ) :
    ρ.binomialCenter K hdim hm hprim c ≫ Φ.characterRuling K m h =
      projectiveLine.polynomialPoint K (RingHom.id K) 0 (-(↑c⁻¹ : K)) := by
  have hm' : (if (0 : Fin 2) = 0 then m else -m) ∈
      dualSemigroup Φ.lattice ρ.toCone.val := by
    simpa only [ite_true, ρ.coe_chartCharacter] using (ρ.chartCharacter hm).property
  rw [ρ.binomialCenter_def, Category.assoc, Φ.affineToricChartι_comp_characterRuling K m h ρ.toCone
    0 hm', projectiveLine.polynomialPoint_def, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  let e := ρ.binomialCenterEval K hdim hm hprim c
  have hχ : (⟨_, hm'⟩ : dualSemigroup Φ.lattice ρ.toCone.val) = ρ.chartCharacter hm :=
    Subtype.ext (by simp)
  have he : e.comp (Polynomial.aeval
      (AddMonoidAlgebra.single (⟨_, hm'⟩ : dualSemigroup Φ.lattice ρ.toCone.val) (1 : K))) =
      Polynomial.aeval (-(↑c⁻¹ : K)) := by
    apply Polynomial.algHom_ext
    rw [hχ]
    simp [e, ρ.binomialCenterEval_character K hdim hm hprim c]
  exact congrArg (fun φ : Polynomial K →+* K ↦
    Spec.map (CommRingCat.ofHom φ) ≫ projectiveLine.polynomialChartι K 0)
    (congrArg AlgHom.toRingHom he)

end TauCeti.Toric.Fan.Ray
