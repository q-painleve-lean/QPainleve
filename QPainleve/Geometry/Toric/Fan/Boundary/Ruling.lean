/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Center
public import QPainleve.Geometry.Toric.Fan.Ruling

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

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {Φ : Fan i} {m : N →+ ℤ}
  (h : ∀ σ : Φ.cones, (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter m x) ∨
    ∀ x ∈ σ.val, Φ.lattice.realCharacter m x ≤ 0)

/-- The binomial boundary center is in the ruling fiber at the affine coordinate
`-c⁻¹`. This equality is between the complex points as scheme morphisms. -/
theorem binomialCenter_comp_characterRuling (ρ : Φ.Ray)
    (hdim : Module.finrank ℤ N = 2)
    (hm : m ρ.primitiveGenerator = 0) (hprim : Function.Surjective m) (c : ℂˣ) :
    ρ.binomialCenter hdim hm hprim c ≫ Φ.characterRuling m h =
      projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) 0 (-(↑c⁻¹ : ℂ)) := by
  have hm' : (if (0 : Fin 2) = 0 then m else -m) ∈
      dualSemigroup Φ.lattice ρ.toCone.val := by
    simpa only [ite_true, ρ.coe_chartCharacter] using (ρ.chartCharacter hm).property
  rw [ρ.binomialCenter_def, Category.assoc, Φ.affineToricChartι_comp_characterRuling m h ρ.toCone
    0 hm', projectiveLine.polynomialPoint_def, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  let e := ρ.binomialCenterEval hdim hm hprim c
  have hχ : (⟨_, hm'⟩ : dualSemigroup Φ.lattice ρ.toCone.val) = ρ.chartCharacter hm :=
    Subtype.ext (by simp)
  have he : e.comp (Polynomial.aeval (MonoidAlgebra.of ℂ _ (ofAdd ⟨_, hm'⟩))) =
      Polynomial.aeval (-(↑c⁻¹ : ℂ)) := by
    apply Polynomial.algHom_ext
    rw [hχ]
    simp [e, MonoidAlgebra.of_apply]
  exact congrArg (fun φ : Polynomial ℂ →+* ℂ ↦
    Spec.map (CommRingCat.ofHom φ) ≫ projectiveLine.polynomialChartι ℂ 0)
    (congrArg AlgHom.toRingHom he)

end TauCeti.Toric.Fan.Ray
