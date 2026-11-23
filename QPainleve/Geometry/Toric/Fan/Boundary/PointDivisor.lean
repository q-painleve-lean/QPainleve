/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.PointDivisor
public import QPainleve.Geometry.Toric.Fan.Boundary.ProjectiveLine
public import TauCeti.AlgebraicGeometry.LineBundle.Pullback
import QPainleve.AlgebraicGeometry.CartierDivisor.Pullback
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange

/-!
# Binomial point divisors on toric boundary components

In the projective coordinate on a proper ray divisor, the restricted ideal of a
binomial center with parameter `c` is cut out by `X₀ + c⁻¹ X₁`. This identifies the
ideal entering the boundary period calculation with the section whose values can
be compared at the two toric nodes.

See [Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*,
Proposition 2.9](https://arxiv.org/html/1211.6367v5#S2).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] (hΦ : Φ.IsRegular) (ρ : Φ.Ray)
  (hdim : Module.finrank ℤ N = 2) {m : N →+ ℤ}
  (hm : m ρ.primitiveGenerator = 0) (hprim : Function.Surjective m)
  [IsProper ((Φ.rayBoundaryIdeal hΦ ρ).subscheme ↘ Spec (.of ℂ))]

/-- Restrict the binomial center ideal on the full toric boundary to its own ray.
It is the zero ideal of the pullback of the section `X₀ + c⁻¹ X₁` of `𝒪(1)`. -/
theorem Ray.comap_ker_binomialCenterOnBoundary_eq_zeroIdeal (c : ℂˣ) :
    let e := ρ.boundaryIsoProjectiveLine hΦ hdim hm hprim
    let L := Proj.symmetricAlgebraTwistingBundle ℂ (Fin 2 → ℂ) 1
    (ρ.binomialCenterOnBoundary hdim hm hprim c).ker.comap (ρ.boundaryComponentι hΦ) =
      ((InvertibleSheaf.pullback e.hom).obj L).zeroIdeal
        (e.hom.pullbackSections L.obj ⊤ (projectiveLine.binomialSection ℂ (↑c⁻¹ : ℂ))) := by
  dsimp only
  let p := ρ.binomialCenterOnComponent hΦ hdim hm hprim c
  let e := ρ.boundaryIsoProjectiveLine hΦ hdim hm hprim
  have hp : p ≫ e.hom = projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) 0 (-(c : ℂ)) := by
    have h :=
      projectiveLine.polynomialPoint_rev (RingHom.id ℂ) 1 ((-1 : ℂˣ) * c⁻¹)
    rw [ρ.binomialCenterOnComponent_comp_boundaryIsoProjectiveLine hΦ hdim hm hprim c]
    simpa using h
  rw [← ρ.binomialCenterOnComponent_boundaryComponentι hΦ hdim hm hprim c,
    Scheme.Hom.comap_ker_comp_of_isClosedImmersion,
    InvertibleSheaf.zeroIdeal_pullbackSections, projectiveLine.zeroIdeal_binomialSection ℂ c⁻¹]
  simp only [inv_inv]
  rw [← hp, Scheme.Hom.comap_ker_comp_of_isClosedImmersion]

end TauCeti.Toric.Fan
