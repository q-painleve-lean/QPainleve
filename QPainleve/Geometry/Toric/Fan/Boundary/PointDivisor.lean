/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.PointDivisor
public import QPainleve.Geometry.Toric.Fan.Boundary.InternalCenter
public import QPainleve.Geometry.Toric.Fan.Boundary.ProjectiveLine
public import TauCeti.AlgebraicGeometry.LineBundle.Degree
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality
public import TauCeti.AlgebraicGeometry.LineBundle.Pullback
import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.CartierDivisor.Pullback
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.IntersectionNumber.ClosedPoint
import QPainleve.Geometry.Toric.Fan.Boundary.Normalization
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

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry LineBundleClass

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]

section

variable (hΦ : Φ.IsRegular) (ρ : Φ.Ray)
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

end

local notation "C" => Scheme.IdealSheafData.subscheme (Φ.boundaryIdeal inferInstance)

/-- The internal center ideal has degree `-1` on its own ray divisor and degree
`0` on every other ray divisor. -/
theorem Ray.eulerDegree_pullback_internalCenter (ρ : Φ.Ray)
    [PrestableFamily (C ↘ Spec (.of ℂ))] (hΦ : Φ.IsRegular)
    (b : Module.Basis (Fin 2) ℤ N) (τ : Φ.Ray) (c : ℂˣ) :
    eulerDegree ℂ (pullback (τ.boundaryComponentι hΦ)
      (LineBundleClass.mk (ρ.internalCenter b c).property.toInvertibleSheaf)) =
      if ρ = τ then -1 else 0 := by
  classical
  have hdim : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  let := τ.isProper_boundaryComponent_of_prestableFamily hΦ
  have := τ.isCurveOver_boundaryComponent hΦ hdim (b.detDualEquiv_self _)
    (τ.surjective_detCharacter b)
  let z := ρ.binomialCenterOnBoundary hdim (b.detDualEquiv_self _) (ρ.surjective_detCharacter b) c
  have : IsClosedImmersion z := ρ.isClosedImmersion_binomialCenterOnBoundary
    hdim (b.detDualEquiv_self _) (ρ.surjective_detCharacter b) c
  let q := z (IsLocalRing.closedPoint ℂ)
  have hq : IsClosed ({q} : Set C) := by
    have hrange : Set.range z = {q} :=
      Set.range_eq_singleton fun y ↦ congrArg z (Subsingleton.elim y _)
    rw [← hrange]
    exact z.isClosedEmbedding.isClosed_range
  have hJ : (ρ.internalCenter b c).val = ((C).fromSpecResidueField q).ker :=
    (ρ.internalCenter_val b c).trans z.ker_eq_ker_fromSpecResidueField
  have hI : ((C).fromSpecResidueField q).ker.IsEffectiveCartier :=
    hJ ▸ (ρ.internalCenter b c).property
  rw [mk_toInvertibleSheaf_congr _ hI hJ, ← intersectionNumber_def,
    intersectionNumber_mk_ker_fromSpecResidueField (τ.boundaryComponentι hΦ) hq hI]
  have hmem : q ∈ Set.range (τ.boundaryComponentι hΦ) ↔ ρ = τ :=
    ρ.binomialCenterOnBoundary_mem_range_boundaryComponentι_iff hΦ hdim
      (b.detDualEquiv_self _) (ρ.surjective_detCharacter b) c τ
  simp only [hmem]

end TauCeti.Toric.Fan
