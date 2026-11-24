/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Chart
public import QPainleve.AlgebraicGeometry.RationalMap.Composition.Defined
public import QPainleve.Geometry.Toric.Fan.Boundary.Transport
public import QPainleve.Geometry.Toric.Fan.Evaluation.ToricIso

/-!
# X evaluation along resolved toric isomorphisms

A specified change between regular toric projections can act by a lattice
equivalence followed by a torus translation. When the ordered presentations
carry the corresponding rays and binomial centers, the independent X map is
the typed relabeling, with the translation absorbed by the center parameters.
The comparison is on the common resolving surface and works for fixed-center
evaluations with nondense image in the X torus.
-/

public section

open AlgebraicGeometry CategoryTheory Module Multiplicative
open QPainleve.Cluster TauCeti.LaurentRing

namespace TauCeti.Toric.FanEquiv

open Fan Scheme.RationalMap

variable {N N' V V' : Type} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}
  [hΦ₀ : Nonempty Φ.cones] [hΨ₀ : Nonempty Ψ.cones]
  {ι : Type} [Fintype ι] [DecidableEq ι]

/-- For a resolved toric isomorphism with a translation, matching the center
rays and the binomial center ideals gives the exchange matrix of the
typed relabeling and its fixed-center X evaluation on the original resolving
surface. The permutation reads target labels in the source ordering. -/
theorem comp_xEvaluation_of_resolved_toric_iso (e : FanEquiv Φ Ψ)
    (hΦ : Φ.IsRegular)
    (b : Basis (Fin 2) ℤ N) (b' : Basis (Fin 2) ℤ N')
    (s : ι → Φ.Ray) (t : ι → Ψ.Ray) (σ : Equiv.Perm ι)
    (c d : Multiplicative (ι → ℤ) →* ℂˣ)
    (χ : Multiplicative (N' →+ ℤ) →* ℂˣ)
    (hray : ∀ j, e.rayEquiv (s (σ j)) = t j)
    (hdet : ∀ x y, b'.detDualEquiv (e.latticeEquiv x) (e.latticeEquiv y) = b.detDualEquiv x y)
    (hc : ∀ j, ((t j).internalCenter b' (d (ofAdd (Pi.single j 1)))).val.comap
      ((e.boundaryIso hΦ₀ hΨ₀).hom ≫ (Ψ.boundaryTranslation χ).hom) =
        ((s (σ j)).internalCenter b (c (ofAdd (Pi.single (σ j) 1)))).val)
    {Z : Scheme} [IsIntegral Z]
    (p : Z ⟶ Φ.algebraicRealization) [IsDominant p]
    (q : Z ⟶ Ψ.algebraicRealization)
    (hpq : p.toRationalMap.comp
      (e.toFanHom.algebraicMap ≫ (Ψ.torusTranslation χ).hom).toRationalMap = q.toRationalMap)
    (B : SkewExchangeMatrix ι)
    (hB : B.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (rayChargeMap s)) :
    letI : q.toRationalMap.IsDominant := hpq ▸ inferInstance
    let w := ((Generator.permute σ).toStep B).toPath
    let a := p.toRationalMap.comp (Φ.xEvaluation b s c)
    ((Generator.permute σ).target B).matrix =
      chargeExchangeMatrix b'.detDualEquiv.toLinearMap (rayChargeMap t) ∧
    ∃ hdom : a.fromFunctionField (IsLocalRing.closedPoint Z.functionField) ∈
        (w.xRationalMap ℂ).domain,
      a.compOfDefined (w.xRationalMap ℂ) hdom =
        q.toRationalMap.comp (Ψ.xEvaluation b' t d) := by
  intro w a
  refine ⟨?_, ?_⟩
  · ext j k
    simp only [Generator.target_permute, SkewExchangeMatrix.reindex_matrix, Equiv.symm_symm,
      Matrix.submatrix_apply, hB, chargeExchangeMatrix_apply, rayChargeMap_single,
      ← hray j, ← hray k, primitiveGenerator_rayEquiv]
    exact (hdet _ _).symm
  let ρ := Spec.map (CommRingCat.ofHom (rename (R := ℂ) σ).toRingHom)
  have hw : w.xRationalMap ℂ = ρ.toRationalMap := Quiver.Path.xRationalMap_permute ℂ B σ
  obtain ⟨hdom, heval⟩ := a.compOfDefined_toRationalMap ρ
  refine ⟨hw.symm ▸ hdom, ?_⟩
  simp only [hw, heval, a, ← comp_compHom]
  have hparam (j : ι) :
      d (ofAdd (Pi.single j 1)) *
        χ (ofAdd (b'.detDualEquiv (t j).primitiveGenerator).toAddMonoidHom) =
        c (ofAdd (Pi.single (σ j) 1)) := by
    have hj := hc j
    rw [← hray j] at hj ⊢
    exact (e.comap_internalCenter_toricIso_eq_iff b b' hdet hΦ (s (σ j)) χ _ _).mp hj
  rw [← e.comp_xEvaluation_of_toric_iso b b' s t σ c d χ hray hdet hparam]
  simp only [← comp_assoc, hpq]

end TauCeti.Toric.FanEquiv
