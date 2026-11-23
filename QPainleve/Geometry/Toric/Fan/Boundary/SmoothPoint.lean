/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.InternalCenter

import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.Geometry.Toric.Fan.Boundary.Node
import TauCeti.AlgebraicGeometry.Pullback.Carrier
import TauCeti.AlgebraicGeometry.Scheme.SpecOver

/-!
# Binomial coordinates of smooth toric boundary points

A smooth closed point of a complete regular toric surface boundary lies on a ray orbit.
In its determinant character coordinate, the reduced point ideal is the internal center
with parameter minus the reciprocal of the orbit coordinate.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

variable (b : Module.Basis (Fin 2) ℤ N)

local notation "rankTwo" => (Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2))
local notation "χ(" ρ ")" => LinearMap.toAddMonoidHom (b.detDualEquiv (Ray.primitiveGenerator ρ))

private theorem Ray.exists_binomialCenterOnBoundary_eq_comp_orbitToBoundary (ρ : Φ.Ray)
    (hdim : Module.finrank ℤ N = 2) {m : N →+ ℤ}
    (hm : m ρ.primitiveGenerator = 0) (hprim : Function.Surjective m)
    (q : Spec (.of ℂ) ⟶ Spec (.of (LaurentPolynomial ℂ)))
    (hq : q ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (LaurentPolynomial ℂ))) = 𝟙 _) :
    ∃ a : ℂˣ, ρ.binomialCenterOnBoundary hdim hm hprim a =
      q ≫ ρ.orbitToBoundary hdim hm hprim := by
  let φ : LaurentPolynomial ℂ →ₐ[ℂ] ℂ :=
    Spec.homEquivAlgHom ⟨q, by
      -- Write the structural maps as Spec of their coefficient maps.
      change q ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (LaurentPolynomial ℂ))) =
        Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ))
      simpa only [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id] using hq⟩
  let a := laurentEvalEquiv.symm φ
  have he : Spec.map (CommRingCat.ofHom (laurentEval a).toRingHom) = q := by
    rw [laurentEval_laurentEvalEquiv_symm, ← Spec.homEquivAlgHom_symm_apply_val]
    exact congrArg Subtype.val (Spec.homEquivAlgHom.symm_apply_apply _)
  refine ⟨(-a)⁻¹, ?_⟩
  rw [Ray.binomialCenterOnBoundary_def, inv_inv, ← neg_eq_neg_one_mul, neg_neg, he]

/-- The reduced ideal of a smooth closed point of a complete regular toric boundary
is a binomial center ideal in any chosen oriented lattice basis. -/
theorem exists_internalCenter_eq_ker_fromSpecResidueField
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (p : (Φ.boundaryIdeal hc.nonempty_cones).subscheme) (hp : IsClosed ({p} : Set _))
    (hs : (((Φ.boundaryIdeal hc.nonempty_cones).subschemeι ≫
      Φ.algebraicRealizationStructureMap).stalkMap p).hom.FormallySmooth) :
    let := hc.nonempty_cones
    ∃ (ρ : Φ.Ray) (a : ℂˣ),
      (ρ.internalCenter b a).val =
        ((Φ.boundaryIdeal hc.nonempty_cones).subscheme.fromSpecResidueField p).ker := by
  let := hc.nonempty_cones
  let D := Φ.boundaryIdeal hc.nonempty_cones
  let s := D.subschemeι ≫ Φ.algebraicRealizationStructureMap
  have hnodal := Φ.atWorstNodalOfRelativeDimensionOne_boundary hΦ hc rankTwo
  have := hnodal.syntomic
  have : IsReduced D.subscheme := by
    dsimp only [D]
    rw [Φ.boundaryIdeal_def]
    infer_instance
  have hnot : ¬ D.IsNodeOfReducedBoundary Φ.algebraicRealizationStructureMap (D.subschemeι p) := by
    rw [D.isNodeOfReducedBoundary_iff_of_isReduced]
    rintro ⟨z, hz, hn⟩
    exact hn.not_formallySmooth_stalkMap ((D.subschemeι.isClosedEmbedding.injective hz).symm ▸ hs)
  have hx : D.subschemeι p ∈ D.support := by
    rw [← SetLike.mem_coe, ← D.range_subschemeι]
    exact Set.mem_range_self p
  obtain ⟨ρ, hρ⟩ := Φ.exists_mem_range_rayChart_of_not_isNodeOfReducedBoundary hΦ hc rankTwo hx hnot
  have hm : χ(ρ) ρ.primitiveGenerator = 0 := b.detDualEquiv_self _
  let j := ρ.orbitToBoundary rankTwo hm (ρ.surjective_detCharacter b)
  have hj : p ∈ Set.range j := by
    rw [Scheme.Pullback.range_snd_of_isPullback
      (ρ.isPullback_orbitToBoundary rankTwo hm (ρ.surjective_detCharacter b))]
    exact hρ
  let f := pointOfClosedPoint s p hp
  have hf : Set.range f ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    simpa [f] using hj
  let q := IsOpenImmersion.lift j f hf
  have hq : q ≫ j = f := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨a, ha⟩ := ρ.exists_binomialCenterOnBoundary_eq_comp_orbitToBoundary rankTwo hm
    (ρ.surjective_detCharacter b) q (by
      have hbase : j ≫ D.subschemeι ≫ Φ.algebraicRealizationStructureMap = _ :=
        ρ.orbitToBoundary_comp_algebraicRealizationStructureMap rankTwo hm
          (ρ.surjective_detCharacter b)
      rw [← hbase, ← Category.assoc, hq]
      exact pointOfClosedPoint_comp s p hp)
  refine ⟨ρ, a, ?_⟩
  rw [Ray.internalCenter_val, ha, hq, f.ker_eq_ker_fromSpecResidueField]
  exact congrArg (fun x ↦ (D.subscheme.fromSpecResidueField x).ker)
    (pointOfClosedPoint_apply s p hp (IsLocalRing.closedPoint ℂ))

end TauCeti.Toric.Fan
