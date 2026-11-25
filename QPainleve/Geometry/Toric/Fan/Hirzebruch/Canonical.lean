/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Hirzebruch
public import QPainleve.Geometry.Toric.Fan.Boundary.Node

import QPainleve.AlgebraicGeometry.CartierDivisor.Support

/-!
# The anticanonical boundary of a Hirzebruch fan

The reduced toric boundary on a Hirzebruch surface represents the anticanonical
class. In the fiber–section basis the sum of the ray classes has coordinates
`(e + 2, 2)`.
-/

public section

open AlgebraicGeometry Module TauCeti.AlgebraicGeometry LineBundleClass
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones]
  (b : Basis (Fin 2) ℤ N) (e : ℤ) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])

local notation "X" => Φ.algebraicRealization
local notation "S" => Spec (CommRingCat.of ℂ)
local notation "D" => Φ.boundaryIdeal h₀
local notation "C" => hirzebruchPicardBasis b e hΦ r hr
local notation "P" j:arg => Additive.ofMul (primeDivisorClass (Φ.rayBoundaryPoint hΦ (r j)))

variable [Φ.algebraicRealization.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ Spec (CommRingCat.of ℂ))]

include b e hΦ hc r hr in
/-- The Cartier ideal of the full reduced boundary represents the canonical
line bundle of a complete regular Hirzebruch fan. -/
theorem mk_toInvertibleSheaf_boundaryIdeal_eq_mk_canonicalBundle_of_hirzebruch
    (hD : (D).IsEffectiveCartier) :
    LineBundleClass.mk hD.toInvertibleSheaf =
      LineBundleClass.mk (QPainleve.canonicalBundle ℂ X 2) := by
  classical
  let := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  have : IsReduced (D).subscheme := by
    rw [boundaryIdeal_def]
    infer_instance
  let p := r.toEmbedding.trans ⟨Φ.rayBoundaryPoint hΦ, Φ.rayBoundaryPoint_injective hΦ⟩
  have hp (q : CodimensionOnePoint X) : q.val ∈ (D).support ↔ q ∈ Set.range p := by
    -- The support formula uses the underlying set of the closed support.
    change q.val ∈ ((D).support : Set X) ↔ q ∈ Set.range p
    simp only [p, Function.Embedding.coe_trans, Function.Embedding.coeFn_mk,
      Set.range_comp, Equiv.range_eq_univ, Set.image_univ, Φ.range_rayBoundaryPoint hΦ h₀,
      support_boundaryIdeal, Set.mem_compl_iff, Set.mem_ofPred_eq]
  have hD' := hD.ofMul_inv_toInvertibleSheaf_eq_sum_primeDivisorClass p hp
  have hS := hirzebruch_section_coordinates b e hΦ r hr
  have hS' := hirzebruch_opposite_section_coordinates b e hΦ r hr
  have hF : P 1 = (C) 0 := by
    rw [hirzebruchPicardBasis_apply_zero, rayDivisorToPicard_single, one_smul]
  have hF' : P 3 = (C) 0 := by
    rw [hirzebruchPicardBasis_apply_zero_eq_ray_three, rayDivisorToPicard_single, one_smul]
  have hK := hirzebruch_anticanonical_coordinates b e hΦ r hr hc
  have hEq : Additive.ofMul (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹ =
      -Additive.ofMul (LineBundleClass.mk (QPainleve.canonicalBundle ℂ X 2)) := by
    apply (C).repr.injective
    rw [hD', map_sum, Fin.sum_univ_four]
    simp only [p, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
      Function.Embedding.coeFn_mk]
    rw [hF, hF', Basis.repr_self]
    apply Finsupp.ext
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · simp only [Finsupp.add_apply, hS.1, hS'.1, hK.1, Finsupp.single_eq_same]
      omega
    · simp only [Finsupp.add_apply, hS.2, hS'.2, hK.2,
        Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0)]
      omega
  exact inv_injective (Additive.ofMul.injective hEq)

end TauCeti.Toric.Fan
