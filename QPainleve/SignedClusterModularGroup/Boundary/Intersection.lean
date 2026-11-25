/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import QPainleve.AlgebraicGeometry.Chow.NodalIntersection
public import QPainleve.AlgebraicGeometry.Chow.Nef.Basic
import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.Curves.DualGraph.Cycle.Basic
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.Scheme.DiscreteValuationStalk

/-!
# Intersection form of a nef square-zero boundary cycle

An ordered cycle of the components of a nodal Cartier divisor has its off-diagonal
intersections given by the nodes between those components. When the total divisor is
nef of square zero, its intersection with each component vanishes. The resulting
Picard Gram matrix is the negative cycle Laplacian, including the single-component
and two-component cycles.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData LinearMap

universe u

namespace QPainleve.BoundaryCycle

variable {n : ℕ}

variable [NeZero n] {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "B" => Chow.intersectionBilinForm k X
local notation "D(" p ")" => Additive.ofMul (LineBundleClass.primeDivisorClass p)
local notation "cl" => Scheme.CartierDivisor.weilToLineBundleClassHom X

/-- In a nef, square-zero nodal Cartier divisor with cyclically labelled components
and nodes, the Picard intersection form on the component classes is the negative
cycle Laplacian. For distinct components, the incidence condition specifies the
actual points common to their supports. The two cyclic incidences are counted
separately, so the formula also holds for one component or two components. -/
theorem intersectionBilinForm_eq_of_nodal_cycle {I : X.IdealSheafData}
    (hI : I.IsEffectiveCartier)
    (hnodal : AtWorstNodalOfRelativeDimensionOne (I.subscheme ↘ Spec (.of k)))
    (hnef : ((LineBundleClass.mk hI.toInvertibleSheaf)⁻¹).IsNef k (X ↘ Spec (.of k)))
    (hsq : Chow.classIntersectionNumber k X (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹
      (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹ = 0)
    (p : ZMod n ↪ CodimensionOnePoint X) (node : ZMod n ↪ X)
    (hp : ∀ q : CodimensionOnePoint X, (q : X) ∈ I.support ↔ q ∈ Set.range p)
    (hinc : ∀ i j, i ≠ j →
      closure {(p i : X)} ∩ closure {(p j : X)} =
        node '' {e | (e = i ∧ j = i + 1) ∨ (e = j ∧ i = j + 1)}) :
    let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
    let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
      (X ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    ∀ i j : ZMod n, B (D(p i)) (D(p j)) =
      (-2 : ℤ) * (if i = j then 1 else 0) +
        (if j = i + 1 then 1 else 0) + (if j = i - 1 then 1 else 0) := by
  intro _ _
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
  have : IsNormalScheme X := IsNormalScheme.of_uniqueFactorizationMonoid_stalk
  let : IsReduced I.subscheme := hnodal.isReduced
  let : ∀ q : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (q : X)) :=
    fun q ↦ IsNormalScheme.isDiscreteValuationRing_stalk q.val q.property
  let W := hI.toCartierDivisor.toWeilDivisor
  have hW : 0 ≤ W :=
    (Scheme.CartierDivisor.isEffective_iff_toWeilDivisor_nonneg _).mp
      hI.isEffective_toCartierDivisor
  have hclass : cl W = Additive.ofMul (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹ := by
    dsimp only [W]
    rw [Scheme.CartierDivisor.weilToLineBundleClassHom_toWeilDivisor,
      hI.toLineBundleClass_toCartierDivisor]
  have hsumClass := hclass.trans (hI.ofMul_inv_toInvertibleSheaf_eq_sum_primeDivisorClass p hp)
  have hmem (i : ZMod n) : p i ∈ W.support := by
    rw [Finsupp.mem_support_iff, ← WeilDivisor.coeff]
    exact fun hz ↦ (hI.coeff_toWeilDivisor_eq_zero_iff (p i)).mp hz ((hp _).mpr
      (Set.mem_range_self i))
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of k)) (n := 2)
  have hzero (i : ZMod n) : B (D(p i)) (∑ j, D(p j)) = 0 := by
    rw [← hsumClass, Chow.intersectionBilinForm_apply, toMul_ofMul,
      Chow.classIntersectionNumber_comm]
    apply (Chow.classIntersectionNumber_weilToLineBundleClassHom_self_eq_zero_iff k hdim hW
      (by simpa only [hclass, toMul_ofMul] using hnef)).mp
      (by simpa only [hclass, toMul_ofMul] using hsq) _ (hmem i)
  let F (i j : ZMod n) : ℤ := -2 * (if i = j then 1 else 0) +
    (if j = i + 1 then 1 else 0) + (if j = i - 1 then 1 else 0)
  have hoff (i j : ZMod n) (hij : i ≠ j) : B (D(p i)) (D(p j)) = F i j := by
    rw [Chow.intersectionBilinForm_apply, toMul_ofMul, toMul_ofMul,
      Chow.classIntersectionNumber_eq_ncard_of_nodal hI hnodal (p.injective.ne hij)
        ((hp _).mpr (Set.mem_range_self i)) ((hp _).mpr (Set.mem_range_self j)),
      hinc i j hij, Set.ncard_image_of_injective _ node.injective,
      DualGraph.ncard_cycle_edges_of_ne i j hij]
    simp [F, hij, apply_ite ((↑) : ℕ → ℤ)]
  intro i j
  by_cases hij : i = j
  · subst j
    -- The off-diagonal entries agree, and both rows sum to zero.
    have hsumF : ∑ l, F i l = 0 := by
      simp [F, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']
    have hsum : ∑ l, (B (D(p i)) (D(p l)) - F i l) = 0 := by
      rw [Finset.sum_sub_distrib, ← BilinForm.sum_right, hzero, hsumF, sub_zero]
    have hsingle := Finset.sum_eq_single i
      (s := Finset.univ) (f := fun l ↦ B (D(p i)) (D(p l)) - F i l)
      (fun l _ hli ↦ sub_eq_zero.mpr (hoff i l hli.symm)) (by simp)
    exact sub_eq_zero.mp (hsingle.symm.trans hsum)
  · exact hoff i j hij

end QPainleve.BoundaryCycle
