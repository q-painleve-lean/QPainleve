/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.ProperIntersection
public import QPainleve.AlgebraicGeometry.Curves.Node.Intersection
public import QPainleve.AlgebraicGeometry.Curves.Node.NumberedPrime
public import QPainleve.AlgebraicGeometry.Modules.Differentials.Canonical

import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.Curves.DualGraph.Cycle.Basic
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced

/-!
# Intersection numbers of nodal divisor components

Two distinct prime components of a nodal Cartier divisor on a smooth projective
surface over an algebraically closed field intersect with multiplicity one at
each common point. Their intersection number therefore counts the common points.
In an anticanonical cycle with at least two components, the two nodes incident
to each component contribute two to its anticanonical degree.
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry LineBundleClass

universe u v

namespace TauCeti.AlgebraicGeometry.Chow

/-- The intersection number of distinct components of a nodal Cartier divisor on
a smooth projective surface over an algebraically closed field counts their common points. -/
theorem classIntersectionNumber_eq_ncard_of_nodal
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
    {D : X.IdealSheafData} (hD : D.IsEffectiveCartier)
    (hnodal : AtWorstNodalOfRelativeDimensionOne (D.subscheme ↘ Spec (.of k)))
    {p q : CodimensionOnePoint X} (hpq : p ≠ q)
    (hp : (p : X) ∈ D.support) (hq : (q : X) ∈ D.support) :
    let : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
    let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
    let : ∀ x : X, IsDomain (X.presheaf.stalk x) := fun x ↦
      letI := isRegularLocalRing_stalk_of_smooth (X ↘ Spec (.of k)) x
      inferInstance
    let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
      (X ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    classIntersectionNumber k X (LineBundleClass.primeDivisorClass p)
      (LineBundleClass.primeDivisorClass q) = (closure {(p : X)} ∩ closure {(q : X)}).ncard := by
  intro _ _ _ _
  have : Nonempty X := ⟨p⟩
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of k)) (n := 2)
  let P := vanishingIdeal ⟨closure {(p : X)}, isClosed_closure⟩
  let Q := vanishingIdeal ⟨closure {(q : X)}, isClosed_closure⟩
  have hP : P.IsEffectiveCartier := isEffectiveCartier_vanishingIdeal_closure_singleton p.property
  have hQ : Q.IsEffectiveCartier := isEffectiveCartier_vanishingIdeal_closure_singleton q.property
  have hPQ := hP.comap_subschemeι_vanishingIdeal_closure_singleton_of_ne hpq.symm
  have hsupport : ((P ⊔ Q).support : Set X) = closure {(p : X)} ∩ closure {(q : X)} := by
    simp only [P, Q, support_sup, Closeds.coe_inf, coe_support_vanishingIdeal, Closeds.coe_mk]
  rw [LineBundleClass.primeDivisorClass_def, LineBundleClass.primeDivisorClass_def, ← hsupport]
  apply classIntersectionNumber_eq_ncard_of_stalkIdeal_sup_eq_maximalIdeal k hdim.le hP hQ hPQ
  intro x hx
  have hx' : x ∈ closure {(p : X)} ∩ closure {(q : X)} :=
    hsupport ▸ (SetLike.mem_coe.mpr hx)
  exact hD.stalkIdeal_sup_eq_maximalIdeal_of_nodal hnodal hpq hp hq
    (specializes_iff_mem_closure.mpr hx'.1) (specializes_iff_mem_closure.mpr hx'.2)

end TauCeti.AlgebraicGeometry.Chow

namespace AlgebraicGeometry.Scheme.NodalCycleNumbering

/-- Distinct numbered components intersect once for each edge joining them.
The two edges of a two-component cycle each contribute one. -/
theorem intersectionBilinForm_boundaryPrime_of_ne
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
    {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ Spec (.of k))]
    {ι : Type v} {p : ι → (D.subscheme ↘ Spec (.of k)).smoothLocus}
    {n : ℕ} [NeZero n] (A : NodalCycleNumbering p n) (hD : D.IsEffectiveCartier)
    {i j : ZMod n} (hij : i ≠ j) :
    letI := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
    letI := (X ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let c : ZMod n → Additive (LineBundleClass X) := fun l ↦
      Additive.ofMul (primeDivisorClass (D.boundaryPrimeEmbedding (A.boundaryPrimeEquiv hD l)))
    Chow.intersectionBilinForm k X (c i) (c j) =
      (if j = i + 1 then 1 else 0) + (if i = j + 1 then 1 else 0) := by
  intros
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let := (X ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let q := D.boundaryPrimeEmbedding ∘ A.boundaryPrimeEquiv hD
  have hq (l : ZMod n) : (q l : X) ∈ D.support :=
    D.range_boundaryPrimeEmbedding.le ⟨A.boundaryPrimeEquiv hD l, rfl⟩
  have h := Chow.classIntersectionNumber_eq_ncard_of_nodal (k := k) hD
    PrestableFamily.atWorstNodalOfRelativeDimensionOne
    ((D.boundaryPrimeEmbedding.injective.comp (A.boundaryPrimeEquiv hD).injective).ne hij)
    (hq i) (hq j)
  simp only [Function.comp_apply, coe_boundaryPrimeEmbedding] at h
  rw [Chow.intersectionBilinForm_apply, toMul_ofMul, toMul_ofMul, h]
  rw [A.closure_boundaryPrime_inter_of_ne hD hij,
    Set.ncard_image_of_injective _ A.ambientNode_injective,
    DualGraph.ncard_cycle_edges_of_ne i j hij]
  simp only [Nat.cast_add, apply_ite ((↑) : ℕ → ℤ), Nat.cast_zero, Nat.cast_one,
    eq_sub_iff_add_eq, (eq_comm : j + 1 = i ↔ i = j + 1)]

variable {k : Type u} [Field k] [IsAlgClosed k]

local notation "S(" k ")" => Spec (CommRingCat.of k)
local notation "K[" k "," X "]" => LineBundleClass.mk (canonicalBundle k X 2)
local notation "g[" k "," X "]" => (X ↘ S(k))

variable {X : Scheme.{u}} [X.Over S(k)] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 g[k,X]]
  {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ S(k))]
  {ι : Type v} {marks : ι → (D.subscheme ↘ S(k)).smoothLocus}
  {n : ℕ} [NeZero n] (A : NodalCycleNumbering marks n) (hD : D.IsEffectiveCartier)

local notation "P[" j "]" => D.boundaryPrimeEmbedding (A.boundaryPrimeEquiv hD j)
local notation "C[" j "]" => Additive.ofMul (primeDivisorClass P[j])
local notation "B[" k "," X "]" => Chow.intersectionBilinForm k X

/-- The anticanonical degree of a component in a cycle of length at least two is
its self-intersection plus two. The two incident nodes contribute separately. -/
theorem intersectionBilinForm_anticanonical_boundaryPrime
    (hcan : LineBundleClass.mk hD.toInvertibleSheaf = K[k,X]) (hn : 1 < n) (j : ZMod n) :
    letI := isNoetherian_of_finiteType g[k,X]
    letI := g[k,X].uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    B[k,X] C[j] (Additive.ofMul K[k,X]⁻¹) = B[k,X] C[j] C[j] + 2 := by
  let : IsNoetherian X := isNoetherian_of_finiteType g[k,X]
  let := g[k,X].uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  classical
  let : IsReduced D.subscheme :=
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := D.subscheme ↘ S(k))).isReduced
  let q := (A.boundaryPrimeEquiv hD).toEmbedding.trans D.boundaryPrimeEmbedding
  have hq (x : CodimensionOnePoint X) : (x : X) ∈ D.support ↔ x ∈ Set.range q := by
    simp only [q, Function.Embedding.coe_trans, Set.range_comp, Equiv.coe_toEmbedding,
      Equiv.range_eq_univ,
      Set.image_univ, D.range_boundaryPrimeEmbedding]
    rfl
  have hsum := hD.ofMul_inv_toInvertibleSheaf_eq_sum_primeDivisorClass q hq
  rw [hcan] at hsum
  have h1 : (1 : ZMod n) ≠ 0 := fun h ↦ (Nat.ne_of_gt hn) (ZMod.one_eq_zero_iff.mp h)
  have hs : j + 1 ≠ j := by simpa using h1
  have hp : j - 1 ≠ j := by simpa using h1
  have hterm (l : ZMod n) (hl : l ∈ Finset.univ.erase j) :
      B[k,X] C[j] C[l] = (if l = j + 1 then 1 else 0) + (if l = j - 1 then 1 else 0) := by
    rw [A.intersectionBilinForm_boundaryPrime_of_ne hD (Finset.ne_of_mem_erase hl).symm]
    simp only [show j = l + 1 ↔ l = j - 1 from eq_comm.trans eq_sub_iff_add_eq.symm]
  rw [hsum, map_sum]
  simp only [q, Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), Finset.sum_congr rfl hterm,
    Finset.sum_add_distrib]
  simp [hs, hp, add_comm]

end AlgebraicGeometry.Scheme.NodalCycleNumbering
