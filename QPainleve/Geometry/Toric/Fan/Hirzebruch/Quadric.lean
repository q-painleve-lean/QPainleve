/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Primes
public import QPainleve.AlgebraicGeometry.Modules.Differentials.Canonical
public import QPainleve.Geometry.Toric.Fan.Ruling.Hirzebruch.Prime
public import QPainleve.Geometry.Toric.Fan.Ruling.Quadric

import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.BoundaryPrimes
import QPainleve.Geometry.Toric.Fan.Hirzebruch.Anticanonical
import QPainleve.Geometry.Toric.Fan.Hirzebruch.Bisection
import QPainleve.Geometry.Toric.Fan.Picard.Quadric

/-!
# Anticanonical bisections on the toric quadric

If a reduced anticanonical divisor contains a bisection and a second component,
exchanging the rulings exhibits both components as sections. For a nodal boundary
this gives the ruling used for the next elementary transformation in
[Gross, Hacking and Keel, Proposition 1.3, Case II][GHK].

[GHK]: https://arxiv.org/html/1106.4977v3#S1.Thmproposition3
-/

public section

open AlgebraicGeometry CategoryTheory Module TopologicalSpace
open Scheme.IdealSheafData TauCeti.AlgebraicGeometry LineBundleClass

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]
  (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])

local notation "X" => Fan.algebraicRealization Φ
local notation "S" => Spec (CommRingCat.of ℂ)
local notation "C" => Fan.hirzebruchPicardBasis b 0 hΦ r hr
local notation "P" p:arg => Additive.ofMul
  (@primeDivisorClass X _ _ (Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ) p)
local notation "I[" p "]" => vanishingIdeal (Closeds.mk (closure {(p : X)}) isClosed_closure)
local notation "q" =>
  Fan.characterRuling Φ (LinearMap.toAddMonoidHom (Basis.coord b 1))
    (nonneg_or_nonpos_hirzebruch_ruling_character b 0 r hr)
local notation "q'" =>
  Fan.characterRuling Φ (LinearMap.toAddMonoidHom (Basis.coord b 0))
    (nonneg_or_nonpos_quadric_transverse_character b r hr)
local notation "b'" => Basis.reindex b (Equiv.swap 0 1)
local notation "r'" => Equiv.trans (Equiv.trans (Equiv.swap (0 : Fin 4) 1) (Equiv.swap 2 3)) r
local notation "hr'" => quadric_swapped_generators b r hr
local notation "C'" => Fan.hirzebruchPicardBasis b' 0 hΦ r' hr'

variable [Φ.algebraicRealization.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ S)]

include hc in
private theorem quadric_bisection_fiberCoeff_pos (p : CodimensionOnePoint X)
    (hp : (C).repr (P p) 1 = 2) : 0 < (C).repr (P p) 0 := by
  by_contra! h
  have hnonneg := hirzebruch_fiber_coeff_nonneg b 0 hΦ r hr hc le_rfl p
  have hz : (C').repr (P p) 1 = 0 := by
    rw [hirzebruchPicardBasis_quadric_swap b hΦ r hr, Basis.repr_reindex_apply]
    simpa using le_antisymm h hnonneg
  obtain ⟨_, _, hclass, _⟩ := exists_hirzebruch_ruling_fiber_of_degree_zero b' 0 hΦ hc r' hr' p hz
  rw [hirzebruchPicardBasis_quadric_swap b hΦ r hr, Basis.reindex_apply] at hclass
  rw [hclass, show (Equiv.swap (0 : Fin 2) 1).symm 0 = 1 by decide, Basis.repr_self] at hp
  simp at hp

variable {D : Φ.algebraicRealization.IdealSheafData} [AlgebraicGeometry.IsReduced D.subscheme]
  (hD : D.IsEffectiveCartier)

local notation "p[" j "]" => D.boundaryPrimeEmbedding j
local notation "a[" j "]" => Basis.repr (C) (P p[j]) 0
local notation "d[" j "]" => Basis.repr (C) (P p[j]) 1

include hc hD in
private theorem quadric_bisection_components
    (hK : LineBundleClass.mk hD.toInvertibleSheaf =
      LineBundleClass.mk (QPainleve.canonicalBundle ℂ X 2)) {s t : D.boundaryPrimes}
    (hs : d[s] = 2) (hst : s ≠ t) (hta : a[t] = 1)
    (hvertical : ∀ j : D.boundaryPrimes, j ≠ s → d[j] = 0) :
    a[s] = 1 ∧ (∀ j : D.boundaryPrimes, j = s ∨ j = t) := by
  classical
  let : Fintype D.boundaryPrimes := hD.finite_boundaryPrimes.fintype
  have hpos := quadric_bisection_fiberCoeff_pos b hΦ hc r hr p[s] hs
  let A : Finset D.boundaryPrimes := Finset.univ.erase s
  let R := A.erase t
  have ht : t ∈ A := by simp [A, hst.symm]
  have hsum : (∑ j ∈ R, a[j]) + a[t] + a[s] = 2 := calc
    _ = (∑ j ∈ A, a[j]) + a[s] :=
      congrArg (· + a[s]) (Finset.sum_erase_add A (fun j ↦ a[j]) ht)
    _ = ∑ j : D.boundaryPrimes, a[j] :=
      Finset.sum_erase_add Finset.univ (fun j ↦ a[j]) (Finset.mem_univ s)
    _ = 2 := by simpa only [Matrix.cons_val_zero, zero_add] using
      sum_hirzebruch_boundary_prime_coordinates b 0 hΦ hc r hr hD hK 0
  have hnonneg (j : D.boundaryPrimes) : 0 ≤ a[j] :=
    hirzebruch_fiber_coeff_nonneg b 0 hΦ r hr hc le_rfl p[j]
  have hrest := Finset.sum_nonneg (fun j (_ : j ∈ R) ↦ hnonneg j)
  have hzero : ∑ j ∈ R, a[j] = 0 := by omega
  refine ⟨by omega, fun j ↦ ?_⟩
  by_contra! hj
  have hjR : j ∈ R := by simp [R, A, hj.1, hj.2]
  have hjzero := (Finset.sum_eq_zero_iff_of_nonneg (fun u _ ↦ hnonneg u)).mp hzero j hjR
  have hjpos := hirzebruch_fiber_coeff_pos_of_degree_zero b 0 hΦ r hr hc le_rfl p[j]
    (hvertical j hj.1)
  omega

include hc hD in
/-- On the toric quadric, a reduced anticanonical divisor with a bisection and
another prime is the bisection plus a single scheme-theoretic fiber. Both
components map isomorphically to the base of the transverse ruling. -/
theorem quadric_bisection_transverse_sections
    (hK : LineBundleClass.mk hD.toInvertibleSheaf =
      LineBundleClass.mk (QPainleve.canonicalBundle ℂ X 2))
    {s t : D.boundaryPrimes} (hs : d[s] = 2) (hst : s ≠ t) :
    IsIso (I[p[s]].subschemeι ≫ q') ∧ IsIso (I[p[t]].subschemeι ≫ q') ∧
    ∃ y : S ⟶ projectiveLine ℂ,
      y ≫ (projectiveLine ℂ ↘ S) = 𝟙 S ∧ I[p[t]] = y.ker.comap q ∧
      D = I[p[s]] * (y.ker.comap q) := by
  have hvertical (j : D.boundaryPrimes) (hj : j ≠ s) : d[j] = 0 :=
    hirzebruch_boundary_prime_degree_eq_zero_of_bisection b 0 hΦ hc r hr hD hK hs hj
  obtain ⟨y, hy, hclass, hf⟩ :=
    exists_hirzebruch_ruling_fiber_of_degree_zero b 0 hΦ hc r hr p[t] (hvertical t hst.symm)
  have ht : a[t] = 1 := by rw [hclass, Basis.repr_self, Finsupp.single_eq_same]
  obtain ⟨ha, hall⟩ := quadric_bisection_components b hΦ hc r hr hD hK hs hst ht hvertical
  have hsection (j : D.boundaryPrimes) (hj : a[j] = 1) : IsIso (I[p[j]].subschemeι ≫ q') := by
    rw [← characterRuling_quadric_swap b r hr]
    apply isIso_hirzebruch_ruling_prime_of_degree_one b' 0 hΦ hc r' hr'
    rw [hirzebruchPicardBasis_quadric_swap b hΦ r hr, Basis.repr_reindex_apply]
    exact hj
  refine ⟨hsection s ha, hsection t ht, y, hy, hf, ?_⟩
  let := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  rw [← hf]
  simpa only [coe_boundaryPrimeEmbedding] using hD.eq_mul_vanishingIdeal_of_boundaryPrimes hst hall

end TauCeti.Toric.Fan
