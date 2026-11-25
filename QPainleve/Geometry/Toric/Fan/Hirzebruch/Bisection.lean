/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Contraction
public import QPainleve.Geometry.Toric.Fan.Hirzebruch.Anticanonical
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Basic

import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.BoundaryPrimes
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Integral
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Smooth
import QPainleve.Geometry.Toric.Fan.StarSubdivision.ProjectivePlane
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.RationalPoint.Basic

/-!
# Anticanonical bisections on Hirzebruch surfaces

A degree-two boundary component uses the whole fiber degree of the
anticanonical class. Each remaining prime is vertical and contributes at
least one to the fiber coefficient. Intersecting the bisection with the
distinguished section bounds the index of the ruled surface.

For index one with a second component, the bisection is disjoint from the
negative section and the second component is a single scheme-theoretic fiber.
This is the contraction case in [Gross, Hacking and Keel, Proposition 1.3][GHK].

[GHK]: https://arxiv.org/html/1106.4977v3#S1.Thmproposition3
-/

public section

open AlgebraicGeometry CategoryTheory Module TopologicalSpace
open TauCeti.AlgebraicGeometry LineBundleClass
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]
  (b : Basis (Fin 2) ℤ N) (e : ℤ) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])

local notation "X" => Fan.algebraicRealization Φ
local notation "S" => Spec (CommRingCat.of ℂ)
local notation "C" => Fan.hirzebruchPicardBasis b e hΦ r hr
local notation "P" p:arg =>
  Additive.ofMul
    (@primeDivisorClass X _ _ (Fan.uniqueFactorizationMonoid_stalk_algebraicRealization Φ hΦ) p)
local notation "S₀" => Fan.rayBoundaryPoint Φ hΦ (r 0)
local notation "I[" p "]" => vanishingIdeal (Closeds.mk (closure {(p : X)}) isClosed_closure)
local notation "q" => Fan.characterRuling Φ (LinearMap.toAddMonoidHom (Basis.coord b 1))
  (nonneg_or_nonpos_hirzebruch_ruling_character b e r hr)

variable [(Φ.algebraicRealization).IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ Spec (CommRingCat.of ℂ))]

variable {D : Φ.algebraicRealization.IdealSheafData} [AlgebraicGeometry.IsReduced (subscheme D)]
  (hD : D.IsEffectiveCartier) (hK : LineBundleClass.mk hD.toInvertibleSheaf =
    LineBundleClass.mk (QPainleve.canonicalBundle ℂ Φ.algebraicRealization 2))

local notation "p[" j "]" => boundaryPrimeEmbedding D j
local notation "a[" j "]" => Basis.repr (C) (P p[j]) 0
local notation "d[" j "]" => Basis.repr (C) (P p[j]) 1

include hc hK in
/-- Every other component of a reduced anticanonical divisor containing a
bisection has fiber degree zero. -/
theorem hirzebruch_boundary_prime_degree_eq_zero_of_bisection
    {s : D.boundaryPrimes} (hs : d[s] = 2) {t : D.boundaryPrimes} (ht : t ≠ s) :
    d[t] = 0 := by
  classical
  let : Fintype D.boundaryPrimes := hD.finite_boundaryPrimes.fintype
  have hsum : ∑ j : D.boundaryPrimes, d[j] = 2 :=
    sum_hirzebruch_boundary_prime_coordinates b e hΦ hc r hr hD hK 1
  have hrest := Finset.sum_erase_add Finset.univ (fun j ↦ d[j]) (Finset.mem_univ s)
  rw [hsum, hs] at hrest
  have hzero : ∑ j ∈ Finset.univ.erase s, d[j] = 0 := by omega
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦
    hirzebruch_fiber_degree_nonneg b e hΦ r hr hc p[j])).mp hzero t (by simp [ht])

include hc hK in
private theorem hirzebruch_bisection_fiber_coeff_le_of_components
    (he : 0 ≤ e) (s : D.boundaryPrimes)
    (hvertical : ∀ j : D.boundaryPrimes, j ≠ s → d[j] = 0) :
    a[s] + (D.boundaryPrimes.ncard : ℤ) ≤ e + 3 := by
  classical
  let : Fintype D.boundaryPrimes := hD.finite_boundaryPrimes.fintype
  let A : Finset D.boundaryPrimes := Finset.univ.erase s
  have hsum : ∑ j : D.boundaryPrimes, a[j] = e + 2 :=
    sum_hirzebruch_boundary_prime_coordinates b e hΦ hc r hr hD hK 0
  have hrest : (∑ j ∈ A, a[j]) + a[s] = e + 2 :=
    (Finset.sum_erase_add Finset.univ (fun j ↦ a[j]) (Finset.mem_univ s)).trans hsum
  have hle : (A.card : ℤ) ≤ ∑ j ∈ A, a[j] := by
    calc
      (A.card : ℤ) = ∑ _j ∈ A, (1 : ℤ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun j hj ↦
        hirzebruch_fiber_coeff_pos_of_degree_zero b e hΦ r hr hc he p[j]
          (hvertical j (Finset.mem_erase.mp hj).1)
  have hcard : A.card + 1 = D.boundaryPrimes.ncard := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card, ← Finset.card_univ]
    exact Finset.card_erase_add_one (Finset.mem_univ s)
  omega

include hc hK in
/-- A bisection in a reduced anticanonical boundary has nonnegative
intersection with the distinguished section. Its fiber coefficient plus the
number of other components is at most `e + 2`. In particular the index plus
the number of other components is at most two. -/
theorem hirzebruch_anticanonical_bisection (he : 0 ≤ e)
    (s : D.boundaryPrimes) (hs : d[s] = 2) :
    0 ≤ a[s] - 2 * e ∧ a[s] + (D.boundaryPrimes.ncard : ℤ) ≤ e + 3 ∧
      e + (D.boundaryPrimes.ncard : ℤ) ≤ 3 := by
  have hlow : 2 * e ≤ a[s] := by
    by_contra! h
    have hsec : p[s] = S₀ :=
      eq_section_of_hirzebruch_fiber_coeff_lt b e hΦ r hr hc p[s] (by
        simpa only [hs, mul_comm] using h)
    have hdegree : d[s] = 1 := by
      rw [hsec]
      exact (hirzebruch_section_coordinates b e hΦ r hr).2
    omega
  have hupper := hirzebruch_bisection_fiber_coeff_le_of_components b e hΦ hc r hr hD hK
    he s (fun _ hj ↦ hirzebruch_boundary_prime_degree_eq_zero_of_bisection
      b e hΦ hc r hr hD hK hs hj)
  omega

include hc hK in
private theorem hirzebruch_one_bisection_coordinates (he : e = 1)
    (s t : D.boundaryPrimes) (hs : d[s] = 2) (hst : s ≠ t) :
    (∀ j : D.boundaryPrimes, j = s ∨ j = t) ∧ a[s] = 2 := by
  classical
  let : Fintype D.boundaryPrimes := hD.finite_boundaryPrimes.fintype
  obtain ⟨hsec, -, hbound⟩ := hirzebruch_anticanonical_bisection b e hΦ hc r hr hD hK
    (by omega) s hs
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card, ← Finset.card_univ] at hbound
  have hpair : ({s, t} : Finset D.boundaryPrimes) = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by
      rw [Finset.card_pair hst]
      omega)
  have hsum : ∑ j : D.boundaryPrimes, a[j] = e + 2 :=
    sum_hirzebruch_boundary_prime_coordinates b e hΦ hc r hr hD hK 0
  rw [← hpair, Finset.sum_pair hst] at hsum
  have hdt := hirzebruch_boundary_prime_degree_eq_zero_of_bisection b e hΦ hc r hr hD hK hs hst.symm
  have hat := hirzebruch_fiber_coeff_pos_of_degree_zero b e hΦ r hr hc (by omega) p[t] hdt
  refine ⟨fun j ↦ ?_, by omega⟩
  have hj : j ∈ ({s, t} : Finset D.boundaryPrimes) := hpair ▸ Finset.mem_univ j
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hj

omit [AlgebraicGeometry.IsReduced D.subscheme] in
include hc in
private theorem disjoint_hirzebruch_bisection_section {s : D.boundaryPrimes} (hs : d[s] = 2)
    (ha : a[s] = 2 * e) :
    Disjoint (closure {(s : X)}) (closure {(S₀ : X)}) := by
  let := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  have hne : p[s] ≠ S₀ := by
    intro h
    rw [h, (hirzebruch_section_coordinates b e hΦ r hr).2] at hs
    omega
  have hzero := (Φ.hirzebruchPicardBasis_intersection_repr b e hΦ r hr hc (P p[s])).2
  rw [ha, hs, mul_comm (2 : ℤ), sub_self, hirzebruchPicardBasis_apply_one,
    rayDivisorToPicard_single, one_zsmul, Chow.intersectionBilinForm_apply, toMul_ofMul,
    toMul_ofMul] at hzero
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  refine Set.disjoint_left.mpr fun x hx hy ↦ ?_
  have hpos := (Chow.classIntersectionNumber_primeDivisorClass_pos_iff ℂ hdim.le hne).mpr
    ⟨x, by simpa only [coe_boundaryPrimeEmbedding] using hx, hy⟩
  exact (ne_of_gt hpos) hzero

include hc hK in
/-- On the index-one Hirzebruch surface, a reduced anticanonical boundary with
a bisection and another component is exactly the bisection plus one fiber.
The bisection is disjoint from the negative section. -/
theorem exists_fiber_of_hirzebruch_one_anticanonical_bisection (he : e = 1)
    (s t : D.boundaryPrimes) (hs : d[s] = 2) (hst : s ≠ t) :
    Disjoint (closure {(s : X)}) (closure {(S₀ : X)}) ∧
    ∃ y : S ⟶ projectiveLine ℂ,
      y ≫ (projectiveLine ℂ ↘ S) = 𝟙 S ∧
      I[p[t]] = y.ker.comap q ∧ D = I[p[s]] * (y.ker.comap q) := by
  classical
  let := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  obtain ⟨hall, ha⟩ := hirzebruch_one_bisection_coordinates b e hΦ hc r hr hD hK he s t hs hst
  have ht := hirzebruch_boundary_prime_degree_eq_zero_of_bisection b e hΦ hc r hr hD hK hs hst.symm
  obtain ⟨y, hy, -, hf⟩ := exists_hirzebruch_ruling_fiber_of_degree_zero b e hΦ hc r hr p[t] ht
  refine ⟨disjoint_hirzebruch_bisection_section b e hΦ hc r hr hs (by rw [ha, he]; decide),
    y, hy, hf, ?_⟩
  rw [← hf]
  simpa only [coe_boundaryPrimeEmbedding] using hD.eq_mul_vanishingIdeal_of_boundaryPrimes hst hall

include hc hK in
/-- In the presence of a bisection the distinguished invariant section is not a
component of the reduced anticanonical divisor. -/
theorem hirzebruch_section_notMem_boundary_support_of_bisection
    {s : D.boundaryPrimes} (hs : d[s] = 2) :
    (S₀ : X) ∉ D.support := by
  intro h
  obtain ⟨j, hj⟩ := (Set.ext_iff.mp D.range_boundaryPrimeEmbedding (S₀)).mpr h
  have hdegree : d[j] = 1 := by
    rw [hj]
    exact (hirzebruch_section_coordinates b e hΦ r hr).2
  have hne : j ≠ s := by
    intro heq
    rw [heq, hs] at hdegree
    omega
  have := hirzebruch_boundary_prime_degree_eq_zero_of_bisection b e hΦ hc r hr hD hK hs hne
  omega

open AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin 3) ℂ
local notation "Plane" => Proj 𝒜
local notation "J[" p "]" => Scheme.IdealSheafData.vanishingIdeal
  (Closeds.mk (closure {(p : Plane)}) isClosed_closure)
local notation "E" => Fan.rayBoundaryIdeal Φ hΦ (r 0)
local instance : SmoothOfRelativeDimension 2 (Plane ↘ S) :=
  smoothOfRelativeDimension_toSpecCoeff ℂ 2

omit [AlgebraicGeometry.IsReduced D.subscheme] in
include hc hK in
/-- On the index-one Hirzebruch surface, contract the negative section of a
nodal anticanonical pair with a bisection. The specified contraction is a
point blowup of the projective plane, and it maps the boundary isomorphically
onto a nodal anticanonical divisor of order one at the center. -/
theorem exists_plane_internalBlowdown_of_hirzebruch_one_anticanonical_bisection
    (he : e = 1) {s : D.boundaryPrimes} (hs : d[s] = 2)
    (hnodal : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S)) :
    ∃ (p : Plane) (a : X ≅ (J[p]).blowup),
      let f := a.hom ≫ (J[p]).blowupToBase
      let A := D.map f
      IsClosed ({p} : Set Plane) ∧ f ≫ (Plane ↘ S) = (X ↘ S) ∧ (J[p]).comap f = E ∧
      ∃ hA : A.IsEffectiveCartier,
        LineBundleClass.mk hA.toInvertibleSheaf =
          LineBundleClass.mk (QPainleve.canonicalBundle ℂ Plane 2) ∧
        AtWorstNodalOfRelativeDimensionOne (A.subschemeι ≫ Plane ↘ S) ∧
        A.stalkOrder p = 1 ∧ A.comap f = D * E ∧
        ((J[p]).comap A.subschemeι).IsEffectiveCartier ∧
        (let : Smooth (Plane ↘ S) := SmoothOfRelativeDimension.smooth 2 _
         let : LocallyOfFinitePresentation (A.subschemeι ≫ Plane ↘ S) :=
           TauCeti.locallyOfFinitePresentation_subschemeι_comp_of_isEffectiveCartier hA
         ∃ x : A.subscheme, A.subschemeι x = p ∧ x ∈ (A.subschemeι ≫ Plane ↘ S).smoothLocus) ∧
        ∃ u : D.subscheme ≅ A.subscheme, u.hom ≫ A.subschemeι = D.subschemeι ≫ f := by
  have hrays : Set.range (Fan.Ray.primitiveGenerator (Phi := Φ)) =
      {b 0, b 1, -b 0, b 0 - b 1} := by
    rw [← r.surjective.range_comp, Function.comp_def, hr, he, one_smul]
    ext x
    simp
    tauto
  obtain ⟨d, h, ρ, a, -, -, hρ, hz, -, hf, hE, -, -⟩ :=
    Φ.exists_iso_blowup_projectivePlane_of_hirzebruchOne b hΦ hc hrays
  let z := (Fan.projectiveSpace d Φ.lattice).distinguishedPointHom
    (Fan.projectiveSpaceMaximalCone d Φ.lattice none) ≫ (Fan.projectivePlaneIso d Φ.lattice).hom
  let p := z (IsLocalRing.closedPoint ℂ)
  have hp : IsClosed ({p} : Set Plane) :=
    isClosed_singleton_of_section (f := Plane ↘ S) hz
  have hi : z.ker = J[p] :=
    z.ker_eq_ker_fromSpecResidueField.trans (Scheme.ker_fromSpecResidueField_eq_vanishingIdeal p)
  have hρ₀ : ρ = r 0 :=
    Fan.Ray.primitiveGenerator_injective (hρ.trans (congrFun hr 0).symm)
  rw [hρ₀] at hE
  generalize z.ker = J at a hf hE hi
  subst J
  let f := a.hom ≫ (J[p]).blowupToBase
  have hover : f ≫ (Plane ↘ S) = (X ↘ S) := by
    dsimp only [f]
    rw [hf, Category.assoc, over_polynomial, Fan.projectivePlaneIso_hom_toSpecCoeff,
      FanHom.algebraicMap_comp_algebraicRealizationStructureMap, Fan.algebraicRealization_over]
  have : f.IsOver S := ⟨hover⟩
  have : IsIntegral Plane := Proj.isIntegral_polynomialProj
  have : IsNoetherian Plane := isNoetherian_of_finiteType (Plane ↘ S)
  have : AlgebraicGeometry.IsReduced D.subscheme := hnodal.isReduced
  have hnot : ¬ (E).support ≤ D.support := by
    intro hsub
    apply hirzebruch_section_notMem_boundary_support_of_bisection b e hΦ hc r hr hD hK hs
    apply hsub
    rw [← SetLike.mem_coe, coe_support_rayBoundaryIdeal]
    exact subset_closure (Set.mem_singleton _)
  obtain ⟨hA, hcan, hnode, hm, htotal, hcenter, hsmooth, u, hu⟩ :=
    hD.internalBlowdown_of_anticanonical_of_blowupIso ℂ hp f a.symm
      (a.inv_hom_id_assoc _) (hE.symm ▸ hnot) hnodal hK
  exact ⟨p, a, hp, hover, hE, hA, hcan, hnode, hm, htotal.trans (congrArg (D * ·) hE),
    hcenter, hsmooth, u, hu⟩

end TauCeti.Toric.Fan
