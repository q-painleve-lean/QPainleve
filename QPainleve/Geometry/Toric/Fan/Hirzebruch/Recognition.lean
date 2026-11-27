/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Hirzebruch.Anticanonical

import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.CoordinateChange
import QPainleve.Geometry.Toric.Fan.Hirzebruch.CoordinateBoundary
import QPainleve.Geometry.Toric.Fan.Picard.Quadric
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap

/-!
# Toric boundary recognition on the quadric

A reduced anticanonical divisor of complexity zero on the quadric consists of two
fibers in each ruling. Projective linear changes of coordinates in the two factors
carry the divisor to the toric boundary, scheme-theoretically. This is the quadric
case of the ruled reduction in [Gross, Hacking and Keel, Proposition 1.3][GHK].

[GHK]: https://arxiv.org/html/1106.4977v3#S1.Thmproposition3
-/

public section

open AlgebraicGeometry CategoryTheory Limits Module TopologicalSpace
open Scheme.IdealSheafData TauCeti.AlgebraicGeometry LineBundleClass

namespace TauCeti.Toric.Fan

variable (k₀ : Type) [Field k₀] [IsAlgClosed k₀]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]
  (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])

local notation "X" => Fan.finiteFanScheme k₀ Φ
local notation "S" => Spec (CommRingCat.of k₀)
local notation "L" => projectiveLine k₀
local notation "p[" k "]" => projectiveLine.polynomialPoint k₀ (RingHom.id k₀) k 0
local notation "b'" => b.reindex (Equiv.swap 0 1)
local notation "r'" => Equiv.trans (Equiv.trans (Equiv.swap (0 : Fin 4) 1) (Equiv.swap 2 3)) r
local notation "hr'" => quadric_swapped_generators b r hr
local notation "q₀" =>
  Fan.characterRuling k₀ Φ (LinearMap.toAddMonoidHom (Basis.coord b 0))
    (nonneg_or_nonpos_quadric_transverse_character b r hr)
local notation "q₁" =>
  Fan.characterRuling k₀ Φ (LinearMap.toAddMonoidHom (Basis.coord b 1))
    (nonneg_or_nonpos_hirzebruch_ruling_character b 0 r hr)

variable {D : (Φ.finiteFanScheme k₀).IdealSheafData} [AlgebraicGeometry.IsReduced D.subscheme]
  (hD : D.IsEffectiveCartier)

include hΦ hc hr hD in
private theorem exists_eq_four_ruling_fibers [(Φ.finiteFanScheme k₀).IsProjectiveOver k₀]
    [SmoothOfRelativeDimension 2 ((Φ.finiteFanScheme k₀) ↘ S)]
    (hzero : D.boundaryComplexity = 0)
    (hK : LineBundleClass.mk hD.toInvertibleSheaf =
      LineBundleClass.mk (QPainleve.canonicalBundle k₀ X 2)) :
    ∃ a a' c d : S ⟶ L,
      a ≠ a' ∧ c ≠ d ∧
      a ≫ (L ↘ S) = 𝟙 S ∧ a' ≫ (L ↘ S) = 𝟙 S ∧
      c ≫ (L ↘ S) = 𝟙 S ∧ d ≫ (L ↘ S) = 𝟙 S ∧
      D = (a.ker.comap q₀) * (a'.ker.comap q₀) * (c.ker.comap q₁) * (d.ker.comap q₁) := by
  let := Φ.uniqueFactorizationMonoid_stalk_finiteFanScheme (R := k₀) hΦ
  obtain ⟨s, t, hst, hs, ht, hf, hdisj, -⟩ :=
    Φ.exists_boundaryPrimes_of_hirzebruch_boundaryComplexity_zero k₀ b 0 hΦ hc r hr
      le_rfl hD hzero hK
  have hdeg (j : D.boundaryPrimes) (hj : Additive.ofMul
      (primeDivisorClass (D.boundaryPrimeEmbedding j)) = hirzebruchPicardBasis k₀ b 0 hΦ r hr 1) :
      (hirzebruchPicardBasis k₀ (b') 0 hΦ (r') (hr')).repr
        (Additive.ofMul (primeDivisorClass (D.boundaryPrimeEmbedding j))) 1 = 0 := by
    rw [hirzebruchPicardBasis_quadric_swap k₀ b hΦ r hr, Basis.repr_reindex_apply, hj,
      Basis.repr_self]
    simp
  obtain ⟨a, ha, -, hA⟩ := exists_hirzebruch_ruling_fiber_of_degree_zero k₀
    b' 0 hΦ hc r' hr'
    (D.boundaryPrimeEmbedding s) (hdeg s hs)
  obtain ⟨a', ha', -, hA'⟩ := exists_hirzebruch_ruling_fiber_of_degree_zero k₀
    b' 0 hΦ hc r' hr'
    (D.boundaryPrimeEmbedding t) (hdeg t (by simpa only [zero_smul, zero_add] using ht))
  obtain ⟨c, d, hcd, hc', hd, hD'⟩ :=
    exists_ruling_fiber_pair_of_hirzebruch_boundary k₀ b 0 hΦ hc r hr hD hzero hst hf
  rw [characterRuling_quadric_swap k₀ b r hr] at hA hA'
  have haa' : a ≠ a' := by
    intro he
    have h := congrArg (fun J : (X).IdealSheafData ↦ (J.support : Set X))
      (hA.trans (he ▸ hA'.symm))
    simp only [coe_support_vanishingIdeal, Closeds.coe_mk, coe_boundaryPrimeEmbedding] at h
    exact Set.disjoint_left.mp hdisj (subset_closure (Set.mem_singleton (s : X)))
      (h ▸ subset_closure (Set.mem_singleton (s : X)))
  exact ⟨a, a', c, d, haa', fun he ↦ hcd (congrArg (fun f : S ⟶ L ↦
    f (IsLocalRing.closedPoint k₀)) he), ha, ha', hc', hd, by rw [hD', hA, hA']⟩

include hΦ hc hr hD in
/-- A reduced anticanonical divisor of complexity zero on a complete regular
Hirzebruch fan of index zero is carried to the toric boundary by an automorphism
over `k₀`. The comparison identifies the full ideal sheaves. -/
theorem exists_toric_of_quadric_boundary_complexity_zero (hzero : D.boundaryComplexity = 0) :
    let : SmoothOfRelativeDimension 2 (X ↘ S) := by
      rw [finiteFanScheme_over]
      exact ((finrank_eq_card_basis b).trans (Fintype.card_fin 2)) ▸
        Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΦ
    LineBundleClass.mk hD.toInvertibleSheaf =
      LineBundleClass.mk (QPainleve.canonicalBundle k₀ X 2) →
    ∃ e : X ≅ X, e.hom ≫ (X ↘ S) = (X ↘ S) ∧
      (Φ.toricBoundaryIdeal k₀ inferInstance).comap e.hom = D := by
  intro hSmooth hK
  let := hSmooth
  let : ((Φ.finiteFanScheme k₀)).IsProjectiveOver k₀ := isProjectiveOver_quadric k₀ b hΦ hc r hr
  obtain ⟨a, a', c, c', ha, hc', ha₀, ha₁, hc₀, hc₁, hD'⟩ :=
    exists_eq_four_ruling_fibers k₀ b hΦ hc r hr hD hzero hK
  obtain ⟨g, hg₀, hg₁⟩ := projectiveLine.exists_linearEquiv_comp_eq_coordinatePoints ha₀ ha₁ ha
  obtain ⟨k, hk₀, hk₁⟩ := projectiveLine.exists_linearEquiv_comp_eq_coordinatePoints hc₀ hc₁ hc'
  let u := Proj.symmetricAlgebraMapIso k₀ g
  let v := Proj.symmetricAlgebraMapIso k₀ k
  have over (m : (Fin 2 → k₀) ≃ₗ[k₀] (Fin 2 → k₀)) :
      (Proj.symmetricAlgebraMapIso k₀ m).hom ≫ (L ↘ S) = (L ↘ S) := by
    rw [SymmetricAlgebra.over_eq_projToSpec, Proj.symmetricAlgebraMapIso_hom_projToSpec]
  have hp := isPullback_quadric_characterRulings k₀ b hΦ hc r hr
  have hp' : IsPullback (q₀ ≫ u.hom) (q₁ ≫ v.hom) (L ↘ S) (L ↘ S) :=
    hp.of_iso' (Iso.refl _) u.symm v.symm (Iso.refl _)
      (by simp) (by simp) (by simpa using u.inv_comp_eq.mpr (over g).symm)
      (by simpa using v.inv_comp_eq.mpr (over k).symm)
  let e := hp'.isoIsPullback _ _ hp
  have e₀ : e.hom ≫ q₀ = q₀ ≫ u.hom := hp'.isoIsPullback_hom_fst _ _ hp
  have e₁ : e.hom ≫ q₁ = q₁ ≫ v.hom := hp'.isoIsPullback_hom_snd _ _ hp
  have hker {y z : S ⟶ L} (f : L ≅ L) (hf : y ≫ f.hom = z) :
      z.ker.comap f.hom = y.ker := hf ▸ Scheme.Hom.comap_ker_comp_of_isClosedImmersion y f.hom
  refine ⟨e, ?_, ?_⟩
  · rw [← comp_over q₀ S, reassoc_of% e₀, over g]
  · rw [boundaryIdeal_eq_four_coordinate_fibers k₀ b hΦ hc r hr, hD']
    simp only [comap_mul, ← comap_comp, e₀, e₁]
    simp only [comap_comp, hker u hg₀, hker u hg₁, hker v hk₀, hker v hk₁]

end TauCeti.Toric.Fan
