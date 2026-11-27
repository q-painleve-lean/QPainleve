/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RelativeProj.Ruling.Sections
public import QPainleve.Geometry.Toric.Fan.Hirzebruch.Anticanonical

import QPainleve.Geometry.Toric.Fan.Ruling.Hirzebruch.Fiber
import QPainleve.Geometry.Toric.Fan.Ruling.Hirzebruch.SplitBundle
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective

/-!
# Split presentations of complexity-zero Hirzebruch boundaries

A reduced anticanonical divisor of complexity zero on a Hirzebruch surface is
carried to the summand sections and coordinate fibers of a split projective
bundle. The ruling comparison identifies the ideal sheaf of the full boundary.
These split-bundle coordinates are used in the two-fiber case of
[Gross, Hacking and Keel, Proposition 1.3][GHK].

[GHK]: https://arxiv.org/html/1106.4977v3#S1.Thmproposition3
-/

public section

open AlgebraicGeometry CategoryTheory Module TopologicalSpace
open Scheme.IdealSheafData TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable (K : Type) [Field K] [IsAlgClosed K]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}
  (b : Basis (Fin 2) ℤ N) (e : ℤ) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])

local notation "X" => Fan.finiteFanScheme K Φ
local notation "S" => Spec (CommRingCat.of K)
local notation "P" => projectiveLine K
local notation "q" => Fan.characterRuling K Φ (LinearMap.toAddMonoidHom (Basis.coord b 1))
  (nonneg_or_nonpos_hirzebruch_ruling_character b e r hr)
local notation "L[" a "]" => Functor.obj (InvertibleSheaf.toFixedRankOne P)
  (Proj.symmetricAlgebraTwistingBundle K (Fin 2 → K) a)
local notation "F[" a "," b "]" => Functor.obj (FiniteLocallyFreeSheaf.toQuasicoherent P)
  (ObjectProperty.FullSubcategory.obj (FiniteLocallyFreeSheaf.FixedRank.biprod L[a] L[b]))
local notation "A[" a "," b "]" => ObjectProperty.FullSubcategory.obj
  (Functor.obj (gradedSymmetricAlgebra P) F[a,b])
local notation "p[" j "]" => projectiveLine.polynomialPoint K (RingHom.id K) j 0
local notation "σ[" a "," b ";" j "]" => projectiveLine.relativeProjSplitTwistingSection K a b j
local notation "I[" x "]" =>
  vanishingIdeal (Closeds.mk (closure ({(x : X)} : Set X)) isClosed_closure)
local notation "π[" a "," b "]" => CommMon.relativeProjToBase A[a,b]
local notation "D[" a "," b "]" =>
  (Scheme.Hom.ker σ[a,b;0] * Scheme.Hom.ker σ[a,b;1] *
    comap (Scheme.Hom.ker p[0]) π[a,b] * comap (Scheme.Hom.ker p[1]) π[a,b])

omit [IsAlgClosed K] in
private theorem section_of_prime_of_isIso {D : (X).IdealSheafData} (p : D.boundaryPrimes)
    (h : IsIso (I[D.boundaryPrimeEmbedding p].subschemeι ≫ q)) :
    ∃ s : P ⟶ X, s ≫ q = 𝟙 P ∧ s.ker = I[D.boundaryPrimeEmbedding p] ∧
      Set.range s = closure ({(p : X)} : Set X) := by
  let I := I[D.boundaryPrimeEmbedding p]
  let g := asIso (I.subschemeι ≫ q)
  let s := g.inv ≫ I.subschemeι
  refine ⟨s, g.inv_hom_id, ?_, ?_⟩
  · rw [Scheme.Hom.ker_comp_of_isIso, ker_subschemeι]
  · calc
      Set.range s = Set.range I.subschemeι := g.inv.surjective.range_comp I.subschemeι
      _ = closure ({(p : X)} : Set X) := by
        simp only [I, D.coe_boundaryPrimeEmbedding, range_subschemeι, coe_support_vanishingIdeal,
          Closeds.coe_mk]

include hc in
/-- A reduced anticanonical divisor of complexity zero on a complete regular Hirzebruch
fan becomes the two summand sections and the two coordinate fibers of a split bundle.
The isomorphism identifies the boundary ideal and lies over a projective-line
automorphism over the coefficient field. -/
theorem exists_split_relativeProj_of_hirzebruch_boundaryComplexity_zero (he : 0 ≤ e)
    {D : (X).IdealSheafData} [IsReduced D.subscheme] (hD : D.IsEffectiveCartier)
    (hzero : D.boundaryComplexity = 0) :
    let : SmoothOfRelativeDimension 2 (X ↘ S) := by
      rw [finiteFanScheme_over K]
      exact ((finrank_eq_card_basis b).trans (Fintype.card_fin 2)) ▸
        Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec K hΦ
    LineBundleClass.mk hD.toInvertibleSheaf = LineBundleClass.mk (QPainleve.canonicalBundle K X 2) →
    ∃ (a d : ℤ) (g : P ≅ P) (u : X ≅ A[a,d].relativeProj),
      g.hom ≫ P ↘ S = P ↘ S ∧ u.hom ≫ π[a,d] = q ≫ g.hom ∧ D[a,d].comap u.hom = D := by
  intro hSmooth hK
  let := hc.nonempty_cones
  let := hSmooth
  let : (X).IsProjectiveOver K := Φ.isProjectiveOver_finiteFanScheme_of_isComplete K hΦ hc b
  have hq := smoothOfRelativeDimension_hirzebruch_characterRuling K b e hΦ hc r hr
  let : Smooth q := hq.smooth 1 _
  let C := Φ.hirzebruchPicardBasis K b e hΦ r hr
  obtain ⟨M, hM⟩ := LineBundleClass.mk_surjective (C 1).toMul
  have hf (y : P) (hy : IsClosed ({y} : Set P)) :
      ∃ a : P ≅ Scheme.Hom.fiber q y, a.hom ≫ Scheme.Hom.fiberι q y ≫ X ↘ S = P ↘ S ∧
        LineBundleClass.intersectionNumber K (a.hom ≫ Scheme.Hom.fiberι q y)
          (LineBundleClass.mk M) = 1 := by
    obtain ⟨u, hu, hdeg⟩ := exists_hirzebruch_fiber_iso_with_degree K b e hΦ hc r hr y hy
    refine ⟨u, hu, ?_⟩
    rw [hdeg, hM, ofMul_toMul, Basis.repr_self]
    simp
  obtain ⟨j, k, hj, hk, hd, y, z, hyz, hy, hz, hB⟩ :=
    exists_sections_and_fibers_of_hirzebruch_boundaryComplexity_zero K b e hΦ hc r hr he hD hzero hK
  obtain ⟨s, hs, hsK, hrS⟩ := section_of_prime_of_isIso K b e r hr j hj
  obtain ⟨t, ht, htK, hrT⟩ := section_of_prime_of_isIso K b e r hr k hk
  have hDis : Disjoint (Set.range s) (Set.range t) := by
    rw [hrS, hrT]
    exact hd
  obtain ⟨a, d, g, f, hg, hfπ, -, -, hfD⟩ :=
    (q).exists_iso_split_relativeProj_of_disjoint_sections_and_fibers M hf s t hs ht hDis
      hy hz (fun h ↦ hyz (congrArg (fun p : S ⟶ P ↦ p (IsLocalRing.closedPoint K)) h))
  exact ⟨a, d, g, f, hg, hfπ, hfD.trans (by rw [hB, hsK, htK])⟩

include hc r hr in
/-- A reduced anticanonical divisor of complexity zero on a complete regular
Hirzebruch surface gives a toric pair over the coefficient field, with its actual boundary ideal. -/
theorem exists_toric_of_hirzebruch_boundaryComplexity_zero (he : 0 ≤ e)
    {D : (X).IdealSheafData} [IsReduced D.subscheme] (hD : D.IsEffectiveCartier)
    (hzero : D.boundaryComplexity = 0) :
    let : SmoothOfRelativeDimension 2 (X ↘ S) := by
      rw [finiteFanScheme_over K]
      exact ((finrank_eq_card_basis b).trans (Fintype.card_fin 2)) ▸
        Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec K hΦ
    LineBundleClass.mk hD.toInvertibleSheaf = LineBundleClass.mk (QPainleve.canonicalBundle K X 2) →
    ∃ (Ψ : Fan i) (_ : Ψ.IsRegular) (hΨc : Ψ.IsComplete) (f : (Ψ.finiteFanScheme K) ≅ X),
      f.hom ≫ X ↘ S = (Ψ.finiteFanScheme K) ↘ S ∧
      D.comap f.hom = Ψ.toricBoundaryIdeal K hΨc.nonempty_cones := by
  intro _ hK
  obtain ⟨a, d, g, u, hg, hu, hDu⟩ :=
    exists_split_relativeProj_of_hirzebruch_boundaryComplexity_zero K b e hΦ hc r hr he hD hzero hK
  obtain ⟨Ψ, hΨ, hΨc, _, _, v, hv, hDv⟩ :=
    exists_hirzebruch_model_of_split_twisting K b Φ.lattice a d
  have hfield : u.inv ≫ X ↘ S = π[a,d] ≫ P ↘ S := by
    apply (cancel_epi u.hom).mp
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, hu, Category.assoc, hg, comp_over (q) S]
  refine ⟨Ψ, hΨ, hΨc, v ≪≫ u.symm, ?_, ?_⟩
  · rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, hfield, ← Category.assoc, hv, comp_over]
  · rw [← hDu, Iso.trans_hom, Iso.symm_hom, ← comap_comp, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    exact hDv

end TauCeti.Toric.Fan
