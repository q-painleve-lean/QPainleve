/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Subdivision
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.Factorization
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Hirzebruch
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.RulingExchange
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.SectionContraction

import QPainleve.AlgebraicGeometry.Modules.Differentials.PoleIdeal

/-!
# Logarithmic Sarkisov reduction without high multiplicities

If a specified Hirzebruch-to-plane resolution has no base order greater than half
its fiber degree, the homaloidal identities force one of two reductions. On the
quadric, exchange the rulings. On the first Hirzebruch surface, contract the
negative section to the plane. The original resolved surface gives the regular
composite with the chosen link and carries the same logarithmic pole ideal.

This is the no-high-multiplicity step in the proof of Theorem 8.4 of
[Lutz's appendix to Hacking and Keating][HKL], using Lemma 8.8.

[HKL]: https://arxiv.org/abs/2005.05010v3#page=73
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData TauCeti.SymmetricAlgebra
open TauCeti.Toric

namespace QPainleve.BlowupTower.IsClosedPointTower

attribute [local instance] MvPolynomial.gradedAlgebra

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Φ.algebraicRealization.IsProjectiveOver ℂ]
  (b : Basis (Fin 2) ℤ N) (e : ℕ) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (e : ℤ) • b 0 - b 1])

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" A "]" => Fan.algebraicRealization A
local notation "f[" A "]" => (X[A] ↘ S)
local notation "B[" A "," h "]" => Fan.boundaryIdeal A (Fan.IsComplete.nonempty_cones h)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "fP" => (P ↘ S)
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "degree" => Module.Basis.picardTwistEquiv (Pi.basisFun ℂ (Fin 3))
local notation "C" => Fan.hirzebruchPicardBasis b e hΦ r hr
local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "π[" s "]" => FanHom.algebraicMap (Fan.IsSubdivision.toFanHom s)
local notation "τ[" h "]" =>
  FanHom.algebraicMap (FanEquiv.toFanHom (Fan.quadricRulingExchange b hΦ hc r h))
local notation "Plane[" d "]" => Fan.projectiveSpace d Φ.lattice
local notation "planeIso[" d "]" =>
  (Fan.projectivePlaneIso d Φ.lattice ≪≫ Module.Basis.polynomialProjIso (Pi.basisFun ℂ (Fin 3)))

variable {n : ℕ} {Y : Scheme} {T : BlowupTower X[Φ] n Y}
  (hT : IsClosedPointTower X[Φ] T) (g : Y ⟶ P)
  (hg : g ≫ fP = T.toBase ≫ f[Φ]) (hbir : Scheme.BirationalOver g (𝟙 P))

include hg hbir in
/-- If every base order is at most half the fiber degree, the given Hirzebruch
resolution admits a degree-decreasing regular toric link. For index zero it is
the ruling exchange, and for index one it is the subdivision projection to a
toric plane. In both cases the link carries the original pole factorization on
the specified resolving surface, and the transported tower resolves the original
morphism to the plane up to the displayed isomorphism. The first coordinate of
the Sarkisov bidegree decreases, independently of the resulting total base order. -/
theorem exists_sarkisov_decrease_of_no_high_multiplicity (D : Y.IdealSheafData) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 f[Φ] :=
      rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : Y.Over S := ⟨T.toBase ≫ f[Φ]⟩
    let : T.toBase.IsOver S := ⟨rfl⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f[Φ]
    let : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    let x := (T.picardMarking hT f[Φ]).symm (Additive.ofMul (pullback g H))
    let M := (∑ j, -x.2 j).toNat
    let β := (C).repr x.1 1
    B[Φ,hc].comap T.toBase = D * ramificationIdealSheaf ℂ T.toBase →
    (∀ j, 2 * (-x.2 j) ≤ β) →
    (∃ (hr₀ : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])
      (Z : Scheme) (U : BlowupTower X[Φ] n Z) (hU : IsClosedPointTower X[Φ] U) (k : Y ≅ Z),
      e = 0 ∧
      k.hom ≫ U.toBase = T.toBase ≫ τ[hr₀] ∧
      (k.inv ≫ g) ≫ fP = U.toBase ≫ f[Φ] ∧
      Scheme.BirationalOver (k.inv ≫ g) (𝟙 P) ∧
      B[Φ,hc].comap (T.toBase ≫ τ[hr₀]) = D * ramificationIdealSheaf ℂ (T.toBase ≫ τ[hr₀]) ∧
      let y := (U.picardMarking hU f[Φ]).symm (Additive.ofMul (pullback (k.inv ≫ g) H))
      let β' := (Fan.hirzebruchPicardBasis b 0 hΦ r hr₀).repr y.1 1
      0 < β' ∧ ∀ M', hirzebruchSarkisovBidegree β'.toNat M' <
        hirzebruchSarkisovBidegree β.toNat M) ∨
    (∃ (d : Basis (Fin 2) ℤ N) (s : Φ.IsSubdivision Plane[d])
      (Z : Scheme) (U : BlowupTower P (1 + n) Z) (hU : IsClosedPointTower P U) (k : Y ≅ Z),
      e = 1 ∧
      Relation.ReflTransGen Fan.IsTwoRayStarSubdivision Plane[d] Φ ∧
      k.hom ≫ U.toBase = T.toBase ≫ π[s] ≫ planeIso[d].hom ∧
      (k.inv ≫ g) ≫ fP = U.toBase ≫ fP ∧
      Scheme.BirationalOver (k.inv ≫ g) (𝟙 P) ∧
      B[Plane[d],Fan.isComplete_projectiveSpace d Φ.lattice].comap (T.toBase ≫ π[s]) =
        D * ramificationIdealSheaf ℂ (T.toBase ≫ π[s]) ∧
      let y := (U.picardMarking hU fP).symm (Additive.ofMul (pullback (k.inv ≫ g) H))
      0 < degree y.1 ∧ ∀ M', planeSarkisovBidegree (degree y.1).toNat M' <
        hirzebruchSarkisovBidegree β.toNat M) := by
  intro hcones hdim hY hOver hdimY hSmooth x M β hpole hlow
  let := hcones
  let := hdim
  let := hY
  let := hOver
  let := hdimY
  let := hSmooth
  let : Smooth f[Φ] := hdim.smooth
  have ⟨hβ, ha, hm⟩ := hirzebruch_resolution_degree_bounds b e hΦ hc r hr hT g hg hbir
  rcases hT.exists_fiber_degree_lt_two_mul_or_of_hirzebruch_resolution b e hΦ hc r hr g hg hbir with
    ⟨j, hj⟩ | ⟨-, he⟩
  · exact (not_lt_of_ge (hlow j) hj).elim
  rcases he with ⟨rfl, haβ⟩ | ⟨rfl, haβ⟩
  · let τ := τ[hr]
    let q := T.transport (asIso τ)
    let hQ := q.isLift.isClosedPointTower hT
    obtain ⟨-, hproj, hg', hbir', hpos, -⟩ :=
      hT.rulingExchange_bidegree_lt_of_no_high_multiplicity b hΦ hc r hr g hg hbir
        hβ (fun j ↦ ⟨hm j, hlow j⟩)
    refine Or.inl ⟨hr, _, q.tower, hQ, q.iso, rfl, hproj, hg', hbir', ?_, hpos, fun M' ↦ ?_⟩
    · apply comap_eq_mul_ramificationIdealSheaf_comp ℂ T.toBase τ 2 _ hpole
      rw [ramificationIdealSheaf_eq_top_of_isOpenImmersion, mul_top]
      exact (Fan.quadricRulingExchange b hΦ hc r hr).comap_boundaryIdeal_algebraicMap _ _
    · have hswap := (hT.picardMarking_symm_rulingExchange b hΦ hc r hr (pullback g H)).1 1
      rw [pullback_comp, Equiv.swap_apply_right] at hswap
      rw [hswap, Prod.Lex.lt_iff, ofLex_hirzebruchSarkisovBidegree,
        ofLex_hirzebruchSarkisovBidegree]
      simp only [β, x, Nat.cast_zero] at haβ ⊢
      exact Or.inl (by omega)
  · obtain ⟨d, s, Z, U, hU, k, hproj, hg', hbir', hdegree, -, -, -⟩ :=
      hT.exists_plane_resolution_of_hirzebruchOne b hΦ hc r hr g hg hbir
    have hReg := Fan.isRegular_projectiveSpace d Φ.lattice
    refine Or.inr ⟨d, s, Z, U, hU, k, rfl, s.exists_starSubdivision_factorization hReg hΦ rankTwo,
      hproj, hg', hbir', ?_, ?_, fun M' ↦ ?_⟩
    · let : SmoothOfRelativeDimension 2 f[Plane[d]] := by
        simpa only [Fan.algebraicRealization_over, rankTwo] using
          (Plane[d]).smoothOfRelativeDimension_algebraicRealizationStructureMap hReg
      exact comap_eq_mul_ramificationIdealSheaf_comp ℂ T.toBase π[s] 2
        (s.comap_boundaryIdeal_eq_mul_ramificationIdealSheaf hReg hΦ
          (Fan.isComplete_projectiveSpace d Φ.lattice) rankTwo) hpole
    · rw [hdegree]
      simp only [Nat.cast_one, one_mul] at hβ ha
      exact hβ.trans_le ha
    · rw [hdegree, Prod.Lex.lt_iff, ofLex_planeSarkisovBidegree, ofLex_hirzebruchSarkisovBidegree]
      simp only [β, x, Nat.cast_one] at hβ haβ ⊢
      exact Or.inl (by omega)

end QPainleve.BlowupTower.IsClosedPointTower
