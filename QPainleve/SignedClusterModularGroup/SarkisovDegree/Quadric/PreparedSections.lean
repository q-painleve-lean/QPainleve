/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.PlaneResolution
public import QPainleve.Geometry.Toric.Fan.Picard.FiberDegree
public import QPainleve.Geometry.Toric.Fan.Picard.ProjectedPoint

/-!
# Base orders on the sections of a prepared quadric

Preparing a Hirzebruch surface for the quadric Sarkisov links changes one
invariant fiber. The two invariant sections retain their open orbits. If the
original line system has no high orders over those orbits, neither does the
prepared one, including at infinitely near centers. This is the section
comparison for Case C of [Lutz, Proposition 8.11][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=73
-/

public section

open AlgebraicGeometry CategoryTheory Module
open TauCeti.AlgebraicGeometry TauCeti.SymmetricAlgebra TauCeti.Toric
open LineBundleClass

namespace QPainleve.BlowupTower.IsClosedPointTower

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "X[" Δ "]" => Fan.algebraicRealization Δ
local notation "f[" Δ "]" => (X[Δ] ↘ S)
local notation "π[" J "]" => FanHom.algebraicMap (Fan.IsSubdivision.toFanHom J)
local notation "rankTwo(" b ")" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "center[" b "," ρ "," c "]" => Fan.Ray.binomialCenter ρ rankTwo(b)
  (Basis.detDualEquiv_self b (Fan.Ray.primitiveGenerator ρ)) (Fan.Ray.surjective_detCharacter ρ b)
  c (IsLocalRing.closedPoint ℂ)
local notation "sectionIndex[" t "]" => (![0, 2] : Fin 2 → Fin 4) t
local notation "mark[" T "," hT "," f "," g "]" =>
  LinearEquiv.symm (BlowupTower.picardMarking T hT f) (Additive.ofMul (pullback g H))

/-- A common toric subdivision of a Hirzebruch surface and the quadric in the
same ruling frame transports the upper bound of half the ruling degree on the
orders over the open orbits of both sections. A bound on the first orders over
each original point suffices to bound every order over the corresponding
quadric point. The morphism to the plane on the quadric tower is the pullback
of the specified original morphism along the resolving maps. -/
theorem base_order_le_half_on_prepared_quadric_sections
    {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
    {Φ Ψ Ω : Fan i} [X[Φ].IsProjectiveOver ℂ] [X[Ψ].IsProjectiveOver ℂ]
    (b : Basis (Fin 2) ℤ N) (a : ℕ)
    (hΦ : Φ.IsRegular) (hcΦ : Φ.IsComplete) (hΨ : Ψ.IsRegular) (hcΨ : Ψ.IsComplete)
    (r : Fin 4 ≃ Φ.Ray) (s : Fin 4 ≃ Ψ.Ray)
    (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (a : ℤ) • b 0 - b 1])
    (hs : (fun j ↦ (s j).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])
    {Y W Z : Scheme} {n m l : ℕ}
    {T : BlowupTower X[Φ] n Y} {R : BlowupTower Y m W} {U : BlowupTower X[Ψ] l Z}
    (hT : IsClosedPointTower X[Φ] T) (hR : IsClosedPointTower Y R)
    (hU : IsClosedPointTower X[Ψ] U) (e : W ≅ Z)
    (J : Ω.IsSubdivision Φ) (K : Ω.IsSubdivision Ψ) (q : W ⟶ X[Ω])
    (hq : q ≫ π[J] = R.toBase ≫ T.toBase) (hq' : q ≫ π[K] = e.hom ≫ U.toBase)
    (g : Y ⟶ P) (hg : g ≫ (P ↘ S) = T.toBase ≫ f[Φ]) :
    let : Nonempty Φ.cones := hcΦ.nonempty_cones
    let : Nonempty Ψ.cones := hcΨ.nonempty_cones
    let : SmoothOfRelativeDimension 2 f[Φ] :=
      rankTwo(b) ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : SmoothOfRelativeDimension 2 f[Ψ] :=
      rankTwo(b) ▸ Ψ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΨ
    let : IsNoetherian X[Φ] := isNoetherian_of_finiteType f[Φ]
    let : IsNoetherian X[Ψ] := isNoetherian_of_finiteType f[Ψ]
    let g' := e.inv ≫ R.toBase ≫ g
    let v := mark[T,hT,f[Φ],g]
    let w := mark[U,hU,f[Ψ],g']
    let β := (Φ.hirzebruchPicardBasis b a hΦ r hr).repr v.1 1
    let β' := (Ψ.hirzebruchPicardBasis b 0 hΨ s hs).repr w.1 1
    ∀ t : Fin 2, ∀ c : ℂˣ,
      (∀ j : Fin n, hT.baseCenter j = center[b,r sectionIndex[t],c] →
        (∀ k < j, hT.baseCenter k ≠ hT.baseCenter j) → 2 * (-v.2 j) ≤ β) →
      ∀ j : Fin l, hU.baseCenter j = center[b,s sectionIndex[t],c] → 2 * (-w.2 j) ≤ β' := by
  intro hcones hcones' hdim hdim' hnoeth hnoeth' g' v w β β' t c hlow j hj
  let := hcones
  let := hcones'
  let := hdim
  let := hdim'
  let := hnoeth
  let := hnoeth'
  have hOver : e.hom ≫ U.toBase ≫ f[Ψ] = R.toBase ≫ T.toBase ≫ f[Φ] := by
    rw [← Category.assoc e.hom, ← hq', ← Category.assoc R.toBase, ← hq]
    simp only [Category.assoc, Fan.algebraicRealization_over,
      FanHom.algebraicMap_comp_algebraicRealizationStructureMap]
  have hg' : g' ≫ (P ↘ S) = U.toBase ≫ f[Ψ] := by
    simp only [g', Category.assoc, hg, ← hOver, Iso.inv_hom_id_assoc]
  have hβ : β = β' := by
    simpa only [β, β', v, w, g', Category.assoc, pullback_comp] using
      hT.hirzebruch_fiber_degree_eq_of_common_subdivision b a hΦ hcΦ r hr 0 hΨ hcΨ s hs
        hR hU e J K q hq hq' (pullback g H)
  have hray : (r sectionIndex[t]).primitiveGenerator = (s sectionIndex[t]).primitiveGenerator := by
    fin_cases t
    · exact (congrFun hr (0 : Fin 4)).trans (congrFun hs (0 : Fin 4)).symm
    · exact (congrFun hr (2 : Fin 4)).trans (congrFun hs (2 : Fin 4)).symm
  -- Compare the first blowup over the point, which bounds all later orders there.
  obtain ⟨k, hk, hfirst, hle⟩ := hU.exists_first_baseCenter_ge_of_plane_resolution g' hg' j
  have hp := hk.trans hj
  have hle' : -w.2 j ≤ -w.2 k := hle
  rcases hT.base_order_eq_zero_or_exists_of_common_subdivision hR hU hΦ hΨ e J K q hq hq'
    b (r sectionIndex[t]) (s sectionIndex[t]) hray c k hp (hp ▸ hfirst) (pullback g H) with
    hzero | ⟨k₀, hk₀, hfirst₀, heq⟩
  · have hz : w.2 k = 0 := by
      simpa only [w, g', Category.assoc, pullback_comp] using hzero
    have hdegree : -w.2 k ≤ β' :=
      hU.base_order_le_hirzebruch_fiber_degree b 0 hΨ s hs hcΨ g' hg' k
    omega
  · have hord : -w.2 k = -v.2 k₀ := by
      simpa only [w, g', Category.assoc, pullback_comp, v] using heq
    have hbound := hlow k₀ hk₀ (fun i hi ↦ (hk₀ ▸ hfirst₀ i hi))
    omega

end QPainleve.BlowupTower.IsClosedPointTower
