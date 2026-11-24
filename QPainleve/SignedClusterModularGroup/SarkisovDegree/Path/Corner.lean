/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Picard
public import QPainleve.Geometry.Toric.Fan.Logarithmic.Factorization
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Corner

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.Blowup.Tower.PlaneResolution
import QPainleve.Geometry.Toric.Fan.Picard.FiberDegree
import QPainleve.Geometry.Toric.Fan.StarSubdivision.Descent

/-!
# Resolved Sarkisov path at a Hirzebruch corner

The first blowup above a high-order toric corner determines two successive
links on the original resolution, a star subdivision and a reverse star
subdivision. The endpoint is a projective Hirzebruch surface. Its point tower
resolves the given plane map with the same fiber degree and smaller total base
order. This is the toric corner case of [Lutz's Proposition 8.11][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=72
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module PointedCone
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData
open TauCeti.SymmetricAlgebra TauCeti.Toric

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" Δ "]" => Fan.algebraicRealization Δ
local notation "f[" Δ "]" => (X[Δ] ↘ S)
local notation "B[" Δ "," h "]" => Fan.boundaryIdeal Δ (Fan.IsComplete.nonempty_cones h)
local notation "rankTwo(" b ")" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "L[" D "]" => Fan.LogarithmicProjection i D
local notation "coordinates(" U "," hU "," g "," s ")" =>
  LinearEquiv.symm (BlowupTower.picardMarking U hU s) (Additive.ofMul (pullback g H))

private theorem corner_coordinates_of_pullback_eq {Ψ : Fan i} {n : ℕ} {Y Z : Scheme}
    {U : BlowupTower X[Ψ] (1 + n) Z} [Nonempty Ψ.cones] [SmoothOfRelativeDimension 2 f[Ψ]]
    [IsNoetherian X[Ψ]] (hU : IsClosedPointTower X[Ψ] U)
    (C' : Basis (Fin 2) ℤ (Additive (LineBundleClass X[Ψ])))
    (k : Y ≅ Z) (g : Y ⟶ P) (a β : ℤ) (x : Fin (n + 1) → ℤ) (j : Fin (n + 1))
    (hclass : pullback k.hom (U.picardHom
      ((a + β + x j) • C' 0 + β • C' 1,
        Fin.append (fun _ : Fin 1 ↦ -β - x j) (x ∘ j.succAbove))).toMul = pullback g H) :
    let y := coordinates(U,hU,k.inv ≫ g,f[Ψ])
    C'.repr y.1 0 = a + β + x j ∧ C'.repr y.1 1 = β ∧
      y.2 = Fin.append (fun _ : Fin 1 ↦ -β - x j) (x ∘ j.succAbove) := by
  let x' := Fin.append (fun _ : Fin 1 ↦ -β - x j) (x ∘ j.succAbove)
  have hcancel := congrArg (pullback k.inv) hclass
  rw [pullback_comp, Iso.inv_hom_id, pullback_id, pullback_comp] at hcancel
  have hy : coordinates(U,hU,k.inv ≫ g,f[Ψ]) = ((a + β + x j) • C' 0 + β • C' 1, x') := by
    rw [LinearEquiv.symm_apply_eq, U.picardMarking_apply hU f[Ψ], ← hcancel, ofMul_toMul]
  dsimp only
  rw [hy]
  simp [x']

variable (b : Basis (Fin 2) ℤ N) (e : ℤ) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun l ↦ (r l).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])

local notation "C" => Fan.hirzebruchPicardBasis b e hΦ r hr

variable {n : ℕ} {Y : Scheme} {T : BlowupTower X[Φ] (n + 1) Y}
  (hT : IsClosedPointTower X[Φ] T)
  (g : Y ⟶ P) (hg : g ≫ (P ↘ S) = T.toBase ≫ f[Φ])
  (hbir : Scheme.BirationalOver g (𝟙 P))

include hc hg in
private theorem corner_bidegree_comparison
    [X[Φ].IsProjectiveOver ℂ] [Nonempty Φ.cones] [SmoothOfRelativeDimension 2 f[Φ]]
    [IsNoetherian X[Φ]] {Ψ : Fan i} [Nonempty Ψ.cones]
    [SmoothOfRelativeDimension 2 f[Ψ]] [IsNoetherian X[Ψ]]
    {Z : Scheme} {U : BlowupTower X[Ψ] (1 + n) Z} (hU : IsClosedPointTower X[Ψ] U)
    (C' : Basis (Fin 2) ℤ (Additive (LineBundleClass X[Ψ]))) (k : Y ≅ Z) (j : Fin (n + 1)) :
    let x := coordinates(T,hT,g,f[Φ])
    let a := (C).repr x.1 0
    let β := (C).repr x.1 1
    let x' := Fin.append (fun _ : Fin 1 ↦ -β - x.2 j) (x.2 ∘ j.succAbove)
    (pullback k.hom (U.picardHom ((a + β + x.2 j) • C' 0 + β • C' 1, x')).toMul =
        (T.picardHom (a • C 0 + β • C 1, x.2)).toMul) →
    ((∑ l, -x' l) = (∑ l, -x.2 l) + β + 2 * x.2 j) →
    ((∀ l, 0 ≤ -x.2 l) → -x.2 j ≤ β → β < 2 * (-x.2 j) →
      hirzebruchSarkisovBidegree β.toNat (∑ l, -x' l).toNat <
        hirzebruchSarkisovBidegree β.toNat (∑ l, -x.2 l).toNat) →
    β < 2 * (-x.2 j) →
    let y := coordinates(U,hU,k.inv ≫ g,f[Ψ])
    let β' := C'.repr y.1 1
    C'.repr y.1 0 = a + β + x.2 j ∧ β' = β ∧ y.2 = x' ∧
    (∑ l, -y.2 l) = (∑ l, -x.2 l) + β + 2 * x.2 j ∧
    hirzebruchSarkisovBidegree β'.toNat (∑ l, -y.2 l).toNat <
      hirzebruchSarkisovBidegree β.toNat (∑ l, -x.2 l).toNat := by
  intro x a β x' hclass hsum hlt hhigh y β'
  have hsum_repr : a • C 0 + β • C 1 = x.1 := by
    simpa only [Fin.sum_univ_two] using (C).sum_repr x.1
  have hsrc : (T.picardHom x).toMul = pullback g H := by
    rw [← T.picardMarking_apply hT f[Φ], LinearEquiv.apply_symm_apply, toMul_ofMul]
  rw [hsum_repr, Prod.mk.eta, hsrc] at hclass
  have hcoeff : C'.repr y.1 0 = a + β + x.2 j ∧ β' = β ∧ y.2 = x' :=
    corner_coordinates_of_pullback_eq hU C' k g a β x.2 j hclass
  obtain ⟨ha', hβ', hy⟩ := hcoeff
  obtain ⟨_, J, -, -, -, -, -, horders⟩ := hT.exists_moving_base_ideal_of_plane_resolution g hg
  have hnonneg (l : Fin (n + 1)) : 0 ≤ -x.2 l := by
    rw [horders l]
    exact Int.natCast_nonneg _
  have hbound := hT.base_order_le_hirzebruch_fiber_degree b e hΦ r hr hc g hg j
  refine ⟨ha', hβ', hy, ?_, ?_⟩
  · rwa [hy]
  · rw [hβ', hy]
    exact hlt hnonneg hbound hhigh

include hg hbir in
/-- A first blowup above a specified Hirzebruch corner of order greater than half
the fiber degree gives a two-link resolved Sarkisov path on the original surface.
The path blows up the corner and contracts the strict transform of its fiber.
Every vertex carries the same pole ideal. The endpoint projection identifies the
transported point tower, with its pole ideal and prescribed morphism to the plane.
In the transported marking the fiber degree is unchanged, the remaining orders
keep their relative order, and the Sarkisov bidegree strictly decreases. -/
theorem exists_sarkisov_path_decrease_of_toric_corner [X[Φ].IsProjectiveOver ℂ]
    (σ : Φ.cones) (hσ : σ.val = hull ℝ (Set.range (i ∘ b))) (j : Fin (n + 1))
    (hj : hT.baseCenter j = Φ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ))
    (hfirst : ∀ l < j, hT.baseCenter l ≠ hT.baseCenter j) (D : Y.IdealSheafData) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 f[Φ] :=
      rankTwo(b) ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : IsNoetherian X[Φ] := isNoetherian_of_finiteType f[Φ]
    let : Y.Over S := ⟨T.toBase ≫ f[Φ]⟩
    let : T.toBase.IsOver S := ⟨rfl⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f[Φ]
    let : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    let : IsIntegral Y := hT.isIntegral f[Φ]
    let : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two f[Φ]
    let x := coordinates(T,hT,g,f[Φ])
    let β := (C).repr x.1 1
    ∀ hpole : B[Φ,hc].comap T.toBase = D * ramificationIdealSheaf ℂ T.toBase,
    β < 2 * (-x.2 j) →
    let A : L[D] := ⟨Φ, hΦ, hc, T.toBase, inferInstance, inferInstance, hpole⟩
    ∃ (B : L[D]) (path : Fan.LogarithmicProjection.SarkisovPath A B)
      (d : Basis (Fin 2) ℤ N) (r' : Fin 4 ≃ B.fan.Ray)
      (hr' : (fun l ↦ (r' l).primitiveGenerator) = ![d 0, d 1, -d 0, (e + 1) • d 0 - d 1])
      (Z : Scheme) (U : BlowupTower X[B.fan] (1 + n) Z)
      (hU : IsClosedPointTower X[B.fan] U) (k : Y ≅ Z),
      @Quiver.Path.length _ Fan.LogarithmicProjection.sarkisovQuiver A B path = 2 ∧
      path.rationalMap = (A.fan.denseTorusPartialIso B.fan).toRationalMap ∧
      B.hom = k.hom ≫ U.toBase ∧ X[B.fan].IsProjectiveOver ℂ ∧
      (k.inv ≫ g) ≫ (P ↘ S) = U.toBase ≫ f[B.fan] ∧
      Scheme.BirationalOver (k.inv ≫ g) (𝟙 P) ∧
      let : SmoothOfRelativeDimension 2 f[B.fan] :=
        rankTwo(b) ▸ B.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap B.isRegular
      let : IsNoetherian X[B.fan] := by
        let : Smooth f[B.fan] := SmoothOfRelativeDimension.smooth 2 _
        exact isNoetherian_of_finiteType f[B.fan]
      B[B.fan,B.isComplete].comap U.toBase =
        D.comap k.inv * hU.ramificationIdealSheafToBase ℂ ∧
      let y := coordinates(U,hU,k.inv ≫ g,f[B.fan])
      let C' := B.fan.hirzebruchPicardBasis d (e + 1) B.isRegular r' hr'
      let β' := C'.repr y.1 1
      C'.repr y.1 0 = (C).repr x.1 0 + β + x.2 j ∧ β' = β ∧
      y.2 = Fin.append (fun _ : Fin 1 ↦ -β - x.2 j) (x.2 ∘ j.succAbove) ∧
      (∑ l, -y.2 l) = (∑ l, -x.2 l) + β + 2 * x.2 j ∧
      hirzebruchSarkisovBidegree β'.toNat (∑ l, -y.2 l).toNat <
        hirzebruchSarkisovBidegree β.toNat (∑ l, -x.2 l).toNat := by
  intro hcones hdim hNoeth hOver hToBase hdimY hSmoothY hInt hMod x β hpole hhigh A
  let := hcones
  let := hdim
  let := hNoeth
  let := hOver
  let := hToBase
  let := hdimY
  let := hSmoothY
  let := hInt
  let := hMod
  have hrays : Set.range (Fan.Ray.primitiveGenerator (Phi := Φ)) =
      {b 0, b 1, -b 0, e • b 0 - b 1} := by
    rw [← r.surjective.range_comp, Function.comp_def, hr]
    simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  obtain ⟨Ψ, F, hΨ, hF, hcΨ, hcF, d, τ, s, t, v, w, q, r₀, r', hr₀, hr', Z, U, hU, k,
    -, -, -, hv, hw, hs, ht, hq, hq', -, -, hg', hbir', hmodq, -, -, -, hp, hcoord⟩ :=
    exists_sarkisov_decrease_of_toric_corner b e hΦ hc hrays σ hσ hT j hj
      (by simpa only [← hj] using hfirst) g (P ↘ S) hg hbir
  have hr₀' : r₀ = r := Equiv.ext fun l ↦ Fan.Ray.primitiveGenerator_injective
    (congrFun (hr₀.trans hr.symm) l)
  subst r₀
  let : Nonempty F.cones := hcF.nonempty_cones
  let : Nonempty Ψ.cones := hcΨ.nonempty_cones
  let : SmoothOfRelativeDimension 2 f[Ψ] :=
    rankTwo(b) ▸ Ψ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΨ
  let : IsNoetherian X[Ψ] := by
    let : Smooth f[Ψ] := SmoothOfRelativeDimension.smooth 2 _
    exact isNoetherian_of_finiteType f[Ψ]
  let : IsModification q := hmodq
  obtain ⟨hqOver, hkOver, hPole⟩ := hp
  obtain ⟨hpF, hpΨ, hpU⟩ := hPole D
    ((congrArg (fun I ↦ D * I) (hT.ramificationIdealSheafToBase_def ℂ)).symm ▸ hpole)
  let M : L[D] := ⟨F, hF, hcF, q, hqOver, inferInstance, hpF⟩
  have hDominant : IsDominant (k.hom ≫ U.toBase) := by
    rw [← hq']
    infer_instance
  let B : L[D] := ⟨Ψ, hΨ, hcΨ, k.hom ≫ U.toBase, hkOver, hDominant, hpΨ⟩
  let p₀ : @Quiver.Path _ Fan.LogarithmicProjection.instQuiver A M :=
    Quiver.Path.nil.cons (Fan.LogarithmicProjection.StarStep.blowup hs hq)
  let p : @Quiver.Path _ Fan.LogarithmicProjection.instQuiver A B :=
    p₀.cons (Fan.LogarithmicProjection.StarStep.blowdown ht hq')
  let path := Fan.LogarithmicProjection.SarkisovPath.ofStar p
  refine ⟨B, path, d, r', hr', Z, U, hU, k, ?_, ?_, rfl,
    t.isProjectiveOver_of_common_pointBlowup s σ τ v w hv hw,
    hg', hbir', hpU, ?_⟩
  · exact (Fan.LogarithmicProjection.SarkisovPath.length_ofStar p).trans rfl
  · exact (Fan.LogarithmicProjection.SarkisovPath.rationalMap_ofStar p).trans
      (Fan.LogarithmicProjection.pathRationalMap_eq_denseTorusPartialIso p)
  · obtain ⟨hclass, hsum, hlt⟩ := hcoord ((C).repr x.1 0) β x.2
    exact corner_bidegree_comparison b e hΦ hc r hr hT g hg hU
      (Ψ.hirzebruchPicardBasis d (e + 1) hΨ r' hr') k j hclass hsum hlt hhigh

end QPainleve.BlowupTower.IsClosedPointTower
