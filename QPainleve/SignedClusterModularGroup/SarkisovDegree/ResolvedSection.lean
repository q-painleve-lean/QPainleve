/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Factorization
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.LogarithmicSection

/-!
# Resolved Sarkisov path at a smooth section point

A high-order pivot on a smooth point of either Hirzebruch section gives a single
resolved mutation between the specified projections. A nonnegative Hirzebruch
marking on the target retains the fiber degree and the strict decrease in total
base order, so the resulting resolution can enter the same degree induction.
This is the smooth-section case of Lutz's [Proposition 8.11][HKL].

[HKL]: https://arxiv.org/abs/2005.05010v3#page=71
-/

public section

open AlgebraicGeometry CategoryTheory Module PointedCone
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra TauCeti.Toric
open Fan (LogarithmicProjection)
open Fan.LogarithmicProjection Scheme.IdealSheafData
open scoped Sarkisov

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Φ.algebraicRealization.IsProjectiveOver ℂ]
  (b : Basis (Fin 2) ℤ N) (e : ℕ) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun l ↦ (r l).primitiveGenerator) = ![b 0, b 1, -b 0, (e : ℤ) • b 0 - b 1])
  (s : Fin 2)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" Δ "]" => Fan.algebraicRealization Δ
local notation "f[" Δ "]" => (X[Δ] ↘ S)
local notation "B[" Δ "," h "]" => Fan.boundaryIdeal Δ (Fan.IsComplete.nonempty_cones h)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "ρ" => r ((![0, 2] : Fin 2 → Fin 4) s)
local notation "onSection" => decide (s = 0)
local notation "pivot" => Fan.Ray.primitiveGenerator ρ
local notation "hv" => Fan.Ray.primitiveGenerator_ne_zero ρ
local notation "hp" => Fan.Ray.hull_primitiveGenerator_mem ρ

local notation "Ψ[" h "]" => Φ.mutationFan b (v := pivot) hv hp h
local notation "μ[" c "," h "]" =>
  Scheme.PartialMap.toRationalMap (Φ.mutationPartialMap b (c : ℂ) (v := pivot) hv hp h)
local notation "reg[" h "]" => Iff.mpr (Φ.isRegular_mutationFan_iff b (v := pivot) hv hp h) hΦ
local notation "comp[" h "]" => Iff.mpr (Φ.isComplete_mutationFan_iff b (v := pivot) hv hp h) hc
local notation "e'" => ite (onSection = true) ((e : ℤ) + 1) ((e : ℤ) - 1)

variable {n : ℕ} {Y : Scheme} {T : BlowupTower X[Φ] (n + 1) Y}
  (hT : IsClosedPointTower X[Φ] T)
  (g : Y ⟶ P) (hg : g ≫ (P ↘ S) = T.toBase ≫ f[Φ])
  (hbir : Scheme.BirationalOver g (𝟙 P))

include hg hbir in
/-- A first center over a smooth section point of order greater than half the
fiber degree gives a one-edge Sarkisov path on the given resolving surface.
The terminal projection is the transported tower projection, and the target
Hirzebruch marking has nonnegative index, the same fiber degree, and strictly
smaller Sarkisov bidegree. The transported resolution still resolves the
specified map to the plane and carries the pulled-back pole ideal. The reverse
base order comes first, and the other exceptional coordinates keep their order. -/
theorem exists_sarkisov_path_decrease_of_smooth_section
    (c : ℂˣ) (j : Fin (n + 1))
    (hj : hT.baseCenter j = Fan.Ray.binomialCenter ρ rankTwo (b.detDualEquiv_self pivot)
      (Fan.Ray.surjective_detCharacter ρ b) c (IsLocalRing.closedPoint ℂ))
    (hfirst : ∀ l < j, hT.baseCenter l ≠ hT.baseCenter j)
    (D : Y.IdealSheafData) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 f[Φ] :=
      rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : IsNoetherian X[Φ] := inferInstance
    let : Y.Over S := ⟨T.toBase ≫ f[Φ]⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f[Φ]
    let : IsIntegral Y := hT.isIntegral f[Φ]
    let x := (T.picardMarking hT f[Φ]).symm (Additive.ofMul (pullback g H))
    let β := (Fan.hirzebruchPicardBasis b e hΦ r hr).repr x.1 1
    B[Φ,hc].comap T.toBase = D * hT.ramificationIdealSheafToBase ℂ →
    β < 2 * (-x.2 j) →
    let hOpp : hull ℝ {i (-pivot)} ∈ Φ.cones := by
      fin_cases s
      · exact Fan.hull_neg_primitiveGenerator_mem_of_hirzebruch b e r hr
      · exact Fan.hull_neg_primitiveGenerator_mem_of_hirzebruch_section_two b e r hr
    let Ψ := Ψ[hOpp]
    let : Nonempty Ψ.cones := (comp[hOpp]).nonempty_cones
    let : SmoothOfRelativeDimension 2 f[Ψ] :=
      rankTwo ▸ Ψ.smoothOfRelativeDimension_algebraicRealizationStructureMap (reg[hOpp])
    let : IsNoetherian X[Ψ] := inferInstance
    X[Ψ].IsProjectiveOver ℂ ∧
    ∃ (Z : Scheme) (U : BlowupTower X[Ψ] (1 + n) Z) (hU : IsClosedPointTower X[Ψ] U) (k : Y ≅ Z)
      (d : Basis (Fin 2) ℤ N) (t : Fin 4 ≃ Ψ.Ray)
      (ht : (fun l ↦ (t l).primitiveGenerator) =
        ![d 0, d 1, -d 0, (Int.natAbs e' : ℤ) • d 0 - d 1]),
      (k.inv ≫ g) ≫ (P ↘ S) = U.toBase ≫ f[Ψ] ∧
      Scheme.BirationalOver (k.inv ≫ g) (𝟙 P) ∧
      B[Ψ,comp[hOpp]].comap U.toBase = D.comap k.inv * hU.ramificationIdealSheafToBase ℂ ∧
      (∃ (A B : LogarithmicProjection i D) (p : SarkisovPath A B),
        A.fan = Φ ∧ A.hom ≍ T.toBase ∧ B.fan = Ψ ∧ B.hom ≍ k.hom ≫ U.toBase ∧
        p.length = 1 ∧ p.rationalMap ≍ μ[c,hOpp]) ∧
      let y := (U.picardMarking hU f[Ψ]).symm (Additive.ofMul (pullback (k.inv ≫ g) H))
      let β' := (Fan.hirzebruchPicardBasis d (Int.natAbs e' : ℤ) (reg[hOpp]) t ht).repr y.1 1
      β' = β ∧
      y.2 = Fin.addCases (fun _ : Fin 1 ↦ -β - x.2 j) (x.2 ∘ j.succAbove) ∧
      hirzebruchSarkisovBidegree β'.toNat (∑ l, -y.2 l).toNat <
        hirzebruchSarkisovBidegree β.toNat (∑ l, -x.2 l).toNat := by
  intro hcones hdim hnoeth hY hdimY hInt x β hD hhigh hOpp Ψ hcones' hdim' hnoeth'
  let := hcones
  let := hdim
  let := hnoeth
  let := hY
  let := hdimY
  let := hInt
  let := hcones'
  let := hdim'
  let := hnoeth'
  have hρ : ρ = r (if onSection = true then (0 : Fin 4) else 2) := by
    fin_cases s <;> rfl
  obtain ⟨hproj, d₀, ht₀, Z, U, hU, k, hlink, hOver, hg', hbir', hPole, hDecrease⟩ :=
    hT.exists_sarkisov_decrease_of_logarithmic_smooth_section b e hΦ hc r hr onSection
      ρ hOpp c g hg hbir hρ j hj (by simpa only [← hj] using hfirst) D hD hhigh
  obtain ⟨d, t, ht, -, hFiber⟩ := Fan.exists_hirzebruchPicardBasis_natAbs d₀ e' (reg[hOpp]) _ ht₀
  refine ⟨hproj, Z, U, hU, k, d, t, ht, hg', hbir', hPole, ?_, ?_⟩
  · let : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two f[Φ]
    let : IsModification U.toBase := hU.isModification_of_smoothOfRelativeDimension_two f[Ψ]
    let A : LogarithmicProjection i D :=
      ⟨Φ, hΦ, hc, T.toBase, ⟨rfl⟩, inferInstance, (hT.ramificationIdealSheafToBase_def ℂ) ▸ hD⟩
    let : (k.hom ≫ U.toBase).IsOver S := ⟨(Category.assoc _ _ _).trans hOver⟩
    let : Smooth (Y ↘ S) := hdimY.smooth
    -- Compare both boundary pullbacks on the original resolving surface.
    have hram := hU.comap_ramificationIdealSheafToBase ℂ k (f := k.hom ≫ U.toBase) rfl
    have hD' : B[Ψ,comp[hOpp]].comap (k.hom ≫ U.toBase) =
        D * ramificationIdealSheaf ℂ (k.hom ≫ U.toBase) := by
      rw [comap_comp, hPole, comap_mul, hram, ← comap_comp, k.hom_inv_id, comap_id]
    let B : LogarithmicProjection i D :=
      ⟨Ψ, reg[hOpp], comp[hOpp], k.hom ≫ U.toBase, inferInstance, inferInstance, hD'⟩
    let a : SarkisovStep A B := ⟨μ[c,hOpp], .mutation b ρ c hOpp, hlink⟩
    exact ⟨A, B, Quiver.Hom.toPath a, rfl, HEq.rfl, rfl, HEq.rfl, rfl, by
      simp only [Quiver.Hom.toPath, SarkisovPath.rationalMap_cons, SarkisovPath.rationalMap_nil,
        Scheme.RationalMap.id_comp]
      rfl⟩
  · obtain ⟨-, hβ, horders, -, hlt⟩ := hDecrease
    dsimp only
    rw [hFiber]
    exact ⟨hβ, horders, hlt⟩

end QPainleve.BlowupTower.IsClosedPointTower
