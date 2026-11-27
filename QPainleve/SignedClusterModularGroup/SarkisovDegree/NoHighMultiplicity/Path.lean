/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Factorization
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.NoHighMultiplicity.Basic

/-!
# Resolved Hirzebruch links without high base orders

When a Hirzebruch-to-plane map has no base order above half its fiber degree, the
ruling exchange or negative-section contraction gives a decreasing Sarkisov path
on the specified resolving surface. The endpoint projection recovers the
transported point tower, so the degree induction can continue from that projection.

This is the case without high multiplicities in the proof of Theorem 8.4 of
[Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=73
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra
open TauCeti.Toric Fan.LogarithmicProjection

namespace QPainleve.BlowupTower.IsClosedPointTower

variable (k₀ : Type) [Field k₀] [IsAlgClosed k₀]

attribute [local instance] MvPolynomial.gradedAlgebra

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [(Φ.finiteFanScheme k₀).IsProjectiveOver k₀]
  (b : Basis (Fin 2) ℤ N) (e : ℕ) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (e : ℤ) • b 0 - b 1])

local notation "S" => Spec (CommRingCat.of k₀)
local notation "X[" coeff "," A "]" => Fan.finiteFanScheme coeff A
local notation "f[" A "]" => (X[k₀,A] ↘ S)
local notation "P" => Proj (homogeneousSubmodule k₀ (Fin 3 → k₀))
local notation "fP" => (P ↘ S)
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle k₀ (Fin 3 → k₀) 1)
local notation "degree" => Module.Basis.picardTwistEquiv (Pi.basisFun k₀ (Fin 3))
local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "exchange[" h "]" => Fan.quadricRulingExchange b hΦ hc r h
local notation "τ[" h "]" => FanHom.finiteFanSchemeHom k₀ (FanEquiv.toFanHom exchange[h])
local notation "Plane[" d "]" => Fan.projectiveSpace d Φ.lattice
local notation "planeIso[" d "]" =>
  (Fan.projectivePlaneIso k₀ d Φ.lattice ≪≫ Module.Basis.polynomialProjIso (Pi.basisFun k₀ (Fin 3)))
local notation "π[" s "]" => FanHom.finiteFanSchemeHom k₀ (Fan.IsSubdivision.toFanHom s)

variable {n : ℕ} {Y : Scheme} {T : BlowupTower X[k₀,Φ] n Y}
  (hT : IsClosedPointTower X[k₀,Φ] T) (g : Y ⟶ (Proj (homogeneousSubmodule k₀ (Fin 3 → k₀))))

local notation "mark[" U "," hU "," f "," g "]" =>
  LinearEquiv.symm (BlowupTower.picardMarking U hU f) (Additive.ofMul (pullback g H))

/-- The case without high base orders admits a decreasing Sarkisov path on the
given resolution. Its composite is the ruling exchange for index zero or the
subdivision projection for index one. The endpoint projection agrees with the
returned tower under the resolving isomorphism (and the coordinate-plane
identification in index one). The same map to the target plane is retained. -/
theorem exists_sarkisov_path_decrease_of_no_high_multiplicity
    (hg : g ≫ fP = T.toBase ≫ f[Φ]) (hbir : Scheme.BirationalOver g (𝟙 P))
    {D : Y.IdealSheafData} :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : Y.Over S := ⟨T.toBase ≫ f[Φ]⟩
    let : SmoothOfRelativeDimension 2 (X[k₀,Φ] ↘ S) :=
      rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΦ
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f[Φ]
    let : IsIntegral Y := hT.isIntegral f[Φ]
    let x := mark[T,hT,f[Φ],g]
    let β := (Fan.hirzebruchPicardBasis k₀ b e hΦ r hr).repr x.1 1
    let M := (∑ j, -x.2 j).toNat
    ∀ (A : Fan.LogarithmicProjection k₀ i D), A.fan = Φ →
      A.hom ≍ T.toBase →
      (∀ j, 2 * (-x.2 j) ≤ β) →
      ∃ (B : Fan.LogarithmicProjection k₀ i D) (p : SarkisovPath A B),
        (∃ (hr₀ : (fun j ↦ (r j).primitiveGenerator) =
            ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])
          (Z : Scheme) (U : BlowupTower X[k₀,Φ] n Z) (hU : IsClosedPointTower X[k₀,Φ] U)
          (k : Y ≅ Z),
          e = 0 ∧ B.fan = Φ ∧ p.rationalMap ≍ (τ[hr₀]).toRationalMap ∧
          B.hom ≍ k.hom ≫ U.toBase ∧
          (k.inv ≫ g) ≫ fP = U.toBase ≫ f[Φ] ∧
          Scheme.BirationalOver (k.inv ≫ g) (𝟙 P) ∧
          let y := mark[U,hU,f[Φ],k.inv ≫ g]
          let β' := (Fan.hirzebruchPicardBasis k₀ b 0 hΦ r hr₀).repr y.1 1
          0 < β' ∧ ∀ M', hirzebruchSarkisovBidegree β'.toNat M' <
            hirzebruchSarkisovBidegree β.toNat M) ∨
        (∃ (d : Basis (Fin 2) ℤ N) (s : Φ.IsSubdivision Plane[d])
          (Z : Scheme) (U : BlowupTower P (1 + n) Z) (hU : IsClosedPointTower P U)
          (k : Y ≅ Z),
          e = 1 ∧ B.fan = Plane[d] ∧ p.rationalMap ≍ (π[s]).toRationalMap ∧
          B.hom ≍ k.hom ≫ U.toBase ≫ (planeIso[d]).inv ∧
          (k.inv ≫ g) ≫ fP = U.toBase ≫ fP ∧
          Scheme.BirationalOver (k.inv ≫ g) (𝟙 P) ∧
          let y := mark[U,hU,fP,k.inv ≫ g]
          0 < degree y.1 ∧ ∀ M', planeSarkisovBidegree (degree y.1).toNat M' <
            hirzebruchSarkisovBidegree β.toNat M) := by
  intro hcones hY hdim hdimY hIntegral x β M A hA hhom hlow
  let := hY
  let := hdim
  let := hdimY
  let := hIntegral
  let := hcones
  let : T.toBase.IsOver S := ⟨rfl⟩
  rcases A with ⟨Ψ, hreg, hcomplete, a, haOver, haDom, haPole⟩
  dsimp only at hA hhom
  subst Ψ
  obtain rfl : a = T.toBase := eq_of_heq hhom
  let A : Fan.LogarithmicProjection k₀ i D := ⟨Φ, hreg, hcomplete, T.toBase, haOver, haDom, haPole⟩
  rcases hT.exists_sarkisov_decrease_of_no_high_multiplicity k₀ b e hΦ hc r hr g hg hbir
    D haPole hlow with ⟨hr₀, Z, U, hU, k, he, hproj, hg', hbir', hp, hpos, hlt⟩ |
      ⟨d, s, Z, U, hU, k, he, _, hproj, hg', hbir', hp, hpos, hlt⟩
  · let B : Fan.LogarithmicProjection k₀ i D :=
      ⟨Φ, hΦ, hc, T.toBase ≫ τ[hr₀], inferInstance, inferInstance, hp⟩
    let link : SarkisovStep A B :=
      { rationalMap := (τ[hr₀]).toRationalMap
        isSarkisovLink := by
          simpa only [Fan.torusTranslationIso_one, Iso.refl_hom, Category.comp_id] using
            (Fan.IsSarkisovLink.toricIso exchange[hr₀] 1)
        comp_rationalMap := by
          rw [Scheme.RationalMap.comp_toRationalMap, Scheme.Hom.toRationalMap_compHom] }
    exact ⟨B, @Quiver.Hom.toPath _ sarkisovQuiver _ _ link, Or.inl ⟨hr₀, Z, U, hU, k, he, rfl,
      heq_of_eq (by
        simp only [Quiver.Hom.toPath, SarkisovPath.rationalMap_cons, SarkisovPath.rationalMap_nil,
          Scheme.RationalMap.id_comp]
        rfl), heq_of_eq hproj.symm, hg', hbir', hpos, hlt⟩⟩
  · let hreg' := Fan.isRegular_projectiveSpace d Φ.lattice
    let hc' := Fan.isComplete_projectiveSpace d Φ.lattice
    let : Nonempty (Plane[d]).cones := hc'.nonempty_cones
    let B : Fan.LogarithmicProjection k₀ i D :=
      ⟨Plane[d], hreg', hc', T.toBase ≫ π[s], inferInstance, inferInstance, hp⟩
    have hB : A.coarsen s hreg' rankTwo = B :=
      Fan.LogarithmicProjection.ext (A.coarsen_fan ..) (A.coarsen_hom ..)
    obtain ⟨q⟩ := hB ▸ A.nonempty_path_of_subdivision rankTwo hreg' s
    let p := SarkisovPath.ofStar q.reverse
    have hmap : p.rationalMap ≍ (π[s]).toRationalMap := by
      rw [SarkisovPath.rationalMap_ofStar, pathRationalMap_eq_denseTorusPartialIso]
      exact heq_of_eq (s.toRationalMap_finiteFanSchemeHom k₀).symm
    have hproj' : B.hom ≍ k.hom ≫ U.toBase ≫ (planeIso[d]).inv := heq_of_eq (by
      rw [← Category.assoc, (planeIso[d]).eq_comp_inv, Category.assoc, hproj])
    exact ⟨B, p, Or.inr ⟨d, s, Z, U, hU, k, he, rfl, hmap, hproj', hg', hbir', hpos, hlt⟩⟩

end QPainleve.BlowupTower.IsClosedPointTower
