/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.SymmetricAlgebra
public import QPainleve.Geometry.Toric.Fan.Logarithmic.Factorization
public import QPainleve.Geometry.Toric.Fan.Picard.Hirzebruch
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.ElementaryTransform

import QPainleve.AlgebraicGeometry.Blowup.Tower.PlaneResolution
import QPainleve.SignedClusterModularGroup.SarkisovDegree.Path.Corner
import QPainleve.SignedClusterModularGroup.SarkisovDegree.ResolvedSection

/-!
# Decreasing paths at Hirzebruch corners and sections

A proper base point on either invariant section of a Hirzebruch surface gives a
resolved elementary transformation when its order exceeds half the fiber degree.
The corner and smooth section constructions give the same change of base orders.
Their common conclusion supplies a smaller marked Hirzebruch resolution of the
specified map to the plane, as in [Lutz, Proposition 8.11][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=72
-/

public section

open AlgebraicGeometry CategoryTheory Module PointedCone
open TauCeti.AlgebraicGeometry TauCeti.SymmetricAlgebra TauCeti.Toric
open LineBundleClass
open Fan (LogarithmicProjection)
open Fan.LogarithmicProjection
open scoped Sarkisov

namespace QPainleve.BlowupTower.IsClosedPointTower

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "X[" Φ "]" => Fan.algebraicRealization Φ
local notation "f[" Φ "]" => (X[Φ] ↘ S)
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "coords[" T "," hT "," f "," g "]" =>
  LinearEquiv.symm (BlowupTower.picardMarking T hT f) (Additive.ofMul (pullback g H))
local notation "dimTwo(" b ")" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "center[" b "," ρ "," c "]" => Fan.Ray.binomialCenter ρ dimTwo(b)
  (Basis.detDualEquiv_self b (Fan.Ray.primitiveGenerator ρ))
  (Fan.Ray.surjective_detCharacter ρ b) c (IsLocalRing.closedPoint ℂ)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [X[Φ].IsProjectiveOver ℂ]
  (b : Basis (Fin 2) ℤ N) (e : ℕ) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun l ↦ (r l).primitiveGenerator) = ![b 0, b 1, -b 0, (e : ℤ) • b 0 - b 1])
  {Y : Scheme} {n : ℕ} {T : BlowupTower X[Φ] (n + 1) Y}
  (hT : IsClosedPointTower X[Φ] T) (g : Y ⟶ P)

/-- A base order above half the fiber degree over a corner or a smooth point of
an invariant section gives a strictly decreasing resolved Sarkisov block on
the same surface. The pivot is the first blowup over that point. The new
Hirzebruch marking retains the specified map to the plane and the pole ideal.
Its fiber degree is unchanged, the reverse pivot has order equal to the fiber
degree minus the pivot order, and every other order retains its relative position. -/
theorem exists_sarkisov_path_decrease_of_hirzebruch_corner_or_section
    (hg : g ≫ (P ↘ S) = T.toBase ≫ f[Φ]) (hbir : Scheme.BirationalOver g (𝟙 P))
    (j : Fin (n + 1))
    (hp : (∃ σ : Φ.cones, Nat.card (ToricRay σ.val) = 2 ∧
        hT.baseCenter j = Φ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ)) ∨
      ∃ s : Fin 2, ∃ c : ℂˣ, hT.baseCenter j = center[b,r ((![0, 2] : Fin 2 → Fin 4) s),c])
    {D : Y.IdealSheafData} :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 f[Φ] :=
      dimTwo(b) ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : IsNoetherian X[Φ] := isNoetherian_of_finiteType f[Φ]
    let : Y.Over S := ⟨T.toBase ≫ f[Φ]⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f[Φ]
    let : IsIntegral Y := hT.isIntegral f[Φ]
    let x := coords[T,hT,f[Φ],g]
    let β := (Φ.hirzebruchPicardBasis b e hΦ r hr).repr x.1 1
    ∀ (A : LogarithmicProjection i D), A.fan = Φ → A.hom ≍ T.toBase →
    β < 2 * (-x.2 j) →
    ∃ (q : Fin (n + 1)) (B : LogarithmicProjection i D) (p : SarkisovPath A B) (a : ℕ)
      (d : Basis (Fin 2) ℤ N) (t : Fin 4 ≃ B.fan.Ray)
      (ht : (fun l ↦ (t l).primitiveGenerator) = ![d 0, d 1, -d 0, (a : ℤ) • d 0 - d 1])
      (Z : Scheme) (U : BlowupTower X[B.fan] (1 + n) Z)
      (hU : IsClosedPointTower X[B.fan] U) (k : Y ≅ Z),
      hT.baseCenter q = hT.baseCenter j ∧
      (∀ l < q, hT.baseCenter l ≠ hT.baseCenter q) ∧ β < 2 * (-x.2 q) ∧
      B.hom = k.hom ≫ U.toBase ∧
      X[B.fan].IsProjectiveOver ℂ ∧ (p.length = 1 ∨ p.length = 2) ∧
      (k.inv ≫ g) ≫ (P ↘ S) = U.toBase ≫ f[B.fan] ∧
      Scheme.BirationalOver (k.inv ≫ g) (𝟙 P) ∧
      let : SmoothOfRelativeDimension 2 f[B.fan] :=
        dimTwo(d) ▸ B.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap B.isRegular
      let : IsNoetherian X[B.fan] := by
        let : Smooth f[B.fan] := SmoothOfRelativeDimension.smooth 2 _
        exact isNoetherian_of_finiteType f[B.fan]
      (B.fan.boundaryIdeal B.isComplete.nonempty_cones).comap U.toBase =
        D.comap k.inv * hU.ramificationIdealSheafToBase ℂ ∧
      let y := coords[U,hU,f[B.fan],k.inv ≫ g]
      let β' := (B.fan.hirzebruchPicardBasis d a B.isRegular t ht).repr y.1 1
      β' = β ∧
      y.2 = Fin.addCases (fun _ : Fin 1 ↦ -β - x.2 q) (x.2 ∘ q.succAbove) ∧
      hirzebruchSarkisovBidegree β'.toNat (∑ l, -y.2 l).toNat <
        hirzebruchSarkisovBidegree β.toNat (∑ l, -x.2 l).toNat := by
  intro hcones hdim hnoeth hOver hdimY hInt x β A hA hAh hhigh
  let := hcones
  let := hdim
  let := hnoeth
  let := hOver
  let := hdimY
  let := hInt
  obtain ⟨q, hcenter, hfirst, horder⟩ := hT.exists_first_baseCenter_ge_of_plane_resolution g hg j
  have hq : β < 2 * (-x.2 q) := hhigh.trans_le (mul_le_mul_of_nonneg_left horder (by norm_num))
  rw [← hcenter] at hp
  rcases A with ⟨Ψ, hreg, hcomplete, f, hf, hdom, hpole⟩
  dsimp only at hA hAh
  subst Ψ
  obtain rfl : f = T.toBase := eq_of_heq hAh
  rcases hp with ⟨σ, hσ, hp⟩ | ⟨s, c, hp⟩
  · obtain ⟨d, a, t, ht, _, hcone, _, _, hrepr⟩ :=
      Φ.exists_hirzebruch_corner_picardBasis b e hΦ r hr hc σ hσ
    have hβ : (Φ.hirzebruchPicardBasis d a hΦ t ht).repr
        (coords[T,hT,f[Φ],g]).1 1 = β := (hrepr x.1).2
    obtain ⟨B, p, d', t', ht', Z, U, hU, k, hlen, _, hh, hproj, hg', hbir',
        hpole', _, hdegree, horders, _, hlt⟩ :=
      hT.exists_sarkisov_path_decrease_of_toric_corner d a hΦ hc t ht g hg hbir σ hcone q hp
        hfirst D hpole (hβ.symm ▸ hq)
    let : Nonempty B.fan.cones := B.isComplete.nonempty_cones
    obtain ⟨d'', t'', ht'', _, hnormalize⟩ :=
      B.fan.exists_hirzebruchPicardBasis_natAbs d' (a + 1) B.isRegular t' ht'
    refine ⟨q, B, p, (a + 1).natAbs, d'', t'', ht'', Z, U, hU, k, hcenter, hfirst, hq, hh,
      hproj, Or.inr hlen, hg', hbir', hpole', ?_⟩
    dsimp only
    rw [hnormalize]
    refine ⟨hdegree.trans hβ, ?_, ?_⟩
    · rw [← hβ]
      simpa only [Fin.append] using horders
    · rwa [← hβ]
  · obtain ⟨hproj, Z, U, hU, k, d, t, ht, hg', hbir', hpole',
        ⟨A, B, p, hA, hAh, hB, hBh, hlen, _⟩, hdegree, horders, hlt⟩ :=
      hT.exists_sarkisov_path_decrease_of_smooth_section b e hΦ hc r hr s g hg hbir
        c q hp hfirst D ((hT.ramificationIdealSheafToBase_def ℂ).symm ▸ hpole) hq
    let A₀ : LogarithmicProjection i D := ⟨Φ, hreg, hcomplete, T.toBase, hf, hdom, hpole⟩
    have hsource : A = A₀ := LogarithmicProjection.ext hA hAh
    subst A
    rcases B with ⟨Ψ, hreg', hcomplete', f', hf', hdom', hpole''⟩
    dsimp only at hB hBh
    subst Ψ
    exact ⟨q, _, p, _, d, t, ht, Z, U, hU, k, hcenter, hfirst, hq, eq_of_heq hBh,
      hproj, Or.inl hlen, hg', hbir', hpole', hdegree, horders, hlt⟩

end QPainleve.BlowupTower.IsClosedPointTower
