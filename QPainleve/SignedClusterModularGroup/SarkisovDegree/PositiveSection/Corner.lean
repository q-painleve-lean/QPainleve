/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Path.Corner

import QPainleve.AlgebraicGeometry.Blowup.Tower.PlaneResolution

/-!
# Toric pivots on the positive Hirzebruch section

A corner pivot on the positive section descends the Hirzebruch index by one.
A retained center on the contracted invariant fiber is replaced by the reverse
corner, whose order is at least the retained order. A center on the other invariant
fiber stays on its open orbit. These comparisons use the actual resolution of
the prescribed plane map, with its infinitely near centers.

The link uses the Picard formulas for the elementary transformations in
[Lutz's appendix to Hacking and Keating, Lemma 8.9][HKL].

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module PointedCone TauCeti.Toric
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData
open TauCeti.SymmetricAlgebra

namespace QPainleve.BlowupTower.IsClosedPointTower

variable (k₀ : Type) [Field k₀] [IsAlgClosed k₀]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

local notation "S" => Spec (CommRingCat.of k₀)
local notation "X[" Δ "]" => Fan.finiteFanScheme k₀ Δ
local notation "f[" Δ "]" => (X[Δ] ↘ S)
local notation "B[" Δ "," h "]" => Fan.toricBoundaryIdeal k₀ Δ (Fan.IsComplete.nonempty_cones h)
local notation "rankTwo(" b ")" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "P" => Proj (homogeneousSubmodule k₀ (Fin 3 → k₀))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle k₀ (Fin 3 → k₀) 1)
local notation "pt" => IsLocalRing.closedPoint k₀
local notation "center[" b "," ρ "," c "]" =>
  Fan.Ray.binomialCenter ρ k₀ rankTwo(b)
    (Module.Basis.detDualEquiv_self b (Fan.Ray.primitiveGenerator ρ))
    (Fan.Ray.surjective_detCharacter ρ b) c pt
local notation "coordinates(" T "," hT "," g "," s ")" =>
  LinearEquiv.symm (BlowupTower.picardMarking T hT s) (Additive.ofMul (pullback g H))
local notation "ruling[" b "," e "," r "," hr "]" =>
  Fan.characterRuling k₀ _ (LinearMap.toAddMonoidHom (Basis.coord b 1))
    (Fan.nonneg_or_nonpos_hirzebruch_ruling_character b e r hr)

/-- A pivot at the positive section's corner on fiber `r 1` of a marked
Hirzebruch surface of index `e > 0` gives a resolved path to index `e - 1`.
The source marking can place either invariant fiber at `r 1`.

In the nonnegative-index markings the fiber coefficient drops by the pivot
order and the fiber degree stays constant. The first reverse center is at
the corner on the target's distinguished section, of square zero when `e = 1`.
Its order is at least that of any
retained center originally in the contracted fiber's open orbit. The remaining
invariant fiber's open-orbit centers retain their orders and first occurrences.
Any retained first center distinct from the pivot keeps its ruling value and has
order at least its original order. This also applies to marked corners produced
by earlier pivots. The strict positive section retains its coefficients at every
surviving center and misses the reverse center. -/
theorem exists_sarkisov_path_of_positive_corner [X[Φ].IsProjectiveOver k₀]
    (b : Basis (Fin 2) ℤ N) (e : ℕ) (he : 0 < e) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (r : Fin 4 ≃ Φ.Ray)
    (hr : (fun l ↦ (r l).primitiveGenerator) = ![b 0, b 1, -b 0, (e : ℤ) • b 0 - b 1])
    {n : ℕ} {Y : Scheme} {T : BlowupTower X[Φ] (n + 1) Y}
    (hT : IsClosedPointTower X[Φ] T) (g : Y ⟶ P)
    (hg : g ≫ (P ↘ S) = T.toBase ≫ f[Φ]) (hbir : Scheme.BirationalOver g (𝟙 P))
    (σ : Φ.cones) (hσ : σ.val = hull ℝ {i (-b 0), i (b 1)}) (j : Fin (n + 1))
    (hj : hT.baseCenter j = (Φ.distinguishedSection (R := k₀) σ) pt)
    (hfirst : ∀ l < j, hT.baseCenter l ≠ hT.baseCenter j) (D : Y.IdealSheafData) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 f[Φ] :=
      rankTwo(b) ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΦ
    let : IsNoetherian X[Φ] := isNoetherian_of_finiteType f[Φ]
    let : Y.Over S := ⟨T.toBase ≫ f[Φ]⟩
    let : T.toBase.IsOver S := ⟨rfl⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f[Φ]
    let : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    let : IsIntegral Y := hT.isIntegral f[Φ]
    let : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two f[Φ]
    let x := coordinates(T,hT,g,f[Φ])
    let C := Φ.hirzebruchPicardBasis k₀ b (e : ℤ) hΦ r hr
    ∀ hpole : B[Φ,hc].comap T.toBase = D * ramificationIdealSheaf k₀ T.toBase,
    let A : Fan.LogarithmicProjection k₀ i D :=
      ⟨Φ, hΦ, hc, T.toBase, inferInstance, inferInstance, hpole⟩
    ∃ (B : Fan.LogarithmicProjection k₀ i D) (path : Fan.LogarithmicProjection.SarkisovPath A B)
      (d : Basis (Fin 2) ℤ N) (s : Fin 4 ≃ B.fan.Ray)
      (hs : (fun l ↦ (s l).primitiveGenerator) =
        ![d 0, d 1, -d 0, ((e - 1 : ℕ) : ℤ) • d 0 - d 1])
      (Z : Scheme) (U : BlowupTower X[B.fan] (1 + n) Z)
      (hU : IsClosedPointTower X[B.fan] U) (k : Y ≅ Z),
      @Quiver.Path.length _ Fan.LogarithmicProjection.sarkisovQuiver A B path = 2 ∧
      path.rationalMap = (A.fan.denseTorusPartialIso k₀ B.fan).toRationalMap ∧
      B.hom = k.hom ≫ U.toBase ∧ X[B.fan].IsProjectiveOver k₀ ∧
      (k.inv ≫ g) ≫ (P ↘ S) = U.toBase ≫ f[B.fan] ∧
      Scheme.BirationalOver (k.inv ≫ g) (𝟙 P) ∧
      let : SmoothOfRelativeDimension 2 f[B.fan] :=
        rankTwo(b) ▸ B.fan.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ B.isRegular
      let : IsNoetherian X[B.fan] := by
        let : Smooth f[B.fan] := SmoothOfRelativeDimension.smooth 2 _
        exact isNoetherian_of_finiteType f[B.fan]
      B[B.fan,B.isComplete].comap U.toBase =
        D.comap k.inv * hU.ramificationIdealSheafToBase k₀ ∧
      let y := coordinates(U,hU,k.inv ≫ g,f[B.fan])
      let C' := B.fan.hirzebruchPicardBasis k₀ d ((e - 1 : ℕ) : ℤ) B.isRegular s hs
      let first := Fin.castAdd n (0 : Fin 1)
      C'.repr y.1 0 = C.repr x.1 0 + x.2 j ∧ C'.repr y.1 1 = C.repr x.1 1 ∧
      y.2 = Fin.append (fun _ : Fin 1 ↦ -C.repr x.1 1 - x.2 j) (x.2 ∘ j.succAbove) ∧
      (∃ τ : B.fan.cones, τ.val = hull ℝ {i (d 0), i (d 1)} ∧
        hU.baseCenter first = (B.fan.distinguishedSection (R := k₀) τ) pt) ∧
      (∀ (l : Fin n) (c : k₀ˣ), hT.baseCenter (j.succAbove l) = center[b,r 1,c] →
        hU.baseCenter (l.natAdd 1) = hU.baseCenter first ∧
          -x.2 (j.succAbove l) ≤ -y.2 first) ∧
      (∀ (l : Fin n) (c : k₀ˣ), hT.baseCenter (j.succAbove l) = center[b,r 3,c] →
        ∃ c' : k₀ˣ, hU.baseCenter (l.natAdd 1) = center[d,s 3,c'] ∧
          ((∀ m < j.succAbove l, hT.baseCenter m ≠ hT.baseCenter (j.succAbove l)) →
            ∀ m < l.natAdd 1, hU.baseCenter m ≠ hU.baseCenter (l.natAdd 1))) ∧
      hU.strictTransformCoefficients (B.fan.rayDivisorIdeal k₀ B.isRegular (s 2)) =
        Fin.append (0 : Fin 1 → ℤ)
          (hT.strictTransformCoefficients (Φ.rayDivisorIdeal k₀ hΦ (r 2)) ∘ j.succAbove) ∧
      let f := ruling[b,(e : ℤ),r,hr]
      let q := ruling[d,((e - 1 : ℕ) : ℤ),s,hs]
      ∀ l : Fin n, hT.baseCenter (j.succAbove l) ≠ hT.baseCenter j →
        (∀ a < j.succAbove l, hT.baseCenter a ≠ hT.baseCenter (j.succAbove l)) →
        ∃ a : Fin (1 + n), (∀ k < a, hU.baseCenter k ≠ hU.baseCenter a) ∧
          q (hU.baseCenter a) = f (hT.baseCenter (j.succAbove l)) ∧ -x.2 (j.succAbove l) ≤ -y.2 a ∧
          (f (hT.baseCenter (j.succAbove l)) = f (hT.baseCenter j) → a = 0) ∧
          (f (hT.baseCenter (j.succAbove l)) ≠ f (hT.baseCenter j) →
            a = l.natAdd 1 ∧ y.2 a = x.2 (j.succAbove l)) := by
  intro hcones hdim hnoeth hOver hProjection hdimY hSmoothY hInt hMod x C hpole A
  let := hcones
  let := hdim
  let := hnoeth
  let := hOver
  let := hProjection
  let := hdimY
  let := hSmoothY
  let := hInt
  let := hMod
  -- Put the positive section first to apply the signed corner formula.
  obtain ⟨b₀, r₀, hr₀, hb₀, hb₁, h₀, h₁, -, h₃, -, hrepr⟩ :=
    Φ.exists_hirzebruchPicardBasis_opposite_section k₀ b (e : ℤ) hΦ r hr
  have hcone : σ.val = hull ℝ (Set.range (i ∘ b₀)) := by
    rw [hσ]
    congr 1
    ext u
    simp [Fin.exists_fin_succ, hb₀, hb₁, eq_comm]
  obtain ⟨B, path, d₀, s₀, hs₀, Z, U, hU, k, hlen, htoric, hB, hproj, hg', hbir', hpole',
    ⟨τ, hτ, hhead⟩, hcoll, hstay, hsection, ha, hβ, horders, -, -, hretained⟩ :=
    hT.exists_sarkisov_path_of_toric_corner k₀ b₀ (-(e : ℤ)) hΦ hc r₀ hr₀ g hg hbir σ hcone j
      hj hfirst D hpole
  let : Nonempty B.fan.cones := B.isComplete.nonempty_cones
  -- Swap the sections even at index zero to keep track of the reverse corner.
  obtain ⟨d, s, hs, hd₀, hd₁, -, -, hs₂, hs₃, -, hrepr'⟩ :=
    B.fan.exists_hirzebruchPicardBasis_opposite_section k₀ d₀ (-(e : ℤ) + 1) B.isRegular s₀ hs₀
  have he' : -(-(e : ℤ) + 1) = ((e - 1 : ℕ) : ℤ) := by omega
  rw [← he']
  refine ⟨B, path, d, s, hs, Z, U, hU, k, hlen, htoric, hB, hproj, hg', hbir', hpole', ?_⟩
  intro y C' first
  have hdimB : SmoothOfRelativeDimension 2 (B.fan.finiteFanSchemeToSpec k₀) := by
    simpa only [rankTwo(b)] using
      B.fan.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ B.isRegular
  let : SmoothOfRelativeDimension 2 f[B.fan] :=
    (Fan.finiteFanScheme_over k₀ (Φ := B.fan)).symm ▸ hdimB
  rw [(hrepr' y.1).1, (hrepr' y.1).2, ha, hβ, (hrepr x.1).1, (hrepr x.1).2]
  have hβ₀ := (hrepr (coordinates(T,hT,g,f[Φ])).1).2
  have horders' : y.2 = Fin.append (fun _ : Fin 1 ↦ -C.repr x.1 1 - x.2 j)
      (x.2 ∘ j.succAbove) := by
    simpa only [x, y, C, hβ₀] using horders
  refine ⟨by ring, rfl, horders', ⟨τ, by rw [hτ, hd₀, hd₁, Set.pair_comm], hhead⟩, ?_, ?_, ?_, ?_⟩
  · intro l c hl
    obtain ⟨c₀, hc₀⟩ := (r₀ 1).exists_binomialCenter_eq_of_basis k₀ b₀ b c
    have hl' : hT.baseCenter (j.succAbove l) = center[b₀,r₀ 1,c₀] := by
      rw [hc₀, h₁]
      exact hl
    have hsame := hcoll l c₀ hl'
    -- The contracted mark is now over the first point of the new tower.
    obtain ⟨a, ha', hfirst', hle⟩ := hU.exists_first_baseCenter_ge_of_plane_resolution
      (k.inv ≫ g) hg' (l.natAdd 1)
    have ha₀ : a = first := by
      by_contra hne
      have hlt : first < a := lt_of_le_of_ne (Fin.zero_le a) (Ne.symm hne)
      exact hfirst' first hlt (hsame.symm.trans ha'.symm)
    have hle' : -y.2 (l.natAdd 1) ≤ -y.2 first := by simpa only [ha₀, y] using hle
    exact ⟨hsame, by simpa only [horders', Fin.append_right, Function.comp_apply] using hle'⟩
  · intro l c hl
    obtain ⟨c₀, hc₀⟩ := (r₀ 3).exists_binomialCenter_eq_of_basis k₀ b₀ b c
    have hl' : hT.baseCenter (j.succAbove l) = center[b₀,r₀ 3,c₀] := by rw [hc₀, h₃]; exact hl
    obtain ⟨c', hc', hfirst'⟩ := hstay l c₀ hl'
    obtain ⟨c'', hc''⟩ := (s 3).exists_binomialCenter_eq_of_basis k₀ d d₀ c'
    refine ⟨c'', ?_, hfirst'⟩
    rw [hc'', hs₃]
    exact hc'
  · simpa only [h₀, hs₂] using hsection
  · have coord_eq (u v : Basis (Fin 2) ℤ N) (h₀ : v 0 = -u 0) (h₁ : v 1 = u 1) :
        v.coord 1 = u.coord 1 := v.ext fun l ↦ by
      simp only [Basis.coord_apply, Basis.repr_self]
      fin_cases l <;> simp [h₀, h₁]
    simpa only [congrArg LinearMap.toAddMonoidHom (coord_eq b b₀ hb₀ hb₁),
      congrArg LinearMap.toAddMonoidHom (coord_eq d₀ d hd₀ hd₁)] using hretained

end QPainleve.BlowupTower.IsClosedPointTower
