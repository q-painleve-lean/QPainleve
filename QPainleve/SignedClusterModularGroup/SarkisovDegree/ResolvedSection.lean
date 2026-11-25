/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Factorization
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.LogarithmicSection

import QPainleve.Geometry.Toric.Fan.Mutation.Center
import QPainleve.Geometry.Toric.Fan.Mutation.Orientation

/-!
# Resolved Sarkisov path at a smooth section point

A pivot at a smooth point of either Hirzebruch section gives a single
resolved mutation between the specified projections. A nonnegative Hirzebruch
marking on the target retains the fiber degree. Low-order pivots on the
positive section can be used to prepare the quadric, and high-order pivots
decrease the Sarkisov bidegree.
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
  {i : N →+ V} {Φ : Fan i}
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
local notation "sourceOpen[" c "," h "]" => Φ.mutationComplement b
  (Φ.detCharacter_nonneg_or_nonpos b hv hp h) (c : ℂ)
local notation "targetOpen[" c "," h "]" => Fan.mutationComplement (Ψ[h]) b
  (Φ.mutationDetCharacter_nonneg_or_nonpos b hv hp h) (c : ℂ)
local notation "complementIso[" c "," h "]" => Φ.mutationComplementIso b (c : ℂ) hv hp h
local notation "node[" Δ "," σ "]" =>
  Fan.distinguishedPointHom Δ σ (IsLocalRing.closedPoint ℂ)
local notation "fiber[" l "]" => ((![1, 3] : Fin 2 → Fin 4) l)
local notation "center[" b "," τ "," c "]" =>
  Fan.Ray.binomialCenter τ rankTwo (Basis.detDualEquiv_self b (Fan.Ray.primitiveGenerator τ))
    (Fan.Ray.surjective_detCharacter τ b) c (IsLocalRing.closedPoint ℂ)
local notation "coordinatePoint[" t "]" =>
  TauCeti.AlgebraicGeometry.projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) t 0
    (IsLocalRing.closedPoint ℂ : S)

local notation "ruling[" Δ "," b "," a "," r "," hr "]" =>
  Fan.characterRuling Δ (LinearMap.toAddMonoidHom (Basis.coord b 1))
    (Fan.nonneg_or_nonpos_hirzebruch_ruling_character b a r hr)
local notation "e'" => ite (onSection = true) ((e : ℤ) + 1) ((e : ℤ) - 1)

variable {n : ℕ} {Y : Scheme} {T : BlowupTower X[Φ] (n + 1) Y}
  (hT : IsClosedPointTower X[Φ] T)
  (g : Y ⟶ P) (hg : g ≫ (P ↘ S) = T.toBase ≫ f[Φ])
  (hbir : Scheme.BirationalOver g (𝟙 P))

include hr in
private theorem invariant_fiber_ne_section_rays (l : Fin 2)
    (hρ : ρ = r (if onSection then 0 else 2)) :
    (r (fiber[l])).primitiveGenerator ≠ pivot ∧
      (r (fiber[l])).primitiveGenerator ≠ -pivot := by
  have hsection : b.coord 1 pivot = 0 := by
    rw [congrArg Fan.Ray.primitiveGenerator hρ]
    split <;> simp [congrFun hr 0, congrFun hr 2, Basis.coord_apply]
  have hfiber : b.coord 1 ((r (fiber[l])).primitiveGenerator) ≠ 0 := by
    have h : ∀ u : Fin 2, fiber[u] = 1 ∨ fiber[u] = 3 :=
      Fin.forall_fin_two.mpr ⟨Or.inl rfl, Or.inr rfl⟩
    rcases h l with h | h <;> simp [h, congrFun hr 1, congrFun hr 3, Basis.coord_apply]
  refine ⟨fun h ↦ hfiber ((congrArg (b.coord 1) h).trans hsection), ?_⟩
  intro h
  apply hfiber
  rw [h, map_neg, hsection, neg_zero]

include hΦ in
private theorem exists_sarkisov_path_of_resolved_section (c : ℂˣ)
    (hOpp : hull ℝ {i (-pivot)} ∈ Φ.cones)
    [Nonempty Φ.cones] [SmoothOfRelativeDimension 2 f[Φ]]
    [Nonempty (Ψ[hOpp]).cones] [SmoothOfRelativeDimension 2 f[Ψ[hOpp]]]
    [IsIntegral Y]
    {Z : Scheme} {U : BlowupTower X[Ψ[hOpp]] (1 + n) Z} (hU : IsClosedPointTower X[Ψ[hOpp]] U)
    (k : Y ≅ Z) (hOver : k.hom ≫ U.toBase ≫ f[Ψ[hOpp]] = T.toBase ≫ f[Φ])
    (D : Y.IdealSheafData) (hD : B[Φ,hc].comap T.toBase = D * hT.ramificationIdealSheafToBase ℂ)
    (hPole : B[Ψ[hOpp],comp[hOpp]].comap U.toBase =
      D.comap k.inv * hU.ramificationIdealSheafToBase ℂ) :
    let : Y.Over S := ⟨T.toBase ≫ f[Φ]⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f[Φ]
    let : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two f[Φ]
    T.toBase.toRationalMap.comp μ[c,hOpp] = (k.hom ≫ U.toBase).toRationalMap →
    ∃ (A B : LogarithmicProjection i D) (p : SarkisovPath A B),
      A.fan = Φ ∧ A.hom ≍ T.toBase ∧ B.fan = Ψ[hOpp] ∧ B.hom ≍ k.hom ≫ U.toBase ∧
      p.length = 1 ∧ p.rationalMap ≍ μ[c,hOpp] := by
  intro hY hdimY hmod hlink
  let := hY
  let := hdimY
  let := hmod
  let : IsModification U.toBase :=
    hU.isModification_of_smoothOfRelativeDimension_two f[Ψ[hOpp]]
  let : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let A : LogarithmicProjection i D :=
    ⟨Φ, hΦ, hc, T.toBase, ⟨rfl⟩, inferInstance, (hT.ramificationIdealSheafToBase_def ℂ) ▸ hD⟩
  let : (k.hom ≫ U.toBase).IsOver S := ⟨(Category.assoc _ _ _).trans hOver⟩
  -- Compare both boundary pullbacks on the original resolving surface.
  have hram := hU.comap_ramificationIdealSheafToBase ℂ k (f := k.hom ≫ U.toBase) rfl
  have hD' : B[Ψ[hOpp],comp[hOpp]].comap (k.hom ≫ U.toBase) =
      D * ramificationIdealSheaf ℂ (k.hom ≫ U.toBase) := by
    rw [comap_comp, hPole, comap_mul, hram, ← comap_comp, k.hom_inv_id,
      Scheme.IdealSheafData.comap_id]
  let B : LogarithmicProjection i D :=
    ⟨Ψ[hOpp], reg[hOpp], comp[hOpp], k.hom ≫ U.toBase, inferInstance, inferInstance, hD'⟩
  let a : SarkisovStep A B := ⟨μ[c,hOpp], .mutation b ρ c hOpp, hlink⟩
  exact ⟨A, B, Quiver.Hom.toPath a, rfl, HEq.rfl, rfl, HEq.rfl, rfl, by
    simp only [Quiver.Hom.toPath, SarkisovPath.rationalMap_cons, SarkisovPath.rationalMap_nil,
      Scheme.RationalMap.id_comp]
    rfl⟩

variable [X[Φ].IsProjectiveOver ℂ]

include hg hbir in
/-- The first center over a smooth section point gives a one-edge Sarkisov
path on the given resolving surface.
The terminal projection is the transported tower projection, and the target
Hirzebruch marking has index `|e ± 1|` and the same fiber degree. When the
signed index is nonnegative, the section labels are preserved and the fiber
coefficient changes by `-m` for a pivot of order `m` on the second section,
or by `β - m` on the first section. The reverse base order comes first,
and the other exceptional coordinates keep their order. With nonnegative
signed index, a marked open-orbit center on either invariant fiber stays
on that fiber's open orbit. A retained corner goes to the corner of the sheared
cone, with the same incidence with each sheared ray. First occurrences in the
tower remain first for both kinds of center. The indices on the successive
strict transforms of the pivot section are exactly the reindexed original
section indices with the pivot removed.
A retained center over either invariant fiber keeps the same ruling value in
the normalized marking, including at index zero, and preserves its first
occurrence. A pivot order greater than half the fiber degree strictly lowers
the Sarkisov bidegree. -/
theorem exists_sarkisov_path_of_smooth_section
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
      (0 ≤ e' → t = r.trans (Φ.mutationFanRayEquiv b hv hp hOpp)) ∧
      (0 ≤ e' → ∀ (l : Fin 2) (a : ℂˣ) (m : Fin n),
        hT.baseCenter (j.succAbove m) = center[b,r (fiber[l]),a] →
        ∃ a' : ℂˣ, hU.baseCenter (m.natAdd 1) = center[d,t (fiber[l]),a'] ∧
          ((∀ u < j.succAbove m, hT.baseCenter u ≠ hT.baseCenter (j.succAbove m)) →
            ∀ u < m.natAdd 1, hU.baseCenter u ≠ hU.baseCenter (m.natAdd 1))) ∧
      (∀ (σ : Φ.cones) (m : Fin n), Nat.card (ToricRay σ.val) = 2 →
        hT.baseCenter (j.succAbove m) = node[Φ,σ] →
        let σ' := Φ.mutationFanConeEquiv b hv hp hOpp σ
        Nat.card (ToricRay σ'.val) = 2 ∧ hU.baseCenter (m.natAdd 1) = node[Ψ,σ'] ∧
          (∀ u : Φ.Ray, (Φ.mutationFanRayEquiv b hv hp hOpp u).toCone ≤ σ' ↔ u.toCone ≤ σ) ∧
          ((∀ u < j.succAbove m, hT.baseCenter u ≠ hT.baseCenter (j.succAbove m)) →
            ∀ u < m.natAdd 1, hU.baseCenter u ≠ hU.baseCenter (m.natAdd 1))) ∧
      hU.strictTransformCenterIndices
          (Ψ.rayBoundaryIdeal (reg[hOpp]) ((Φ.mutationFanRayEquiv b hv hp hOpp) ρ)) =
        (Finset.univ.filter fun l : Fin n ↦
          j.succAbove l ∈ hT.strictTransformCenterIndices (Φ.rayBoundaryIdeal hΦ ρ)).map
            (Fin.natAddEmb 1) ∧
      (let q := ruling[Φ,b,e,r,hr]
       let q' := ruling[Ψ,d,Int.natAbs e',t,ht]
       ∀ (l : Fin n) (t : Fin 2), q (hT.baseCenter (j.succAbove l)) = coordinatePoint[t] →
         q' (hU.baseCenter (l.natAdd 1)) = coordinatePoint[t] ∧
           ((∀ a < j.succAbove l, hT.baseCenter a ≠ hT.baseCenter (j.succAbove l)) →
             ∀ a < l.natAdd 1, hU.baseCenter a ≠ hU.baseCenter (l.natAdd 1))) ∧
      let y := (U.picardMarking hU f[Ψ]).symm (Additive.ofMul (pullback (k.inv ≫ g) H))
      let C := Fan.hirzebruchPicardBasis b e hΦ r hr
      let C' := Fan.hirzebruchPicardBasis d (Int.natAbs e' : ℤ) (reg[hOpp]) t ht
      let β' := C'.repr y.1 1
      (0 ≤ e' → C'.repr y.1 0 = C.repr x.1 0 + x.2 j + (if onSection then β else 0)) ∧
      β' = β ∧
      y.2 = Fin.addCases (fun _ : Fin 1 ↦ -β - x.2 j) (x.2 ∘ j.succAbove) ∧
      (β < 2 * (-x.2 j) →
        hirzebruchSarkisovBidegree β'.toNat (∑ l, -y.2 l).toNat <
          hirzebruchSarkisovBidegree β.toNat (∑ l, -x.2 l).toNat) := by
  intro hcones hdim hnoeth hY hdimY hInt x β hD hOpp Ψ hcones' hdim' hnoeth'
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
  obtain ⟨hproj, d₀, ht₀, Z, U, hU, k, hlink, hOver, hg', hbir', hPole,
    hcenters, hsection, hRuling, hDecrease⟩ :=
    hT.exists_sarkisov_link_of_logarithmic_smooth_section b e hΦ hc r hr onSection
      ρ hOpp c g hg hbir hρ j hj (by simpa only [← hj] using hfirst) D hD
  obtain ⟨d, t, ht, -, hmark, hcoord, hfiber⟩ :=
    Fan.exists_hirzebruchPicardBasis_natAbs d₀ e' (reg[hOpp]) _ ht₀
  refine ⟨hproj, Z, U, hU, k, d, t, ht, hg', hbir', hPole, ?_,
    fun he ↦ (hmark he).1, ?_, ?_, hsection, ?_, ?_⟩
  · exact exists_sarkisov_path_of_resolved_section b hΦ hc r s hT c hOpp hU k hOver D hD hPole hlink
  · intro he l a m hm
    let τ := r (fiber[l])
    let τ' := (Φ.mutationFanRayEquiv b hv hp hOpp) τ
    obtain ⟨hne, hneg⟩ := invariant_fiber_ne_section_rays b e r hr s l hρ
    obtain ⟨p, hp₀, hp₁⟩ := Φ.exists_binomialCenter_mutationComplementIso b τ hv hp hOpp c a
      (Fan.Ray.primitiveGenerator_isPrimitive ρ) (fun h ↦ (hne h).elim) (fun h ↦ (hneg h).elim)
    let pt := IsLocalRing.closedPoint ℂ
    have hsrc : (sourceOpen[c,hOpp]).ι (p pt) = hT.baseCenter (j.succAbove m) :=
      (congrArg (fun f : S ⟶ X[Φ] ↦ f pt) hp₀).trans hm.symm
    have hmem : hT.baseCenter (j.succAbove m) ∈ sourceOpen[c,hOpp] :=
      hsrc ▸ (p pt).property
    obtain ⟨himage, hfirst'⟩ := hcenters m hmem
    have hz : (⟨hT.baseCenter (j.succAbove m), hmem⟩ : (sourceOpen[c,hOpp]).toScheme) = p pt :=
      Subtype.ext hsrc.symm
    rw [hz] at himage
    obtain ⟨a', ha'⟩ := τ'.exists_binomialCenter_eq_of_basis d b _
    rw [(hmark he).1]
    refine ⟨a', himage.trans ?_, hfirst'⟩
    exact congrArg (fun f : S ⟶ X[Ψ] ↦ f pt) (hp₁.trans ha'.symm)
  · intro σ m hσ hm σ'
    obtain ⟨hmem, hcard, himage⟩ := Φ.mutationComplementIso_apply_distinguishedPointHom
      b hv hp hOpp c hΦ hσ (IsLocalRing.closedPoint ℂ)
    obtain ⟨hcenter, hfirst'⟩ := hcenters m (hm.symm ▸ hmem)
    have hlift : (⟨hT.baseCenter (j.succAbove m), hm.symm ▸ hmem⟩ :
        (sourceOpen[c,hOpp]).toScheme) = ⟨node[Φ,σ], hmem⟩ := Subtype.ext hm
    rw [hlift] at hcenter
    refine ⟨hcard, hcenter.trans himage, fun u ↦ ?_, hfirst'⟩
    rw [Fan.mutationFanRayEquiv_toCone, OrderIso.le_iff_le]
  · intro q q'
    have hχ := congrArg LinearMap.toAddMonoidHom hcoord
    simpa only [q, q', hχ] using hRuling
  · obtain ⟨ha, hβ, horders, -, hlt⟩ := hDecrease
    dsimp only
    rw [hfiber]
    refine ⟨fun he ↦ ?_, hβ, horders, hlt⟩
    rw [(hmark he).2]
    exact ha

end QPainleve.BlowupTower.IsClosedPointTower
