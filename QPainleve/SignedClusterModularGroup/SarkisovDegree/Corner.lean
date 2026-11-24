/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Ramification
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Reorder
public import QPainleve.Geometry.Toric.Fan.Birational
public import QPainleve.Geometry.Toric.Fan.Boundary.Basic
public import QPainleve.Geometry.Toric.Fan.Ruling.Basic
public import QPainleve.Geometry.Toric.Fan.Smooth
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.ToricLink

import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.Morphisms.Modification.Birational
import QPainleve.AlgebraicGeometry.RationalMap.FunctionField
import QPainleve.Geometry.Toric.Fan.Logarithmic.Subdivision
import QPainleve.Geometry.Toric.Fan.Ruling.FixedPoint
import QPainleve.Geometry.Toric.Fan.Ruling.Subdivision
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition

/-!
# Sarkisov degree decrease at a toric corner

A specified resolution lifts to the common toric blowup once the first center
over the chosen corner has been moved to the front. Both projections of the
elementary link are then regular on the original resolution, and the reverse
projection has the transformed Picard coordinates.

This is the torus-fixed case of Proposition 8.11 in
[Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module PointedCone TauCeti.Toric
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} {n : ℕ} {Y P : Scheme}

local notation "X[" Δ "]" => Fan.algebraicRealization Δ
local notation "f[" Δ "]" => Fan.algebraicRealizationStructureMap Δ
local notation "rays[" Δ "]" => Set.range (Fan.Ray.primitiveGenerator (Phi := Δ))
local notation "I[" σ "]" => Scheme.Hom.ker (Fan.distinguishedPointHom _ σ)
local notation "S" => Spec (CommRingCat.of ℂ)
local notation "π[" s "]" => FanHom.algebraicMap (Fan.IsSubdivision.toFanHom s)
local notation "B[" F "," hc "]" => Fan.boundaryIdeal F (Fan.IsComplete.nonempty_cones hc)
local notation "rankTwo(" b ")" =>
  Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)

private theorem isModification_corner_projection {F : Fan i} [Nonempty Φ.cones]
    [SmoothOfRelativeDimension 2 f[Φ]] (σ : Φ.cones) (s : F.IsSubdivision Φ)
    (v : X[F] ≅ (I[σ]).blowup)
    (hv : v.hom ≫ (I[σ]).blowupToBase = π[s]) :
    IsModification π[s] := by
  have hσ : IsClosedPointTower X[Φ] (BlowupTower.nil.snoc (I[σ])) :=
    .snoc .nil _ (Φ.isClosed_singleton_distinguishedPoint σ)
      (Φ.distinguishedPointHom σ).ker_eq_ker_fromSpecResidueField
  have : IsModification (I[σ]).blowupToBase := by
    simpa only [toBase_snoc, toBase_nil, Category.comp_id] using
      hσ.isModification_of_smoothOfRelativeDimension_two f[Φ]
  rw [← hv]
  infer_instance

private theorem toric_corner_baseCenter_ruling {F Ψ : Fan i}
    (b d : Basis (Fin 2) ℤ N) (σ : Φ.cones) (τ : Ψ.cones)
    (hσ : σ.val = hull ℝ (Set.range (i ∘ b))) (hτ : τ.val = hull ℝ {i (d 1), i (-d 0)})
    (hd₀ : d 0 = b 0) (hd₁ : d 1 = b 0 + b 1) (s : F.IsSubdivision Φ) (t : F.IsSubdivision Ψ)
    {p : Fin (n + 1) → X[Φ]} {q : Fin (1 + n) → X[Ψ]} (j : Fin (n + 1))
    (hp : p j = Φ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ))
    (hq : q (Fin.castAdd n (0 : Fin 1)) = Ψ.distinguishedPointHom τ (IsLocalRing.closedPoint ℂ))
    (hpts : ∀ l : Fin n, ∃ z : X[F], s.toFanHom.algebraicMap z = p (j.succAbove l) ∧
      t.toFanHom.algebraicMap z = q (l.natAdd 1))
    (h₀ : ∀ γ : Φ.cones, (∀ x ∈ γ.val, 0 ≤ Φ.lattice.realCharacter
      (b.coord 1).toAddMonoidHom x) ∨ ∀ x ∈ γ.val,
        Φ.lattice.realCharacter (b.coord 1).toAddMonoidHom x ≤ 0)
    (h₁ : ∀ γ : Ψ.cones, (∀ x ∈ γ.val, 0 ≤ Ψ.lattice.realCharacter
      (b.coord 1).toAddMonoidHom x) ∨ ∀ x ∈ γ.val,
        Ψ.lattice.realCharacter (b.coord 1).toAddMonoidHom x ≤ 0)
    (l : Fin (1 + n)) :
    Ψ.characterRuling (b.coord 1).toAddMonoidHom h₁ (q l) =
      Φ.characterRuling (b.coord 1).toAddMonoidHom h₀
        (Fin.addCases (fun _ : Fin 1 ↦ p j) (p ∘ j.succAbove) l) := by
  induction l using Fin.addCases with
  | left l =>
    rw [Subsingleton.elim l (0 : Fin 1), Fin.addCases_left, hq, hp]
    exact (Fan.characterRuling_distinguishedPointHom_eq_of_hirzebruch_link
      b d hd₀ hd₁ σ τ hσ hτ h₀ h₁ (IsLocalRing.closedPoint ℂ)).symm
  | right l =>
    obtain ⟨z, hz, hz'⟩ := hpts l
    have h := s.comp_characterRuling_eq t (b.coord 1).toAddMonoidHom h₀ h₁
    simpa only [Fin.addCases_right, Function.comp_apply, Scheme.Hom.comp_apply, hz, hz'] using
      congrArg (fun f ↦ f z) h.symm

/-- Perform the toric elementary link at the first center over the selected
corner of a specified Hirzebruch resolution. The two projections from the
common toric blowup are regular lifts of the link on the original resolution.
The map to the common blowup is a modification. Both partial composites
represent the corresponding canonical dense-torus changes.
Any pole ideal for the original projection is also the pole ideal for both
partial composites. On the returned tower it pulls back along the inverse of
the resolving isomorphism.
The new point tower retains the specified birational morphism up to the
displayed isomorphism over the base field. Each retained center comes from a
point of the common blowup. The reverse center lies over the same point of the
ruling as the selected center, and every other center retains its ruling value.

For a class with fiber and section coefficients `a, β` and selected base order
`m`, the new coordinates are `a + β - m, β` with reverse order `β - m`.
All other orders keep their relative order, including infinitely near centers,
and the total order changes by `β - 2 * m`. When `β / 2 < m ≤ β` and the
original orders are nonnegative, the Sarkisov bidegree decreases strictly. -/
theorem exists_sarkisov_decrease_of_toric_corner
    (b : Basis (Fin 2) ℤ N) (e : ℤ) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (hrays : rays[Φ] = {b 0, b 1, -b 0, e • b 0 - b 1})
    (σ : Φ.cones) (hσ : σ.val = hull ℝ (Set.range (i ∘ b)))
    {T : BlowupTower X[Φ] (n + 1) Y} (hT : IsClosedPointTower X[Φ] T)
    (j : Fin (n + 1))
    (hj : hT.baseCenter j = Φ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ))
    (hfirst : ∀ l < j, hT.baseCenter l ≠ Φ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ))
    (g : Y ⟶ P) (p : P ⟶ S) (hg : g ≫ p = T.toBase ≫ f[Φ])
    (hbir : Scheme.BirationalOver g (𝟙 P)) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let hdim : SmoothOfRelativeDimension 2 f[Φ] :=
      rankTwo(b) ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : IsIntegral Y := hT.isIntegral f[Φ]
    let : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two f[Φ]
    ∃ (Ψ F : Fan i) (hΨ : Ψ.IsRegular) (_ : F.IsRegular)
      (hc' : Ψ.IsComplete) (hcF : F.IsComplete) (d : Basis (Fin 2) ℤ N)
      (τ : Ψ.cones) (s : F.IsSubdivision Φ) (t : F.IsSubdivision Ψ)
      (v : X[F] ≅ (I[σ]).blowup) (v' : X[F] ≅ (I[τ]).blowup) (q : Y ⟶ X[F])
      (r : Fin 4 ≃ Φ.Ray) (r' : Fin 4 ≃ Ψ.Ray)
      (hr : (fun l ↦ (r l).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])
      (hr' : (fun l ↦ (r' l).primitiveGenerator) = ![d 0, d 1, -d 0, (e + 1) • d 0 - d 1])
      (Z : Scheme) (U : BlowupTower X[Ψ] (1 + n) Z)
      (hU : IsClosedPointTower X[Ψ] U) (k : Y ≅ Z),
      d 0 = b 0 ∧ d 1 = b 0 + b 1 ∧ τ.val = hull ℝ {i (d 1), i (-d 0)} ∧
      v.hom ≫ (I[σ]).blowupToBase = s.toFanHom.algebraicMap ∧
      v'.hom ≫ (I[τ]).blowupToBase = t.toFanHom.algebraicMap ∧
      q ≫ s.toFanHom.algebraicMap = T.toBase ∧
      q ≫ t.toFanHom.algebraicMap = k.hom ≫ U.toBase ∧
      (∀ l : Fin n, ∃ z : X[F],
        s.toFanHom.algebraicMap z = hT.baseCenter (j.succAbove l) ∧
        t.toFanHom.algebraicMap z = hU.baseCenter (l.natAdd 1)) ∧
      (∀ (h₀ : ∀ γ : Φ.cones, (∀ x ∈ γ.val, 0 ≤ Φ.lattice.realCharacter
        (b.coord 1).toAddMonoidHom x) ∨ ∀ x ∈ γ.val,
          Φ.lattice.realCharacter (b.coord 1).toAddMonoidHom x ≤ 0)
        (h₁ : ∀ γ : Ψ.cones, (∀ x ∈ γ.val, 0 ≤ Ψ.lattice.realCharacter
          (b.coord 1).toAddMonoidHom x) ∨ ∀ x ∈ γ.val,
            Ψ.lattice.realCharacter (b.coord 1).toAddMonoidHom x ≤ 0) (l : Fin (1 + n)),
        Ψ.characterRuling (b.coord 1).toAddMonoidHom h₁ (hU.baseCenter l) =
          Φ.characterRuling (b.coord 1).toAddMonoidHom h₀
            (Fin.addCases (fun _ : Fin 1 ↦ hT.baseCenter j) (hT.baseCenter ∘ j.succAbove) l)) ∧
      (k.inv ≫ g) ≫ p = U.toBase ≫ f[Ψ] ∧
      Scheme.BirationalOver (k.inv ≫ g) (𝟙 P) ∧
      IsModification q ∧
      let : Nonempty F.cones := hcF.nonempty_cones
      let : Nonempty Ψ.cones := hc'.nonempty_cones
      T.toBase.toRationalMap.comp (Φ.denseTorusPartialIso F).toRationalMap = q.toRationalMap ∧
      T.toBase.toRationalMap.comp (Φ.denseTorusPartialIso Ψ).toRationalMap =
        (k.hom ≫ U.toBase).toRationalMap ∧
      (∃! φ : X[Φ] ⤏ X[Ψ], (π[s]).toRationalMap.comp φ = (π[t]).toRationalMap ∧
        T.toBase.toRationalMap.comp φ = (k.hom ≫ U.toBase).toRationalMap) ∧
      (letI : SmoothOfRelativeDimension 2 (X[Φ] ↘ S) := by
         rw [Fan.algebraicRealization_over]
         exact hdim
       letI : SmoothOfRelativeDimension 2 (X[Ψ] ↘ S) := by
         rw [Fan.algebraicRealization_over]
         exact rankTwo(b) ▸ Ψ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΨ
       letI : Y.Over S := ⟨T.toBase ≫ X[Φ] ↘ S⟩
       letI : Smooth (Y ↘ S) := (hT.smoothOfRelativeDimension (X[Φ] ↘ S)).smooth
       ∃ (_ : q.IsOver S) (_ : (k.hom ≫ U.toBase).IsOver S),
         ∀ D : Y.IdealSheafData,
           B[Φ,hc].comap T.toBase = D * hT.ramificationIdealSheafToBase ℂ →
             B[F,hcF].comap q = D * ramificationIdealSheaf ℂ q ∧
             B[Ψ,hc'].comap (k.hom ≫ U.toBase) =
               D * ramificationIdealSheaf ℂ (k.hom ≫ U.toBase) ∧
             B[Ψ,hc'].comap U.toBase = D.comap k.inv * hU.ramificationIdealSheafToBase ℂ) ∧
      let C := Fan.hirzebruchPicardBasis b e hΦ r hr
      let C' := Fan.hirzebruchPicardBasis d (e + 1) hΨ r' hr'
      ∀ (a β : ℤ) (x : Fin (n + 1) → ℤ),
        let x' := Fin.append (fun _ : Fin 1 ↦ -β - x j) (x ∘ j.succAbove)
        pullback k.hom (U.picardHom ((a + β + x j) • C' 0 + β • C' 1, x')).toMul =
          (T.picardHom (a • C 0 + β • C 1, x)).toMul ∧
        (∑ l, -x' l) = (∑ l, -x l) + β + 2 * x j ∧
        ((∀ l, 0 ≤ -x l) → -x j ≤ β → β < 2 * (-x j) →
          hirzebruchSarkisovBidegree β.toNat (∑ l, -x' l).toNat <
            hirzebruchSarkisovBidegree β.toNat (∑ l, -x l).toNat) := by
  intro hcones hdim hintegral hmod
  let := hcones
  let := hdim
  let := hintegral
  let := hmod
  have hI := (Φ.distinguishedPointHom σ).ker_eq_ker_fromSpecResidueField
  have hmove := hT.exists_move_closed_point_blowup_to_front j
    (Φ.isClosed_singleton_distinguishedPoint σ) hj hfirst
  rw [← hI] at hmove
  obtain ⟨W, A, h, hA, hbase, hE, hcenters, htail⟩ := hmove
  obtain ⟨Ψ, F, hΨ, hF, hc', hcF, d, τ, s, t, v, v', r, r', hr, hr', Z, A', k,
      hU, hd₀, hd₁, hτ, hv, hv', hproj, hhead, htarget, hcoord⟩ :=
    hA.exists_hirzebruch_toric_link_resolution b e hΦ hc hrays σ hσ
  let U := (BlowupTower.nil.snoc (I[τ])).append A'
  -- The common blowup gives both projections and hence the ruling comparison.
  let q := h.hom ≫ A.toBase ≫ v.inv
  let k' := h ≪≫ k
  have hq : q ≫ s.toFanHom.algebraicMap = T.toBase := by
    simp only [q, Category.assoc, ← hv, Iso.inv_hom_id_assoc, hbase]
  have hq' : q ≫ t.toFanHom.algebraicMap = k'.hom ≫ U.toBase := by
    simp only [q, k', U, Iso.trans_hom, Category.assoc, hproj]
  have hover : (k'.inv ≫ g) ≫ p = U.toBase ≫ f[Ψ] := by
    apply (cancel_epi k'.hom).mp
    rw [← Category.assoc k'.hom, Iso.hom_inv_id_assoc, hg, ← hq, ← reassoc_of% hq']
    simp only [Category.assoc, FanHom.algebraicMap_comp_algebraicRealizationStructureMap]
  have hbir' : Scheme.BirationalOver (k'.inv ≫ g) (𝟙 P) :=
    Scheme.BirationalOver.trans (sY := g)
      ⟨.ofIso k'.symm, by simp [Scheme.PartialIso.IsOver, Scheme.PartialIso.ofIso]⟩ hbir
  have hpts (l : Fin n) : ∃ z : X[F],
      s.toFanHom.algebraicMap z = hT.baseCenter (j.succAbove l) ∧
      t.toFanHom.algebraicMap z = hU.baseCenter (l.natAdd 1) := by
    refine ⟨v.inv (hA.baseCenter l), ?_, htarget l⟩
    rw [← Scheme.Hom.comp_apply, ← hv, Iso.inv_hom_id_assoc, hcenters]
  refine ⟨Ψ, F, hΨ, hF, hc', hcF, d, τ, s, t, v, v', q, r, r', hr, hr', Z, U, hU, k',
    hd₀, hd₁, hτ, hv, hv', hq, hq', hpts,
    toric_corner_baseCenter_ruling b d σ τ hσ hτ hd₀ hd₁ s t j hj hhead hpts, hover, hbir', ?_⟩
  -- Identify the rational partial composites and their poles on the same resolution.
  let : Nonempty F.cones := hcF.nonempty_cones
  let : Nonempty Ψ.cones := hc'.nonempty_cones
  have : IsModification π[s] := isModification_corner_projection σ s v hv
  have : IsModification (q ≫ π[s]) := hq ▸ inferInstance
  have hmodq : IsModification q := IsModification.of_comp_right q π[s]
  have hmiddle := s.comp_denseTorusPartialIso (Fan.IsSubdivision.refl F) q
  have hlink : T.toBase.toRationalMap.comp (Φ.denseTorusPartialIso Ψ).toRationalMap =
      (k'.hom ≫ U.toBase).toRationalMap := by
    simpa only [hq, hq'] using s.comp_denseTorusPartialIso t q
  have htoric : (π[s]).toRationalMap.comp (Φ.denseTorusPartialIso Ψ).toRationalMap =
      (π[t]).toRationalMap := by
    simpa only [Category.id_comp] using s.comp_denseTorusPartialIso t (𝟙 X[F])
  refine ⟨hmodq, ?_, hlink, ⟨_, ⟨htoric, hlink⟩, fun φ hφ ↦
    (π[s]).toRationalMap.comp_left_injective (hφ.1.trans htoric.symm)⟩, ?_⟩
  · simpa only [hq, Fan.IsSubdivision.toFanHom_refl, FanHom.algebraicMap_id, Category.comp_id]
      using hmiddle
  let : SmoothOfRelativeDimension 2 (X[Φ] ↘ S) := by
    rw [Fan.algebraicRealization_over]
    exact hdim
  let : SmoothOfRelativeDimension 2 (X[Ψ] ↘ S) := by
    rw [Fan.algebraicRealization_over]
    exact rankTwo(b) ▸ Ψ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΨ
  refine ⟨s.pole_ideal_of_blowup_towers t hΦ hF hΨ hc hcF hc' rankTwo(b) hT hU q k' hq hq', ?_⟩
  -- Read the degree in the new marking and undo the permutation in the old order sum.
  intro C C' a β x x'
  obtain ⟨hclass, hsum, hlt⟩ := hcoord a β (x j) (x ∘ j.succAbove)
  have hsumOld : (∑ l, -Fin.append (fun _ : Fin 1 ↦ x j) (x ∘ j.succAbove) l) =
      ∑ l, -x l := by
    rw [Fin.sum_univ_succAbove _ j, Fin.sum_univ_add]
    simp only [Fin.sum_univ_one, Fin.append_left, Fin.append_right, Function.comp_apply]
  refine ⟨?_, hsum.trans (by rw [hsumOld]), fun hx hm hhigh ↦ ?_⟩
  · have hmark := T.pullback_picardHom_move_to_front j h hbase hE htail
      (a • C 0 + β • C 1) x
    have hcoeff : Fin.addCases (fun _ : Fin 1 ↦ x j) (x ∘ j.succAbove) =
        Fin.append (fun _ : Fin 1 ↦ x j) (x ∘ j.succAbove) := (rfl)
    rw [hcoeff] at hmark
    rw [Iso.trans_hom, ← pullback_comp, hclass, ← hmark, pullback_comp, Iso.hom_inv_id, pullback_id]
  · simpa only [hsumOld] using hlt (fun l ↦ hx (j.succAbove l)) hm hhigh

end QPainleve.BlowupTower.IsClosedPointTower
