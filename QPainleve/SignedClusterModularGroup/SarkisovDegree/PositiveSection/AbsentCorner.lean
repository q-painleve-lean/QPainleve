/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Basic
public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.Incidence
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Picard
public import QPainleve.Geometry.Toric.Fan.Logarithmic.Factorization
public import QPainleve.Geometry.Toric.Fan.Picard.Hirzebruch
public import QPainleve.Geometry.Toric.Fan.Ruling.Hirzebruch
public import QPainleve.Geometry.Toric.Fan.Smooth
public import TauCeti.AlgebraicGeometry.Noetherian

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.Blowup.Tower.Centres.First
import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.PoleIdeal
import QPainleve.AlgebraicGeometry.Morphisms.Modification.Birational
import QPainleve.Geometry.Toric.Fan.Boundary.Node
import QPainleve.Geometry.Toric.Fan.StarSubdivision.Picard.Resolution
import QPainleve.Geometry.Toric.Fan.StarSubdivision.Tower
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition

/-!
# Sarkisov paths at absent Hirzebruch corners

A toric elementary transformation at a corner absent from a resolving tower
requires blowing up the inverse image of that corner on the resolving surface.
The new blowup is nodal. On this refinement the two links have the same pole
boundary, and the pullback of the specified plane map has the original orders
at all retained centers. The reverse corner has order equal to the fiber degree.

The coefficient change is the zero-order case of [Lutz, Lemma 8.9][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=71
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module PointedCone TauCeti.Toric
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData
open TauCeti.SymmetricAlgebra

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" Δ "]" => Fan.algebraicRealization Δ
local notation "f[" Δ "]" => (X[Δ] ↘ S)
local notation "B[" Δ "," h "]" => Fan.boundaryIdeal Δ (Fan.IsComplete.nonempty_cones h)
local notation "π[" s "]" => FanHom.algebraicMap (Fan.IsSubdivision.toFanHom s)
local notation "I[" σ "]" => Scheme.Hom.ker (Fan.distinguishedPointHom _ σ)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "rankTwo(" b ")" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "mark[" T "," hT "," s "," g "]" =>
  LinearEquiv.symm (BlowupTower.picardMarking T hT s) (Additive.ofMul (pullback g H))
local notation "pt" => IsLocalRing.closedPoint ℂ
local notation "length" p:arg =>
  @Quiver.Path.length _ Fan.LogarithmicProjection.sarkisovQuiver _ _ p
local notation "ruling[" b "," e "," r "," h "]" =>
  Fan.characterRuling _ (LinearMap.toAddMonoidHom (Basis.coord b 1))
    (Fan.nonneg_or_nonpos_hirzebruch_ruling_character b e r h)

private theorem absent_corner_nodal_refinement
    (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    [SmoothOfRelativeDimension 2 f[Φ]]
    (ρ τ : Φ.Ray) (hne : ρ ≠ τ) (σ : Φ.cones)
    (hρ : ρ.toCone ≤ σ) (hτ : τ.toCone ≤ σ)
    {Y : Scheme} {n : ℕ} {T : BlowupTower X[Φ] n Y} (hT : IsClosedPointTower X[Φ] T)
    (hp : Φ.distinguishedPointHom σ pt ∉ Set.range hT.baseCenter)
    {D : Y.IdealSheafData} (hpole : B[Φ,hc].comap T.toBase = D * hT.ramificationIdealSheafToBase ℂ)
    {q : Y} (hq : IsClosed ({q} : Set Y)) (hqp : T.toBase q = Φ.distinguishedPointHom σ pt)
    (hI : (I[σ]).comap T.toBase = (Y.fromSpecResidueField q).ker) :
    IsNodalBoundaryTower D (T.toBase ≫ f[Φ]) (𝟙 Y)
      (.snoc .nil ((I[σ]).comap T.toBase)) := by
  have hcard := Φ.card_toricRay_eq_two_of_ray_ne_of_le hΦ rankTwo(b) hne hρ hτ
  have hnode := Φ.isNodeOfReducedBoundary_distinguishedPointHom hΦ σ rankTwo(b) hcard
  have h := hT.isNodeOfReducedBoundary_of_notMem_range_baseCenter hp hqp hnode hpole
  exact .snoc .nil q hq hI (by simpa only [toBase_nil, Category.id_comp, comap_id] using h)

private theorem absent_corner_target_marking {Ψ : Fan i} [Nonempty Ψ.cones]
    {Y Z W : Scheme} (p : W ⟶ Y) (k : W ≅ Z) (g : Y ⟶ P)
    {n : ℕ} {T : BlowupTower X[Ψ] n Z} (hT : IsClosedPointTower X[Ψ] T)
    [SmoothOfRelativeDimension 2 f[Ψ]] [IsNoetherian X[Ψ]]
    (C : Basis (Fin 2) ℤ (Additive (LineBundleClass X[Ψ])))
    (a β : ℤ) (m : Fin n → ℤ)
    (hclass : pullback k.inv (pullback p (pullback g H)) =
      (T.picardHom (a • C 0 + β • C 1, m)).toMul) :
    let y := mark[T,hT,f[Ψ],k.inv ≫ p ≫ g]
    C.repr y.1 0 = a ∧ C.repr y.1 1 = β ∧ y.2 = m := by
  have hy : mark[T,hT,f[Ψ],k.inv ≫ p ≫ g] = (a • C 0 + β • C 1, m) := by
    rw [LinearEquiv.symm_apply_eq, T.picardMarking_apply hT f[Ψ],
      ← pullback_comp, ← pullback_comp, hclass, ofMul_toMul]
  dsimp only
  rw [hy]
  simp [Basis.repr_self]

private theorem absent_corner_pole_on_target
    {W Z : Scheme} [W.Over S] [SmoothOfRelativeDimension 2 (W ↘ S)] {D : W.IdealSheafData}
    (B : Fan.LogarithmicProjection i D) {n : ℕ} {U : BlowupTower X[B.fan] n Z}
    (hU : IsClosedPointTower X[B.fan] U) (k : W ≅ Z) (hB : B.hom = k.hom ≫ U.toBase)
    [SmoothOfRelativeDimension 2 f[B.fan]] :
    B[B.fan,B.isComplete].comap U.toBase = D.comap k.inv * hU.ramificationIdealSheafToBase ℂ := by
  let : Z.Over S := ⟨U.toBase ≫ f[B.fan]⟩
  let : U.toBase.IsOver S := ⟨rfl⟩
  let : k.hom.IsOver S := ⟨(Category.assoc _ _ _).symm.trans (hB ▸ comp_over B.hom S)⟩
  let : SmoothOfRelativeDimension 2 (Z ↘ S) := hU.smoothOfRelativeDimension f[B.fan]
  let : Smooth (W ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have hcomp : B[B.fan,B.isComplete].comap (k.hom ≫ U.toBase) =
      D * ramificationIdealSheaf ℂ (k.hom ≫ U.toBase) :=
    (congrArg B[B.fan,B.isComplete].comap hB.symm).trans
      (B.comap_boundaryIdeal.trans (congrArg (D * ·) (ramificationIdealSheaf_congr ℂ hB)))
  simpa only [IsIso.inv_eq_of_hom_inv_id k.hom_inv_id, hU.ramificationIdealSheafToBase_def ℂ]
    using (comap_eq_mul_ramificationIdealSheaf_comp_iff_of_isIso ℂ k.hom U.toBase 2).mp hcomp

/-- A toric elementary transformation at a corner absent from the projected centers
is resolved on the blowup of its inverse image, a single node of the pole boundary.
The signed Hirzebruch parameter changes from `e` to `e + 1`. The two toric steps
carry the same reduced pole boundary and the same specified map to the plane.
The fiber coefficient increases by the fiber degree, which is unchanged.
The reverse corner has that degree as its order, and every retained center comes
from a common point of the intermediate toric model and keeps its original order
and ruling value. A first center remains first if it does not project to the
reverse corner.
The section centers are reindexed by the insertion of the reverse corner,
which lies off the strict section. -/
theorem exists_sarkisov_path_of_absent_corner
    (b : Basis (Fin 2) ℤ N) (e : ℤ) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (r : Fin 4 ≃ Φ.Ray)
    (hr : (fun l ↦ (r l).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])
    {Y : Scheme} {n : ℕ} {T : BlowupTower X[Φ] n Y} (hT : IsClosedPointTower X[Φ] T)
    (g : Y ⟶ P) (hg : g ≫ (P ↘ S) = T.toBase ≫ f[Φ]) (hbir : Scheme.BirationalOver g (𝟙 P))
    (σ : Φ.cones) (hσ : σ.val = hull ℝ (Set.range (i ∘ b)))
    (hp : Φ.distinguishedPointHom σ pt ∉ Set.range hT.baseCenter)
    (D : Y.IdealSheafData) (hD : D.IsEffectiveCartier)
    (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ T.toBase ≫ f[Φ])) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 f[Φ] :=
      rankTwo(b) ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : IsNoetherian X[Φ] := by
      let : Smooth f[Φ] := SmoothOfRelativeDimension.smooth 2 _
      exact isNoetherian_of_finiteType f[Φ]
    let : SmoothOfRelativeDimension 2 (T.toBase ≫ f[Φ]) := hT.smoothOfRelativeDimension f[Φ]
    let : IsIntegral Y := hT.isIntegral f[Φ]
    let : IsNoetherian Y := T.isNoetherian
    let J := (I[σ]).comap T.toBase
    let R := BlowupTower.snoc BlowupTower.nil J
    let D' := (D.comap R.toBase).radical
    let x := mark[T,hT,f[Φ],g]
    let C := Φ.hirzebruchPicardBasis b e hΦ r hr
    B[Φ,hc].comap T.toBase = D * hT.ramificationIdealSheafToBase ℂ →
    ∃ hR : IsNodalBoundaryTower D (T.toBase ≫ f[Φ]) (𝟙 Y) R,
      let : J.blowup.Over S := ⟨R.toBase ≫ T.toBase ≫ f[Φ]⟩
      let : SmoothOfRelativeDimension 2 (J.blowup ↘ S) :=
        hR.isClosedPointTower.smoothOfRelativeDimension (T.toBase ≫ f[Φ])
      let : IsIntegral J.blowup := hR.isClosedPointTower.isIntegral (T.toBase ≫ f[Φ])
      ∃ (A B : Fan.LogarithmicProjection i D') (path : Fan.LogarithmicProjection.SarkisovPath A B)
        (d : Basis (Fin 2) ℤ N) (r' : Fin 4 ≃ B.fan.Ray)
        (hr' : (fun l ↦ (r' l).primitiveGenerator) = ![d 0, d 1, -d 0, (e + 1) • d 0 - d 1])
        (Z : Scheme) (U : BlowupTower X[B.fan] (1 + n) Z)
        (hU : IsClosedPointTower X[B.fan] U) (k : J.blowup ≅ Z),
        A.fan = Φ ∧ A.hom ≍ R.toBase ≫ T.toBase ∧ B.hom = k.hom ≫ U.toBase ∧
        length path = 2 ∧ path.rationalMap = (Scheme.PartialIso.ofDenseOpenImmersions
          (Fan.denseTorusι A.fan inferInstance)
          (Fan.denseTorusι B.fan inferInstance)).toRationalMap ∧
        (k.inv ≫ R.toBase ≫ g) ≫ (P ↘ S) = U.toBase ≫ f[B.fan] ∧
        Scheme.BirationalOver (k.inv ≫ R.toBase ≫ g) (𝟙 P) ∧
        (∃ τ : B.fan.cones, τ.val = hull ℝ {i (d 1), i (-d 0)} ∧
          hU.baseCenter (Fin.castAdd n (0 : Fin 1)) = B.fan.distinguishedPointHom τ pt) ∧
        (∃ (F : Fan i) (s : F.IsSubdivision Φ) (t : F.IsSubdivision B.fan),
          Φ.IsTwoRayStarSubdivision F ∧ B.fan.IsTwoRayStarSubdivision F ∧
          ∀ j : Fin n, ∃ z : X[F],
            π[s] z = hT.baseCenter j ∧ π[t] z = hU.baseCenter (j.natAdd 1)) ∧
        hU.strictTransformCenterIndices (B.fan.rayBoundaryIdeal B.isRegular (r' 0)) =
          (hT.strictTransformCenterIndices (Φ.rayBoundaryIdeal hΦ (r 0))).map
            (Fin.natAddEmb 1) ∧
        (let f := ruling[b,e,r,hr]
         let f' := ruling[d,e + 1,r',hr']
         f' (hU.baseCenter 0) = f (Φ.distinguishedPointHom σ pt) ∧
           ∀ j, f' (hU.baseCenter (j.natAdd 1)) = f (hT.baseCenter j)) ∧
        (∀ j : Fin n, hU.baseCenter (j.natAdd 1) ≠ hU.baseCenter 0 →
          (∀ l < j, hT.baseCenter l ≠ hT.baseCenter j) →
          ∀ l < j.natAdd 1, hU.baseCenter l ≠ hU.baseCenter (j.natAdd 1)) ∧
        let : SmoothOfRelativeDimension 2 f[B.fan] :=
          rankTwo(b) ▸ B.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap B.isRegular
        B[B.fan,B.isComplete].comap U.toBase =
          D'.comap k.inv * hU.ramificationIdealSheafToBase ℂ ∧
        let : IsNoetherian X[B.fan] := by
          let : Smooth f[B.fan] := SmoothOfRelativeDimension.smooth 2 _
          exact isNoetherian_of_finiteType f[B.fan]
        let y := mark[U,hU,f[B.fan],k.inv ≫ R.toBase ≫ g]
        let C' := B.fan.hirzebruchPicardBasis d (e + 1) B.isRegular r' hr'
        C'.repr y.1 0 = C.repr x.1 0 + C.repr x.1 1 ∧ C'.repr y.1 1 = C.repr x.1 1 ∧
        y.2 = Fin.addCases (fun _ : Fin 1 ↦ -C.repr x.1 1) x.2 := by
  intro hcones hdim hNoeth hdimY hIntY hNoethY J R D' x C hpole
  let := hcones
  let := hdim
  let := hNoeth
  let := hdimY
  let := hIntY
  let := hNoethY
  have hrays : Set.range (Fan.Ray.primitiveGenerator (Phi := Φ)) =
      {b 0, b 1, -b 0, e • b 0 - b 1} := by
    rw [← r.surjective.range_comp, Function.comp_def, hr]
    simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  obtain ⟨q, Ψ, F, hΨ, hF, hc', d, τ, s, t, r₀, r', hr₀, hr', v, w, Z, U, k, hU, hU',
    hq, hqp, hJ, hd₀, hd₁, hτ, -, _, hs, ht, hsource, htarget, hcenters, hhead, htail,
    hrulingHead, hrulingTail, hinc, hfirst, hPic⟩ :=
    hT.exists_hirzebruch_toric_link_resolution_of_absent_corner σ b e hΦ hc hrays hσ hp
  have hr₀' : r₀ = r := Equiv.ext fun l ↦ Fan.Ray.primitiveGenerator_injective
    (congrFun (hr₀.trans hr.symm) l)
  subst r₀
  have hle (l : Fin 2) : (r l.castSucc.castSucc).toCone ≤ σ := by
    rw [(r l.castSucc.castSucc).toCone_le_iff σ, hσ, congrFun hr l.castSucc.castSucc]
    exact subset_hull ⟨l, by fin_cases l <;> rfl⟩
  have hR := absent_corner_nodal_refinement b hΦ hc (r 0) (r 1)
    (r.injective.ne (by decide)) σ (hle 0) (hle 1) hT hp hpole hq hqp hJ
  refine ⟨hR, ?_⟩
  -- The resolving surface has one added node blowup. Its two projections factor through
  -- the same toric model, so the refined pole formula supplies both vertices.
  let : Y.Over S := ⟨T.toBase ≫ f[Φ]⟩
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f[Φ]
  let : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : T.toBase.IsOver S := ⟨rfl⟩
  let : J.blowup.Over S := ⟨R.toBase ≫ T.toBase ≫ f[Φ]⟩
  let : SmoothOfRelativeDimension 2 (J.blowup ↘ S) :=
    hR.isClosedPointTower.smoothOfRelativeDimension (T.toBase ≫ f[Φ])
  let : IsIntegral J.blowup := hR.isClosedPointTower.isIntegral (T.toBase ≫ f[Φ])
  let : R.toBase.IsOver S := ⟨rfl⟩
  let : IsModification R.toBase :=
    hR.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (Y ↘ S)
  let : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two f[Φ]
  let : Smooth (J.blowup ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : Nonempty F.cones := (s.isComplete_iff.mpr hc).nonempty_cones
  let : Nonempty Ψ.cones := hc'.nonempty_cones
  let q' := k.hom ≫ U.toBase ≫ w.inv
  have hq₀ : q' ≫ π[s] = R.toBase ≫ T.toBase := by
    simpa only [q', Category.assoc, R, toBase_snoc, toBase_nil, Category.comp_id] using hsource
  let U' := (BlowupTower.nil.snoc (I[τ])).append U
  have hq₁ : q' ≫ π[t] = k.hom ≫ U'.toBase := by
    simpa only [q', Category.assoc, U'] using htarget
  let : q'.IsOver S := ⟨by
    rw [F.algebraicRealization_over,
      ← s.toFanHom.algebraicMap_comp_algebraicRealizationStructureMap,
      ← Category.assoc, hq₀, Category.assoc, ← Φ.algebraicRealization_over]
    rfl⟩
  let : IsModification π[s] := s.isModification_algebraicMap hΦ hF hcones rankTwo(b)
  let : IsModification (q' ≫ π[s]) := hq₀ ▸ inferInstance
  let : IsModification q' := IsModification.of_comp_right q' π[s]
  have hRLog := hR.comap_eq_radical_mul_ramificationIdealSheaf_of_iso hD hNode
    (Iso.refl J.blowup) R.toBase (Category.id_comp _)
  have hLog := comap_eq_mul_ramificationIdealSheaf_comp ℂ R.toBase T.toBase 2
    ((hT.ramificationIdealSheafToBase_def ℂ) ▸ hpole) hRLog
  have hqLog : B[Φ,hc].comap (q' ≫ π[s]) = D' * ramificationIdealSheaf ℂ (q' ≫ π[s]) := by
    simpa only [hq₀, ramificationIdealSheaf_congr ℂ hq₀] using
      (congrArg (B[Φ,hc]).comap hq₀).trans hLog
  obtain ⟨A, B, path, hA, hAq, hB, hBq, hlen, hrat⟩ :=
    Fan.LogarithmicProjection.exists_sarkisovPath_of_twoRayStarSubdivisions
      rankTwo(b) hΦ hc hΨ hF s t hs ht q' hqLog
  subst Ψ
  have hg' : (k.inv ≫ R.toBase ≫ g) ≫ (P ↘ S) = U'.toBase ≫ f[B.fan] := by
    apply (cancel_epi k.hom).mp
    simp only [Category.assoc, Iso.hom_inv_id_assoc, hg,
      ← reassoc_of% hq₀, ← reassoc_of% hq₁,
      FanHom.algebraicMap_comp_algebraicRealizationStructureMap, Fan.algebraicRealization_over]
  -- Transport the specified plane morphism and evaluate its pulled-back line class.
  have hbir' := (k.inv.birationalOver (R.toBase ≫ g) (k.inv ≫ R.toBase ≫ g) rfl).trans
    (by simpa only [R, toBase_snoc, toBase_nil, Category.comp_id] using
      hT.birationalOver_blowupToBase_comp f[Φ] hq hJ hbir)
  refine ⟨A, B, path, d, r', hr', Z, U', hU', k, hA, hAq.trans (heq_of_eq hq₀),
    (eq_of_heq hBq).trans hq₁, hlen, hrat, hg', hbir', ⟨τ, hτ, hhead⟩,
    ⟨F, s, t, hs, ht, fun j ↦ ⟨w.inv (hU.baseCenter j), hcenters j, htail j⟩⟩, hinc, ?_, hfirst, ?_⟩
  · intro f₀ f₁
    have hcoord : d.coord 1 = b.coord 1 := d.ext fun l ↦ by
      simp only [Basis.coord_apply, Basis.repr_self]
      fin_cases l <;> simp [hd₀, hd₁]
    have hd := congrArg LinearMap.toAddMonoidHom hcoord
    have sign₀ := Fan.nonneg_or_nonpos_hirzebruch_ruling_character b e r hr
    have sign₁ := Fan.nonneg_or_nonpos_hirzebruch_ruling_character d (e + 1) r' hr'
    have hzero : Fin.castAdd n (0 : Fin 1) = 0 := rfl
    refine ⟨?_, fun j ↦ ?_⟩
    · simpa only [f₀, f₁, hd, hzero] using hrulingHead sign₀ (hd ▸ sign₁)
    · simpa only [f₀, f₁, hd] using hrulingTail _ sign₀ (hd ▸ sign₁) j
  intro hdim'
  let := hdim'
  refine ⟨absent_corner_pole_on_target B hU' k ((eq_of_heq hBq).trans hq₁), ?_⟩
  intro hNoeth' y C'
  let := hNoeth'
  have hsum : C.repr x.1 0 • C 0 + C.repr x.1 1 • C 1 = x.1 := by
    simpa only [Fin.sum_univ_two] using C.sum_repr x.1
  have hx : (T.picardHom ((C.repr x.1 0) • C 0 + (C.repr x.1 1) • C 1, x.2)).toMul =
      pullback g H := by
    rw [hsum, Prod.mk.eta, ← T.picardMarking_apply hT f[Φ], LinearEquiv.apply_symm_apply,
      toMul_ofMul]
  have hclass := hPic (C.repr x.1 0) (C.repr x.1 1) x.2
  rw [hx] at hclass
  exact absent_corner_target_marking (Ψ := B.fan) R.toBase k g hU' C' _ _ _ (by
    simpa only [R, U', toBase_snoc, toBase_nil, Category.comp_id] using hclass)

/-- An unused corner on the positive section is a zero-order pivot from
`F_e` to `F_{e-1}`. On a single nodal refinement it gives a two-link
path carrying the prescribed plane map. In the nonnegative markings both
ruling coefficients and all retained orders stay fixed. The reverse corner
lies on the opposite section and has order equal to the fiber degree.
The positive-section center indices are the original indices shifted past
the reverse corner, including at infinitely near centers.
A marked first center with order at most the fiber degree can be followed
by a first center of at least that order over the same ruling value. On the
pivot fiber take the reverse corner. On every other fiber keep the retained
center and its order. -/
theorem exists_sarkisov_path_of_absent_positive_corner
    (b : Basis (Fin 2) ℤ N) (e : ℕ) (he : 0 < e) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (r : Fin 4 ≃ Φ.Ray)
    (hr : (fun l ↦ (r l).primitiveGenerator) = ![b 0, b 1, -b 0, (e : ℤ) • b 0 - b 1])
    {Y : Scheme} {n : ℕ} {T : BlowupTower X[Φ] n Y} (hT : IsClosedPointTower X[Φ] T)
    (g : Y ⟶ P) (hg : g ≫ (P ↘ S) = T.toBase ≫ f[Φ]) (hbir : Scheme.BirationalOver g (𝟙 P))
    (σ : Φ.cones) (hσ : σ.val = hull ℝ {i (-b 0), i (b 1)})
    (hp : Φ.distinguishedPointHom σ pt ∉ Set.range hT.baseCenter)
    (D : Y.IdealSheafData) (hD : D.IsEffectiveCartier)
    (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ T.toBase ≫ f[Φ])) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 f[Φ] :=
      rankTwo(b) ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : IsNoetherian X[Φ] := by
      let : Smooth f[Φ] := SmoothOfRelativeDimension.smooth 2 _
      exact isNoetherian_of_finiteType f[Φ]
    let : SmoothOfRelativeDimension 2 (T.toBase ≫ f[Φ]) := hT.smoothOfRelativeDimension f[Φ]
    let : IsIntegral Y := hT.isIntegral f[Φ]
    let : IsNoetherian Y := T.isNoetherian
    let J := (I[σ]).comap T.toBase
    let R := BlowupTower.snoc BlowupTower.nil J
    let D' := (D.comap R.toBase).radical
    let x := mark[T,hT,f[Φ],g]
    let C := Φ.hirzebruchPicardBasis b (e : ℤ) hΦ r hr
    B[Φ,hc].comap T.toBase = D * hT.ramificationIdealSheafToBase ℂ →
    ∃ hR : IsNodalBoundaryTower D (T.toBase ≫ f[Φ]) (𝟙 Y) R,
      let : J.blowup.Over S := ⟨R.toBase ≫ T.toBase ≫ f[Φ]⟩
      let : SmoothOfRelativeDimension 2 (J.blowup ↘ S) :=
        hR.isClosedPointTower.smoothOfRelativeDimension (T.toBase ≫ f[Φ])
      let : IsIntegral J.blowup := hR.isClosedPointTower.isIntegral (T.toBase ≫ f[Φ])
      ∃ (A B : Fan.LogarithmicProjection i D') (path : Fan.LogarithmicProjection.SarkisovPath A B)
        (d : Basis (Fin 2) ℤ N) (r' : Fin 4 ≃ B.fan.Ray)
        (hr' : (fun l ↦ (r' l).primitiveGenerator) =
          ![d 0, d 1, -d 0, ((e - 1 : ℕ) : ℤ) • d 0 - d 1])
        (Z : Scheme) (U : BlowupTower X[B.fan] (1 + n) Z)
        (hU : IsClosedPointTower X[B.fan] U) (k : J.blowup ≅ Z),
        A.fan = Φ ∧ A.hom ≍ R.toBase ≫ T.toBase ∧ B.hom = k.hom ≫ U.toBase ∧
        length path = 2 ∧ path.rationalMap = (Scheme.PartialIso.ofDenseOpenImmersions
          (Fan.denseTorusι A.fan inferInstance)
          (Fan.denseTorusι B.fan inferInstance)).toRationalMap ∧
        (k.inv ≫ R.toBase ≫ g) ≫ (P ↘ S) = U.toBase ≫ f[B.fan] ∧
        Scheme.BirationalOver (k.inv ≫ R.toBase ≫ g) (𝟙 P) ∧
        (∃ τ : B.fan.cones, τ.val = hull ℝ {i (d 0), i (d 1)} ∧
          hU.baseCenter (Fin.castAdd n (0 : Fin 1)) = B.fan.distinguishedPointHom τ pt) ∧
        (∃ (F : Fan i) (s : F.IsSubdivision Φ) (t : F.IsSubdivision B.fan),
          Φ.IsTwoRayStarSubdivision F ∧ B.fan.IsTwoRayStarSubdivision F ∧
          ∀ j : Fin n, ∃ z : X[F],
            π[s] z = hT.baseCenter j ∧ π[t] z = hU.baseCenter (j.natAdd 1)) ∧
        hU.strictTransformCenterIndices (B.fan.rayBoundaryIdeal B.isRegular (r' 2)) =
          (hT.strictTransformCenterIndices (Φ.rayBoundaryIdeal hΦ (r 2))).map
            (Fin.natAddEmb 1) ∧
        let : SmoothOfRelativeDimension 2 f[B.fan] :=
          rankTwo(b) ▸ B.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap B.isRegular
        B[B.fan,B.isComplete].comap U.toBase =
          D'.comap k.inv * hU.ramificationIdealSheafToBase ℂ ∧
        let : IsNoetherian X[B.fan] := by
          let : Smooth f[B.fan] := SmoothOfRelativeDimension.smooth 2 _
          exact isNoetherian_of_finiteType f[B.fan]
        let y := mark[U,hU,f[B.fan],k.inv ≫ R.toBase ≫ g]
        let C' := B.fan.hirzebruchPicardBasis d ((e - 1 : ℕ) : ℤ) B.isRegular r' hr'
        C'.repr y.1 0 = C.repr x.1 0 ∧ C'.repr y.1 1 = C.repr x.1 1 ∧
        y.2 = Fin.addCases (fun _ : Fin 1 ↦ -C.repr x.1 1) x.2 ∧
        let f := ruling[b,(e : ℤ),r,hr]
        let f' := ruling[d,((e - 1 : ℕ) : ℤ),r',hr']
        ∀ j : Fin n, (∀ l < j, hT.baseCenter l ≠ hT.baseCenter j) →
          -x.2 j ≤ C.repr x.1 1 →
          ∃ l : Fin (1 + n), (∀ t < l, hU.baseCenter t ≠ hU.baseCenter l) ∧
            f' (hU.baseCenter l) = f (hT.baseCenter j) ∧
            -x.2 j ≤ -y.2 l ∧ -y.2 l ≤ C'.repr y.1 1 ∧
            (f (hT.baseCenter j) = f (Φ.distinguishedPointHom σ pt) → l = 0) ∧
            (f (hT.baseCenter j) ≠ f (Φ.distinguishedPointHom σ pt) →
              l = j.natAdd 1 ∧ y.2 l = x.2 j) := by
  intro hcones hdim hNoeth hdimY hIntY hNoethY J R D' x C hpole
  let := hcones
  let := hdim
  let := hNoeth
  let := hdimY
  let := hIntY
  let := hNoethY
  obtain ⟨b₀, r₀, hr₀, hb₀, hb₁, hs, -, -, -, -, hrepr⟩ :=
    Φ.exists_hirzebruchPicardBasis_opposite_section b (e : ℤ) hΦ r hr
  have hcone : σ.val = hull ℝ (Set.range (i ∘ b₀)) := by
    rw [hσ]
    congr 1
    ext u
    simp [Fin.exists_fin_succ, hb₀, hb₁, eq_comm]
  obtain ⟨hR, A, B, path, d₀, s₀, hs₀, Z, U, hU, k, hA, hAh, hB, hlen, hrat, hg', hbir',
    ⟨τ, hτ, hhead⟩, hcenters, hinc, hruling, hfirst, hpole', hmark⟩ :=
    hT.exists_sarkisov_path_of_absent_corner b₀ (-(e : ℤ)) hΦ hc r₀ hr₀ g hg hbir σ hcone
      hp D hD hNode hpole
  let : J.blowup.Over S := ⟨R.toBase ≫ T.toBase ≫ f[Φ]⟩
  let : SmoothOfRelativeDimension 2 (J.blowup ↘ S) :=
    hR.isClosedPointTower.smoothOfRelativeDimension (T.toBase ≫ f[Φ])
  -- At index zero the distinction between the two marked sections still matters.
  let e₀ := -(e : ℤ) + 1
  have he₀ : -e₀ = ((e - 1 : ℕ) : ℤ) := by dsimp only [e₀]; omega
  let : Nonempty B.fan.cones := B.isComplete.nonempty_cones
  obtain ⟨d, s, ht, hd₀, hd₁, -, -, ht₂, -, -, hrepr'⟩ :=
    B.fan.exists_hirzebruchPicardBasis_opposite_section d₀ e₀ B.isRegular s₀ hs₀
  rw [hs, ← ht₂] at hinc
  rw [← he₀]
  refine ⟨hR, A, B, path, d, s, ht, Z, U, hU, k, hA, hAh, hB, hlen, hrat, hg', hbir',
    ⟨τ, by rw [hτ, hd₀, hd₁, Set.pair_comm], hhead⟩, hcenters, hinc, hpole', ?_⟩
  intro hNoeth' y C'
  obtain ⟨ha, hβ, hm⟩ := hmark
  have hFiber : C'.repr y.1 0 = C.repr x.1 0 := by
    rw [(hrepr' y.1).1, ha, hβ, (hrepr x.1).1, (hrepr x.1).2]
    dsimp only [e₀]
    ring
  have hDegree : C'.repr y.1 1 = C.repr x.1 1 := by
    rw [(hrepr' y.1).2, hβ, (hrepr x.1).2]
  have hOrders : y.2 = Fin.addCases (fun _ : Fin 1 ↦ -C.repr x.1 1) x.2 := by
    rw [← (hrepr x.1).2]
    exact hm
  refine ⟨hFiber, hDegree, hOrders, ?_⟩
  intro f₀ f₁
  -- Changing which section supplies the first basis vector leaves the ruling character fixed.
  have coord_eq (u v : Basis (Fin 2) ℤ N) (h₀ : v 0 = -u 0) (h₁ : v 1 = u 1) :
      v.coord 1 = u.coord 1 := v.ext fun l ↦ by
    simp only [Basis.coord_apply, Basis.repr_self]
    fin_cases l <;> simp [h₀, h₁]
  have hsrc := congrArg LinearMap.toAddMonoidHom (coord_eq b b₀ hb₀ hb₁)
  have htgt := congrArg LinearMap.toAddMonoidHom (coord_eq d₀ d hd₀ hd₁)
  have hhead' : f₁ (hU.baseCenter 0) = f₀ (Φ.distinguishedPointHom σ pt) := by
    simpa only [f₀, f₁, htgt, hsrc] using hruling.1
  have htail' (j : Fin n) : f₁ (hU.baseCenter (j.natAdd 1)) = f₀ (hT.baseCenter j) := by
    simpa only [f₀, f₁, htgt, hsrc] using hruling.2 j
  rw [hDegree]
  exact exists_retained_first_center hT hU f₀ f₁ _ x.2 y.2 _ hOrders hhead' htail' hfirst

end QPainleve.BlowupTower.IsClosedPointTower
