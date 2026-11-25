/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Ruling.NodalCycle
public import QPainleve.Geometry.Toric.Fan.Hirzebruch.HorizontalNodes
public import QPainleve.Geometry.Toric.Fan.Hirzebruch.NodalReplacement
public import QPainleve.Geometry.Toric.Fan.Hirzebruch.Quadric
public import QPainleve.Geometry.Toric.Fan.Ruling.Hirzebruch.Fiber

import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Contraction
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Reduced
import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Canonical
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.IdealSheaf.Restriction
import QPainleve.AlgebraicGeometry.Modules.Differentials.Restriction
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Dominant
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced

/-!
# Reducing positive-complexity Hirzebruch boundaries

A numbered anticanonical cycle of positive complexity on a Hirzebruch surface
admits a nodal blowup followed by an internal contraction that lowers its
complexity. The bisection case on the quadric uses the transverse ruling.

The reduction follows the ruled case of
[Gross, Hacking and Keel, Proposition 1.3][GHK].

[GHK]: https://arxiv.org/html/1106.4977v3#S1.Thmproposition3
-/

public section

open AlgebraicGeometry CategoryTheory Limits Module TopologicalSpace
open QPainleve QPainleve.BlowupTower TauCeti.AlgebraicGeometry LineBundleClass
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "P₁" => projectiveLine ℂ
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "Plane" => Proj (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)
local notation "I[" x "]" => Scheme.Hom.ker (Scheme.fromSpecResidueField _ x)
local notation "J[" x "]" => vanishingIdeal (Closeds.mk (closure ({x} : Set _)) isClosed_closure)
local notation "π[" x "]" => blowupToBase (I[x])
local notation "T[" x "]" => BlowupTower.nil.snoc (I[x])
local notation "St[" I "," E "]" => Scheme.Hom.ker (blowupMap I (subschemeι E))
local notation "R[" D "," x "]" => radical (comap D (π[x]))
local notation "K[" X "]" => LineBundleClass.mk (canonicalBundle ℂ X 2)

private theorem fiber_not_le_boundary_of_omitted_point {Y : Scheme}
    {D : Y.IdealSheafData} {f : Y ⟶ P₁} {x : Y}
    {y : S ⟶ P₁} (hy : y ≫ (P₁ ↘ S) = 𝟙 S) (hx : x ∈ (y.ker.comap f).support)
    (hF : ¬ (y.ker.comap f).support ≤ D.support) :
    ¬ (I[f x].comap f).support ≤ D.support := by
  have : IsClosedImmersion y := y.isClosedImmersion_of_comp_eq_id hy
  have hyx : y (IsLocalRing.closedPoint ℂ) = f x := by
    rw [← SetLike.mem_coe, support_comap, Closeds.coe_preimage, Set.mem_preimage,
      y.support_ker, y.isClosedEmbedding.isClosed_range.closure_eq,
      Set.range_eq_singleton (y := y (IsLocalRing.closedPoint ℂ))
        (fun z ↦ congrArg y (Subsingleton.elim z _)), Set.mem_singleton_iff] at hx
    exact hx.symm
  rwa [y.ker_eq_ker_fromSpecResidueField, hyx] at hF

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]
  (b : Basis (Fin 2) ℤ N) {e : ℤ} (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])

local notation "X" => Φ.algebraicRealization
local notation "C" => Φ.hirzebruchPicardBasis b e hΦ r hr
local notation "P[" p "]" => Additive.ofMul
  (@primeDivisorClass X _ _ (Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ) p)
local notation "χ[" b "]" => LinearMap.toAddMonoidHom (Basis.coord b 1)
local notation "f[" b "," e "," r "," hr "]" =>
  Φ.characterRuling χ[b] (nonneg_or_nonpos_hirzebruch_ruling_character b e r hr)

private theorem characterRuling_closed_fibers (b : Basis (Fin 2) ℤ N) (e : ℤ)
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (r : Fin 4 ≃ Φ.Ray)
    (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1]) :
    let f := f[b, e, r, hr]
    IsDominant f ∧ ∀ z : P₁, IsClosed ({z} : Set P₁) →
      ∃ a : P₁ ≅ f.fiber z, a.hom ≫ f.fiberι z ≫ X ↘ S = P₁ ↘ S := by
  intro f
  have hχ : χ[b] ≠ 0 := by
    intro hh
    simpa [Basis.coord_apply] using DFunLike.congr_fun hh (b 1)
  refine ⟨Φ.isDominant_characterRuling _ _ hχ, fun z hz ↦ ?_⟩
  obtain ⟨a, ha, -⟩ := exists_hirzebruch_fiber_iso_with_degree b e hΦ hc r hr z hz
  exact ⟨a, ha⟩

variable [Φ.algebraicRealization.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ Spec (CommRingCat.of ℂ))]
  {D : Φ.algebraicRealization.IdealSheafData}
  [PrestableFamily (D.subscheme ↘ Spec (CommRingCat.of ℂ))] (hD : D.IsEffectiveCartier)
  (hK : LineBundleClass.mk hD.toInvertibleSheaf =
    LineBundleClass.mk (canonicalBundle ℂ Φ.algebraicRealization 2))
  {n : ℕ} [NeZero n] {α : Type*} {p : α → (D.subscheme ↘ Spec (CommRingCat.of ℂ)).smoothLocus}
  (A : Scheme.NodalCycleNumbering p n)

local notation "prime[" j "]" => D.boundaryPrimeEmbedding (A.boundaryPrimeEquiv hD j)
local notation "d[" j "]" => (Basis.repr C) P[prime[j]] (1 : Fin 2)

include hc hD hK A in
private theorem exists_omitted_fiber_of_quadric_bisection (he : e = 0) (hn : n = 2)
    (hpos : D.boundaryComplexity ≠ 0)
    (s : ZMod n) (hs : d[s] = 2) :
    let b' := b.reindex (Equiv.swap 0 1)
    let r' := ((Equiv.swap (0 : Fin 4) 1).trans (Equiv.swap 2 3)).trans r
    let hr' := quadric_swapped_generators b r (he ▸ hr)
    let f := f[b', 0, r', hr']
    ∃ j : ZMod n, ¬ (I[f (A.ambientNode j)].comap f).support ≤ D.support := by
  subst e
  intro b' r' hr' f
  have : IsReduced D.subscheme :=
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := D.subscheme ↘ S)).isReduced
  have hst : s ≠ s + 1 := by
    have hone : (1 : ZMod n) ≠ 0 := by
      exact fun h ↦ by have := ZMod.one_eq_zero_iff.mp h; omega
    exact fun h ↦ hone (add_eq_left.mp h.symm)
  have hsections := quadric_bisection_transverse_sections b hΦ hc r hr hD hK hs
    ((A.boundaryPrimeEquiv hD).injective.ne hst)
  have hq : f[b', 0, r', hr'] = Φ.characterRuling (b.coord 0).toAddMonoidHom
      (nonneg_or_nonpos_quadric_transverse_character b r hr) := by
    have hχ : χ[b'] = (b.coord 0).toAddMonoidHom := by
      ext x
      simp [b', Basis.coord_apply]
    congr
  have hdegree (j : ZMod n)
      (h : IsIso (J[prime[j].val].subschemeι ≫ f[b', 0, r', hr'])) :
      (Φ.hirzebruchPicardBasis b' 0 hΦ r' hr').repr P[prime[j]] 1 = 1 := by
    let g := J[prime[j].val].subschemeι ≫ f[b', 0, r', hr']
    let : IsIso g := h
    obtain ⟨_, _, hrank⟩ := hirzebruch_ruling_prime_degree_of_isDominant b' 0 r' hr' prime[j]
    obtain ⟨y⟩ : Nonempty P₁ := inferInstance
    have h := (eulerDegree_hirzebruch_ruling_prime b' 0 hΦ hc r' hr' prime[j]).symm.trans (hrank y)
    have hr : g.finrank y = 1 := congrFun (g.finrank_eq_one_of_isIso) y
    exact h.trans (by exact_mod_cast hr)
  have h₀ := hdegree s (by rw [hq]; exact hsections.1)
  have h₁ := hdegree (s + 1) (by rw [hq]; exact hsections.2.1)
  have hall (j : ZMod n) : j = s ∨ j = s + 1 := by
    have hcard : Fintype.card (ZMod n) = 2 := by simpa only [ZMod.card] using hn
    have huniv : ({s, s + 1} : Finset (ZMod n)) = Finset.univ :=
      Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
        (by rw [Finset.card_pair hst, Finset.card_univ, hcard])
    have hj : j ∈ ({s, s + 1} : Finset (ZMod n)) := huniv ▸ Finset.mem_univ j
    simpa using hj
  rcases exists_hirzebruch_horizontal_node_or_boundary_cases b' 0 hΦ hc r' hr' A hD hK rfl with
    ⟨j, y, -, -, hy, hx, hF⟩ | hzero | ⟨-, j, hj⟩
  · exact ⟨j, fiber_not_le_boundary_of_omitted_point hy hx hF⟩
  · exact (hpos hzero).elim
  · rcases hall j with rfl | rfl <;> omega

include hc hD hK A in
private theorem exists_omitted_fiber_or_hirzebruch_one_bisection (he : 0 ≤ e)
    (hpos : 0 < D.boundaryComplexity) :
    (∃ (f : X ⟶ P₁) (_ : f.IsOver S), IsDominant f ∧
      (∀ z : P₁, IsClosed ({z} : Set P₁) →
        ∃ a : P₁ ≅ f.fiber z, a.hom ≫ f.fiberι z ≫ X ↘ S = P₁ ↘ S) ∧
      ∃ j : ZMod n, ¬ (I[f (A.ambientNode j)].comap f).support ≤ D.support)
    ∨ (e = 1 ∧ ∃ s : ZMod n, d[s] = 2) := by
  rcases exists_hirzebruch_horizontal_node_or_boundary_cases b e hΦ hc r hr A hD hK rfl with
    ⟨j, y, -, -, hy, hx, hF⟩ | hzero | ⟨hn, s, hs⟩
  · obtain ⟨hdom, hfiber⟩ := characterRuling_closed_fibers b e hΦ hc r hr
    exact Or.inl ⟨f[b, e, r, hr], inferInstance, hdom, hfiber,
      j, fiber_not_le_boundary_of_omitted_point hy hx hF⟩
  · exact (hpos.ne' hzero).elim
  · have : IsReduced D.subscheme :=
      (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := D.subscheme ↘ S)).isReduced
    have hcard : D.boundaryPrimes.ncard = n := by
      rw [← Nat.card_coe_set_eq, ← Nat.card_congr (A.boundaryPrimeEquiv hD), Nat.card_zmod]
    obtain ⟨-, -, hbound⟩ :=
      hirzebruch_anticanonical_bisection b e hΦ hc r hr hD hK he
        (A.boundaryPrimeEquiv hD s) hs
    rw [hcard, hn] at hbound
    by_cases hzero : e = 0
    · subst e
      let b' := b.reindex (Equiv.swap 0 1)
      let r' := ((Equiv.swap (0 : Fin 4) 1).trans (Equiv.swap 2 3)).trans r
      let hr' := quadric_swapped_generators b r hr
      obtain ⟨j, hj⟩ := exists_omitted_fiber_of_quadric_bisection b hΦ hc r hr hD hK A
        rfl hn hpos.ne' s hs
      obtain ⟨hdom, hfiber⟩ := characterRuling_closed_fibers b' 0 hΦ hc r' hr'
      exact Or.inl ⟨f[b', 0, r', hr'], inferInstance, hdom, hfiber, j, hj⟩
    · exact Or.inr ⟨by omega, s, hs⟩

omit [Φ.algebraicRealization.IsProjectiveOver ℂ] in
include hD hK in
private theorem boundary_image_of_replacement
    {x : X} (hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T[x])
    {Y : Scheme} [Y.Over S] [IsIntegral Y] [Y.IsProjectiveOver ℂ]
    [SmoothOfRelativeDimension 2 (Y ↘ S)] {y : Y} (hy : IsClosed ({y} : Set Y))
    {E : Y.IdealSheafData} (hE : E.IsEffectiveCartier) [IsReduced E.subscheme]
    (u : (I[x]).blowup ≅ (I[y]).blowup)
    (hu : u.hom ≫ π[y] ≫ Y ↘ S = π[x] ≫ X ↘ S)
    (hstrict : (St[I[y],E]).comap u.hom = R[D,x]) :
    (R[D,x]).map (u.hom ≫ π[y]) = E ∧
      ¬ ((I[y]).comap (u.hom ≫ π[y])).support ≤ (R[D,x]).support := by
  have hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S) := by
    rw [← D.over_eq_subschemeι_comp]
    exact PrestableFamily.atWorstNodalOfRelativeDimensionOne
  let W := (I[x]).blowup
  let : W.Over S := ⟨T[x].toBase ≫ X ↘ S⟩
  let : SmoothOfRelativeDimension 2 (W ↘ S) := hT.isClosedPointTower.smoothOfRelativeDimension _
  have hπ : T[x].toBase = π[x] := by simp
  obtain ⟨hCartier, hNodal⟩ := hT.radical_comap_toBase hD hN
  have hKtotal := (hT.canonicalClass_radical_comap_toBase_iff hD hN).mpr hK
  generalize hI : I[y] = J at u hu hstrict ⊢
  have hJ : J = J[y] := hI.symm.trans (Y.ker_fromSpecResidueField_eq_vanishingIdeal y)
  clear hI
  subst J
  let B := St[J[y],E]
  let : (J[y]).blowup.Over S := ⟨(J[y]).blowupToBase ≫ Y ↘ S⟩
  let : SmoothOfRelativeDimension 2 ((J[y]).blowup ↘ S) :=
    smoothOfRelativeDimension_blowup_closed_point (Y ↘ S) hy
  have hWover : W ↘ S = T[x].toBase ≫ X ↘ S := rfl
  have hBover : (J[y]).blowup ↘ S = (J[y]).blowupToBase ≫ Y ↘ S := rfl
  have huOver : u.hom ≫ ((J[y]).blowup ↘ S) = W ↘ S := by
    rwa [hWover, hBover, hπ]
  have : u.inv.IsOver S := ⟨by rw [← huOver, Iso.inv_hom_id_assoc]⟩
  have hBcomap : (D.comap T[x].toBase).radical.comap u.inv = B := by
    rw [hπ, ← hstrict, ← comap_comp, Iso.inv_hom_id, comap_id]
  have hB : B.IsEffectiveCartier := hBcomap ▸ hCartier.comap u.inv
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ S)
  have : IsNoetherian Y := isNoetherian_of_finiteType (Y ↘ S)
  have : IsReduced B.subscheme := isReduced_subscheme_ker_blowupMap (J[y]) E
  have hKB : LineBundleClass.mk hB.toInvertibleSheaf = K[(J[y]).blowup] := by
    have hclass := (hCartier.pullback_mk_toInvertibleSheaf (hCartier.comap u.inv)).trans
      (mk_toInvertibleSheaf_congr _ hB hBcomap)
    rw [hKtotal, pullback_mk] at hclass
    exact hclass.symm.trans (mk_pullback_canonicalBundle ℂ u.inv 2)
  obtain ⟨hmap, homit⟩ :=
    hB.map_eq_and_not_le_support_of_eq_strictTransform ℂ hy hE rfl hKB
  refine ⟨?_, ?_⟩
  · rw [← hstrict, map_comp, map_comap_of_isClosedImmersion,
      Scheme.Hom.ker_eq_bot_of_isIso u.hom, sup_bot_eq]
    exact hmap
  · rw [← hstrict, comap_comp, support_comap _ u.hom, support_comap _ u.hom]
    exact fun h ↦ homit (SetLike.coe_subset_coe.mp
      (u.hom.surjective.preimage_subset_preimage_iff.mp (SetLike.coe_subset_coe.mpr h)))

omit [Φ.algebraicRealization.IsProjectiveOver ℂ] in
include b hΦ hc r hr hD hK A in
/-- A numbered anticanonical boundary of positive complexity on a Hirzebruch
surface admits one nodal blowup followed by an internal contraction. The schematic
image on the contracted surface is anticanonical, has one more numbered component,
and has complexity one less. The contracted surface still admits a ruling by
projective lines. -/
theorem exists_hirzebruch_positive_complexity_reduction (he : 0 ≤ e)
    (hpos : 0 < D.boundaryComplexity) :
    ∃ (j : ZMod n) (Y : Scheme) (s : Y ⟶ S) (y : Y)
      (u : (I[A.ambientNode j]).blowup ≅ (I[y]).blowup) (f : Y ⟶ P₁),
      let x := A.ambientNode j
      let g := u.hom ≫ π[y]
      let E := (R[D,x]).map g
      letI : Y.Over S := ⟨s⟩
      ∃ hSmooth : SmoothOfRelativeDimension 2 s,
        letI : SmoothOfRelativeDimension 2 (Y ↘ S) := hSmooth
        IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T[x] ∧
        IsIntegral Y ∧ Y.IsProjectiveOver ℂ ∧ IsClosed ({y} : Set Y) ∧
        g ≫ s = π[x] ≫ X ↘ S ∧ ¬ ((I[y]).comap g).support ≤ (R[D,x]).support ∧
        f.IsOver S ∧ Flat f ∧
        (∀ z : P₁, IsClosed ({z} : Set P₁) →
          ∃ a : P₁ ≅ f.fiber z, a.hom ≫ f.fiberι z ≫ s = P₁ ↘ S) ∧
        ∃ hE : E.IsEffectiveCartier,
          LineBundleClass.mk hE.toInvertibleSheaf = K[Y] ∧
          E.boundaryComplexity + 1 = D.boundaryComplexity ∧
          ∃ _ : PrestableFamily (E.subscheme ↘ S),
            Nonempty (Scheme.NodalCycleNumbering
              (Empty.elim : Empty → (E.subscheme ↘ S).smoothLocus) (n + 1)) := by
  let : (X).IsProjectiveOver ℂ :=
    Φ.isProjectiveOver_algebraicRealization_of_isComplete hΦ hc b
  let : SmoothOfRelativeDimension 1 (P₁ ↘ S) := projectiveLine.smoothOfRelativeDimension ℂ
  let : Smooth (P₁ ↘ S) := SmoothOfRelativeDimension.smooth 1 _
  rcases exists_omitted_fiber_or_hirzebruch_one_bisection b hΦ hc r hr hD hK A he hpos with
    ⟨f, hf, hd, hfib, j, hF⟩ | ⟨heq, t, ht⟩
  · let : Module.Finite ℤ (Additive (LineBundleClass X)) := Module.Finite.of_basis C
    let x := A.ambientNode j
    obtain ⟨Y, s, g, y, f', hSmooth, hY, hproj, -, -, hg, -, hf', -, -, hflat, hfib',
      hy, ⟨u, hu⟩, homit, -, -, hE, hK', -, hcomplexity, hpre, hnumber⟩ :=
      f.exists_elementary_transform_of_numbered_nodal_fiber hfib hD hK A j hF
    let : Y.Over S := ⟨s⟩
    let : (J[x]).blowup.Over S := ⟨(J[x]).blowupToBase ≫ X ↘ S⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hSmooth
    -- Identify the vanishing-ideal blowup with the residue-field blowup of the numbered node.
    have hI : I[x] = J[x] := Φ.algebraicRealization.ker_fromSpecResidueField_eq_vanishingIdeal x
    let v := blowupIso (Iso.refl X) (hI.trans (comap_id _).symm)
    have hv : v.hom ≫ (J[x]).blowupToBase = π[x] := by simp [v]
    have hgv : (v ≪≫ u).hom ≫ π[y] = v.hom ≫ g := by
      simp only [Iso.trans_hom, Category.assoc, hu]
    have hR : ((D.comap (J[x]).blowupToBase).radical).comap v.hom = R[D,x] := by
      rw [← radical_comap_of_isOpenImmersion _ v.hom, ← comap_comp, hv]
    have hImage : (R[D,x]).map ((v ≪≫ u).hom ≫ π[y]) =
        (D.comap (J[x]).blowupToBase).radical.map g := by
      rw [hgv, ← hR, map_comp, map_comap_of_isClosedImmersion,
        Scheme.Hom.ker_eq_bot_of_isIso, sup_bot_eq]
    refine ⟨j, Y, s, y, v ≪≫ u, f', hSmooth, isNodalBoundaryTower_numbered_node A j,
      hY, hproj, hy, ?_, ?_, hf', hflat, hfib', ?_⟩
    · have hg' : g ≫ s = (J[x]).blowupToBase ≫ X ↘ S := hg.comp_over
      rw [hgv, Category.assoc, hg', ← Category.assoc, hv]
    · rw [hgv, comap_comp, ← hR, support_comap _ v.hom, support_comap _ v.hom]
      exact fun h ↦ homit (SetLike.coe_subset_coe.mp
        (v.hom.surjective.preimage_subset_preimage_iff.mp (SetLike.coe_subset_coe.mpr h)))
    · rw [hImage]
      exact ⟨hE, hK', hcomplexity, hpre, hnumber⟩
  · -- The bisection replacement first contracts to the plane and then changes the blowup center.
    subst e
    obtain ⟨p, q, a, Ψ, hΨ, hcΨ, b', r', v, y, u, -, -, -, -, ha, hv, hr', hy, -, -,
      hT, hpb, hstrict, hcomplexity, hE, hpre, hKE, hnumber⟩ :=
      exists_hirzebruch_one_nodal_replacement_of_bisection b hΦ hc r hr hD hK
        (A.boundaryPrimeEquiv hD t) ht A t
    let x := A.ambientNode t
    let : Nonempty Ψ.cones := hcΨ.nonempty_cones
    let Y := Ψ.algebraicRealization
    let hproj : Y.IsProjectiveOver ℂ :=
      Ψ.isProjectiveOver_algebraicRealization_of_isComplete hΨ hcΨ b'
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := by
      rw [algebraicRealization_over]
      exact ((finrank_eq_card_basis b').trans (Fintype.card_fin 2)) ▸
        Ψ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΨ
    have hr₁ : (fun j ↦ (r' j).primitiveGenerator) =
        ![b' 0, b' 1, -b' 0, (1 : ℤ) • b' 0 - b' 1] := by simpa only [one_zsmul] using hr'
    let f := Ψ.characterRuling χ[b'] (nonneg_or_nonpos_hirzebruch_ruling_character b' 1 r' hr₁)
    have hf : f.IsOver S :=
      inferInstanceAs ((Ψ.characterRuling χ[b']
        (nonneg_or_nonpos_hirzebruch_ruling_character b' 1 r' hr₁)).IsOver S)
    obtain ⟨hfdom, hfiber⟩ := characterRuling_closed_fibers b' 1 hΨ hcΨ r' hr₁
    let : IsDominant f := hfdom
    have hFlat : Flat f := f.flat_of_isDominant_of_smooth (P₁ ↘ S)
    have hbase : u.hom ≫ π[y] ≫ Y ↘ S = π[x] ≫ X ↘ S := by
      have h := congrArg (· ≫ (Plane ↘ S)) hpb.w
      simpa only [Category.assoc, ha, hv] using h.symm
    let := hpre
    let E := (D.map (a.hom ≫ π[p])).comap T[q].toBase |>.radical.comap v.hom
    have : IsReduced E.subscheme :=
      (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := E.subscheme ↘ S)).isReduced
    let : Y.IsProjectiveOver ℂ := hproj
    obtain ⟨hImage, homit⟩ := boundary_image_of_replacement hD hK hT hy hE u hbase hstrict
    refine ⟨t, Y, Y ↘ S, y, u, f, inferInstance, hT,
      inferInstance, hproj, hy, ?_, homit, hf, hFlat, hfiber, ?_⟩
    · exact (Category.assoc _ _ _).trans hbase
    · rw [hImage]
      exact ⟨hE, hKE, hcomplexity, hpre, hnumber⟩

end TauCeti.Toric.Fan
