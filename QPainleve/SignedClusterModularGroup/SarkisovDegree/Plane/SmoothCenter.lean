/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Plane.Edge
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Plane.VertexBlowup

import QPainleve.SignedClusterModularGroup.SarkisovDegree.Plane.Multiplicity

import QPainleve.Geometry.Toric.Fan.Boundary.Component
import QPainleve.Geometry.Toric.Fan.Mutation.Hirzebruch
import QPainleve.LinearAlgebra.Determinant.Dual
import QPainleve.AlgebraicGeometry.Blowup.Projective.Global
import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import TauCeti.AlgebraicGeometry.Blowup.Restriction
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The Sarkisov link at a smooth plane boundary center

The plane-edge block starts by blowing up the vertex opposite the edge. The
specified resolution either already factors through this blowup, or admits one
more blowup over that vertex. The section mutation and ruling exchange then
act on the prepared resolution. This is the smooth plane case of Proposition
8.11 in [Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/abs/2005.05010v3#page=71
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module PointedCone TopologicalSpace
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra TauCeti.Toric
open Scheme.IdealSheafData

namespace QPainleve.BlowupTower.IsClosedPointTower

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "fP" => (P ↘ S)
local notation "degree" => Module.Basis.picardTwistEquiv (Pi.basisFun ℂ (Fin 3))
local notation "J[" p "]" => Scheme.Hom.ker (Scheme.fromSpecResidueField P p)
local notation "single[" I "]" => BlowupTower.snoc BlowupTower.nil I
local notation "first[" m "]" => Fin.castAdd m (0 : Fin 1)

variable {Y : Scheme} {n : ℕ} {T : BlowupTower P (n + 1) Y}
  (hT : IsClosedPointTower P T) (j : Fin (n + 1))
  (g : Y ⟶ P) (hg : g ≫ fP = T.toBase ≫ fP) (hbir : Scheme.BirationalOver g (𝟙 P))

local notation "mark[" T "," h "," g "]" =>
  LinearEquiv.symm (BlowupTower.picardMarking T h fP) (Additive.ofMul (pullback g H))

include hbir in
private theorem exists_plane_edge_preparation {p : P} (hp : IsClosed ({p} : Set P))
    (hjp : hT.baseCenter j ≠ p) (hfirst : ∀ l < j, hT.baseCenter l ≠ hT.baseCenter j) :
    ∃ (m : ℕ) (W : Scheme) (L : BlowupTower (J[p]).blowup (m + 1) W)
      (hL : IsClosedPointTower (J[p]).blowup L)
      (hB : IsClosedPointTower P ((single[J[p]]).append L))
      (q : W ⟶ Y) (j' : Fin (m + 1)),
      (p ∈ Set.range hT.baseCenter → IsIso q) ∧
      (p ∉ Set.range hT.baseCenter → ∃ (z : Y) (e : W ≅ ((J[p]).comap T.toBase).blowup),
        IsClosed ({z} : Set Y) ∧ T.toBase z = p ∧
        (J[p]).comap T.toBase = (Y.fromSpecResidueField z).ker ∧
        q = e.hom ≫ ((J[p]).comap T.toBase).blowupToBase) ∧
      L.toBase ≫ (J[p]).blowupToBase = q ≫ T.toBase ∧
      Scheme.BirationalOver (q ≫ g) (𝟙 P) ∧
      (J[p]).blowupToBase (hL.baseCenter j') = hT.baseCenter j ∧
      (∀ l < j', (J[p]).blowupToBase (hL.baseCenter l) ≠ hT.baseCenter j) ∧
      let v := mark[T,hT,g]
      let w := mark[((single[J[p]]).append L),hB,(q ≫ g)]
      w.1 = v.1 ∧ w.2 (j'.natAdd 1) = v.2 j ∧
      (∑ l, (-w.2 l).toNat) = ∑ l, (-v.2 l).toNat := by
  classical
  let hP : IsClosedPointTower P single[J[p]] := .snoc .nil p hp rfl
  let v := mark[T,hT,g]
  have hv : (T.picardHom v).toMul = pullback g H := by
    rw [← picardMarking_apply T hT fP, LinearEquiv.apply_symm_apply, toMul_ofMul]
  by_cases h : p ∈ Set.range hT.baseCenter
  · obtain ⟨a, ha, hmin⟩ := (wellFounded_lt (α := Fin (n + 1))).has_min
      {l | hT.baseCenter l = p} h
    obtain ⟨W, L, e, hL, he, hE, hcenter, hTail⟩ :=
      hT.exists_move_closed_point_blowup_to_front a hp ha (fun l hl hlp ↦ hmin l hlp hl)
    cases n with
    | zero =>
      exact (hjp ((congrArg hT.baseCenter ((Fin.ext (by omega) : j = a))).trans ha)).elim
    | succ m =>
      have hja : j ≠ a := fun heq ↦ hjp (heq.symm ▸ ha)
      obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hja
      have hq := (e.inv.birationalOver g (e.inv ≫ g) rfl).trans hbir
      refine ⟨m, W, L, hL, hP.append hL, e.inv, j', fun _ ↦ inferInstance,
        fun hn ↦ (hn h).elim, ?_, hq,
        (hcenter j').trans (congrArg hT.baseCenter hj'), ?_, ?_⟩
      · rw [← he, Iso.inv_hom_id_assoc]
      · intro l hl
        rw [hcenter]
        exact hfirst _ (hj' ▸ Fin.strictMono_succAbove a hl)
      · have hmark := T.pullback_picardHom_move_to_front a e he hE hTail v.1 v.2
        rw [Prod.mk.eta, hv] at hmark
        intro v' w
        have hw : w = (v.1, Fin.addCases (fun _ : Fin 1 ↦ v.2 a) (v.2 ∘ a.succAbove)) := by
          apply (LinearEquiv.symm_apply_eq _).mpr
          apply Additive.toMul.injective
          rw [picardMarking_apply, toMul_ofMul, ← pullback_comp]
          exact hmark
        rw [hw]
        refine ⟨rfl, by simp only [Fin.addCases_right, Function.comp_apply, hj']; rfl, ?_⟩
        rw [Fin.sum_univ_add (a := 1) (b := m + 1), Fin.sum_univ_one,
          Fin.sum_univ_succAbove _ a]
        simp only [Fin.addCases_left, Fin.addCases_right, Function.comp_apply]
        rfl
  · obtain ⟨x, W, L, e, hL, hx, hxp, hI, he, hcenter, -, -, hmark⟩ :=
      hT.exists_prepend_closed_point_blowup hp h
    refine ⟨n, W, L, hL, hP.append hL, e.inv ≫ ((J[p]).comap T.toBase).blowupToBase, j,
      fun hm ↦ (h hm).elim, fun _ ↦ ⟨x, e.symm, hx, hxp, hI, rfl⟩, ?_, ?_, hcenter j,
      fun l hl ↦ hcenter l ▸ hfirst l hl, ?_⟩
    · rw [Category.assoc, ← he, Iso.inv_hom_id_assoc]
    · rw [Category.assoc]
      exact (e.inv.birationalOver _ _ rfl).trans
        (hT.birationalOver_blowupToBase_comp fP hx hI hbir)
    · have hv' := hmark v.1 v.2
      rw [Prod.mk.eta, hv] at hv'
      intro v' w
      have hw : w = (v.1, Fin.addCases (fun _ : Fin 1 ↦ 0) v.2) := by
        apply (LinearEquiv.symm_apply_eq _).mpr
        apply Additive.toMul.injective
        rw [picardMarking_apply, toMul_ofMul, ← pullback_comp]
        exact hv'
      rw [hw]
      refine ⟨rfl, by simp only [Fin.addCases_right]; rfl, ?_⟩
      rw [Fin.sum_univ_add (a := 1) (b := n + 1), Fin.sum_univ_one]
      simp only [Fin.addCases_left, Fin.addCases_right, neg_zero, Int.toNat_zero, zero_add]
      rfl

section Edge

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {Φ : Fan i} (regΦ : Φ.IsRegular) (hcΦ : Φ.IsComplete)
  (b : Basis (Fin 2) ℤ N) (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun l ↦ (r l).primitiveGenerator) = ![b 0, b 1, -b 0, (1 : ℤ) • b 0 - b 1])
  (c : ℂˣ)

local notation "X[" U "]" => Fan.algebraicRealization U
local notation "f[" U "]" => (X[U] ↘ S)

variable {p₀ : P} (hp₀ : IsClosed ({p₀} : Set P))
  (e₀ : X[Φ] ≅ (J[p₀]).blowup)

local notation "π" => Iso.hom e₀ ≫ Scheme.IdealSheafData.blowupToBase (J[p₀])
local notation "ρ" => (r 2 : Fan.Ray Φ)
local notation "v" => Fan.Ray.primitiveGenerator ρ
local notation "rankTwo" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "center" =>
  Fan.Ray.binomialCenter ρ (m := LinearMap.toAddMonoidHom (Basis.detDualEquiv b v))
    rankTwo (b.detDualEquiv_self v) (Fan.Ray.surjective_detCharacter ρ b) c
local notation "u" => center (IsLocalRing.closedPoint ℂ)
local notation "hOpp" =>
  Eq.mpr (congrArg (fun x : N ↦ hull ℝ {i x} ∈ Fan.cones Φ)
    (Eq.trans (congrArg Neg.neg (congrFun hr 2))
      (Eq.trans (neg_neg (b 0)) (Eq.symm (congrFun hr 0)))))
    (Fan.Ray.hull_primitiveGenerator_mem (r 0))
local notation "hv" => Fan.Ray.primitiveGenerator_ne_zero ρ
local notation "hp" => Fan.Ray.hull_primitiveGenerator_mem ρ
local notation "Ψ" => Fan.mutationFan Φ b hv hp hOpp
local notation "regΨ" => Iff.mpr (Fan.isRegular_mutationFan_iff Φ b hv hp hOpp) regΦ
local notation "hcΨ" => Iff.mpr (Fan.isComplete_mutationFan_iff Φ b hv hp hOpp) hcΦ
local notation "s" => Equiv.trans r (Fan.mutationFanRayEquiv Φ b hv hp hOpp)
local notation "μ" =>
  Scheme.PartialMap.toRationalMap (Fan.mutationPartialMap Φ b (c : ℂ) hv hp hOpp)
local notation "C" => Fan.hirzebruchPicardBasis b 1 regΦ r hr
local notation "C'[" d' "," hd' "]" => Fan.hirzebruchPicardBasis d' 0 regΨ s hd'

include hp₀ in
private theorem edge_point_ne_vertex (hE : (J[p₀]).comap π = (Φ).rayBoundaryIdeal regΦ (r 0))
    : π u ≠ p₀ := by
  intro heq
  have hm : u ∈ ((J[p₀]).comap π).support := by
    rw [← SetLike.mem_coe, support_comap, Closeds.coe_preimage, Set.mem_preimage, heq,
      Scheme.support_ker_fromSpecResidueField_of_isClosed hp₀]
    exact Set.mem_singleton _
  rw [hE, ← SetLike.mem_coe, ← (Φ.rayBoundaryIdeal regΦ (r 0)).range_subschemeι] at hm
  obtain ⟨y, hy⟩ := hm
  let : Nonempty Φ.cones := ⟨(r 0).toCone⟩
  let B := Φ.boundaryIdeal (inferInstance : Nonempty Φ.cones)
  let m := LinearMap.toAddMonoidHom (Basis.detDualEquiv b v)
  have hm : m v = 0 := b.detDualEquiv_self v
  have hs : Function.Surjective m := Fan.Ray.surjective_detCharacter ρ b
  let z₀ := (ρ).binomialCenterOnBoundary (m := m) rankTwo hm hs c
  let z := z₀ (IsLocalRing.closedPoint ℂ)
  have h : (r 0).boundaryComponentι regΦ y = z := by
    apply B.subschemeι.isClosedEmbedding.injective
    have hz : B.subschemeι z = u := by
      exact (Scheme.Hom.comp_apply z₀ B.subschemeι (IsLocalRing.closedPoint ℂ)).symm.trans
        (congrArg (fun f : S ⟶ X[Φ] ↦ f (IsLocalRing.closedPoint ℂ))
          ((ρ).binomialCenterOnBoundary_comp_subschemeι (m := m) rankTwo hm hs c))
    rw [hz, ← Scheme.Hom.comp_apply, Fan.Ray.boundaryComponentι_subschemeι, hy]
  have hray := ((ρ).binomialCenterOnBoundary_mem_range_boundaryComponentι_iff regΦ rankTwo
    (b.detDualEquiv_self v) (Fan.Ray.surjective_detCharacter ρ b) c (r 0)).mp ⟨y, h⟩
  exact (by decide : (2 : Fin 4) ≠ 0) (r.injective hray)

include hp₀ in
private theorem edge_point_mem_isoLocus (hu : π u ≠ p₀) :
    π u ∈ (π).isoLocus := by
  rw [Scheme.Hom.isoLocus_comp_of_isIso]
  apply ((J[p₀]).blowupToBase.le_isoLocus_iff.mpr
    (J[p₀]).isIso_blowupToBase_restrict_compl_support)
  simpa only [← SetLike.mem_coe, Closeds.coe_compl, Set.mem_compl_iff,
    Scheme.support_ker_fromSpecResidueField_of_isClosed hp₀, Set.mem_singleton_iff] using hu

private theorem planeSarkisovBidegree_of_vertex_preparation {m n' : ℕ}
    (x : Fin m → ℤ) (z : Fin (1 + m) → ℤ) (w : Fin n' → ℤ)
    (a β : ℤ) (hβ : z (first[m]) = β - a)
    (hx : ∀ l : Fin m, z (l.natAdd 1) = x l)
    (hsum : ∑ l, (-z l).toNat = ∑ l, (-w l).toNat) :
    planeSarkisovBidegree a.toNat ((a - β).toNat + ∑ l, (-x l).toNat) =
      planeSarkisovBidegree a.toNat (∑ l, (-w l).toNat) := by
  have hvertex : a - β = -z (first[m]) := (neg_sub _ _).symm.trans (congrArg Neg.neg hβ.symm)
  rw [hvertex]
  simpa only [Fin.sum_univ_add (a := 1) (b := m), Fin.sum_univ_one, hx]
    using congrArg (planeSarkisovBidegree a.toNat) hsum

include hp₀ hg hbir in
/-- At the first center above a smooth plane edge with order greater than one third
of the plane degree, blow up the opposite vertex, mutate at the lifted edge point,
and exchange the rulings. All three partial composites are regular on the same
refinement of the given resolution. This refinement is an isomorphism when the
opposite vertex is already blown up and otherwise blows up its inverse image.
The final quadric resolution carries the given resolving map and has strictly
smaller Sarkisov bidegree. The projection to the prepared Hirzebruch surface
is also identified with a closed-point tower. -/
theorem exists_sarkisov_decrease_of_plane_edge
    (hπ : π ≫ fP = f[Φ]) (hE : (J[p₀]).comap π = Φ.rayBoundaryIdeal regΦ (r 0))
    (hj : hT.baseCenter j = π u)
    (hfirst : ∀ l < j, hT.baseCenter l ≠ hT.baseCenter j)
    (hhigh : let w := mark[T,hT,g]; degree w.1 < 3 * (-w.2 j)) :
    let : Nonempty (Φ).cones := (hcΦ).nonempty_cones
    let : Nonempty (Ψ).cones := (hcΨ).nonempty_cones
    let : SmoothOfRelativeDimension 2 f[Ψ] :=
      Eq.mp (congrArg (fun n ↦ SmoothOfRelativeDimension n f[Ψ]) rankTwo)
        ((Ψ).smoothOfRelativeDimension_algebraicRealizationStructureMap regΨ)
    ∃ (A : Scheme) (q : A ⟶ Y) (k : ℕ) (R : BlowupTower X[Φ] k A)
      (_ : IsClosedPointTower X[Φ] R)
      (d' : Basis (Fin 2) ℤ N)
      (hd' : (fun l ↦ (s l).primitiveGenerator) = ![d' 0, d' 1, -d' 0, (0 : ℤ) • d' 0 - d' 1])
      (m : ℕ) (Z : Scheme) (U : BlowupTower X[Ψ] m Z) (hU : IsClosedPointTower X[Ψ] U)
      (e : A ≅ Z) (p : A ⟶ X[Ψ]) (_ : IsIntegral A) (_ : IsDominant R.toBase),
      let a := R.toBase
      let τ := (Fan.quadricRulingExchange d' regΨ hcΨ s hd').toFanHom.algebraicMap
      let g' := e.inv ≫ q ≫ g
      (p₀ ∈ Set.range hT.baseCenter → IsIso q) ∧
      (p₀ ∉ Set.range hT.baseCenter → ∃ (z : Y)
        (e₁ : A ≅ ((J[p₀]).comap T.toBase).blowup),
        IsClosed ({z} : Set Y) ∧ T.toBase z = p₀ ∧
        (J[p₀]).comap T.toBase = (Y.fromSpecResidueField z).ker ∧
        q = e₁.hom ≫ ((J[p₀]).comap T.toBase).blowupToBase) ∧
      a ≫ π = q ≫ T.toBase ∧
      a.toRationalMap.comp μ = p.toRationalMap ∧
      e.hom ≫ U.toBase = p ≫ τ ∧
      g' ≫ fP = U.toBase ≫ f[Ψ] ∧ Scheme.BirationalOver g' (𝟙 P) ∧
      let w := mark[T,hT,g]
      let y := (U.picardMarking hU f[Ψ]).symm (Additive.ofMul (pullback g' H))
      (C'[d',hd']).repr y.1 1 = degree w.1 + w.2 j ∧
      0 < (C'[d',hd']).repr y.1 1 ∧
      hirzebruchSarkisovBidegree ((C'[d',hd']).repr y.1 1).toNat (∑ l, (-y.2 l).toNat) <
        planeSarkisovBidegree (degree w.1).toNat (∑ l, (-w.2 l).toNat) := by
  let : Nonempty Φ.cones := hcΦ.nonempty_cones
  let : Nonempty (Ψ).cones := (hcΨ).nonempty_cones
  let : SmoothOfRelativeDimension 2 f[Ψ] :=
    Eq.mp (congrArg (fun n ↦ SmoothOfRelativeDimension n f[Ψ]) rankTwo)
      ((Ψ).smoothOfRelativeDimension_algebraicRealizationStructureMap regΨ)
  have hpos := (hT.plane_degree_eq_one_or_exists_high_baseCenter g hg hbir).1
  have hne := edge_point_ne_vertex regΦ b r c hp₀ e₀ hE
  have hloc := edge_point_mem_isoLocus b r c hp₀ e₀ hne
  obtain ⟨m, A, L, hL, hB, q, j', hqIso, hqBlowup, hbase, hbir', hcenter, hfirst', hw, hj', hsum⟩ :=
    exists_plane_edge_preparation hT j g hbir hp₀ (hj.trans_ne hne) hfirst
  -- The lifted pivot is determined by its image in the isomorphism locus.
  let R := L.transport e₀.symm
  let hR := R.isLift.isClosedPointTower hL
  have hproj (l : Fin (m + 1)) : π (hR.baseCenter l) =
      (J[p₀]).blowupToBase (hL.baseCenter l) := by
    rw [← R.isLift.hom_baseCenter hL hR, ← Scheme.Hom.comp_apply, Iso.symm_hom,
      Iso.inv_hom_id_assoc]
  have hpivot : hR.baseCenter j' = u := by
    have hpoint := (hproj j').trans (hcenter.trans hj)
    apply (π).injOn_preimage_isoLocus _ hloc hpoint
    rw [Set.mem_preimage, hpoint]
    exact hloc
  have hpivotFirst (l : Fin (m + 1)) (hl : l < j') : hR.baseCenter l ≠ u := by
    intro h
    apply hfirst' l hl
    rw [← hproj, h, hj]
  let : SmoothOfRelativeDimension 2 f[Φ] :=
    Eq.mp (congrArg (fun n ↦ SmoothOfRelativeDimension n f[Φ]) rankTwo)
      ((Φ).smoothOfRelativeDimension_algebraicRealizationStructureMap regΦ)
  let : Smooth f[Φ] := SmoothOfRelativeDimension.smooth 2 _
  let : IsNoetherian X[Φ] := isNoetherian_of_finiteType f[Φ]
  let : (J[p₀]).blowup.Over S := ⟨(J[p₀]).blowupToBase ≫ fP⟩
  let : e₀.hom.IsOver S := ⟨(Category.assoc _ _ _).symm.trans hπ⟩
  let : (J[p₀]).blowup.IsProjectiveOver ℂ :=
    (J[p₀]).isProjectiveOver_blowup_of_isNoetherianRing ℂ
  let : (X[Φ]).IsProjectiveOver ℂ := Scheme.IsProjectiveOver.of_isClosedImmersion ℂ e₀.hom
  let : IsIntegral R.top := hR.isIntegral f[Φ]
  let : IsModification R.tower.toBase := hR.isModification_of_smoothOfRelativeDimension_two f[Φ]
  let g₁ := R.iso.inv ≫ q ≫ g
  have hTri : R.iso.hom ≫ R.tower.toBase ≫ π = q ≫ T.toBase := by
    rw [← Category.assoc R.iso.hom, R.isLift.hom_toBase, Iso.symm_hom,
      Category.assoc L.toBase, Iso.inv_hom_id_assoc, hbase]
  have hg₁ : g₁ ≫ fP = R.tower.toBase ≫ f[Φ] := by
    apply (cancel_epi R.iso.hom).mp
    simp only [g₁, Category.assoc, Iso.hom_inv_id_assoc, hg,
      ← hπ, ← reassoc_of% hTri]
  have hb₁ := (R.iso.inv.birationalOver (q ≫ g) g₁ rfl).trans hbir'
  have hg' : (R.iso.symm.inv ≫ g₁) ≫ fP = ((single[J[p₀]]).append L).toBase ≫ fP := by
    simpa only [g₁, Iso.symm_inv, Category.assoc, Iso.hom_inv_id_assoc, hg,
      toBase_append, toBase_snoc, toBase_nil, Category.comp_id] using ((reassoc_of% hbase) fP).symm
  have hb' : Scheme.BirationalOver (R.iso.symm.inv ≫ g₁) (𝟙 P) := by
    simpa only [g₁, Iso.symm_inv, Iso.hom_inv_id_assoc] using hbir'
  -- Read the prepared Hirzebruch coordinates against the original plane marking.
  obtain ⟨ha, hβ, horders⟩ :=
    hirzebruchOne_resolution_coordinates b regΦ hcΦ r hr hR hp₀ e₀
      (by simpa only [Category.assoc] using hπ) hE R.isLift.symm g₁ hg₁ hb₁ hB hg' hb'
  simp only [g₁, Iso.symm_inv, Iso.hom_inv_id_assoc] at ha hβ horders
  obtain ⟨d', hd', Z, U, hU, e, p, hmut, -, hτ, -, hUover, hUbir, _, hdegree, _, _, hlt⟩ :=
    exists_quadric_resolution_of_plane_edge_link b regΦ hcΦ r hr ρ c rfl hR j'
      hpivot hpivotFirst g₁ hg₁ hb₁
  let q' := R.iso.inv ≫ q
  have hbase' : R.tower.toBase ≫ π = q' ≫ T.toBase := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, q'] using congrArg (R.iso.inv ≫ ·) hTri
  refine ⟨R.top, q', _, R.tower, hR, d', hd', _, Z, U, hU, e, p, inferInstance, inferInstance,
    ?_, ?_, hbase', hmut, hτ, ?_, ?_, ?_, ?_⟩
  · intro h
    let := hqIso h
    exact inferInstanceAs (IsIso (R.iso.inv ≫ q))
  · intro h
    obtain ⟨z, e₁, hz, hzp, hI, he₁⟩ := hqBlowup h
    exact ⟨z, R.iso.symm ≪≫ e₁, hz, hzp, hI, by simp only [q', he₁, Iso.trans_hom,
      Iso.symm_hom, Category.assoc]⟩
  · simpa only [g₁, q', Category.assoc] using hUover
  · simpa only [g₁, q', Category.assoc] using hUbir
  · rw [ha.symm, hw, ← horders j', hj'] at hdegree
    simpa only [g₁, q', Category.assoc] using hdegree
  · let x := (R.tower.picardMarking hR f[Φ]).symm (Additive.ofMul (pullback g₁ H))
    let w := mark[((single[J[p₀]]).append L),hB,(q ≫ g)]
    have ha' : (C).repr x.1 0 = degree (mark[T,hT,g]).1 :=
      ha.symm.trans (congrArg degree hw)
    have horder' : x.2 j' = (mark[T,hT,g]).2 j := (horders j').symm.trans hj'
    obtain ⟨hpositive, hlt'⟩ := hlt (ha'.symm ▸ hpos) (by rwa [ha', horder'])
    have hplane := planeSarkisovBidegree_of_vertex_preparation x.2 w.2 (mark[T,hT,g]).2
      ((C).repr x.1 0) ((C).repr x.1 1) hβ horders hsum
    dsimp only [x] at ha' hplane
    rw [hplane, ha'] at hlt'
    simpa only [g₁, q', Category.assoc] using And.intro hpositive hlt'

end Edge

end QPainleve.BlowupTower.IsClosedPointTower
