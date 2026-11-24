/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Centres
public import TauCeti.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Centre
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Embedding.Set
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Disjoint
import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.SmoothProjective
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition

/-!
# Contraction of disjoint exceptional curves

A finite disjoint configuration of exceptional curves on a smooth integral projective
surface contracts to distinct closed points of a smooth integral projective surface.
The contraction is the projection of a closed-point blowup tower, with its total
exceptional classes indexed by the original curves.

This iterates the projective contraction in the
[Stacks Project, Lemma 54.16.9(1)](https://stacks.math.columbia.edu/tag/0C2N).
Contracting a matched configuration is also a step in the proof of
[Gross–Hacking–Keel, Theorem 1.8](https://arxiv.org/html/1211.6367v5#S2).
-/

public section

open CategoryTheory TopologicalSpace QPainleve TauCeti.AlgebraicGeometry
open LineBundleClass

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y Z W : Scheme.{u}} {n : ℕ}

private theorem contraction_fibers_snoc (E : Fin (n + 1) → X.IdealSheafData)
    (f : X ⟶ Y) [IsModification f] [IsReduced Y] {p : Y}
    (hp : IsClosed ({p} : Set Y)) (hf : f.centre = {p})
    (hF : (Y.fromSpecResidueField p).ker.comap f = E (Fin.last n))
    (g : Y ⟶ Z) [IsModification g] (q : Fin n → Z) (hq : Function.Injective q)
    (hqclosed : ∀ i, IsClosed ({q i} : Set Z)) (hg : g.centre = Set.range q)
    (hG : ∀ i, (Z.fromSpecResidueField (q i)).ker.comap g = (E i.castSucc).map f)
    (hpull : ∀ i : Fin n, ((E i.castSucc).map f).comap f = E i.castSucc)
    (havoid : ∀ i : Fin n, p ∉ ((E i.castSucc).map f).support) :
    let points : Fin (n + 1) → Z := Fin.snoc q (g p)
    Function.Injective points ∧ (f ≫ g).centre = Set.range points ∧
      ∀ i, IsClosed ({points i} : Set Z) ∧
        (Z.fromSpecResidueField (points i)).ker.comap (f ≫ g) = E i := by
  dsimp only
  have hpq : g p ∉ Set.range q := by
    rintro ⟨i, hi⟩
    apply havoid i
    rw [← SetLike.mem_coe, ← hG i, support_comap, Closeds.coe_preimage,
      Scheme.support_ker_fromSpecResidueField_of_isClosed (hqclosed i)]
    exact Set.mem_singleton_iff.mpr hi.symm
  have hgp : IsClosed ({g p} : Set Z) := by
    simpa only [Set.image_singleton] using g.isClosedMap {p} hp
  have hU : g p ∈ g.isoLocus := by
    rw [← SetLike.mem_coe, ← g.compl_centre, hg]
    exact hpq
  refine ⟨Fin.snoc_injective_of_injective hq hpq, ?_, Fin.lastCases ?_ fun i ↦ ?_⟩
  · rw [f.centre_comp g, hf, hg, Set.image_singleton, Fin.range_snoc, Set.union_singleton]
  · rw [Fin.snoc_last]
    refine ⟨hgp, ?_⟩
    rw [comap_comp, g.comap_ker_fromSpecResidueField_of_mem_isoLocus hgp hU, hF]
  · rw [Fin.snoc_castSucc]
    refine ⟨hqclosed i, ?_⟩
    rw [comap_comp, hG i, hpull i]

private theorem exists_snoc_tower (E : Fin (n + 1) → X.IdealSheafData)
    (hE : ∀ i, (E i).IsEffectiveCartier) (f : X ⟶ Y) {p : Y} (hp : IsClosed ({p} : Set Y))
    (hF : (Y.fromSpecResidueField p).ker.comap f = E (Fin.last n))
    (e : X ≅ (Y.fromSpecResidueField p).ker.blowup)
    (he : e.hom ≫ (Y.fromSpecResidueField p).ker.blowupToBase = f)
    (T : BlowupTower Z n W) (hT : T.IsClosedPointTower Z) (a : Y ≅ W)
    (hmap : ∀ i : Fin n, ((E i.castSucc).map f).IsEffectiveCartier)
    (hclass : ∀ i : Fin n, pullback a.hom (T.exceptionalClass i) =
      (LineBundleClass.mk (hmap i).toInvertibleSheaf)⁻¹)
    (hpull : ∀ i : Fin n, ((E i.castSucc).map f).comap f = E i.castSucc) :
    ∃ (V : Scheme.{u}) (S : BlowupTower Z (n + 1) V) (b : X ≅ V) (hS : S.IsClosedPointTower Z),
      b.hom ≫ S.toBase = f ≫ a.hom ≫ T.toBase ∧
      hS.baseCenter = Fin.snoc hT.baseCenter (T.toBase (a.hom p)) ∧
      ∀ i, pullback b.hom (S.exceptionalClass i) =
        (LineBundleClass.mk (hE i).toInvertibleSheaf)⁻¹ := by
  let J := (W.fromSpecResidueField (a.hom p)).ker
  have hclosed : IsClosed ({a.hom p} : Set W) := by
    simpa only [Set.image_singleton] using a.hom.isClosedMap {p} hp
  have hJ : J.comap a.hom = (Y.fromSpecResidueField p).ker :=
    a.hom.comap_ker_fromSpecResidueField_of_mem_isoLocus hclosed
      (by simp [a.hom.isoLocus_eq_top_iff.mpr inferInstance])
  let b := e ≪≫ J.blowupIso a hJ
  have hb : b.hom ≫ J.blowupToBase = f ≫ a.hom := by
    rw [Iso.trans_hom, Category.assoc, J.blowupIso_hom_blowupToBase, ← Category.assoc, he]
  let hS := hT.snoc (a.hom p) hclosed (I := J) rfl
  refine ⟨J.blowup, T.snoc J, b, hS, ?_, ?_,
    Fin.lastCases ?_ fun i ↦ ?_⟩
  · rw [BlowupTower.toBase_snoc, ← Category.assoc, hb, Category.assoc]
  · funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · rw [hS.baseCenter_snoc_last, hS.lastCenter_eq (a.hom p) hclosed rfl, Fin.snoc_last]
    · rw [hS.baseCenter_snoc_castSucc, Fin.snoc_castSucc]
  · have htotal : (J.comap J.blowupToBase).comap b.hom = E (Fin.last n) := by
      rw [← comap_comp, hb, comap_comp, hJ, hF]
    rw [BlowupTower.exceptionalClass_snoc_last, pullback_inv,
      J.isEffectiveCartier_comap_blowupToBase.pullback_mk_toInvertibleSheaf
        (htotal.symm ▸ hE _), mk_toInvertibleSheaf_congr _ _ htotal]
  · rw [BlowupTower.exceptionalClass_snoc_castSucc, pullback_comp, hb, ← pullback_comp,
      hclass i, pullback_inv, (hmap i).pullback_mk_toInvertibleSheaf ((hpull i).symm ▸ hE _),
      mk_toInvertibleSheaf_congr _ _ (hpull i)]

variable [X.Over (Spec (.of k))] [IsIntegral X] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

/-- Contract all members of a disjoint exceptional configuration on a smooth integral
projective surface. The resulting closed points are distinct and exhaust the centre.
They are the projected centers of the ordered point blowup presentation. Their
scheme-theoretic fibres and the corresponding exceptional classes recover the
specified curves and their divisor classes in the same order. -/
theorem exists_smooth_projective_contraction_of_disjoint_exceptional_curves
    (E : Fin n → X.IdealSheafData) (hE : ∀ i, (E i).IsExceptionalCurveOfFirstKind)
    (hdis : Pairwise fun i j ↦ Disjoint ((E i).support : Set X) (E j).support) :
    ∃ (Z : Scheme.{u}) (t : Z ⟶ Spec (.of k)) (W : Scheme.{u}) (T : BlowupTower Z n W)
      (e : X ≅ W) (hT : T.IsClosedPointTower Z),
      let : Z.Over (Spec (.of k)) := ⟨t⟩
      let f := e.hom ≫ T.toBase
      let q := hT.baseCenter
      IsIntegral Z ∧ Z.IsProjectiveOver k ∧ SmoothOfRelativeDimension 2 t ∧
        f.IsOver (Spec (.of k)) ∧ IsModification f ∧
        Function.Injective q ∧ f.centre = Set.range q ∧
        (∀ i, IsClosed ({q i} : Set Z) ∧ (Z.fromSpecResidueField (q i)).ker.comap f = E i) ∧
        ∀ i, pullback e.hom (T.exceptionalClass i) =
          (LineBundleClass.mk (hE i).isEffectiveCartier.toInvertibleSheaf)⁻¹ := by
  induction n generalizing X with
  | zero =>
    have hproj : X.IsProjectiveOver k := inferInstance
    refine ⟨X, X ↘ Spec (.of k), X, .nil, Iso.refl X, .nil, inferInstance, hproj,
      inferInstance, ?_, ?_, Function.injective_of_subsingleton _, ?_,
      fun i ↦ i.elim0, fun i ↦ i.elim0⟩
    · rw [BlowupTower.toBase_nil, Iso.refl_hom, Category.comp_id]
      exact ⟨Category.id_comp _⟩
    · simpa only [BlowupTower.toBase_nil, Iso.refl_hom, Category.comp_id] using
        (inferInstance : IsModification (𝟙 X))
    · rw [BlowupTower.toBase_nil, Iso.refl_hom, Category.comp_id,
        (Scheme.Hom.centre_eq_empty_iff (𝟙 X)).mpr inferInstance]
      simp
  | succ n ih =>
    have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
    obtain ⟨Y, s, f, p, hY, hprojY, hsmY, hover, hmod, hp, hf, hF, _, e, he⟩ :=
      (hE (Fin.last n)).exists_smooth_projective_contraction (k := k)
    let : Y.Over (Spec (.of k)) := ⟨s⟩
    have : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k)) := hsmY
    obtain ⟨hrest, hpair⟩ := map_pairwise_disjoint_of_contraction E (Fin.last n) hE f hf hF hdis
    let F (i : Fin n) := (E i.castSucc).map f
    let label := (Fin.castSuccEmb (n := n)).codRestrict {i | i ≠ Fin.last n}
      Fin.castSucc_ne_last
    have hEF (i : Fin n) : (F i).IsExceptionalCurveOfFirstKind := (hrest (label i)).1
    have hdisF : Pairwise fun i j ↦ Disjoint ((F i).support : Set Y) (F j).support :=
      fun i j hij ↦ @hpair (label i) (label j) (label.injective.ne hij)
    obtain ⟨Z, t, W, T, a, hT, hZ, hprojZ, hsmZ, hgOver, hgMod, hq, hg, hFib, hclass⟩ :=
      ih F hEF hdisF
    let : Z.Over (Spec (.of k)) := ⟨t⟩
    let g := a.hom ≫ T.toBase
    obtain ⟨V, S, b, hS, hb, hpoints, hbclass⟩ := exists_snoc_tower E
      (fun i ↦ (hE i).isEffectiveCartier) f hp hF e he T hT a
      (fun i ↦ (hEF i).isEffectiveCartier) hclass
      (fun i ↦ (hrest (label i)).2.1)
    have hcomp : b.hom ≫ S.toBase = f ≫ g := hb
    obtain ⟨hinj, hc, hqF⟩ := contraction_fibers_snoc E f hp hf hF g hT.baseCenter hq
      (fun i ↦ (hFib i).1) hg (fun i ↦ (hFib i).2)
      (fun i ↦ (hrest (label i)).2.1) (fun i ↦ (hrest (label i)).2.2)
    have hqS : hS.baseCenter = Fin.snoc hT.baseCenter (g p) := by
      simpa only [g, Scheme.Hom.comp_apply] using hpoints
    refine ⟨Z, t, V, S, b, hS, hZ, hprojZ, hsmZ, ?_, ?_, ?_, ?_, ?_, hbclass⟩
    · rw [hcomp]
      infer_instance
    · rw [hcomp]
      infer_instance
    · exact hqS.symm ▸ hinj
    · rw [hcomp, hqS]
      exact hc
    · rw [hcomp, hqS]
      exact hqF

end AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind
