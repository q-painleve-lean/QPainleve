/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Map
public import QPainleve.AlgebraicGeometry.Curves.Node.Period.Restriction

/-!
# Pullback of periods under subdivision of a nodal cycle

A morphism between nodal cycles that lifts to the normalizations and the singular
subschemes induces a map of the conductor squares. In a subdivision, one node over
each old node has the two old branches in order, and the remaining nodes map their
two branches to a single old branch. Those latter nodes contribute one to the
pulled-back gluing product. This is the gluing computation for inserting exceptional
components in the period of
[Gross, Hacking and Keel, Lemma 2.1](https://arxiv.org/html/1211.6367v5#S2),
*Moduli of surfaces with an anti-canonical cycle*.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TauCeti TauCeti.AlgebraicGeometry
open Scheme.Modules LineBundleClass

universe u v w

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [PrestableFamily (X ↘ Spec (.of k))]
  [Y.Over (Spec (.of k))] [PrestableFamily (Y ↘ Spec (.of k))]

local notation "N[" C "]" => IdealSheafData.subscheme (singularLocus k C)
local notation "ν[" C "]" => IdealSheafData.blowupToBase (singularLocus k C)
local notation "ι[" C "]" => IdealSheafData.subschemeι (singularLocus k C)
local notation "B[" C "]" => branchScheme k C
local notation "π[" C "]" => branchSchemeToSingularLocus k C
local notation "j[" C "]" => branchSchemeToBlowup k C
local notation "P[" C "]" => MonoidHom.ker (LineBundleClass.pullbackHom (ν[C]))
local notation "nodal[" C "]" =>
  PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := C ↘ Spec (CommRingCat.of k))
local notation "conductor[" C "]" =>
  IsPullback.toCommSq (IsPullback.flip (Scheme.isPullback_branchScheme k C))

variable {f : X ⟶ Y} {fν : (singularLocus k X).blowup ⟶ (singularLocus k Y).blowup}
  {fN : (singularLocus k X).subscheme ⟶ (singularLocus k Y).subscheme}
  (hν : CommSq (singularLocus k X).blowupToBase fν f (singularLocus k Y).blowupToBase)

variable [f.IsOver (Spec (.of k))]

section BranchRatios

variable [IsSepClosed k]
  (hN : CommSq (singularLocus k X).subschemeι fN f (singularLocus k Y).subschemeι)

local notation "g" => nodalConductorBranchMap hν hN
local notation "branchPullback" =>
  Units.map (RingHom.toMonoidHom (CommRingCat.Hom.hom (Scheme.Hom.appTop g)))

variable (orderX : ∀ z : (singularLocus k X).subscheme,
    Fin 2 ≃ {b : X.branchScheme k // X.branchSchemeToSingularLocus k b = z})
  (orderY : ∀ z : (singularLocus k Y).subscheme,
    Fin 2 ≃ {b : Y.branchScheme k // Y.branchSchemeToSingularLocus k b = z})
  (keep : (singularLocus k Y).subscheme ↪ (singularLocus k X).subscheme)
  (hkeep : ∀ z i, nodalConductorBranchMap hν hN (orderX (keep z) i).val = (orderY z i).val)
  (hcollapse : ∀ z ∉ Set.range keep,
    nodalConductorBranchMap hν hN (orderX z 1).val =
      nodalConductorBranchMap hν hN (orderX z 0).val)

include hkeep hcollapse in
/-- Pulling back a branch unit along a subdivision preserves the product of its
ordered node ratios. Each selected node contributes the ratio of its corresponding
old node, and every node whose branches coalesce contributes one. -/
theorem finprod_branchRatioHom_nodalConductorBranchMap (a : Γ(B[Y], ⊤)ˣ) :
    (∏ᶠ z : N[X], X.branchRatioHom (k := k) nodal[X] orderX (branchPullback a) z) =
      ∏ᶠ z : N[Y], Y.branchRatioHom (k := k) nodal[Y] orderY a z := by
  have hover : g ≫ π[Y] ≫ ι[Y] ≫ Y ↘ Spec (.of k) = π[X] ≫ ι[X] ≫ X ↘ Spec (.of k) := by
    rw [nodalConductorBranchMap_comp_toSingularLocus_assoc, ← reassoc_of% hN.w, comp_over]
  let r := X.branchRatioHom (k := k) nodal[X] orderX (branchPullback a)
  have hr (z : N[X]) : r z =
      Y.branchSchemeGlobalUnitsEquiv (k := k) nodal[Y] a (g (orderX z 1).val) /
        Y.branchSchemeGlobalUnitsEquiv (k := k) nodal[Y] a (g (orderX z 0).val) := by
    simp only [r, branchRatioHom_apply]
    exact congrArg₂ (· / ·)
      (X.branchSchemeGlobalUnitsEquiv_appTop_of_comp nodal[X] nodal[Y] g hover a _)
      (X.branchSchemeGlobalUnitsEquiv_appTop_of_comp nodal[X] nodal[Y] g hover a _)
  calc
    (∏ᶠ z : N[X], r z) = ∏ᶠ z ∈ Set.range keep, r z := by
      rw [← finprod_mem_univ]
      refine finprod_mem_inter_mulSupport_eq' _ _ _ fun z hz ↦ ?_
      simp only [Set.mem_univ, true_iff]
      by_contra hn
      exact hz (by rw [hr, hcollapse z hn, div_self'])
    _ = ∏ᶠ z : N[Y], r (keep z) := finprod_mem_range keep.injective
    _ = ∏ᶠ z : N[Y], Y.branchRatioHom (k := k) nodal[Y] orderY a z := by
      exact finprod_congr fun z ↦ by rw [hr, hkeep, hkeep, branchRatioHom_apply]

end BranchRatios

variable [IsAlgClosed k] {n m : ℕ} [NeZero n] [NeZero m]
  {α : Type v} {β : Type w}
  {pX : α → (X ↘ Spec (.of k)).smoothLocus}
  {pY : β → (Y ↘ Spec (.of k)).smoothLocus}
  {eX : ZMod n ≃ (X.dualGraph pX).Edge} {eY : ZMod m ≃ (Y.dualGraph pY).Edge}
  {oX : (X.dualGraph pX).Edge → Equiv.Perm (Fin 2)}
  {oY : (Y.dualGraph pY).Edge → Equiv.Perm (Fin 2)}
  {wX : ZMod n ≃ (X.dualGraph pX).Vertex} {wY : ZMod m ≃ (Y.dualGraph pY).Vertex}
  (hwX : ∀ i b, (X.dualGraph pX).endpoint (eX i) (oX (eX i) b) =
    wX ((DualGraph.cycle n).endpoint i b))
  (hwY : ∀ i b, (Y.dualGraph pY).endpoint (eY i) (oY (eY i) b) =
    wY ((DualGraph.cycle m).endpoint i b))

include hν in
/-- Pullback under an oriented subdivision of the nodal conductor preserves the
period. A lift to the normalization guarantees that the pulled-back class still
belongs to the normalization kernel. The selected node over every old node
preserves both ordered branches, including the two branches of a self-node. -/
theorem nodalPicardCycleMulEquiv_pullback_of_subdivision
    (hnodes : Set.MapsTo f (X.singularLocus k).support (Y.singularLocus k).support)
    (keep : N[Y] ↪ N[X])
    (hkeep : ∀ z i, fν (j[X] (X.branchOrderOfDualGraph pX oX (keep z) i).val) =
      j[Y] (Y.branchOrderOfDualGraph pY oY z i).val)
    (hcollapse : ∀ z ∉ Set.range keep,
      fν (j[X] (X.branchOrderOfDualGraph pX oX z 1).val) =
        fν (j[X] (X.branchOrderOfDualGraph pX oX z 0).val))
    (a : P[Y]) :
    ∃ ha : LineBundleClass.pullback f a.val ∈ P[X],
      X.nodalPicardCycleMulEquiv hwX ⟨LineBundleClass.pullback f a.val, ha⟩ =
        Y.nodalPicardCycleMulEquiv hwY a := by
  let fN := f.nodalConductorNodeMap nodal[X] nodal[Y] hnodes
  have hN : CommSq ι[X] fN f ι[Y] :=
    ⟨(f.nodalConductorNodeMap_comp_subschemeι nodal[X] nodal[Y] hnodes).symm⟩
  obtain ⟨L, ⟨t⟩, ⟨d⟩, hL⟩ :=
    Y.exists_trivialized_representative_of_mem_nodalPicardKernel nodal[Y] a
  let t' := hν.pullbackTrivialization t
  let d' := hN.pullbackTrivialization d
  have ha : LineBundleClass.pullback f a.val ∈ P[X] := by
    rw [MonoidHom.mem_ker, LineBundleClass.pullbackHom_apply,
      LineBundleClass.pullback_comp, hν.w, ← LineBundleClass.pullback_comp]
    have ha₀ := MonoidHom.mem_ker.mp a.property
    rw [LineBundleClass.pullbackHom_apply] at ha₀
    rw [ha₀, LineBundleClass.pullback_one]
  refine ⟨ha, ?_⟩
  rw [X.nodalPicardCycleMulEquiv_apply hwX _ ((InvertibleSheaf.pullback f).obj L) t' d'
    (by rw [← LineBundleClass.pullback_mk, hL]), Y.nodalPicardCycleMulEquiv_apply hwY a L t d hL]
  have hglue := (conductor[Y]).lineGluingUnit_pullback (conductor[X]) hν hN
    ⟨(nodalConductorBranchMap_comp_toBlowup hν hN).symm⟩
    ⟨(nodalConductorBranchMap_comp_toSingularLocus hν hN).symm⟩ t d
  refine (congrArg (X.nodalConductorCycleProduct pX eX oX) hglue).trans ?_
  simp only [nodalConductorCycleProduct_eq_finprod]
  refine finprod_branchRatioHom_nodalConductorBranchMap hν hN _ _ keep
    (fun z i ↦ (nodalConductorBranchMap_apply_eq_iff hν hN _ _).mpr (hkeep z i)) ?_ _
  intro z hz
  apply (nodalConductorBranchMap_apply_eq_iff hν hN _ _).mpr
  simpa only [← Scheme.Hom.comp_apply, nodalConductorBranchMap_comp_toBlowup]
    using hcollapse z hz

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

variable {k : Type u} [Field k] [IsAlgClosed k] {S T : Scheme.{u}}
  [S.Over (Spec (.of k))] [T.Over (Spec (.of k))]
  [S.IsProjectiveOver k] [T.IsProjectiveOver k] [IsIntegral S] [IsIntegral T]
  [SmoothOfRelativeDimension 2 (S ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (T ↘ Spec (.of k))]
  {D : S.IdealSheafData} {E : T.IdealSheafData}
  [PrestableFamily (D.subscheme ↘ Spec (.of k))] [PrestableFamily (E.subscheme ↘ Spec (.of k))]
  (hD : D.IsEffectiveCartier) (hE : E.IsEffectiveCartier)

local notation "C" => IdealSheafData.subscheme D
local notation "C'" => IdealSheafData.subscheme E
local notation "N[" W "]" => IdealSheafData.subscheme (singularLocus k W)
local notation "ν[" W "]" => IdealSheafData.blowupToBase (singularLocus k W)
local notation "j[" W "]" => branchSchemeToBlowup k W

variable
  (hgenus : ∀ v : irreducibleComponents (D.subscheme.singularLocus k).blowup,
    (D.subscheme.blowupComponent (K := k) v).toScheme.genus k = 0)
  (hgenus' : ∀ v : irreducibleComponents (E.subscheme.singularLocus k).blowup,
    (E.subscheme.blowupComponent (K := k) v).toScheme.genus k = 0)
  {n m : ℕ} [NeZero n] [NeZero m] {α : Type v} {β : Type w}
  {p : α → (D.subscheme ↘ Spec (.of k)).smoothLocus}
  {p' : β → (E.subscheme ↘ Spec (.of k)).smoothLocus}
  {e : ZMod n ≃ (D.subscheme.dualGraph p).Edge} {e' : ZMod m ≃ (E.subscheme.dualGraph p').Edge}
  {o : (D.subscheme.dualGraph p).Edge → Equiv.Perm (Fin 2)}
  {o' : (E.subscheme.dualGraph p').Edge → Equiv.Perm (Fin 2)}
  {q : ZMod n ≃ (D.subscheme.dualGraph p).Vertex} {q' : ZMod m ≃ (E.subscheme.dualGraph p').Vertex}
  (hq : ∀ i b, (D.subscheme.dualGraph p).endpoint (e i) (o (e i) b) =
    q ((DualGraph.cycle n).endpoint i b))
  (hq' : ∀ i b, (E.subscheme.dualGraph p').endpoint (e' i) (o' (e' i) b) =
    q' ((DualGraph.cycle m).endpoint i b))

/-- A morphism of surfaces whose boundary map subdivides the oriented conductor
pulls back boundary-orthogonal Picard classes and preserves their periods. -/
theorem boundaryPeriod_pullback_of_subdivision
    (f : S ⟶ T) {g : C ⟶ C'} [g.IsOver (Spec (.of k))]
    (hcomm : D.subschemeι ≫ f = g ≫ E.subschemeι)
    {gν : ((C).singularLocus k).blowup ⟶ ((C').singularLocus k).blowup}
    (hν : CommSq ν[C] gν g ν[C'])
    (hnodes : Set.MapsTo g ((C).singularLocus k).support ((C').singularLocus k).support)
    (keep : N[C'] ↪ N[C])
    (hkeep : ∀ z i, gν (j[C] ((C).branchOrderOfDualGraph p o (keep z) i).val) =
      j[C'] ((C').branchOrderOfDualGraph p' o' z i).val)
    (hcollapse : ∀ z ∉ Set.range keep,
      gν (j[C] ((C).branchOrderOfDualGraph p o z 1).val) =
        gν (j[C] ((C).branchOrderOfDualGraph p o z 0).val))
    (a : Multiplicative (E.boundaryOrthogonal k)) :
    let b := Additive.ofMul (pullback f a.toAdd.val.toMul)
    ∃ hb : b ∈ D.boundaryOrthogonal k,
      hD.boundaryPeriod hgenus hq (Multiplicative.ofAdd ⟨b, hb⟩) =
        hE.boundaryPeriod hgenus' hq' a := by
  let c := hE.restrictBoundaryOrthogonal hgenus' a
  obtain ⟨hc, hperiod⟩ := Scheme.Hom.nodalPicardCycleMulEquiv_pullback_of_subdivision
    hν hq hq' hnodes keep hkeep hcollapse c
  have hres : pullback D.subschemeι (pullback f a.toAdd.val.toMul) = pullback g c.val := by
    rw [pullback_comp, hcomm, ← pullback_comp, restrictBoundaryOrthogonal_apply]
  have hb : Additive.ofMul (pullback f a.toAdd.val.toMul) ∈ D.boundaryOrthogonal k := by
    apply (hD.pullback_blowupToBase_comp_subschemeι_eq_one_iff_mem_orthogonal hgenus _).mp
    rw [toMul_ofMul, ← pullback_comp, hres]
    simpa only [pullbackHom_apply] using MonoidHom.mem_ker.mp hc
  refine ⟨hb, ?_⟩
  rw [boundaryPeriod_apply, boundaryPeriod_apply]
  have hclass : hD.restrictBoundaryOrthogonal hgenus
      (Multiplicative.ofAdd ⟨Additive.ofMul (pullback f a.toAdd.val.toMul), hb⟩) =
      ⟨pullback g c.val, hc⟩ := by
    apply Subtype.ext
    rw [restrictBoundaryOrthogonal_apply, toAdd_ofAdd, toMul_ofMul, hres]
  rw [hclass]
  exact hperiod

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
