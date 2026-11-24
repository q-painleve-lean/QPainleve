/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Branches.Exceptional
public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Branches.Normalization
public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Subdivision
public import QPainleve.AlgebraicGeometry.Curves.Node.GenericPoint

import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Option
import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Lift
import QPainleve.AlgebraicGeometry.IdealSheaf.BaseChange
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.IrreducibleOfConnectedDomainStalk
import TauCeti.AlgebraicGeometry.Morphisms.Proper
import TauCeti.Topology.Sober

/-!
# Subdivision of the boundary at a node

The strict part of the normalization of the reduced total boundary comes from
the original boundary normalization. Over the center the two old branches
meet the new exceptional component at different attachment nodes. This is
the boundary subdivision of a toric blowup in [Gross, Hacking and Keel, §1][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S1
-/

public noncomputable section

open CategoryTheory TopologicalSpace TauCeti TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  {D : X.IdealSheafData} [D.subscheme.Over (Spec (.of k))]
  [PrestableFamily (D.subscheme ↘ Spec (.of k))]
  {p : D.subscheme} (hc : IsClosed ({D.subschemeι p} : Set X))

local notation "S" => Spec (CommRingCat.of k)
local notation "C" => IdealSheafData.subscheme D
local notation "I" =>
  vanishingIdeal (Closeds.mk (closure ({D.subschemeι p} : Set X)) isClosed_closure)
local notation "π" => blowupToBase (I)
local notation "R" => radical (D.comap (π))
local notation "B" => subscheme (R)
local notation "j" => subschemeι (R)
local notation "E" => IdealSheafData.comap (I) (π)
local notation "β" => subschemeMap (R) D (π) (le_map_iff_comap_le.mpr (le_radical _))
local notation "N[" T "]" => blowup (Scheme.singularLocus k T)
local notation "ν[" T "]" => blowupToBase (Scheme.singularLocus k T)
local notation "J[" T "]" => Scheme.singularLocus k T
local notation "b[" T "]" => Scheme.branchSchemeToBlowup k T
local notation "nodal[" T "]" =>
  PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := T ↘ S)

variable [(D.comap (vanishingIdeal
  ⟨closure ({D.subschemeι p} : Set X), isClosed_closure⟩).blowupToBase).radical.subscheme.Over
    (Spec (.of k))]
  [PrestableFamily ((D.comap (vanishingIdeal
    ⟨closure ({D.subschemeι p} : Set X), isClosed_closure⟩).blowupToBase).radical.subscheme ↘
      Spec (.of k))]
  (hp : p ∈ (D.subscheme.singularLocus k).support)
  (hCOver : D.subscheme ↘ Spec (.of k) = D.subschemeι ≫ X ↘ Spec (.of k))
  (hBOver :
    (D.comap (vanishingIdeal
      ⟨closure ({D.subschemeι p} : Set X), isClosed_closure⟩).blowupToBase).radical.subscheme ↘
        Spec (.of k) =
      (D.comap (vanishingIdeal
        ⟨closure ({D.subschemeι p} : Set X), isClosed_closure⟩).blowupToBase).radical.subschemeι ≫
        (vanishingIdeal ⟨closure ({D.subschemeι p} : Set X), isClosed_closure⟩).blowupToBase ≫
        X ↘ Spec (.of k))

local notation "s" => D.normalizationToNodalBlowup hc hp hCOver hBOver

include hc in
private theorem mem_isoLocus_nodalBlowupBoundaryMap [IsReduced C] {x : C} (hx : x ≠ p) :
    x ∈ (β).isoLocus := by
  apply (D.preimage_isoLocus_le_subschemeMap_radical (π))
  apply (π).le_isoLocus_iff.mpr (I).isIso_blowupToBase_restrict_compl_support
  simpa only [← SetLike.mem_coe, Closeds.coe_compl, coe_support_vanishingIdeal, Closeds.coe_mk,
    hc.closure_eq, Set.mem_compl_iff, Set.mem_singleton_iff, D.subschemeι.injective.eq_iff] using hx

omit [PrestableFamily (C ↘ S)] [PrestableFamily (B ↘ S)] in
include hCOver hBOver in
private theorem boundaryMap_over : (β) ≫ (C ↘ S) = B ↘ S := by
  rw [hCOver, ← Category.assoc, subschemeMap_subschemeι, Category.assoc, hBOver]

include hp hc hCOver hBOver in
private theorem strictNormalization_over : (s) ≫ ν[B] ≫ B ↘ S = ν[C] ≫ C ↘ S := by
  calc
    _ = (s) ≫ ν[B] ≫ (β) ≫ C ↘ S :=
      congrArg (fun t ↦ (s) ≫ ν[B] ≫ t) (boundaryMap_over hCOver hBOver).symm
    _ = _ := by rw [← Category.assoc (ν[B]), ← Category.assoc (s),
      normalizationToNodalBlowup_blowupToBase_boundaryMap]

include hp hc hCOver hBOver in
private theorem isClosed_range_strictNormalization : IsClosed (Set.range (s)) := by
  have : IsFinite ν[C] := (C).isFinite_blowupToBase_singularLocus nodal[C]
  have : IsFinite ν[B] := (B).isFinite_blowupToBase_singularLocus nodal[B]
  have : IsProper ((s) ≫ ν[B] ≫ B ↘ S) := by
    rw [strictNormalization_over hc hp hCOver hBOver]
    infer_instance
  have : IsProper (s) := IsProper.of_comp (s) (ν[B] ≫ B ↘ S)
  exact (s).isClosedMap.isClosed_range

include hp hc hCOver hBOver in
private theorem boundaryMap_normalizationToNodalBlowup_apply (x : N[C]) :
    (β) (ν[B] ((s) x)) = ν[C] x := by
  simpa only [Scheme.Hom.comp_apply] using congrArg (fun t : N[C] ⟶ C ↦ t x)
    (D.normalizationToNodalBlowup_blowupToBase_boundaryMap hc hp hCOver hBOver)

variable [IsIntegral X] [QuasiCompact (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))] [IsReduced D.subscheme]
  (hD : D.IsEffectiveCartier)

local notation "exc" => hD.exceptionalNormalizationComponent (k := k) hc

include hp hc hCOver hBOver in
private theorem generic_mem_range_strictNormalization {v : irreducibleComponents N[B]}
    (hv : v ≠ (exc)) : (genericPoints.ofComponent v : N[B]) ∈ Set.range (s) := by
  let y : N[B] := genericPoints.ofComponent v
  have hη : y ∈ (v : Set N[B]) := (genericPoints.isGenericPoint_ofComponent v).mem
  have hpy : (β) (ν[B] y) ≠ p := by
    intro he
    have hex := (IsEffectiveCartier.mem_exceptional_iff_boundaryMap_eq hc _).mpr he
    rw [← SetLike.mem_coe, ← (E).range_subschemeι,
      ← hD.range_exceptionalNormalizationComponent (k := k) hc] at hex
    obtain ⟨z, hz⟩ := hex
    have hh : ν[B] z.val = ν[B] y := by
      apply (j).injective
      have hzval : ((B).blowupComponent (K := k) (exc)).ι z = z.val := (rfl)
      simpa only [Scheme.Hom.comp_apply, hzval] using hz
    have hU := (B).blowupComponentGeneric_mem_isoLocus (k := k) v
    have heq : z.val = y := (ν[B]).injOn_preimage_isoLocus
      (by rwa [Set.mem_preimage, hh]) hU hh
    have : IsRegular N[B] := (B).isRegular_blowup_singularLocus nodal[B]
    apply hv
    exact (irreducibleComponentOf_eq_iff.mpr hη).symm.trans
      (irreducibleComponentOf_eq_iff.mpr (by
        rw [← heq, ← (B).coe_blowupComponent]
        exact z.property))
  have := (C).surjective_blowupToBase_singularLocus nodal[C]
  obtain ⟨x, hx⟩ := (ν[C]).surjective ((β) (ν[B] y))
  have hH : (β) (ν[B] ((s) x)) = (β) (ν[B] y) := by
    simpa only [Scheme.Hom.comp_apply] using
      (congrArg (fun t : N[C] ⟶ C ↦ t x)
        (D.normalizationToNodalBlowup_blowupToBase_boundaryMap hc hp hCOver hBOver)).trans hx
  have hU := mem_isoLocus_nodalBlowupBoundaryMap hc hpy
  have hν := (β).injOn_preimage_isoLocus (by rwa [Set.mem_preimage, hH]) hU hH
  have hL := (B).blowupComponentGeneric_mem_isoLocus (k := k) v
  exact ⟨x, (ν[B]).injOn_preimage_isoLocus (by rwa [Set.mem_preimage, hν]) hL hν⟩

include hD hc hp hCOver hBOver in
/-- The image of the original normalization consists of the strict components
of the normalized reduced total boundary. -/
theorem range_normalizationToNodalBlowup :
    Set.range (s) = ((exc) : Set N[B])ᶜ := by
  have : IsRegular N[C] := (C).isRegular_blowup_singularLocus nodal[C]
  have : IsRegular N[B] := (B).isRegular_blowup_singularLocus nodal[B]
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩ hx
    let v := irreducibleComponentOf x
    let y : N[C] := genericPoints.ofComponent v
    have hxy := ((genericPoints.isGenericPoint_ofComponent v).specializes
      (mem_irreducibleComponentOf x)).map (s).continuous
    have hy : (s) y ∈ ((exc) : Set N[B]) :=
      hxy.mem_open (by
        rw [← (B).coe_blowupComponent]
        exact ((B).blowupComponent (K := k) (exc)).isOpen) hx
    have hy' : (s) y ∈ (B).blowupComponent (K := k) (exc) := by
      rwa [← SetLike.mem_coe, (B).coe_blowupComponent]
    have hE := (hD.bijOn_blowupToBase_exceptionalNormalizationComponent (k := k) hc).mapsTo hy'
    have hf := (IsEffectiveCartier.mem_exceptional_iff_boundaryMap_eq hc _).mp hE
    have heq : (β) (ν[B] ((s) y)) = ν[C] y := by
      simpa only [Scheme.Hom.comp_apply] using congrArg (fun t : N[C] ⟶ C ↦ t y)
        (D.normalizationToNodalBlowup_blowupToBase_boundaryMap hc hp hCOver hBOver)
    exact ((C).mem_support_singularLocus_iff_notMem_smoothLocus _).mp
      (heq ▸ hf.symm ▸ hp) ((C).blowupComponentGeneric_mem_smoothLocus v)
  · intro y hy
    let v := irreducibleComponentOf y
    have hv : v ≠ (exc) := fun he ↦ hy (he ▸ mem_irreducibleComponentOf y)
    have hη := generic_mem_range_strictNormalization hc hp hCOver hBOver hD hv
    exact ((genericPoints.isGenericPoint_ofComponent v).specializes (mem_irreducibleComponentOf y))
      |>.mem_closed (isClosed_range_strictNormalization hc hp hCOver hBOver) hη

private theorem branch_projection (T : Scheme.{u}) [T.Over S] [PrestableFamily (T ↘ S)]
    (q : T.branchScheme k) :
    ν[T] (b[T] q) = (J[T]).subschemeι (T.branchSchemeToSingularLocus k q) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
    branchSchemeToSingularLocus_subschemeι]

private theorem branchPoint_mem_singular (T : Scheme.{u}) [T.Over S]
    [PrestableFamily (T ↘ S)] (q : T.branchScheme k) :
    ν[T] (b[T] q) ∈ (J[T]).support :=
  (J[T]).range_subschemeι.le ⟨_, (branch_projection T q).symm⟩

private instance {T : Scheme.{u}} [T.Over S] [PrestableFamily (T ↘ S)] :
    IsClosedImmersion b[T] :=
  MorphismProperty.of_isPullback (T.isPullback_branchScheme k) inferInstance

local notation "centerBranch" =>
  Subtype fun q : Scheme.branchScheme k C ↦
    subschemeι J[C] (Scheme.branchSchemeToSingularLocus k C q) = p

variable [IsAlgClosed k]

local notation "attach" => hD.branchEquivSingularFiber nodal[C] hc hCOver hBOver hp nodal[B]
local notation "excBranch" => hD.exceptionalNormalizationBranchEquiv hc hCOver hBOver hp

include hD hp hc hCOver hBOver in
private theorem strictBranch_mem_range (q : (C).branchScheme k) :
    (s) (b[C] q) ∈ Set.range b[B] := by
  rw [(B).range_branchSchemeToBlowup, Set.mem_preimage]
  let y := ν[B] ((s) (b[C] q))
  have hy := boundaryMap_normalizationToNodalBlowup_apply hc hp hCOver hBOver (b[C] q)
  rw [branch_projection] at hy
  have hn : (β) y ∈ (J[C]).support :=
    (J[C]).range_subschemeι.le ⟨_, hy.symm⟩
  by_cases h : (β) y = p
  · let q' : centerBranch := ⟨q, hy.symm.trans h⟩
    have hq := D.blowupToBase_normalizationToNodalBlowup_branch hc hp hCOver hBOver hD q'
    exact hq.symm ▸ ((attach) q').property.1
  · have hBij := D.bijOn_support_singularLocus_off_blowup nodal[C] hc hCOver hBOver nodal[B]
    obtain ⟨z, hz, hz'⟩ := hBij.surjOn ⟨h, hn⟩
    have hU := mem_isoLocus_nodalBlowupBoundaryMap hc h
    have heq := (β).injOn_preimage_isoLocus (by rwa [Set.mem_preimage, hz']) hU hz'
    exact Eq.mp (congrArg (fun t : B ↦ t ∈ (J[B]).support) heq) hz.2

include hD hp hc hCOver hBOver in
private theorem exceptionalBranch_mem_range (q : centerBranch) :
    ((excBranch) q).val ∈ Set.range b[B] := by
  rw [(B).range_branchSchemeToBlowup]
  exact ((excBranch) q).property.2

include hD hp hc hCOver hBOver in
private theorem exists_lift_with_exceptional_value (q : centerBranch) :
    ∃ g : N[B] ⟶ N[C], g ≫ ν[C] = ν[B] ≫ (β) ∧
      ∀ y ∈ ((exc) : Set N[B]), g y = b[C] q.val := by
  have : (β).IsOver S := ⟨boundaryMap_over hCOver hBOver⟩
  have hcomp (v : irreducibleComponents N[B])
      (hv : (((B).blowupComponent (K := k) v).ι ≫ ν[B] ≫ (β))
        (genericPoint ((B).blowupComponent (K := k) v).toScheme) ∈ (J[C]).support) :
      v = (exc) := by
    by_contra hne
    obtain ⟨x, hx⟩ := generic_mem_range_strictNormalization hc hp hCOver hBOver hD hne
    let y : ((B).blowupComponent (K := k) v).toScheme := ⟨genericPoints.ofComponent v, by
      rw [← SetLike.mem_coe, (B).coe_blowupComponent]
      exact (genericPoints.isGenericPoint_ofComponent v).mem⟩
    let m := ((B).blowupComponent (K := k) v).ι ≫ ν[B] ≫ (β)
    have : IsRegular N[C] := (C).isRegular_blowup_singularLocus nodal[C]
    let w := irreducibleComponentOf x
    let z : N[C] := genericPoints.ofComponent w
    have hsz := ((genericPoints.isGenericPoint_ofComponent w).specializes
      (mem_irreducibleComponentOf x)).map (s).continuous
    have hz : (s) z ∈ ((B).blowupComponent (K := k) v : Set N[B]) :=
      hsz.mem_open ((B).blowupComponent (K := k) v).isOpen (hx.symm ▸ y.property)
    let z' : ((B).blowupComponent (K := k) v).toScheme := ⟨(s) z, hz⟩
    have hy : m z' ∈ (C ↘ S).smoothLocus := by
      have hzval : ((B).blowupComponent (K := k) v).ι z' = (s) z := (rfl)
      simpa only [m, Scheme.Hom.comp_apply, hzval,
        boundaryMap_normalizationToNodalBlowup_apply hc hp hCOver hBOver] using
        (C).blowupComponentGeneric_mem_smoothLocus w
    exact ((C).mem_support_singularLocus_iff_notMem_smoothLocus _).mp hv
      (((genericPoint_specializes z').map m.continuous).mem_open
        (C ↘ S).smoothLocus.isOpen hy)
  let v := (exc)
  let m := ((B).blowupComponent (K := k) v).ι ≫ ν[B] ≫ (β)
  have he (y : ((B).blowupComponent (K := k) v).toScheme) : m y = p := by
    have hE := (hD.bijOn_blowupToBase_exceptionalNormalizationComponent (k := k) hc).mapsTo
      y.property
    have hyval : ((B).blowupComponent (K := k) v).ι y = y.val := (rfl)
    simpa only [m, Scheme.Hom.comp_apply, hyval] using
      (IsEffectiveCartier.mem_exceptional_iff_boundaryMap_eq hc _).mp hE
  obtain ⟨g, ⟨hg, hgq⟩, _⟩ := (β).existsUnique_nodal_normalization_lift
    (fun _ _ ↦ q.val) (fun w hw ↦ by
      obtain rfl := hcomp w hw
      rw [branch_projection, q.property]
      exact (he _).symm)
  refine ⟨g, hg, fun y hy ↦ ?_⟩
  have hy' : y ∈ (B).blowupComponent (K := k) v := by
    rw [← SetLike.mem_coe, (B).coe_blowupComponent]
    exact hy
  have hs : m (genericPoint _) ∈ (J[C]).support := (he _).symm ▸ hp
  simpa only [Scheme.Opens.ι_apply] using hgq v hs ⟨y, hy'⟩

omit [IsIntegral X] [QuasiCompact (X ↘ S)] [SmoothOfRelativeDimension 2 (X ↘ S)]
  [IsReduced C] [IsAlgClosed k] in
include hc hp hCOver hBOver in
private theorem leftInverse_strictNormalization {g : N[B] ⟶ N[C]}
    (hg : g ≫ ν[C] = ν[B] ≫ (β)) : Function.LeftInverse g (s) := by
  intro x
  have h := congrArg (fun t : N[C] ⟶ N[C] ↦ t x)
    (D.normalizationToNodalBlowup_comp_lift hc hp hCOver hBOver hg)
  rw [Scheme.Hom.comp_apply] at h
  exact h.trans (rfl)

omit [IsAlgClosed k] in
private theorem image_point_mem_normalizationComponent
    {T W : Scheme.{u}} [T.Over S] [W.Over S]
    [PrestableFamily (T ↘ S)] [PrestableFamily (W ↘ S)]
    (g : N[T] ⟶ N[W]) (v : irreducibleComponents N[T]) {x : N[T]}
    (hx : x ∈ (v : Set N[T])) :
    g x ∈ (irreducibleComponentOf (g (genericPoints.ofComponent v)) : Set N[W]) :=
  (((genericPoints.isGenericPoint_ofComponent v).specializes hx).map g.continuous).mem_closed
    (isClosed_of_mem_irreducibleComponents _ (irreducibleComponentOf _).property)
    (mem_irreducibleComponentOf _)

omit [IsAlgClosed k] in
include hD hc hp hCOver hBOver in
private theorem strictComponent_bijective {g : N[B] ⟶ N[C]}
    (hg : g ≫ ν[C] = ν[B] ≫ (β)) :
    Function.Bijective (fun v : irreducibleComponents N[C] ↦
      (⟨irreducibleComponentOf ((s) (genericPoints.ofComponent v)), fun hv ↦
        (range_normalizationToNodalBlowup hc hp hCOver hBOver hD).le
          (Set.mem_range_self (f := (s)) (genericPoints.ofComponent v : N[C]))
          (hv ▸ mem_irreducibleComponentOf _)⟩ :
        {v : irreducibleComponents N[B] // v ≠ (exc)})) := by
  have : IsRegular N[C] := (C).isRegular_blowup_singularLocus nodal[C]
  have : IsRegular N[B] := (B).isRegular_blowup_singularLocus nodal[B]
  have hs := leftInverse_strictNormalization hc hp hCOver hBOver hg
  constructor
  · intro v w h
    let t := irreducibleComponentOf ((s) (genericPoints.ofComponent w))
    have hv : irreducibleComponentOf ((s) (genericPoints.ofComponent v)) = t :=
      congrArg Subtype.val h
    have hv' : (s) (genericPoints.ofComponent v) ∈ (t : Set N[B]) := by
      rw [← hv]
      exact mem_irreducibleComponentOf _
    have hgv := image_point_mem_normalizationComponent g t hv'
    have hgw := image_point_mem_normalizationComponent g t
      (mem_irreducibleComponentOf ((s) (genericPoints.ofComponent w)))
    rw [hs] at hgv hgw
    exact ((irreducibleComponentOf_eq_iff.mpr
      (genericPoints.isGenericPoint_ofComponent v).mem).symm.trans
      (irreducibleComponentOf_eq_iff.mpr hgv)).trans
      ((irreducibleComponentOf_eq_iff.mpr hgw).symm.trans
        (irreducibleComponentOf_eq_iff.mpr (genericPoints.isGenericPoint_ofComponent w).mem))
  · intro ⟨v, hv⟩
    obtain ⟨x, hx⟩ := generic_mem_range_strictNormalization hc hp hCOver hBOver hD hv
    refine ⟨irreducibleComponentOf x, Subtype.ext ?_⟩
    have hm := image_point_mem_normalizationComponent (s) (irreducibleComponentOf x)
      (mem_irreducibleComponentOf x)
    rw [hx] at hm
    exact (irreducibleComponentOf_eq_iff.mpr hm).symm.trans
      (irreducibleComponentOf_eq_iff.mpr (genericPoints.isGenericPoint_ofComponent v).mem)

variable (D)

include hc hp hCOver hBOver in
/-- Every old normalized component corresponds to a unique strict normalized component
of the reduced total boundary. The only additional component is exceptional. -/
def strictNormalizationComponentEquiv :
    irreducibleComponents N[C] ≃ {v : irreducibleComponents N[B] // v ≠ (exc)} := by
  have : (β).IsOver S := ⟨boundaryMap_over hCOver hBOver⟩
  let h := (β).exists_nodal_normalization_lift (k := k)
  exact Equiv.ofBijective _ (strictComponent_bijective hc hp hCOver hBOver hD h.choose_spec.w.symm)

include hc hp hCOver hBOver in
/-- The old normalized component maps into its strict counterpart under the strict lift. -/
theorem normalizationToNodalBlowup_mem_strictNormalizationComponentEquiv
    (v : irreducibleComponents N[C]) {x : N[C]} (hx : x ∈ (v : Set N[C])) :
    (s) x ∈ ((D.strictNormalizationComponentEquiv hc hp hCOver hBOver hD v).val :
      Set N[B]) :=
  image_point_mem_normalizationComponent (s) v hx

/-- The strict-side branch of the reduced total boundary corresponding to an original branch. -/
def strictNormalizationBranch (q : (C).branchScheme k) : (B).branchScheme k :=
  (Equiv.ofInjective b[B] (b[B]).isClosedEmbedding.injective).symm ⟨(s) (b[C] q),
    strictBranch_mem_range hc hp hCOver hBOver hD q⟩

/-- The normalized point of the strict branch is the strict lift of the old normalized point. -/
@[simp]
theorem branchSchemeToBlowup_strictNormalizationBranch (q : (C).branchScheme k) :
    b[B] (D.strictNormalizationBranch hc hp hCOver hBOver hD q) = (s) (b[C] q) :=
  Equiv.apply_ofInjective_symm _ _

/-- The exceptional-side branch at the attachment labelled by an original branch at the center. -/
def exceptionalSideBranch (q : centerBranch) : (B).branchScheme k :=
  (Equiv.ofInjective b[B] (b[B]).isClosedEmbedding.injective).symm ⟨((excBranch) q).val,
    exceptionalBranch_mem_range hc hp hCOver hBOver hD q⟩

/-- The exceptional-side branch is the point of the normalized exceptional component
over the given attachment. -/
@[simp]
theorem branchSchemeToBlowup_exceptionalSideBranch (q : centerBranch) :
    b[B] (D.exceptionalSideBranch hc hp hCOver hBOver hD q) = ((excBranch) q).val :=
  Equiv.apply_ofInjective_symm _ _

/-- An attachment node has the indicated strict and exceptional branches over the same point. -/
theorem branchSchemeToSingularLocus_exceptionalSideBranch (q : centerBranch) :
    (B).branchSchemeToSingularLocus k (D.exceptionalSideBranch hc hp hCOver hBOver hD q) =
      (B).branchSchemeToSingularLocus k
        (D.strictNormalizationBranch hc hp hCOver hBOver hD q.val) := by
  apply (J[B]).subschemeι.injective
  rw [← branch_projection, ← branch_projection, branchSchemeToBlowup_exceptionalSideBranch,
    branchSchemeToBlowup_strictNormalizationBranch,
    hD.blowupToBase_exceptionalNormalizationBranchEquiv hc hCOver hBOver hp,
    D.blowupToBase_normalizationToNodalBlowup_branch hc hp hCOver hBOver hD]

local notation "strBranch" => D.strictNormalizationBranch hc hp hCOver hBOver hD
local notation "newBranch" => D.exceptionalSideBranch hc hp hCOver hBOver hD

private theorem strictNormalizationBranch_injective : Function.Injective (strBranch) := by
  have : (β).IsOver S := ⟨boundaryMap_over hCOver hBOver⟩
  obtain ⟨g, hg⟩ := (β).exists_nodal_normalization_lift (k := k)
  have hs := (leftInverse_strictNormalization hc hp hCOver hBOver hg.w.symm).injective
  intro q q' heq
  apply (b[C]).isClosedEmbedding.injective
  apply hs
  simpa only [branchSchemeToBlowup_strictNormalizationBranch] using congrArg (b[B]) heq

private theorem exceptionalSideBranch_injective : Function.Injective (newBranch) := by
  intro q q' heq
  apply (excBranch).injective
  apply Subtype.ext
  simpa only [branchSchemeToBlowup_exceptionalSideBranch] using congrArg (b[B]) heq

private theorem branchSide_ne (q : (C).branchScheme k) (q' : centerBranch) :
    (strBranch) q ≠ (newBranch) q' := by
  intro heq
  have hm : b[B] ((newBranch) q') ∈ ((exc) : Set N[B]) := by
    rw [branchSchemeToBlowup_exceptionalSideBranch, ← (B).coe_blowupComponent]
    exact ((excBranch) q').property.1
  rw [← heq, branchSchemeToBlowup_strictNormalizationBranch] at hm
  exact (range_normalizationToNodalBlowup hc hp hCOver hBOver hD).le
    (Set.mem_range_self (b[C] q)) hm

private theorem branchSide_surjective :
    Function.Surjective (Sum.elim (strBranch) (newBranch)) := by
  intro q
  by_cases he : b[B] q ∈ ((exc) : Set N[B])
  · have h := branchPoint_mem_singular (B) q
    have he' : b[B] q ∈ (B).blowupComponent (K := k) (exc) := by
      rw [← SetLike.mem_coe, (B).coe_blowupComponent]
      exact he
    obtain ⟨i, hi⟩ := (excBranch).surjective ⟨b[B] q, he', h⟩
    refine ⟨Sum.inr i, (b[B]).isClosedEmbedding.injective ?_⟩
    simpa only [Sum.elim_inr, branchSchemeToBlowup_exceptionalSideBranch] using
      congrArg Subtype.val hi
  · obtain ⟨y, hy⟩ := (range_normalizationToNodalBlowup hc hp hCOver hBOver hD).ge he
    have hnode := D.mapsTo_support_singularLocus_nodalBlowup nodal[C] hc hCOver hBOver hp nodal[B]
      (branchPoint_mem_singular (B) q)
    rw [← hy, boundaryMap_normalizationToNodalBlowup_apply hc hp hCOver hBOver] at hnode
    have h : y ∈ Set.range b[C] := by
      rw [(C).range_branchSchemeToBlowup]
      exact hnode
    obtain ⟨i, rfl⟩ := h
    refine ⟨Sum.inl i, (b[B]).isClosedEmbedding.injective ?_⟩
    simpa only [Sum.elim_inl, branchSchemeToBlowup_strictNormalizationBranch] using hy

/-- The branches of the reduced total boundary consist of one strict branch for every
old branch and one exceptional branch for each old branch at the center. -/
def normalizationBranchEquiv :
    (C).branchScheme k ⊕ (centerBranch) ≃ (B).branchScheme k :=
  Equiv.ofBijective (Sum.elim (strBranch) (newBranch))
    ⟨(D.strictNormalizationBranch_injective hc hp hCOver hBOver hD).sumElim
      (D.exceptionalSideBranch_injective hc hp hCOver hBOver hD)
      (D.branchSide_ne hc hp hCOver hBOver hD),
      D.branchSide_surjective hc hp hCOver hBOver hD⟩

@[simp]
theorem normalizationBranchEquiv_inl (q : (C).branchScheme k) :
    D.normalizationBranchEquiv hc hp hCOver hBOver hD (.inl q) = (strBranch) q :=
  (rfl)

@[simp]
theorem normalizationBranchEquiv_inr (q : centerBranch) :
    D.normalizationBranchEquiv hc hp hCOver hBOver hD (.inr q) = (newBranch) q :=
  (rfl)

/-- The blowdown lifts to the normalizations by sending the exceptional component to
either prescribed original branch. The lift sends each strict branch back to its old branch. -/
theorem exists_nodalBlowupNormalizationLift (q : centerBranch) :
    ∃ g : N[B] ⟶ N[C], CommSq ν[B] g (β) ν[C] ∧
      (∀ a : (C).branchScheme k, g (b[B] ((strBranch) a)) = b[C] a) ∧
      (∀ a : centerBranch, g (b[B] ((newBranch) a)) = b[C] q.val) := by
  obtain ⟨g, hg, he⟩ := exists_lift_with_exceptional_value hc hp hCOver hBOver hD q
  refine ⟨g, ⟨hg.symm⟩, ?_, ?_⟩
  · intro a
    rw [branchSchemeToBlowup_strictNormalizationBranch]
    exact leftInverse_strictNormalization hc hp hCOver hBOver hg (b[C] a)
  · intro a
    apply he
    rw [branchSchemeToBlowup_exceptionalSideBranch, ← (B).coe_blowupComponent]
    exact ((excBranch) a).property.1

private theorem branchProjection_strict_apply (q : (C).branchScheme k) :
    (β) ((J[B]).subschemeι ((B).branchSchemeToSingularLocus k ((strBranch) q))) =
      (J[C]).subschemeι ((C).branchSchemeToSingularLocus k q) := by
  rw [← branch_projection, branchSchemeToBlowup_strictNormalizationBranch,
    boundaryMap_normalizationToNodalBlowup_apply hc hp hCOver hBOver, branch_projection]

omit [X.Over S] [(C).Over S] [PrestableFamily (C ↘ S)] [IsIntegral X] [QuasiCompact (X ↘ S)]
  [SmoothOfRelativeDimension 2 (X ↘ S)] [IsAlgClosed k] in
include hc in
private theorem eq_node_of_boundaryMap_eq {a b : (J[B]).subscheme}
    (h : (β) ((J[B]).subschemeι a) = (β) ((J[B]).subschemeι b))
    (hne : (β) ((J[B]).subschemeι b) ≠ p) : a = b := by
  have hU := mem_isoLocus_nodalBlowupBoundaryMap hc hne
  exact (J[B]).subschemeι.injective
    ((β).injOn_preimage_isoLocus (by rwa [Set.mem_preimage, h]) hU h)

section Numbering

variable {n : ℕ} [NeZero n] {ι₀ ι₁ : Type*}
  {pC : ι₀ → (D.subscheme ↘ Spec (.of k)).smoothLocus}
  {pB : ι₁ → ((D.comap (vanishingIdeal
    ⟨closure ({D.subschemeι p} : Set X), isClosed_closure⟩).blowupToBase).radical.subscheme ↘
      Spec (.of k)).smoothLocus}
  (A : Scheme.NodalCycleNumbering pC n) (i : ZMod n)
  (hi : (D.subscheme.singularLocus k).subschemeι (A.node i) = p)

local notation "oldNode" => A.node
local notation "oldBranch" => A.branch

private def numberedStrictNode (a : ZMod n) (b : Fin 2) : (J[B]).subscheme :=
  (B).branchSchemeToSingularLocus k ((strBranch) ((oldBranch) (a, b)))

local notation "nodeAt" => D.numberedStrictNode hc hp hCOver hBOver hD A

private theorem boundaryMap_numberedStrictNode (a : ZMod n) (b : Fin 2) :
    (β) ((J[B]).subschemeι ((nodeAt) a b)) = (J[C]).subschemeι ((oldNode) a) := by
  unfold numberedStrictNode
  rw [branchProjection_strict_apply, Scheme.NodalCycleNumbering.branchSchemeToSingularLocus_branch]

include hi in
private theorem numberedStrictNode_eq_of_ne (a : ZMod n) (ha : a ≠ i) (b : Fin 2) :
    (nodeAt) a b = (nodeAt) a 0 := by
  apply D.eq_node_of_boundaryMap_eq hc
  · rw [D.boundaryMap_numberedStrictNode, D.boundaryMap_numberedStrictNode]
  · rw [D.boundaryMap_numberedStrictNode]
    intro he
    exact ha ((oldNode).injective ((J[C]).subschemeι.injective (he.trans hi.symm)))

private def centerBranchAt (b : Fin 2) : centerBranch :=
  ⟨(oldBranch) (i, b), by rw [Scheme.NodalCycleNumbering.branchSchemeToSingularLocus_branch, hi]⟩

include hi in
private theorem numberedStrictNode_center_ne :
    (nodeAt) i 0 ≠ (nodeAt) i 1 := by
  let u := D.centerBranchAt A i hi 0
  let v := D.centerBranchAt A i hi 1
  intro heq
  have h := congrArg ((J[B]).subschemeι) heq
  simp only [numberedStrictNode, ← branch_projection,
    branchSchemeToBlowup_strictNormalizationBranch] at h
  have hu := D.blowupToBase_normalizationToNodalBlowup_branch hc hp hCOver hBOver hD u
  have hv := D.blowupToBase_normalizationToNodalBlowup_branch hc hp hCOver hBOver hD v
  have he : (attach) u = (attach) v := Subtype.ext (hu.symm.trans (h.trans hv))
  have h01 := congrArg Subtype.val ((attach).injective he)
  have hpair : (i, (0 : Fin 2)) = (i, 1) := (oldBranch).injective h01
  exact (by decide : (0 : Fin 2) ≠ 1) (congrArg Prod.snd hpair)

include hi in
private theorem numberedStrictNode_one_ne (a : ZMod n) :
    (nodeAt) a 0 ≠ (nodeAt) i 1 := by
  intro h
  have he := congrArg (fun t ↦ (β) ((J[B]).subschemeι t)) h
  simp only [D.boundaryMap_numberedStrictNode] at he
  have ha := (oldNode).injective ((J[C]).subschemeι.injective he)
  subst a
  exact D.numberedStrictNode_center_ne hc hp hCOver hBOver hD A i hi h

private theorem mem_range_numberedStrictNode (z : (J[B]).subscheme) :
    ∃ a b, (nodeAt) a b = z := by
  let q := ((B).branchOrderOfDualGraph (ι := Empty) Empty.elim (fun _ ↦ Equiv.refl _) z 0)
  obtain ⟨a | a, ha⟩ := (D.normalizationBranchEquiv hc hp hCOver hBOver hD).surjective q.val
  · obtain ⟨⟨a, b⟩, rfl⟩ := (oldBranch).surjective a
    exact ⟨a, b, by
      rw [numberedStrictNode, ← D.normalizationBranchEquiv_inl, ha, q.property]⟩
  · obtain ⟨⟨a', b⟩, h⟩ := (oldBranch).surjective a.val
    refine ⟨a', b, ?_⟩
    rw [numberedStrictNode, h, ← D.branchSchemeToSingularLocus_exceptionalSideBranch,
      ← D.normalizationBranchEquiv_inr, ha, q.property]

private def nodeEquivOption : Option (ZMod n) ≃ (J[B]).subscheme :=
  Equiv.ofBijective (fun v ↦ v.elim ((nodeAt) i 1) (fun a ↦ (nodeAt) a 0))
    ⟨by
      intro a b heq
      cases a with
      | none =>
        cases b with
        | none => rfl
        | some b =>
          exact (D.numberedStrictNode_one_ne hc hp hCOver hBOver hD A i hi b heq.symm).elim
      | some a =>
        cases b with
        | none => exact (D.numberedStrictNode_one_ne hc hp hCOver hBOver hD A i hi a heq).elim
        | some b =>
          have h : (nodeAt) a 0 = (nodeAt) b 0 := heq
          have he := congrArg (fun t ↦ (β) ((J[B]).subschemeι t)) h
          simp only [D.boundaryMap_numberedStrictNode] at he
          exact congrArg some ((oldNode).injective ((J[C]).subschemeι.injective he)),
      by
        intro z
        obtain ⟨a, b, rfl⟩ := D.mem_range_numberedStrictNode hc hp hCOver hBOver hD A z
        by_cases h : a = i
        · subst a
          fin_cases b
          · exact ⟨some i, rfl⟩
          · exact ⟨none, rfl⟩
        · exact ⟨some a, (D.numberedStrictNode_eq_of_ne hc hp hCOver hBOver hD A i hi a h b).symm⟩⟩

local notation "nodes" => D.nodeEquivOption hc hp hCOver hBOver hD A i hi
local notation "atCenter" => D.centerBranchAt A i hi
private def vertexEquivOption : Option (ZMod n) ≃ irreducibleComponents N[B] :=
  (A.component.trans (D.strictNormalizationComponentEquiv hc hp hCOver hBOver hD)).optionCongr.trans
    (Equiv.optionSubtypeNe (exc))

local notation "vertices" => D.vertexEquivOption hc hp hCOver hBOver hD A

private def orderedBranch (a : Option (ZMod n)) (b : Fin 2) :
    (B).branchScheme k := by
  classical
  exact a.elim
    (if b = 0 then (newBranch) ((atCenter) 1) else (strBranch) ((oldBranch) (i, 1)))
    (fun t ↦ if b = 0 then (strBranch) ((oldBranch) (t, 0))
      else if t = i then (newBranch) ((atCenter) 0) else (strBranch) ((oldBranch) (t, 1)))

local notation "ordered" => D.orderedBranch hc hp hCOver hBOver hD A i hi

private theorem nodes_none : (nodes) none = (nodeAt) i 1 := (rfl)

private theorem nodes_some (a : ZMod n) : (nodes) (some a) = (nodeAt) a 0 := (rfl)

private theorem orderedBranch_proj (a : Option (ZMod n)) (b : Fin 2) :
    (B).branchSchemeToSingularLocus k ((ordered) a b) = (nodes) a := by
  classical
  cases a with
  | none =>
    fin_cases b
    · simpa [orderedBranch, nodes_none, numberedStrictNode, centerBranchAt] using
        D.branchSchemeToSingularLocus_exceptionalSideBranch hc hp hCOver hBOver hD ((atCenter) 1)
    · simp [orderedBranch, nodes_none, numberedStrictNode]
  | some a =>
    fin_cases b
    · simp [orderedBranch, nodes_some, numberedStrictNode]
    · by_cases ha : a = i
      · subst a
        simpa [orderedBranch, nodes_some, numberedStrictNode, centerBranchAt] using
          D.branchSchemeToSingularLocus_exceptionalSideBranch hc hp hCOver hBOver hD ((atCenter) 0)
      · simpa [orderedBranch, ha, nodes_some, numberedStrictNode] using
          D.numberedStrictNode_eq_of_ne hc hp hCOver hBOver hD A i hi a ha 1

private theorem orderedBranch_injective (a : Option (ZMod n)) :
    Function.Injective ((ordered) a) := by
  classical
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have h : (ordered) a 0 ≠ (ordered) a 1 := by
    cases a with
    | none =>
      simpa only [orderedBranch, Option.elim_none, ite_true, ite_eq_right h10] using
        (D.branchSide_ne hc hp hCOver hBOver hD ((oldBranch) (i, 1)) ((atCenter) 1)).symm
    | some a =>
      by_cases ha : a = i
      · simpa only [orderedBranch, Option.elim_some, ite_true, ite_eq_right h10, ite_eq_left ha]
          using D.branchSide_ne hc hp hCOver hBOver hD ((oldBranch) (a, 0)) ((atCenter) 0)
      · have hn : (strBranch) ((oldBranch) (a, 0)) ≠ (strBranch) ((oldBranch) (a, 1)) := by
          intro heq
          have he := (oldBranch).injective
            (D.strictNormalizationBranch_injective hc hp hCOver hBOver hD heq)
          exact h10 (congrArg Prod.snd he.symm)
        simpa only [orderedBranch, Option.elim_some, ite_true, ite_eq_right h10, ite_eq_right ha]
          using hn
  intro a b hab
  fin_cases a <;> fin_cases b
  · rfl
  · exact (h hab).elim
  · exact (h hab.symm).elim
  · rfl

private def branchOrderAt (a : Option (ZMod n)) :
    Fin 2 ≃ {b : (B).branchScheme k // (B).branchSchemeToSingularLocus k b = (nodes) a} := by
  let u := (B).branchOrderOfDualGraph (ι := Empty) Empty.elim (fun _ ↦ Equiv.refl _) ((nodes) a)
  let v (b : Fin 2) : {b : (B).branchScheme k // (B).branchSchemeToSingularLocus k b = (nodes) a} :=
    ⟨(ordered) a b, D.orderedBranch_proj hc hp hCOver hBOver hD A i hi a b⟩
  have hv : Function.Injective v :=
    fun _ _ h ↦ D.orderedBranch_injective hc hp hCOver hBOver hD A i hi a (congrArg Subtype.val h)
  exact (Equiv.ofBijective (u.symm ∘ v) (u.symm.injective.comp hv).bijective_of_finite).trans u

private theorem branchOrderAt_val (a : Option (ZMod n)) (b : Fin 2) :
    (D.branchOrderAt hc hp hCOver hBOver hD A i hi a b).val = (ordered) a b := by
  simp [branchOrderAt]

-- Start immediately after the blown-up node. The extra index is the final one,
-- and the old node at the cut is followed by the extra attachment.
private def indexEquivOption (i : ZMod n) : ZMod (n + 1) ≃ Option (ZMod n) :=
  (ZMod.finEquiv (n + 1)).toEquiv.symm.trans ((finSuccEquiv' (Fin.last n)).trans
    (Equiv.optionCongr ((ZMod.finEquiv n).toEquiv.trans (Equiv.addRight (i + 1)))))

private theorem indexEquivOption_of_lt {a : ZMod (n + 1)} (h : a.val < n) :
    indexEquivOption i a = some ((a.val : ZMod n) + (i + 1)) := by
  cases n with
  | zero => omega
  | succ n =>
    have ha : (ZMod.finEquiv (n + 1 + 1)).symm a = Fin.castSucc ⟨a.val, h⟩ := Fin.ext rfl
    have hx : (ZMod.finEquiv (n + 1)) ⟨a.val, h⟩ = (a.val : ZMod (n + 1)) := by
      apply ZMod.val_injective _
      rw [ZMod.val_natCast_of_lt h]
      rfl
    have ha' : (ZMod.finEquiv (n + 1 + 1)).toEquiv.symm a = Fin.castSucc ⟨a.val, h⟩ := ha
    simp only [indexEquivOption, Equiv.trans_apply, ha', finSuccEquiv'_last_apply_castSucc,
      Equiv.optionCongr_apply, Option.map_some]
    exact congrArg (fun t : ZMod (n + 1) ↦ some (t + (i + 1))) hx

private theorem indexEquivOption_of_eq {a : ZMod (n + 1)} (h : a.val = n) :
    indexEquivOption i a = none := by
  have ha : (ZMod.finEquiv (n + 1)).symm a = Fin.last n := Fin.ext h
  simp [indexEquivOption, ha]

private theorem indexEquivOption_add_one (a : ZMod (n + 1)) :
    indexEquivOption i (a + 1) =
      (indexEquivOption i a).elim (some (i + 1))
        (fun t ↦ if t = i then none else some (t + 1)) := by
  have hpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne _)
  have ha := ZMod.val_lt a
  have hcast : a + 1 = ((a.val + 1 : ℕ) : ZMod (n + 1)) := by simp
  by_cases hlast : a.val = n
  · rw [hcast, hlast, ZMod.natCast_self, indexEquivOption_of_eq i hlast]
    rw [indexEquivOption_of_lt i (by simpa only [ZMod.val_zero] using hpos)]
    simp
  · rw [indexEquivOption_of_lt i (by omega : a.val < n)]
    simp only [Option.elim_some]
    rw [hcast]
    have hv : (((a.val + 1 : ℕ) : ZMod (n + 1))).val = a.val + 1 :=
      ZMod.val_natCast_of_lt (by omega)
    by_cases he : a.val + 1 = n
    · rw [indexEquivOption_of_eq i (hv.trans he)]
      have h : (a.val : ZMod n) + 1 = 0 := by
        calc
          _ = ((a.val + 1 : ℕ) : ZMod n) := by simp
          _ = 0 := by rw [he, ZMod.natCast_self]
      have hh : (a.val : ZMod n) + (i + 1) = i := by
        rw [← add_left_comm, h, add_zero]
      rw [hh, ite_eq_left rfl]
    · rw [indexEquivOption_of_lt i (by omega : (((a.val + 1 : ℕ) : ZMod (n + 1))).val < n),
        hv, Nat.cast_add, Nat.cast_one]
      have h : (a.val : ZMod n) + (i + 1) ≠ i := by
        intro heq
        have h0 : ((a.val + 1 : ℕ) : ZMod n) = 0 := by
          rw [Nat.cast_add, Nat.cast_one]
          exact add_left_cancel (by simpa only [add_left_comm, add_assoc, add_comm, add_zero]
            using heq : i + ((a.val : ZMod n) + 1) = i + 0)
        have hh := congrArg ZMod.val h0
        rw [ZMod.val_natCast_of_lt (by omega : a.val + 1 < n), ZMod.val_zero] at hh
        omega
      rw [ite_eq_right h]
      ac_rfl

private theorem strictBranch_mem_vertex (a : ZMod n) (b : Fin 2) :
    b[B] ((strBranch) ((oldBranch) (a, b))) ∈
      ((vertices) (some ((DualGraph.cycle n).endpoint a b)) : Set N[B]) := by
  rw [D.branchSchemeToBlowup_strictNormalizationBranch]
  simpa only [vertexEquivOption, Equiv.trans_apply, Equiv.optionCongr_apply, Option.map_some,
    Equiv.optionSubtypeNe_some] using
    D.normalizationToNodalBlowup_mem_strictNormalizationComponentEquiv hc hp hCOver hBOver hD _
      ((A.branchSchemeToBlowup_branch_mem_component_iff a b _).mpr rfl)

private theorem exceptionalBranch_mem_vertex (a : centerBranch) :
    b[B] ((newBranch) a) ∈ ((vertices) none : Set N[B]) := by
  rw [D.branchSchemeToBlowup_exceptionalSideBranch]
  simpa only [vertexEquivOption, Equiv.trans_apply, Equiv.optionCongr_apply, Option.map_none,
    Equiv.optionSubtypeNe_none, ← (B).coe_blowupComponent, SetLike.mem_coe] using
    ((excBranch) a).property.1

private theorem orderedBranch_mem_vertex (a : ZMod (n + 1)) (b : Fin 2) :
    b[B] ((ordered) (indexEquivOption i a) b) ∈
      ((vertices) (indexEquivOption i ((DualGraph.cycle (n + 1)).endpoint a b)) : Set N[B]) := by
  classical
  cases ha : indexEquivOption i a with
  | none =>
    fin_cases b
    · simpa [orderedBranch, ha, DualGraph.cycle] using
        D.exceptionalBranch_mem_vertex hc hp hCOver hBOver hD A ((atCenter) 1)
    · simpa [orderedBranch, ha, DualGraph.cycle, indexEquivOption_add_one] using
        D.strictBranch_mem_vertex hc hp hCOver hBOver hD A i 1
  | some t =>
    fin_cases b
    · simpa [orderedBranch, ha, DualGraph.cycle] using
        D.strictBranch_mem_vertex hc hp hCOver hBOver hD A t 0
    · by_cases ht : t = i
      · subst t
        simpa [orderedBranch, ha, DualGraph.cycle, indexEquivOption_add_one] using
          D.exceptionalBranch_mem_vertex hc hp hCOver hBOver hD A ((atCenter) 0)
      · simpa [orderedBranch, ha, ht, DualGraph.cycle, indexEquivOption_add_one] using
          D.strictBranch_mem_vertex hc hp hCOver hBOver hD A t 1

private def subdivisionOrder
    (pB : ι₁ → (B ↘ S).smoothLocus) (a : Option (ZMod n)) : Equiv.Perm (Fin 2) :=
  (D.branchOrderAt hc hp hCOver hBOver hD A i hi a).trans
    ((B).branchOrderOfDualGraph pB (fun _ ↦ Equiv.refl _) ((nodes) a)).symm

private theorem branchOrderOfDualGraph_subdivisionOrder_val
    (pB : ι₁ → (B ↘ S).smoothLocus) (a : Option (ZMod n)) (b : Fin 2) :
    ((B).branchOrderOfDualGraph pB
      (fun e ↦ D.subdivisionOrder hc hp hCOver hBOver hD A i hi pB
        ((nodes).symm ((B).dualGraphNodeEquiv pB e))) ((nodes) a) b).val =
      (ordered) a b := by
  let e := ((B).dualGraphNodeEquiv pB).symm ((nodes) a)
  have he : (B).dualGraphNodeEquiv pB e = (nodes) a := Equiv.apply_symm_apply _ _
  calc
    _ = (B).dualGraphBranchEquiv pB
        (e, D.subdivisionOrder hc hp hCOver hBOver hD A i hi pB a b) := by
      rw [← he, (B).branchOrderOfDualGraph_apply_val, he, Equiv.symm_apply_apply]
    _ = _ := by
      let u := (B).branchOrderOfDualGraph pB (fun _ ↦ Equiv.refl _) ((nodes) a)
      rw [← branchOrderAt_val,
        ← u.apply_symm_apply (D.branchOrderAt hc hp hCOver hBOver hD A i hi a b)]
      have h := (B).branchOrderOfDualGraph_apply_val pB (fun _ ↦ Equiv.refl _) e
        (D.subdivisionOrder hc hp hCOver hBOver hD A i hi pB a b)
      rw [he, Equiv.refl_apply] at h
      exact h.symm

private def subdivisionNumbering (pB : ι₁ → (B ↘ S).smoothLocus) :
    Scheme.NodalCycleNumbering pB (n + 1) where
  vertex := (indexEquivOption i).trans ((vertices).trans ((B).dualGraphVertexEquiv pB).symm)
  edge := (indexEquivOption i).trans ((nodes).trans ((B).dualGraphNodeEquiv pB).symm)
  order e := D.subdivisionOrder hc hp hCOver hBOver hD A i hi pB
    ((nodes).symm ((B).dualGraphNodeEquiv pB e))
  endpoint_eq a b := by
    apply ((B).dualGraphVertexEquiv pB).injective
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
    apply ((B).dualGraphVertexEquiv_endpoint_eq_iff pB _ _ _).mpr
    rw [← (B).branchSchemeToBlowup_dualGraphBranchEquiv]
    have h := D.branchOrderOfDualGraph_subdivisionOrder_val hc hp hCOver hBOver hD A i hi
      pB (indexEquivOption i a) b
    rw [← ((B).dualGraphNodeEquiv pB).apply_symm_apply ((nodes) (indexEquivOption i a)),
      (B).branchOrderOfDualGraph_apply_val] at h
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply] at h
    rw [h]
    exact D.orderedBranch_mem_vertex hc hp hCOver hBOver hD A i hi a b

private theorem orderedBranch_apply_lift (g : N[B] ⟶ N[C])
    (hg : ∀ a : (C).branchScheme k, g (b[B] ((strBranch) a)) = b[C] a)
    (he : ∀ a : centerBranch, g (b[B] ((newBranch) a)) = b[C] ((atCenter) 1).val)
    (a : ZMod n) (b : Fin 2) :
    g (b[B] ((ordered) (some a) b)) = b[C] ((oldBranch) (a, b)) := by
  classical
  fin_cases b
  · simpa [orderedBranch] using hg ((oldBranch) (a, 0))
  · by_cases h : a = i
    · subst a
      simpa [orderedBranch, centerBranchAt] using he ((atCenter) 0)
    · simpa [orderedBranch, h] using hg ((oldBranch) (a, 1))

include hi in
private theorem isOrientedCycleSubdivision_subdivisionNumbering
    (pB : ι₁ → (B ↘ S).smoothLocus) :
    (β).IsOrientedCycleSubdivision (D.subdivisionNumbering hc hp hCOver hBOver hD A i hi pB) A := by
  -- Choosing the second old branch as the image of the exceptional component
  -- retains the first attachment and collapses the ordered pair at the second.
  obtain ⟨g, hg, hstr, hexc⟩ := D.exists_nodalBlowupNormalizationLift hc hp hCOver hBOver hD
    ((atCenter) 1)
  let keep : (J[C]).subscheme ↪ (J[B]).subscheme :=
    ⟨fun z ↦ (nodes) (some ((oldNode).symm z)),
      (nodes).injective.comp (Option.some_injective _ |>.comp (oldNode).symm.injective)⟩
  have hord (a b) :
      ((B).branchOrderOfDualGraph pB
        (D.subdivisionNumbering hc hp hCOver hBOver hD A i hi pB).order ((nodes) a) b).val =
        (ordered) a b :=
    D.branchOrderOfDualGraph_subdivisionOrder_val hc hp hCOver hBOver hD A i hi pB a b
  refine ⟨g, hg, D.mapsTo_support_singularLocus_nodalBlowup nodal[C] hc hCOver hBOver hp nodal[B],
    keep, ?_, ?_⟩
  · intro z b
    obtain ⟨a, rfl⟩ := (oldNode).surjective z
    have hk : keep ((oldNode) a) = (nodes) (some a) := by simp [keep]
    rw [hk, hord, ← A.branch_eq_branchOrderOfDualGraph]
    exact D.orderedBranch_apply_lift hc hp hCOver hBOver hD A i hi g hstr hexc a b
  · intro z hz
    obtain ⟨a, rfl⟩ := (nodes).surjective z
    cases a with
    | some a => exact (hz ⟨(oldNode) a, by simp [keep]⟩).elim
    | none =>
      rw [hord, hord]
      have h10 : (1 : Fin 2) ≠ 0 := by decide
      simp only [orderedBranch, Option.elim_none, ite_eq_right h10, ite_true]
      exact (hstr ((oldBranch) (i, 1))).trans (hexc ((atCenter) 1)).symm

private theorem normalizationToNodalBlowup_genericPoint (v : irreducibleComponents N[C]) :
    (s) (genericPoints.ofComponent v) =
      genericPoints.ofComponent
        (D.strictNormalizationComponentEquiv hc hp hCOver hBOver hD v).val := by
  have : IsRegular N[C] := (C).isRegular_blowup_singularLocus nodal[C]
  have : IsRegular N[B] := (B).isRegular_blowup_singularLocus nodal[B]
  let e := D.strictNormalizationComponentEquiv hc hp hCOver hBOver hD
  let y := genericPoints.ofComponent (e v).val
  have hy : (y : N[B]) ∈ ((e v).val : Set N[B]) :=
    (genericPoints.isGenericPoint_ofComponent (e v).val).mem
  have hy' : (y : N[B]) ∈ Set.range (s) := by
    rw [D.range_normalizationToNodalBlowup hc hp hCOver hBOver hD]
    intro h
    exact (e v).property ((irreducibleComponentOf_eq_iff.mpr hy).symm.trans
      (irreducibleComponentOf_eq_iff.mpr h))
  obtain ⟨x, hx⟩ := hy'
  let w := irreducibleComponentOf x
  have hw := D.normalizationToNodalBlowup_mem_strictNormalizationComponentEquiv
    hc hp hCOver hBOver hD w (mem_irreducibleComponentOf x)
  rw [hx] at hw
  have hwv : w = v := e.injective (Subtype.ext
    ((irreducibleComponentOf_eq_iff.mpr hw).symm.trans (irreducibleComponentOf_eq_iff.mpr hy)))
  have hxv : x ∈ (v : Set N[C]) := hwv ▸ mem_irreducibleComponentOf x
  exact (TauCeti.mem_genericPoints_iff.mp y.property) _
    (hx ▸ ((genericPoints.isGenericPoint_ofComponent v).specializes hxv).map (s).continuous)

include hi in
private theorem ambient_subdivisionNumbering_component (pB : ι₁ → (B ↘ S).smoothLocus)
    (a : ZMod (n + 1)) :
    (π) ((j) ((D.subdivisionNumbering hc hp hCOver hBOver hD A i hi pB).componentGenericPoint a)) =
      if a.val < n then D.subschemeι (A.componentGenericPoint ((a.val : ZMod n) + (i + 1)))
      else D.subschemeι p := by
  let T := D.subdivisionNumbering hc hp hCOver hBOver hD A i hi pB
  have hT : T.component a = (vertices) (indexEquivOption i a) := by
    simp [T, Scheme.NodalCycleNumbering.component_apply, subdivisionNumbering]
  have hπ (x : B) : (π) ((j) x) = D.subschemeι ((β) x) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, subschemeMap_subschemeι]
  rw [hπ, Scheme.NodalCycleNumbering.componentGenericPoint_def, hT]
  split_ifs with ha
  · rw [indexEquivOption_of_lt i ha]
    let b : ZMod n := (a.val : ZMod n) + (i + 1)
    have hv : (vertices) (some b) =
        (D.strictNormalizationComponentEquiv hc hp hCOver hBOver hD (A.component b)).val := by
      simp [vertexEquivOption]
    rw [hv, ← D.normalizationToNodalBlowup_genericPoint hc hp hCOver hBOver hD,
      boundaryMap_normalizationToNodalBlowup_apply hc hp hCOver hBOver,
      Scheme.NodalCycleNumbering.componentGenericPoint_def]
  · rw [indexEquivOption_of_eq i (by have := ZMod.val_lt a; omega)]
    have hv : (vertices) none = (exc) := by simp [vertexEquivOption]
    rw [hv]
    apply congrArg D.subschemeι
    apply (IsEffectiveCartier.mem_exceptional_iff_boundaryMap_eq hc _).mp
    apply (hD.bijOn_blowupToBase_exceptionalNormalizationComponent (k := k) hc).mapsTo
    rw [(B).coe_blowupComponent]
    exact (genericPoints.isGenericPoint_ofComponent (exc)).mem

omit [IsReduced C] in
include hc hp hCOver hBOver hD hi in
/-- At the specified node, the reduced total boundary has the induced oriented
numbering starting just after that node and ending at the exceptional component.
The surface projection sends each numbered generic point to the corresponding
original prime, or to the center for the last component. -/
theorem exists_isOrientedCycleSubdivision_nodalBlowup_at
    (pB : ι₁ → (B ↘ S).smoothLocus) :
    ∃ T : Scheme.NodalCycleNumbering pB (n + 1),
      (β).IsOrientedCycleSubdivision T A ∧
      ∀ a, (π) ((j) (T.componentGenericPoint a)) =
        if a.val < n then D.subschemeι (A.componentGenericPoint ((a.val : ZMod n) + (i + 1)))
        else D.subschemeι p := by
  have : IsReduced C := (nodal[C]).isReduced
  exact ⟨_, D.isOrientedCycleSubdivision_subdivisionNumbering hc hp hCOver hBOver hD A i hi pB,
    D.ambient_subdivisionNumbering_component hc hp hCOver hBOver hD A i hi pB⟩

omit [IsReduced C] in
include hc hp hCOver hBOver hD in
/-- Blowing up a node of a numbered cycle inserts one normalized component and splits
the node into two attachments. The numbering of the longer cycle inherits the old
orientation, and the boundary projection is an oriented conductor subdivision. -/
theorem exists_isOrientedCycleSubdivision_nodalBlowup
    (pB : ι₁ → (B ↘ S).smoothLocus) :
    ∃ T : Scheme.NodalCycleNumbering pB (n + 1), (β).IsOrientedCycleSubdivision T A := by
  have : IsReduced C := (nodal[C]).isReduced
  obtain ⟨z, hz⟩ := (J[C]).range_subschemeι.ge hp
  obtain ⟨i, rfl⟩ := (oldNode).surjective z
  obtain ⟨T, hT, -⟩ :=
    D.exists_isOrientedCycleSubdivision_nodalBlowup_at hc hp hCOver hBOver hD A i hz pB
  exact ⟨T, hT⟩

end Numbering

end AlgebraicGeometry.Scheme.IdealSheafData
