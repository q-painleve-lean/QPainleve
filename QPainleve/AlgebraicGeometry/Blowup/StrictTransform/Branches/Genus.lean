/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Branches.Subdivision
public import TauCeti.AlgebraicGeometry.Curves.Node.Reduced

import QPainleve.AlgebraicGeometry.Blowup.Point.Basic
import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Lift
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveLine.Basic
import TauCeti.AlgebraicGeometry.IdealSheaf.Section

/-!
# Genera of the normalized components after a nodal blowup

Blowing up a node retains the original normalized components and inserts a
projective line. In particular the reduced total boundary still has genus-zero
normalization components if the original boundary did. The components are the
ones identified by `strictNormalizationComponentEquiv` and
`IsEffectiveCartier.exceptionalNormalizationComponent`.
-/

public noncomputable section

open CategoryTheory TopologicalSpace TauCeti TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsIntegral X] [QuasiCompact (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  {D : X.IdealSheafData} [D.subscheme.Over (Spec (.of k))]
  [PrestableFamily (D.subscheme ↘ Spec (.of k))]
  (hD : D.IsEffectiveCartier) {p : D.subscheme} (hc : IsClosed ({D.subschemeι p} : Set X))

local notation "S" => Spec (CommRingCat.of k)
local notation "C" => IdealSheafData.subscheme D
local notation "I" =>
  vanishingIdeal (Closeds.mk (closure ({D.subschemeι p} : Set X)) isClosed_closure)
local notation "π" => blowupToBase (I)
local notation "R" => radical (D.comap (π))
local notation "B" => IdealSheafData.subscheme (R)
local notation "E" => comap (I) (π)
local notation "N[" k "," T "]" => blowup (Scheme.singularLocus k T)
local notation "ν[" k "," T "]" => blowupToBase (Scheme.singularLocus k T)
local notation "β" => subschemeMap (R) D (π) (le_map_iff_comap_le.mpr (le_radical _))

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
local notation "exc" => hD.exceptionalNormalizationComponent (k := k) hc
local notation "strict" => D.strictNormalizationComponentEquiv hc hp hCOver hBOver hD

omit [IsIntegral X] [QuasiCompact (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))] in
include hc hp hCOver hBOver in
private theorem isClosedImmersion_normalizationToNodalBlowup : IsClosedImmersion (s) := by
  let : (β).IsOver S :=
    ⟨by rw [hCOver, ← Category.assoc, subschemeMap_subschemeι, Category.assoc, hBOver]⟩
  obtain ⟨g, hg⟩ := (β).exists_nodal_normalization_lift (k := k)
  have hg' : g ≫ ν[k,C] = ν[k,B] ≫ (β) := hg.w.symm
  have : IsFinite ν[k,B] := (B).isFinite_blowupToBase_singularLocus
    PrestableFamily.atWorstNodalOfRelativeDimensionOne
  have : IsSeparated (g ≫ ν[k,C] ≫ C ↘ S) := by
    rw [reassoc_of% hg', comp_over]
    infer_instance
  have : IsSeparated g := .of_comp g (ν[k,C] ≫ C ↘ S)
  have hs : (s) ≫ g = 𝟙 _ := D.normalizationToNodalBlowup_comp_lift hc hp hCOver hBOver hg'
  exact Scheme.Hom.isClosedImmersion_of_comp_eq_id (s) hs

private theorem surjOn_normalizationToNodalBlowup_strictComponent [IsReduced C]
    (v : irreducibleComponents N[k,C]) :
    Set.SurjOn (s) (v : Set N[k,C]) (((strict) v).val : Set N[k,B]) := by
  intro y hy
  have hdis := (B).pairwise_disjoint_blowupComponent (k := k) ((strict) v).property
  have hd : Disjoint ((B).blowupComponent ((strict) v).val : Set N[k,B])
      ((B).blowupComponent (exc) : Set N[k,B]) :=
    TopologicalSpace.Opens.coe_disjoint.mpr hdis
  simp only [(B).coe_blowupComponent] at hd
  obtain ⟨z, hz⟩ :=
    (D.range_normalizationToNodalBlowup hc hp hCOver hBOver hD).ge (Set.disjoint_left.mp hd hy)
  let w := irreducibleComponentOf z
  have hmem := D.normalizationToNodalBlowup_mem_strictNormalizationComponentEquiv
    hc hp hCOver hBOver hD w (mem_irreducibleComponentOf z)
  rw [hz] at hmem
  have : IsRegular N[k,B] :=
    (B).isRegular_blowup_singularLocus PrestableFamily.atWorstNodalOfRelativeDimensionOne
  have hw : w = v := (strict).injective (Subtype.ext
    ((irreducibleComponentOf_eq_iff.mpr hmem).symm.trans (irreducibleComponentOf_eq_iff.mpr hy)))
  exact ⟨z, hw ▸ mem_irreducibleComponentOf z, hz⟩

namespace IsEffectiveCartier

/-- Each strict normalized component of a nodal blowup is isomorphic over the
ground field to its original normalized component, by restriction of the
canonical map between the two normalizations. -/
theorem exists_iso_strictNormalizationComponent (v : irreducibleComponents N[k,C]) :
    let : IsReduced C :=
      (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := C ↘ S)).isReduced
    let U := (C).blowupComponent v
    let V := (B).blowupComponent ((strict) v).val
    ∃ e : U.toScheme ≅ V.toScheme, e.hom.IsOver S ∧ e.hom ≫ V.ι = U.ι ≫ (s) := by
  intro _ U V
  have : IsClosedImmersion (s) := isClosedImmersion_normalizationToNodalBlowup hc hp hCOver hBOver
  have hr : Set.range (U.ι ≫ (s)) ⊆ Set.range V.ι := by
    rintro y ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply, (B).coe_blowupComponent]
    apply D.normalizationToNodalBlowup_mem_strictNormalizationComponentEquiv hc hp hCOver hBOver hD
    have hx := Set.mem_range_self (f := U.ι) x
    rwa [Scheme.Opens.range_ι, (C).coe_blowupComponent] at hx
  let f := IsOpenImmersion.lift V.ι (U.ι ≫ (s)) hr
  have hf : f ≫ V.ι = U.ι ≫ (s) := IsOpenImmersion.lift_fac _ _ _
  have : IsClosedImmersion U.ι := .of_isPreimmersion _
    (by rw [Scheme.Opens.range_ι, (C).coe_blowupComponent]; exact
      isClosed_of_mem_irreducibleComponents _ v.property)
  have : IsClosedImmersion (f ≫ V.ι) := hf.symm ▸ inferInstance
  have : IsClosedImmersion f := .of_comp f V.ι
  have : Surjective f := by
    constructor
    intro y
    have hy := Set.mem_range_self (f := V.ι) y
    rw [Scheme.Opens.range_ι, (B).coe_blowupComponent] at hy
    obtain ⟨z, hz, hzy⟩ :=
      surjOn_normalizationToNodalBlowup_strictComponent hD hc hp hCOver hBOver v hy
    have hz' : z ∈ (U : Set N[k,C]) := by rwa [(C).coe_blowupComponent]
    have hpoint := congrArg (fun t : U.toScheme ⟶ N[k,B] ↦ t ⟨z, hz'⟩) hf
    exact ⟨⟨z, hz'⟩, V.ι.injective (hpoint.trans hzy)⟩
  have := isIso_of_isClosedImmersion_of_surjective f
  refine ⟨asIso f, ⟨?_⟩, hf⟩
  have hβ : (β) ≫ C ↘ S = B ↘ S := by
    rw [hCOver, ← Category.assoc, subschemeMap_subschemeι, Category.assoc, hBOver]
  calc
    f ≫ V.toScheme ↘ S = U.ι ≫ (s) ≫ ν[k,B] ≫ B ↘ S := by
      rw [(B).blowupComponent_over, ← Category.assoc, hf, Category.assoc]
    _ = U.ι ≫ (s) ≫ ν[k,B] ≫ (β) ≫ C ↘ S :=
      congrArg (fun g ↦ U.ι ≫ (s) ≫ ν[k,B] ≫ g) hβ.symm
    _ = U.toScheme ↘ S := by
      rw [reassoc_of% D.normalizationToNodalBlowup_blowupToBase_boundaryMap hc hp hCOver hBOver]
      exact ((C).blowupComponent_over v).symm

include hD hc hp hCOver hBOver in
/-- The reduced total boundary after a nodal point blowup has genus-zero
normalized components if the original boundary does. -/
theorem genus_blowupComponent_radical_comap_eq_zero
    (hgenus : ∀ v : irreducibleComponents N[k,C], ((C).blowupComponent v).toScheme.genus k = 0)
    (w : irreducibleComponents N[k,B]) : ((B).blowupComponent w).toScheme.genus k = 0 := by
  classical
  have : IsReduced C :=
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := C ↘ S)).isReduced
  by_cases hw : w = (exc)
  · subst w
    let t := hD.exceptionalNormalizationIso (k := k) hc
    have hI : vanishingIdeal ⟨{D.subschemeι p}, hc⟩ = (I) :=
      congrArg vanishingIdeal (SetLike.coe_injective hc.closure_eq.symm)
    have hex := SmoothOfRelativeDimension.exists_iso_projectiveLine_exceptional_blowup_closedPoint
      (X ↘ S) (D.subschemeι p) hc
    dsimp only at hex
    rw [hI] at hex
    obtain ⟨e, he⟩ := hex
    let q := t ≪≫ e.symm
    have hq : q.inv ≫ (((B).blowupComponent (exc)).toScheme ↘ S) =
        projectiveLine k ↘ S := by
      let V := (B).blowupComponent (exc)
      rw [(B).blowupComponent_over]
      calc
        _ = q.inv ≫ V.ι ≫ ν[k,B] ≫ (R).subschemeι ≫ (π) ≫ X ↘ S :=
          congrArg (fun g ↦ q.inv ≫ V.ι ≫ ν[k,B] ≫ g) hBOver
        _ = e.hom ≫ (E).subschemeι ≫ (π) ≫ X ↘ S := by
          rw [← hD.exceptionalNormalizationIso_hom_subschemeι_assoc hc]
          simp only [q, Iso.trans_inv, Iso.symm_inv, Category.assoc, Iso.inv_hom_id_assoc, t]
        _ = projectiveLine k ↘ S := by
          rw [reassoc_of% he.w, pointOfClosedPoint_comp, Category.comp_id]
    let : q.inv.IsOver S := ⟨hq⟩
    rw [Scheme.genus_def, ← q.inv.finrank_cohomology_trivial_of_isIso k 1]
    simpa only [Scheme.genus_def] using projectiveLine.genus_eq_zero k
  · obtain ⟨v, hv⟩ := (strict).surjective ⟨w, hw⟩
    obtain ⟨e, hover, -⟩ := exists_iso_strictNormalizationComponent hD hc hp hCOver hBOver v
    have he : e.hom.IsOver S := hover
    have h := hgenus v
    rw [Scheme.genus_def, e.hom.finrank_cohomology_trivial_of_isIso k 1, ← Scheme.genus_def] at h
    have hv' : ((strict) v).val = w := congrArg Subtype.val hv
    exact (congrArg (fun z ↦ ((B).blowupComponent z).toScheme.genus k) hv').symm.trans h

end IsEffectiveCartier

end AlgebraicGeometry.Scheme.IdealSheafData
