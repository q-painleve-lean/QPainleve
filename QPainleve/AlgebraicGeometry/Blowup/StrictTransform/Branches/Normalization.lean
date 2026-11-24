/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Branches.Attachments
public import TauCeti.AlgebraicGeometry.Curves.Prestable

import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Lift
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal

/-!
# Normalized strict branches under a nodal blowup

The normalization of the original boundary maps to the strict part of the
normalized reduced total boundary. This map is a section of every lift of
the blowdown to the normalizations. Over the blown-up node it identifies
each original branch with the strict branch at its attachment node, the
geometric comparison used in transporting the gluing periods of
[Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S2
-/

public noncomputable section

open CategoryTheory TopologicalSpace TauCeti TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {k : Type u} [Field k] {X : Scheme.{u}} {D : X.IdealSheafData}
  [D.subscheme.Over (Spec (.of k))]
  [PrestableFamily (D.subscheme ↘ Spec (.of k))]
  {p : D.subscheme} (hc : IsClosed ({D.subschemeι p} : Set X))
  (hp : p ∈ (D.subscheme.singularLocus k).support)

local notation "C" => IdealSheafData.subscheme D
local notation "I" =>
  vanishingIdeal (Closeds.mk (closure (singleton (D.subschemeι p))) isClosed_closure)
local notation "R" => radical (D.comap (blowupToBase I))
local notation "B" => subscheme R
local notation "π" => blowupToBase I
local notation "j" => subschemeι R
local notation "N[" A "]" => blowup (Scheme.singularLocus k A)
local notation "ν[" A "]" => blowupToBase (Scheme.singularLocus k A)
local notation "nodal[" A "]" =>
  PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := A ↘ Spec (CommRingCat.of k))
local notation "boundaryMap" => subschemeMap R D (π) (le_map_iff_comap_le.mpr (le_radical _))
local notation "a" =>
  normalizationToStrictTransform D.subschemeι nodal[C] hp ≫ blowupMap I D.subschemeι

private theorem strictNormalization_comp_blowupToBase : (a) ≫ (π) = ν[C] ≫ D.subschemeι := by
  rw [Category.assoc, blowupMap_blowupToBase, ← Category.assoc,
    normalizationToStrictTransform_blowupToBase]

private theorem reducedTotal_le_ker_strictNormalization : (R) ≤ (a).ker := by
  have : IsRegular N[C] := (C).isRegular_blowup_singularLocus nodal[C]
  rw [← vanishingIdeal_support]
  apply vanishingIdeal_le_ker_of_range_subset
  rintro _ ⟨x, rfl⟩
  rw [support_comap, Closeds.coe_preimage,
    Set.mem_preimage, ← Hom.comp_apply, strictNormalization_comp_blowupToBase hp,
    Hom.comp_apply, ← D.range_subschemeι]
  exact Set.mem_range_self _

private def strictNormalizationToBoundary : N[C] ⟶ B :=
  IsClosedImmersion.lift (j) (a) (by
    rw [ker_subschemeι]
    exact reducedTotal_le_ker_strictNormalization hp)

@[reassoc]
private theorem strictNormalizationToBoundary_subschemeι :
    strictNormalizationToBoundary hp ≫ (j) = (a) :=
  IsClosedImmersion.lift_fac _ _ _

@[reassoc]
private theorem strictNormalizationToBoundary_boundaryMap :
    strictNormalizationToBoundary hp ≫ (boundaryMap) = ν[C] := by
  apply (cancel_mono D.subschemeι).mp
  rw [Category.assoc, subschemeMap_subschemeι,
    strictNormalizationToBoundary_subschemeι_assoc, ← Category.assoc,
    strictNormalization_comp_blowupToBase]

variable [X.Over (Spec (.of k))]
  [(D.comap (vanishingIdeal
    ⟨closure ({D.subschemeι p} : Set X), isClosed_closure⟩).blowupToBase).radical.subscheme.Over
      (Spec (.of k))]
  [hB : PrestableFamily
    ((D.comap (vanishingIdeal
      ⟨closure ({D.subschemeι p} : Set X), isClosed_closure⟩).blowupToBase).radical.subscheme ↘
        Spec (.of k))]
  (hCOver : D.subscheme ↘ Spec (.of k) = D.subschemeι ≫ (X ↘ Spec (.of k)))
  (hBOver :
    (D.comap (vanishingIdeal
      ⟨closure ({D.subschemeι p} : Set X), isClosed_closure⟩).blowupToBase).radical.subscheme ↘
        Spec (.of k) =
      (D.comap (vanishingIdeal
        ⟨closure ({D.subschemeι p} : Set X), isClosed_closure⟩).blowupToBase).radical.subschemeι ≫
        (vanishingIdeal ⟨closure ({D.subschemeι p} : Set X), isClosed_closure⟩).blowupToBase ≫
        X ↘ Spec (.of k))

include hc hCOver hBOver hB in
private theorem existsUnique_normalizationToNodalBlowup :
    ∃! s : N[C] ⟶ N[B], s ≫ ν[B] = strictNormalizationToBoundary hp := by
  apply Scheme.Hom.existsUnique_lift_to_nodal_normalization (k := k) (X := C) (Y := B)
  intro v
  let U := (C).blowupComponent (K := k) v
  let y := genericPoints.ofComponent v
  have hy : (y : N[C]) ∈ U := by
    rw [← SetLike.mem_coe, (C).coe_blowupComponent]
    exact (genericPoints.isGenericPoint_ofComponent v).mem
  let x : U := ⟨y, hy⟩
  refine ⟨x, ?_⟩
  have hmap := D.mapsTo_support_singularLocus_nodalBlowup nodal[C] hc hCOver hBOver hp nodal[B]
  by_contra hsmooth
  have hsing := ((B).mem_support_singularLocus_iff_notMem_smoothLocus _).mpr hsmooth
  have hpoint :
      (U.ι ≫ strictNormalizationToBoundary hp) x =
        strictNormalizationToBoundary hp (y : N[C]) :=
    (Scheme.Hom.comp_apply U.ι (strictNormalizationToBoundary hp) x).trans
      (congrArg (fun t : N[C] ↦ strictNormalizationToBoundary hp t) (Scheme.Opens.ι_apply U x))
  have h : (strictNormalizationToBoundary hp ≫ (boundaryMap)) (y : N[C]) ∈
      ((C).singularLocus k).support := by
    exact (Scheme.Hom.comp_apply (strictNormalizationToBoundary hp) (boundaryMap)
      (y : N[C])).symm ▸ hmap (hpoint ▸ hsing)
  rw [strictNormalizationToBoundary_boundaryMap] at h
  exact ((C).mem_support_singularLocus_iff_notMem_smoothLocus _).mp h
    ((C).blowupComponentGeneric_mem_smoothLocus v)

variable (D)

/-- The old normalization lifts to the normalization of the reduced total
boundary via the strict transform. -/
def normalizationToNodalBlowup : N[C] ⟶ N[B] :=
  (existsUnique_normalizationToNodalBlowup hc hp hCOver hBOver).exists.choose

/-- The lift from the old normalization lands in the strict transform in the
ambient blowup. -/
@[reassoc]
theorem normalizationToNodalBlowup_blowupToBase_subschemeι :
    D.normalizationToNodalBlowup hc hp hCOver hBOver ≫ ν[B] ≫ (j) = (a) := by
  rw [← Category.assoc, normalizationToNodalBlowup,
    (existsUnique_normalizationToNodalBlowup hc hp hCOver hBOver).exists.choose_spec,
    strictNormalizationToBoundary_subschemeι]

/-- The projection to the strict transform in the ambient blowup determines the lift. -/
theorem eq_normalizationToNodalBlowup_of_blowupToBase_subschemeι (s : N[C] ⟶ N[B])
    (hs : s ≫ ν[B] ≫ (j) = (a)) :
    s = D.normalizationToNodalBlowup hc hp hCOver hBOver := by
  have h : s ≫ ν[B] = strictNormalizationToBoundary hp := by
    apply (cancel_mono (j)).mp
    rw [Category.assoc, hs, strictNormalizationToBoundary_subschemeι]
  let hex := existsUnique_normalizationToNodalBlowup hc hp hCOver hBOver
  exact hex.unique h hex.exists.choose_spec

/-- The strict lift followed by the original boundary projection is the old normalization map. -/
@[reassoc (attr := simp)]
theorem normalizationToNodalBlowup_blowupToBase_boundaryMap :
    D.normalizationToNodalBlowup hc hp hCOver hBOver ≫ ν[B] ≫ (boundaryMap) = ν[C] := by
  rw [← Category.assoc, normalizationToNodalBlowup,
    (existsUnique_normalizationToNodalBlowup hc hp hCOver hBOver).exists.choose_spec,
    strictNormalizationToBoundary_boundaryMap]

/-- A lift of the boundary blowdown to the normalizations restricts to the
identity on the original normalization. -/
@[reassoc (attr := simp)]
theorem normalizationToNodalBlowup_comp_lift {g : N[B] ⟶ N[C]}
    (hg : g ≫ ν[C] = ν[B] ≫ (boundaryMap)) :
    D.normalizationToNodalBlowup hc hp hCOver hBOver ≫ g = 𝟙 _ := by
  have h : (D.normalizationToNodalBlowup hc hp hCOver hBOver ≫ g) ≫ ν[C] = ν[C] := by
    rw [Category.assoc, hg, normalizationToNodalBlowup_blowupToBase_boundaryMap]
  apply ((C).singularLocus k).blowup_hom_ext (h.trans (Category.id_comp _).symm)
  rw [h]
  exact ((C).singularLocus k).isEffectiveCartier_comap_blowupToBase

variable [PerfectField k] [IsIntegral X] [QuasiCompact (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))] (hD : D.IsEffectiveCartier)

/-- Each original branch at the blown-up node lifts to a normalized point over
its own attachment node. This identifies the strict branches separately even
when the original node is a self-node. -/
theorem blowupToBase_normalizationToNodalBlowup_branch
    (q : {q : (C).branchScheme k |
      ((C).singularLocus k).subschemeι ((C).branchSchemeToSingularLocus k q) = p}) :
    ν[B] (D.normalizationToNodalBlowup hc hp hCOver hBOver ((C).branchSchemeToBlowup k q.val)) =
      (hD.branchEquivSingularFiber nodal[C] hc hCOver hBOver hp nodal[B] q).val := by
  apply (j).injective
  rw [← Hom.comp_apply, ← Hom.comp_apply,
    normalizationToNodalBlowup_blowupToBase_subschemeι,
    hD.subschemeι_branchEquivSingularFiber nodal[C] hc hCOver hBOver hp nodal[B],
    strictTransformBranchMap, Hom.comp_apply, Hom.comp_apply]

end AlgebraicGeometry.Scheme.IdealSheafData
