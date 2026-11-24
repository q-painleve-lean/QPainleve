/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Branches.Genus
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Boundary

import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced
import TauCeti.AlgebraicGeometry.Noetherian

/-!
# Genus-zero boundary components in nodal blowup towers

The normalization of the reduced total boundary of a nodal blowup tower has
genus-zero components if the original boundary does. This permits using the
boundary period character at every stage.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower.IsNodalBoundaryTower

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [IsIntegral X] [QuasiCompact (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ Spec (.of k))]
  {n : ℕ} {T : BlowupTower X n Y}

local notation "S" => Spec (CommRingCat.of k)
local notation "R[" D "," T "]" => radical (comap D (BlowupTower.toBase T))

/-- The normalized components of the reduced total boundary of a nodal blowup
tower over an algebraically closed field all have genus zero when the normalized
components of the original boundary do. -/
theorem genus_blowupComponent_radical_comap_toBase_eq_zero
    (hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T)
    (hD : D.IsEffectiveCartier)
    (hgenus : ∀ v : irreducibleComponents (D.subscheme.singularLocus k).blowup,
      (D.subscheme.blowupComponent v).toScheme.genus k = 0) :
    letI : Y.Over S := ⟨T.toBase ≫ X ↘ S⟩
    ∀ [PrestableFamily ((R[D,T]).subscheme ↘ S)]
      (v : irreducibleComponents ((R[D,T]).subscheme.singularLocus k).blowup),
      ((R[D,T]).subscheme.blowupComponent v).toScheme.genus k = 0 := by
  have hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S) := by
    rw [← D.over_eq_subschemeι_comp]
    exact PrestableFamily.atWorstNodalOfRelativeDimensionOne
  have : IsReduced D.subscheme := hN.isReduced
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  induction hT with
  | nil =>
    rw [toBase_nil, comap_id, Category.id_comp,
      D.isReduced_subscheme_iff_radical_eq.mp ‹IsReduced D.subscheme›]
    exact fun _ ↦ hgenus
  | @snoc m Z U I hU x hx hI hnode ih =>
    let : Z.Over S := ⟨U.toBase ≫ X ↘ S⟩
    have := hU.isClosedPointTower.isIntegral (X ↘ S)
    have : SmoothOfRelativeDimension 2 (Z ↘ S) :=
      hU.isClosedPointTower.smoothOfRelativeDimension (X ↘ S)
    have : IsProper U.toBase := U.isProper_toBase
    have : QuasiCompact (Z ↘ S) := inferInstanceAs (QuasiCompact (U.toBase ≫ X ↘ S))
    have : PrestableFamily ((R[D,U]).subscheme ↘ S) := prestableFamily_radical_comap_toBase hU hD
    have : IsReduced ((R[D,U]).subscheme) :=
      (PrestableFamily.atWorstNodalOfRelativeDimensionOne
        (f := (R[D,U]).subscheme ↘ S)).isReduced
    have hnode' : (R[D,U]).IsNodeOfReducedBoundary (U.toBase ≫ X ↘ S) x := by
      simpa only [isNodeOfReducedBoundary_radical, Category.comp_id] using hnode
    obtain ⟨z, hz, hn⟩ :=
      ((R[D,U]).isNodeOfReducedBoundary_iff_of_isReduced (U.toBase ≫ X ↘ S) x).mp hnode'
    subst x
    subst I
    rw [Scheme.ker_fromSpecResidueField_eq_vanishingIdeal, toBase_snoc, Category.assoc, comap_comp]
    let J := vanishingIdeal ⟨closure ({(R[D,U]).subschemeι z} : Set Z), isClosed_closure⟩
    let g := J.blowupToBase
    have hrad : (((D.comap U.toBase).radical).comap g).radical =
        ((D.comap U.toBase).comap g).radical := by
      have hs : (((D.comap U.toBase).radical).comap g).support =
          ((D.comap U.toBase).comap g).support := by
        simp only [support_comap, support_radical]
      simpa only [vanishingIdeal_support] using congrArg vanishingIdeal hs
    rw [← hrad]
    intro hpre v
    let : J.blowup.Over S := ⟨g ≫ Z ↘ S⟩
    let : (((R[D,U]).comap g).radical.subscheme).Over S :=
      ⟨((R[D,U]).comap g).radical.subschemeι ≫ g ≫ Z ↘ S⟩
    have : PrestableFamily (((R[D,U]).comap g).radical.subscheme ↘ S) := hpre
    have hsing : z ∈ ((R[D,U]).subscheme.singularLocus k).support :=
      ((R[D,U]).subscheme.mem_support_singularLocus_iff_notMem_smoothLocus z).mpr
        (fun hs ↦ hn.not_formallySmooth_stalkMap (Scheme.Hom.mem_smoothLocus.mp hs))
    exact IsEffectiveCartier.genus_blowupComponent_radical_comap_eq_zero
      (radical_comap_toBase hU hD hN).1 hx hsing rfl rfl ih v

end QPainleve.BlowupTower.IsNodalBoundaryTower
