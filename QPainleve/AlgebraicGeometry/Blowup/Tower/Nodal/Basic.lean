/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Refinement
public import QPainleve.AlgebraicGeometry.Curves.Node.Locus

import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.Blowup.Restriction
import QPainleve.AlgebraicGeometry.IdealSheaf.Restriction

/-!
# Common refinements of nodal boundary blowups

Nodal boundary towers blow up nonsmooth nodal points of the reduced total
transform on each successive scheme. Two such towers admit a common nodal
refinement, and the same holds for a finite family. The final isomorphisms
respect the morphisms to the base scheme and identify the reduced boundaries.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower

variable {S K X Y Z : Scheme.{u}} {m n : ℕ}

/-- The reduced total transform of `D` has a node at every blowup center of the tower. -/
abbrev IsNodalBoundaryTower (D : S.IdealSheafData) (s : S ⟶ K) (π : X ⟶ S)
    (T : BlowupTower X n Y) : Prop :=
  IsPointTowerWith (fun {_} g p ↦ (D.comap g).IsNodeOfReducedBoundary (g ≫ s) p) π T

private theorem isLocal_node (D : S.IdealSheafData) (s : S ⟶ K) :
    PointCondition.IsLocal (fun {_} g p ↦ (D.comap g).IsNodeOfReducedBoundary (g ≫ s) p) := by
  constructor
  intro A B f g x hx hn
  rw [D.comap_comp, Category.assoc]
  exact ((D.comap g).isNodeOfReducedBoundary_comap_iff_of_mem_isoLocus (g ≫ s) f hx).mpr hn

/-- A nodal blowup tower is an isomorphism away from the nodes of the original reduced boundary. -/
theorem IsNodalBoundaryTower.centre_subset_nodes {D : X.IdealSheafData} {s : X ⟶ K}
    {T : BlowupTower X n Y} [IsLocallyNoetherian X] (hT : IsNodalBoundaryTower D s (𝟙 X) T) :
    T.toBase.centre ⊆ {x | D.IsNodeOfReducedBoundary s x} := by
  intro x hc
  contrapose hc
  rw [Scheme.Hom.centre_def, Set.mem_compl_iff, SetLike.mem_coe, not_not]
  induction hT with
  | nil =>
    rw [toBase_nil, (Scheme.Hom.isoLocus_eq_top_iff (𝟙 X)).mpr inferInstance]
    trivial
  | @snoc n Y T J hT p hp hJ hP ih =>
    have hpne : T.toBase p ≠ x := by
      intro hpx
      have hpiso : T.toBase p ∈ T.toBase.isoLocus := hpx.symm ▸ ih
      apply hc
      rw [← hpx]
      apply (D.isNodeOfReducedBoundary_comap_iff_of_mem_isoLocus s T.toBase hpiso).mp
      simpa only [Category.comp_id] using hP
    let : IsProper T.toBase := T.isProper_toBase
    have hclosed : IsClosed ({T.toBase p} : Set X) := by
      simpa only [Set.image_singleton] using T.toBase.isClosedMap _ hp
    let V := T.toBase.isoLocus ⊓ (⟨{T.toBase p}ᶜ, hclosed.isOpen_compl⟩ : X.Opens)
    have hV : x ∈ V := ⟨ih, hpne.symm⟩
    have hJsupport : (J.support : Set Y) = {p} :=
      hJ.symm ▸ Scheme.support_ker_fromSpecResidueField_of_isClosed hp
    have hsub : T.toBase ⁻¹ᵁ V ≤ J.support.compl := by
      intro y hy
      rw [← SetLike.mem_coe, Closeds.coe_compl, hJsupport]
      exact fun he ↦ (T.toBase.mem_preimage.mp hy).2 (congrArg T.toBase he)
    have hTiso : IsIso (T.toBase ∣_ V) := T.toBase.le_isoLocus_iff.mp inf_le_left
    have hJiso : IsIso (J.blowupToBase ∣_ (T.toBase ⁻¹ᵁ V)) :=
      J.isIso_blowupToBase_restrict_of_disjoint_support
        (Set.disjoint_left.mpr fun _ hy hI ↦ hsub hy hI)
    rw [toBase_snoc]
    exact (J.blowupToBase ≫ T.toBase).mem_isoLocus_iff.mpr ⟨V, hV,
      (morphismRestrict_comp J.blowupToBase T.toBase V).symm ▸ IsIso.comp_isIso' hJiso hTiso⟩

/-- The nodal condition on a tower depends on the reduced boundary pulled back
to its base and on the induced structure morphism. -/
theorem IsNodalBoundaryTower.congr
    {D : S.IdealSheafData} {E : Z.IdealSheafData} {s : S ⟶ K} {t : Z ⟶ K}
    {π : X ⟶ S} {ρ : X ⟶ Z} {T : BlowupTower X n Y}
    (hT : IsNodalBoundaryTower D s π T)
    (hs : π ≫ s = ρ ≫ t) (hD : (D.comap π).support = (E.comap ρ).support) :
    IsNodalBoundaryTower E t ρ T := by
  induction hT with
  | nil => exact .nil
  | @snoc n Y T I hT p hp hI hnode ih =>
    have hsupport : (D.comap (T.toBase ≫ π)).support = (E.comap (T.toBase ≫ ρ)).support := by
      rw [comap_comp, comap_comp, support_comap (D.comap π), support_comap (E.comap ρ), hD]
    have hrad := congrArg (vanishingIdeal (X := Y)) hsupport
    rw [vanishingIdeal_support, vanishingIdeal_support] at hrad
    have hnode' := (isNodeOfReducedBoundary_radical _ _ _).mpr hnode
    rw [hrad] at hnode'
    exact ih.snoc p hp hI (by simpa only [isNodeOfReducedBoundary_radical, Category.assoc, hs]
      using hnode')

/-- Append a nodal boundary tower along an isomorphism to the top of the preceding
tower. The boundary of the second base agrees with the reduced total boundary of
the first tower, and the final comparison preserves the projections. -/
theorem IsNodalBoundaryTower.exists_append_of_iso
    {D : X.IdealSheafData} {E : Z.IdealSheafData} {s : X ⟶ K} {t : Z ⟶ K}
    {T : BlowupTower X m Y} {U : BlowupTower Z n S}
    (hT : IsNodalBoundaryTower D s (𝟙 X) T) (hU : IsNodalBoundaryTower E t (𝟙 Z) U)
    (e : Y ≅ Z) (hs : e.hom ≫ t = T.toBase ≫ s)
    (hD : (E.comap e.hom).support = (D.comap T.toBase).support) :
    ∃ (W : Scheme.{u}) (V : BlowupTower X (m + n) W) (f : W ≅ S),
      IsNodalBoundaryTower D s (𝟙 X) V ∧
      V.toBase = f.hom ≫ U.toBase ≫ e.inv ≫ T.toBase ∧
      (D.comap V.toBase).radical = ((E.comap U.toBase).radical).comap f.hom := by
  let P := U.transport e.symm
  have hP : IsNodalBoundaryTower E t e.hom P.tower :=
    P.isLift.isPointTowerWith (isLocal_node E t) (by simp) hU
  have hP' : IsNodalBoundaryTower D s (T.toBase ≫ 𝟙 X) P.tower :=
    hP.congr (by simpa using hs) (by simpa using hD)
  have hbase : P.tower.toBase = P.iso.inv ≫ U.toBase ≫ e.inv := by
    have hcomm := P.isLift.hom_toBase
    rw [Iso.symm_hom] at hcomm
    rw [← hcomm, Iso.inv_hom_id_assoc]
  refine ⟨P.top, T.append P.tower, P.iso.symm, hT.append hP', ?_, ?_⟩
  · rw [toBase_append, hbase]
    simp only [Iso.symm_hom, Category.assoc]
  · have hD' : ((D.comap T.toBase).comap e.inv).support = E.support := by
      rw [support_comap, ← hD, ← support_comap, ← comap_comp, Iso.inv_hom_id, comap_id]
    rw [← radical_comap_of_isOpenImmersion, ← vanishingIdeal_support, toBase_append,
      comap_comp, hbase, Iso.symm_hom, comap_comp, comap_comp,
      ← vanishingIdeal_support (I := (E.comap U.toBase).comap P.iso.inv)]
    congr 1
    rw [support_comap (((D.comap T.toBase).comap e.inv).comap U.toBase),
      support_comap ((D.comap T.toBase).comap e.inv), hD',
      support_comap (E.comap U.toBase), support_comap E]

/-- Two nodal boundary towers admit a common refinement through nodal centers.
Each extension has length at most that of the opposite tower. The final isomorphism
lies over the original scheme and matches the reduced total transforms of the boundary. -/
theorem IsNodalBoundaryTower.exists_common_nodal_boundary_tower_refinement
    {D : S.IdealSheafData} {s : S ⟶ K} {π : X ⟶ S}
    {T : BlowupTower X m Y} {U : BlowupTower X n Z}
    (hT : IsNodalBoundaryTower D s π T) (hU : IsNodalBoundaryTower D s π U) :
    ∃ (a b : ℕ) (A B : Scheme.{u}) (L : BlowupTower Y a A)
      (R : BlowupTower Z b B) (e : A ≅ B),
      a ≤ n ∧ b ≤ m ∧ IsNodalBoundaryTower D s (T.toBase ≫ π) L ∧
      IsNodalBoundaryTower D s (U.toBase ≫ π) R ∧
      L.toBase ≫ T.toBase = e.hom ≫ R.toBase ≫ U.toBase ∧
      ((D.comap (R.toBase ≫ U.toBase ≫ π)).radical).comap e.hom =
        (D.comap (L.toBase ≫ T.toBase ≫ π)).radical := by
  obtain ⟨a, b, A, B, L, R, e, ha, hb, hL, hR, h⟩ :=
    IsPointTowerWith.exists_common_point_tower_refinement hT hU (isLocal_node D s)
  refine ⟨a, b, A, B, L, R, e, ha, hb, hL, hR, h, ?_⟩
  rw [← Scheme.IdealSheafData.radical_comap_of_isOpenImmersion, ← D.comap_comp,
    ← reassoc_of% h]

/-- A finite family of nodal boundary towers admits a common nodal boundary refinement.
The comparisons commute with the projections and identify the final reduced boundaries. -/
theorem exists_common_nodal_boundary_tower_refinement_finset
    (D : S.IdealSheafData) (s : S ⟶ K) (π : X ⟶ S)
    {ι : Type*} (F : Finset ι) {n : ι → ℕ} {Y : ι → Scheme.{u}}
    (T : ∀ i, BlowupTower X (n i) (Y i)) (hT : ∀ i ∈ F, IsNodalBoundaryTower D s π (T i)) :
    ∃ (m : ℕ) (Z : Scheme.{u}) (U : BlowupTower X m Z), IsNodalBoundaryTower D s π U ∧
      ∀ i ∈ F, ∃ (a : ℕ) (A : Scheme.{u}) (L : BlowupTower (Y i) a A) (e : Z ≅ A),
        IsNodalBoundaryTower D s ((T i).toBase ≫ π) L ∧
        U.toBase = e.hom ≫ L.toBase ≫ (T i).toBase ∧
        ((D.comap (L.toBase ≫ (T i).toBase ≫ π)).radical).comap e.hom =
          (D.comap (U.toBase ≫ π)).radical := by
  obtain ⟨m, Z, U, hU, h⟩ :=
    IsPointTowerWith.exists_common_point_tower_refinement_finset F T hT (isLocal_node D s)
  refine ⟨m, Z, U, hU, fun i hi ↦ ?_⟩
  obtain ⟨a, A, L, e, hL, hbase⟩ := h i hi
  refine ⟨a, A, L, e, hL, hbase, ?_⟩
  rw [← Scheme.IdealSheafData.radical_comap_of_isOpenImmersion, ← D.comap_comp,
    reassoc_of% hbase]

end QPainleve.BlowupTower
