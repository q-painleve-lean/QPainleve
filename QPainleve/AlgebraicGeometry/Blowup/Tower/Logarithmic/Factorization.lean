/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Logarithmic.Basic
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Basic

import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Nodality
import QPainleve.AlgebraicGeometry.Blowup.Tower.Logarithmic.Boundary
import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Reorder
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced
import TauCeti.AlgebraicGeometry.Morphisms.StalkMap

/-!
# Ordering logarithmic point blowups

In a sequence of boundary blowups, a corner blowup can be moved before all the
preceding internal blowups. Iteration factors the specified projection through
a corner tower followed by internal blowups. The internal centers are indexed
in their original order and retain their center schemes and their maps to the
original surface. The comparison identifies the final boundary ideal.

The factorization uses the internal and corner operations in [Lutz, Definition 8.1
and Theorem 8.4][Lutz].

[Lutz]: https://arxiv.org/pdf/2005.05010v3#page=68
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Scheme.IdealSheafData
open TauCeti.AlgebraicGeometry

universe u

namespace QPainleve.BlowupTower

variable {X S : Scheme.{u}}

/-- A point blowup tower with successive boundary ideals obtained by strict
transform at smooth centers and reduced total transform at nodes. The internal centers
are recorded in order as schemes over the original surface. -/
inductive IsLogarithmicBoundaryTower (D : X.IdealSheafData) (s : X ⟶ S) :
    {n : ℕ} → {Y : Scheme.{u}} → BlowupTower X n Y → Y.IdealSheafData →
    {m : ℕ} → (Fin m → Over X) → Prop
  /-- The empty tower has its original boundary and no centers. -/
  | nil : IsLogarithmicBoundaryTower D s .nil D Fin.elim0
  /-- Blow up a node and take the reduced total transform of the boundary. -/
  | node {n m : ℕ} {Y : Scheme.{u}} {T : BlowupTower X n Y} {P : Y.IdealSheafData}
      {I : Y.IdealSheafData} {c : Fin m → Over X}
      (hT : IsLogarithmicBoundaryTower D s T P c)
      (p : Y) (hp : IsClosed ({p} : Set Y)) (hI : I = (Y.fromSpecResidueField p).ker)
      (hn : P.IsNodeOfReducedBoundary (T.toBase ≫ s) p) :
      IsLogarithmicBoundaryTower D s (T.snoc I) (P.comap I.blowupToBase).radical c
  /-- Blow up a smooth closed point of the boundary and take the strict transform.
  Retain the residue scheme of the center with its original map to the base. -/
  | internal {n m : ℕ} {Y : Scheme.{u}} {T : BlowupTower X n Y} {P : Y.IdealSheafData}
      {c : Fin m → Over X}
      (hT : IsLogarithmicBoundaryTower D s T P c)
      (p : P.subscheme) (hp : IsClosed ({p} : Set P.subscheme))
      (hC : (P.subscheme.fromSpecResidueField p).ker.IsEffectiveCartier)
      (hs : ((P.subschemeι ≫ T.toBase ≫ s).stalkMap p).hom.FormallySmooth) :
      IsLogarithmicBoundaryTower D s (T.snoc ((P.subscheme.fromSpecResidueField p ≫
        P.subschemeι).ker)) (((P.subscheme.fromSpecResidueField p ≫ P.subschemeι).ker.blowupMap
          P.subschemeι).ker)
        (Fin.snoc c (Over.mk (P.subscheme.fromSpecResidueField p ≫ P.subschemeι ≫ T.toBase)))

namespace IsLogarithmicBoundaryTower

variable {Y : Scheme.{u}} {D : X.IdealSheafData} {s : X ⟶ S} {n m : ℕ}
  {T : BlowupTower X n Y} {P : Y.IdealSheafData}

/-- A corner tower followed by the prescribed ordered internal centers, with an
isomorphism over the original surface identifying the final boundary. -/
structure OrderedFactorization (D : X.IdealSheafData) (s : X ⟶ S)
    (T : BlowupTower X n Y) (P : Y.IdealSheafData) (c : Fin m → Over X) where
  /-- The number of corner blowups. -/
  length : ℕ
  /-- The scheme reached after the corner blowups. -/
  middle : Scheme.{u}
  /-- The corner blowups from the original surface. -/
  tower : BlowupTower X length middle
  /-- Each center in the initial tower is a node of the current reduced boundary. -/
  isNodal : IsNodalBoundaryTower D s (𝟙 X) tower
  /-- The lengths of the two towers add to the original length. -/
  length_add : length + m = n
  /-- The reduced boundary after the corner blowups. -/
  boundary : middle.IdealSheafData
  /-- This boundary is the reduced total transform. -/
  boundary_eq : boundary = (D.comap tower.toBase).radical
  /-- The internal center embeddings into the reduced boundary of the middle scheme. -/
  center : ∀ j, (c j).left ⟶ boundary.subscheme
  /-- The center embeddings are closed immersions. -/
  isClosedImmersion_center : ∀ j, IsClosedImmersion (center j)
  /-- Each center is Cartier on the reduced boundary. -/
  isEffectiveCartier_center : ∀ j, (center j).ker.IsEffectiveCartier
  /-- The stalk map at each center is formally smooth. -/
  formallySmooth_stalkMap_center : ∀ j y,
    ((boundary.subschemeι ≫ tower.toBase ≫ s).stalkMap
      (center j y)).hom.FormallySmooth
  /-- The center embeddings retain the original maps to the base. -/
  center_toBase : ∀ j, center j ≫ boundary.subschemeι ≫
    tower.toBase = (c j).hom
  /-- The scheme of the internal blowups is isomorphic to the original final scheme. -/
  iso : (alongBoundary boundary.subschemeι
    (fun j ↦ ⟨(center j).ker, isEffectiveCartier_center j⟩)).1 ≅ Y
  /-- The isomorphism factors the specified composite projection. -/
  iso_hom_toBase : iso.hom ≫ T.toBase =
    (alongBoundary boundary.subschemeι
      (fun j ↦ ⟨(center j).ker, isEffectiveCartier_center j⟩)).2.toTower.toBase ≫ tower.toBase
  /-- The isomorphism identifies the specified final boundary with the strict boundary. -/
  comap_boundary_iso_hom : P.comap iso.hom =
    (alongBoundary boundary.subschemeι
      (fun j ↦ ⟨(center j).ker, isEffectiveCartier_center j⟩)).2.boundaryι.ker

namespace OrderedFactorization

variable {c : Fin m → Over X}

/-- The internal blowup tower in a factorization, equipped with its strict boundary. -/
noncomputable abbrev internalTower (F : OrderedFactorization D s T P c) :
    Σ W, WithBoundary F.boundary.subschemeι m W :=
  alongBoundary F.boundary.subschemeι (fun j ↦ ⟨(F.center j).ker, F.isEffectiveCartier_center j⟩)

private theorem nonempty_nil (D : X.IdealSheafData) (s : X ⟶ S) [IsReduced D.subscheme] :
    Nonempty (OrderedFactorization D s (.nil : BlowupTower X 0 X) D
      (Fin.elim0 : Fin 0 → Over X)) := by
  let J : Fin 0 → {I : D.subscheme.IdealSheafData // I.IsEffectiveCartier} :=
    fun j ↦ ⟨(show (Fin.elim0 j : Over X).left ⟶ D.subscheme from j.elim0).ker, j.elim0⟩
  have hA := alongBoundary_zero D.subschemeι J
  have H : ∃ e : (alongBoundary D.subschemeι J).1 ≅ X,
      e.hom = (alongBoundary D.subschemeι J).2.toTower.toBase ∧
      D.comap e.hom = (alongBoundary D.subschemeι J).2.boundaryι.ker := by
    generalize alongBoundary D.subschemeι J = A at hA ⊢
    subst A
    exact ⟨Iso.refl X, by simp, by simp⟩
  obtain ⟨e, he, hb⟩ := H
  exact ⟨{ length := 0, middle := X, tower := .nil, isNodal := .nil, length_add := rfl
           boundary := D
           boundary_eq := by simp [(D.isReduced_subscheme_iff_radical_eq).mp inferInstance]
           center := fun j ↦ j.elim0, isClosedImmersion_center := fun j ↦ j.elim0
           isEffectiveCartier_center := fun j ↦ j.elim0
           formallySmooth_stalkMap_center := fun j ↦ j.elim0, center_toBase := fun j ↦ j.elim0
           iso := e, iso_hom_toBase := by simpa only [toBase_nil, Category.comp_id] using he
           comap_boundary_iso_hom := hb }⟩

private theorem node_under_iso (F : OrderedFactorization D s T P c)
    {p : Y} (hp : IsClosed ({p} : Set Y)) (hn : P.IsNodeOfReducedBoundary (T.toBase ≫ s) p) :
    let A := F.internalTower
    let q := F.iso.inv p
    IsClosed ({q} : Set A.1) ∧
      (Y.fromSpecResidueField p).ker.comap F.iso.hom = (A.1.fromSpecResidueField q).ker ∧
      A.2.boundaryι.ker.IsNodeOfReducedBoundary (A.2.toTower.toBase ≫ F.tower.toBase ≫ s) q := by
  let I := (Y.fromSpecResidueField p).ker
  let A := F.internalTower
  let r := F.tower.toBase
  let q := F.iso.inv p
  let J := (A.1.fromSpecResidueField q).ker
  have hq : IsClosed ({q} : Set A.1) := by
    simpa only [q, Set.image_singleton] using F.iso.inv.isClosedEmbedding.isClosedMap _ hp
  have hqp : F.iso.hom q = p := by
    calc
      F.iso.hom q = (F.iso.inv ≫ F.iso.hom) p := (Scheme.Hom.comp_apply _ _ _).symm
      _ = p := by rw [F.iso.inv_hom_id]; rfl
  have hJ : I.comap F.iso.hom = J := by
    have h := F.iso.hom.comap_ker_fromSpecResidueField_of_mem_isoLocus (q := q)
      (by rwa [hqp]) (by rw [(F.iso.hom.isoLocus_eq_top_iff).mpr inferInstance]; trivial)
    calc
      I.comap F.iso.hom = (Y.fromSpecResidueField (F.iso.hom q)).ker.comap F.iso.hom :=
        congrArg (fun p' : Y ↦ (Y.fromSpecResidueField p').ker.comap F.iso.hom) hqp.symm
      _ = J := h
  have hqn : A.2.boundaryι.ker.IsNodeOfReducedBoundary (A.2.toTower.toBase ≫ r ≫ s) q := by
    have H := (P.isNodeOfReducedBoundary_comap_iff_of_isOpenImmersion (T.toBase ≫ s)
      F.iso.hom q).mpr (hqp.symm ▸ hn)
    rwa [← Category.assoc F.iso.hom, F.iso_hom_toBase, Category.assoc,
      F.comap_boundary_iso_hom] at H
  exact ⟨hq, hJ, hqn⟩

private theorem exists_node (F : OrderedFactorization D s T P c)
    {p : Y} (hp : IsClosed ({p} : Set Y)) (hn : P.IsNodeOfReducedBoundary (T.toBase ≫ s) p) :
    let I := (Y.fromSpecResidueField p).ker
    Nonempty (OrderedFactorization D s (T.snoc I) (P.comap I.blowupToBase).radical c) := by
  let I := (Y.fromSpecResidueField p).ker
  let A := F.internalTower
  let r := F.tower.toBase
  let q := F.iso.inv p
  let J := (A.1.fromSpecResidueField q).ker
  obtain ⟨hq, hJ, hqn⟩ := F.node_under_iso hp hn
  have (j : Fin m) : IsClosedImmersion (F.center j) := F.isClosedImmersion_center j
  have : IsReduced F.boundary.subscheme := by
    rw [F.boundary_eq, ← vanishingIdeal_support]
    infer_instance
  -- Move the new node before the whole internal suffix, leaving its indexed centers in order.
  obtain ⟨hx, hxn, a, ha, haPb, haSm, e, he, hboundary⟩ :=
    exists_iso_nodal_blowup_alongBoundary (D := F.boundary) (r ≫ s) F.center
      F.isEffectiveCartier_center F.formallySmooth_stalkMap_center q hq hqn
  let x := A.2.toTower.toBase q
  let K := (F.middle.fromSpecResidueField x).ker
  let E := (F.boundary.comap K.blowupToBase).radical
  have HN : IsNodalBoundaryTower D s (𝟙 X) (F.tower.snoc K) := by
    apply F.isNodal.snoc x hx rfl
    rw [Category.comp_id, ← isNodeOfReducedBoundary_radical, ← F.boundary_eq]
    exact hxn
  have hE : E = (D.comap (F.tower.snoc K).toBase).radical := by
    have hSupport : (F.boundary.comap K.blowupToBase).support =
        (D.comap (F.tower.snoc K).toBase).support := by
      rw [toBase_snoc, comap_comp, support_comap, support_comap, F.boundary_eq, support_radical]
    simpa only [E, vanishingIdeal_support] using
      congrArg (vanishingIdeal (X := K.blowup)) hSupport
  -- Compose the interchange with the lift of the previous comparison to the original tower.
  let B := alongBoundary E.subschemeι (fun j ↦ ⟨(a j).ker, ha j⟩)
  let e' := e ≪≫ I.blowupIso F.iso hJ
  have hbase : e'.hom ≫ (T.snoc I).toBase = B.2.toTower.toBase ≫ (F.tower.snoc K).toBase := by
    dsimp only [e']
    rw [Iso.trans_hom, toBase_snoc, Category.assoc, blowupIso_hom_blowupToBase_assoc,
      F.iso_hom_toBase, toBase_snoc]
    simpa only [Category.assoc] using congrArg (· ≫ F.tower.toBase) he.w
  have hbound : (P.comap I.blowupToBase).radical.comap e'.hom = B.2.boundaryι.ker := by
    dsimp only [e']
    rw [Iso.trans_hom, comap_comp, ← radical_comap_of_isOpenImmersion,
      ← comap_comp, blowupIso_hom_blowupToBase, comap_comp, F.comap_boundary_iso_hom]
    exact hboundary
  have hlen := F.length_add
  refine ⟨{ length := F.length + 1, middle := K.blowup, tower := F.tower.snoc K
            isNodal := HN, length_add := by omega
            boundary := E, boundary_eq := hE, center := a
            isClosedImmersion_center := fun j ↦ MorphismProperty.of_isPullback (haPb j).flip
              (F.isClosedImmersion_center j)
            isEffectiveCartier_center := ha, formallySmooth_stalkMap_center := ?_
            center_toBase := ?_, iso := e', iso_hom_toBase := hbase
            comap_boundary_iso_hom := hbound }⟩
  · intro j y
    rw [toBase_snoc, Category.assoc]
    exact haSm j y
  · intro j
    let d := subschemeMap E F.boundary K.blowupToBase
      (le_map_iff_comap_le.mpr (le_radical _))
    have hd : a j ≫ d = F.center j := by
      simpa only [Category.id_comp] using (haPb j).w
    rw [toBase_snoc, ← subschemeMap_subschemeι_assoc E F.boundary K.blowupToBase _,
      ← Category.assoc (a j)]
    exact congrArg (· ≫ F.boundary.subschemeι ≫ F.tower.toBase) hd |>.trans (F.center_toBase j)

private theorem exists_boundaryIso (F : OrderedFactorization D s T P c) :
    ∃ d : F.boundary.subscheme ≅ P.subscheme,
      F.internalTower.2.boundaryι ≫ F.iso.hom = d.hom ≫ P.subschemeι := by
  let b := F.internalTower.2.boundaryι
  have : IsClosedImmersion (b ≫ F.iso.hom) :=
    inferInstanceAs (IsClosedImmersion (F.internalTower.2.boundaryι ≫ F.iso.hom))
  have h : P.subschemeι.ker = (b ≫ F.iso.hom).ker := calc
    P.subschemeι.ker = P := P.ker_subschemeι
    _ = (P.comap F.iso.hom).comap F.iso.inv := by
      rw [← comap_comp, Iso.inv_hom_id, comap_id]
    _ = b.ker.comap F.iso.inv := congrArg (·.comap F.iso.inv) F.comap_boundary_iso_hom
    _ = (b ≫ F.iso.hom).ker := by
      rw [← Scheme.Hom.comap_ker_comp_of_isClosedImmersion b F.iso.hom,
        ← comap_comp, Iso.inv_hom_id, comap_id]
  let d := IsClosedImmersion.lift P.subschemeι (b ≫ F.iso.hom) h.le
  have : IsIso d := IsClosedImmersion.isIso_lift _ _ h
  exact ⟨asIso d, (IsClosedImmersion.lift_fac _ _ _).symm⟩

private theorem exists_snocCenters (F : OrderedFactorization D s T P c)
    {V : Scheme.{u}} (a : V ⟶ F.boundary.subscheme) [IsClosedImmersion a]
    (hC : a.ker.IsEffectiveCartier)
    (hs : ∀ y, ((F.boundary.subschemeι ≫ F.tower.toBase ≫ s).stalkMap (a y)).hom.FormallySmooth)
    {f : V ⟶ X} (hf : a ≫ F.boundary.subschemeι ≫ F.tower.toBase = f) :
    let c' : Fin (m + 1) → Over X := Fin.snoc c (Over.mk f)
    ∃ (a' : ∀ j, (c' j).left ⟶ F.boundary.subscheme)
      (hC' : ∀ j, (a' j).ker.IsEffectiveCartier),
      (∀ j, IsClosedImmersion (a' j)) ∧
      (∀ j y, ((F.boundary.subschemeι ≫ F.tower.toBase ≫ s).stalkMap (a' j y)).hom.FormallySmooth) ∧
      (∀ j, a' j ≫ F.boundary.subschemeι ≫ F.tower.toBase = (c' j).hom) ∧
      (fun j ↦ ⟨(a' j).ker, hC' j⟩) =
        (Fin.snoc (fun j ↦ ⟨(F.center j).ker, F.isEffectiveCartier_center j⟩) ⟨a.ker, hC⟩ :
          Fin (m + 1) → {I : F.boundary.subscheme.IdealSheafData // I.IsEffectiveCartier}) := by
  let c' : Fin (m + 1) → Over X := Fin.snoc c (Over.mk f)
  let tags : Fin (m + 1) → Over F.boundary.subscheme :=
    Fin.snoc (fun j ↦ Over.mk (F.center j)) (Over.mk a)
  have htLast : tags (Fin.last m) = Over.mk a := Fin.snoc_last _ _
  have htCast (j : Fin m) : tags j.castSucc = Over.mk (F.center j) := Fin.snoc_castSucc _ _ _
  have hcLast : c' (Fin.last m) = Over.mk f := Fin.snoc_last _ _
  have hcCast (j : Fin m) : c' j.castSucc = c j := Fin.snoc_castSucc _ _ _
  have hdom (j : Fin (m + 1)) : (c' j).left = (tags j).left :=
    Fin.lastCases (by simp [hcLast, htLast]) (fun j ↦ by simp [hcCast, htCast]) j
  let a' (j : Fin (m + 1)) := eqToHom (hdom j) ≫ (tags j).hom
  have hCl (j : Fin (m + 1)) : IsClosedImmersion (a' j) := by
    have H : IsClosedImmersion (tags j).hom :=
      Fin.lastCases (by rw [htLast]; exact inferInstanceAs (IsClosedImmersion a))
        (fun j ↦ by rw [htCast]; exact F.isClosedImmersion_center j) j
    exact inferInstanceAs (IsClosedImmersion (eqToHom (hdom j) ≫ (tags j).hom))
  have hK (j : Fin (m + 1)) : (a' j).ker = (tags j).hom.ker :=
    Scheme.Hom.ker_comp_of_isIso _ _
  let J : Fin (m + 1) → {I : F.boundary.subscheme.IdealSheafData // I.IsEffectiveCartier} :=
    Fin.snoc (fun j ↦ ⟨(F.center j).ker, F.isEffectiveCartier_center j⟩) ⟨a.ker, hC⟩
  have hjLast : J (Fin.last m) = ⟨a.ker, hC⟩ := Fin.snoc_last _ _
  have hjCast (j : Fin m) : J j.castSucc = ⟨(F.center j).ker, F.isEffectiveCartier_center j⟩ :=
    Fin.snoc_castSucc _ _ _
  have hJ (j : Fin (m + 1)) : (a' j).ker = (J j).val := by
    rw [hK]
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · rw [htLast, hjLast]; rfl
    · rw [htCast, hjCast]; rfl
  have hC' (j : Fin (m + 1)) : (a' j).ker.IsEffectiveCartier := hJ j ▸ (J j).property
  refine ⟨a', hC', hCl, ?_, ?_, funext fun j ↦ Subtype.ext (hJ j)⟩
  · intro j y
    have H : ∀ y, ((F.boundary.subschemeι ≫ F.tower.toBase ≫ s).stalkMap
        ((tags j).hom y)).hom.FormallySmooth :=
      Fin.lastCases (by rw [htLast]; exact hs)
        (fun j ↦ by rw [htCast]; exact F.formallySmooth_stalkMap_center j) j
    exact H (eqToHom (hdom j) y)
  · intro j
    have H : ∀ j (h : (c' j).left = (tags j).left),
        (tags j).hom ≫ F.boundary.subschemeι ≫ F.tower.toBase =
          eqToHom h.symm ≫ (c' j).hom := by
      intro j
      refine Fin.lastCases ?_ (fun i ↦ ?_) j
      · rw [htLast, hcLast]
        intro h
        simpa using hf
      · rw [htCast, hcCast]
        intro h
        simpa using F.center_toBase i
    dsimp only [a']
    rw [Category.assoc, H j (hdom j), ← Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.id_comp]

private theorem extend_internalTower (F : OrderedFactorization D s T P c)
    {V : Scheme.{u}} (a : V ⟶ F.boundary.subscheme) [IsClosedImmersion a]
    (hC : a.ker.IsEffectiveCartier)
    (hs : ∀ y, ((F.boundary.subschemeι ≫ F.tower.toBase ≫ s).stalkMap (a y)).hom.FormallySmooth)
    {I : Y.IdealSheafData} (hI : I.comap F.iso.hom = a.ker.map F.internalTower.2.boundaryι)
    (hP : (I.blowupMap P.subschemeι).ker.comap (I.blowupIso F.iso hI).hom =
      (F.internalTower.2.snoc a.ker hC).boundaryι.ker)
    {f : V ⟶ X} (hf : a ≫ F.boundary.subschemeι ≫ F.tower.toBase = f) :
    Nonempty (OrderedFactorization D s (T.snoc I) (I.blowupMap P.subschemeι).ker
      (Fin.snoc c (Over.mk f))) := by
  let b := F.internalTower.2
  obtain ⟨a', hC', hCl, hSm, hbase, hEq⟩ := F.exists_snocCenters a hC hs hf
  let J : Fin (m + 1) → {I : F.boundary.subscheme.IdealSheafData // I.IsEffectiveCartier} :=
    Fin.snoc (fun j ↦ ⟨(F.center j).ker, F.isEffectiveCartier_center j⟩) ⟨a.ker, hC⟩
  have hjLast : J (Fin.last m) = ⟨a.ker, hC⟩ := Fin.snoc_last _ _
  have hjCast (j : Fin m) : J j.castSucc = ⟨(F.center j).ker, F.isEffectiveCartier_center j⟩ :=
    Fin.snoc_castSucc _ _ _
  have hEq' : (fun j ↦ ⟨(a' j).ker, hC' j⟩) = J := hEq
  have hA : alongBoundary F.boundary.subschemeι (fun j ↦ ⟨(a' j).ker, hC' j⟩) =
      ⟨_, b.snoc a.ker hC⟩ := by
    rw [hEq', alongBoundary_succ, show (fun j : Fin m ↦ J j.castSucc) = _ from funext hjCast,
      hjLast]
  have hlen := F.length_add
  have hiso : ∃ e : (alongBoundary F.boundary.subschemeι (fun j ↦ ⟨(a' j).ker, hC' j⟩)).1
      ≅ I.blowup,
      e.hom ≫ (T.snoc I).toBase =
        (alongBoundary F.boundary.subschemeι (fun j ↦ ⟨(a' j).ker, hC' j⟩)).2.toTower.toBase ≫
          F.tower.toBase ∧
      (I.blowupMap P.subschemeι).ker.comap e.hom =
        (alongBoundary F.boundary.subschemeι (fun j ↦ ⟨(a' j).ker, hC' j⟩)).2.boundaryι.ker := by
    generalize alongBoundary F.boundary.subschemeι (fun j ↦ ⟨(a' j).ker, hC' j⟩) = A at hA ⊢
    subst A
    refine ⟨I.blowupIso F.iso hI, ?_, hP⟩
    rw [toBase_snoc, WithBoundary.toTower_snoc, toBase_snoc, blowupIso_hom_blowupToBase_assoc,
      Category.assoc, F.iso_hom_toBase]
  obtain ⟨e, he, hB⟩ := hiso
  refine ⟨{
    length := F.length
    middle := F.middle
    tower := F.tower
    isNodal := F.isNodal
    length_add := by omega
    boundary := F.boundary
    boundary_eq := F.boundary_eq
    center := a'
    isClosedImmersion_center := hCl
    isEffectiveCartier_center := hC'
    formallySmooth_stalkMap_center := hSm
    center_toBase := hbase
    iso := e
    iso_hom_toBase := he
    comap_boundary_iso_hom := hB }⟩

private theorem exists_internal (F : OrderedFactorization D s T P c)
    (p : P.subscheme) (hp : IsClosed ({p} : Set P.subscheme))
    (hC : (P.subscheme.fromSpecResidueField p).ker.IsEffectiveCartier)
    (hs : ((P.subschemeι ≫ T.toBase ≫ s).stalkMap p).hom.FormallySmooth) :
    let a := P.subscheme.fromSpecResidueField p
    let I := (a ≫ P.subschemeι).ker
    Nonempty (OrderedFactorization D s (T.snoc I) (I.blowupMap P.subschemeι).ker
      (Fin.snoc c (Over.mk (a ≫ P.subschemeι ≫ T.toBase)))) := by
  intro a I
  obtain ⟨d, hd⟩ := F.exists_boundaryIso
  let b := F.internalTower.2
  let a' := a ≫ d.inv
  have : IsClosedImmersion a := isClosed_singleton_iff_isClosedImmersion.mp hp
  have : IsClosedImmersion a' := inferInstanceAs (IsClosedImmersion (a ≫ d.inv))
  have hCa' : a'.ker.IsEffectiveCartier := by
    rw [← Scheme.Hom.comap_ker_comp_of_isClosedImmersion a' d.hom]
    simpa only [a', Category.assoc, Iso.inv_hom_id, Category.comp_id] using hC.comap d.hom
  have hdBase : d.hom ≫ P.subschemeι ≫ T.toBase = F.boundary.subschemeι ≫ F.tower.toBase := by
    rw [← reassoc_of% hd, F.iso_hom_toBase, WithBoundary.boundaryι_toBase_assoc]
  have hComm : a' ≫ b.boundaryι ≫ F.iso.hom = a ≫ P.subschemeι := by
    rw [hd]
    simp [a']
  have hI : I.comap F.iso.hom = a'.ker.map b.boundaryι := by
    dsimp only [I]
    rw [← hComm, ← Category.assoc, Scheme.Hom.comap_ker_comp_of_isClosedImmersion,
      map_ker]
  refine F.extend_internalTower a' hCa' ?_ hI ?_ ?_
  · intro y
    have hpoint : d.hom (a' y) = p := by
      rw [← Scheme.Hom.comp_apply]
      simpa only [a', Category.assoc, Iso.inv_hom_id, Category.comp_id] using
        Scheme.fromSpecResidueField_apply p y
    have h := (RingHom.FormallySmooth.respectsIso.stalkMap_comp_isOpenImmersion_iff
      d.hom (P.subschemeι ≫ T.toBase ≫ s) (a' y)).mpr (hpoint.symm ▸ hs)
    have hds : d.hom ≫ P.subschemeι ≫ T.toBase ≫ s =
        F.boundary.subschemeι ≫ F.tower.toBase ≫ s := by
      simpa only [Category.assoc] using congrArg (· ≫ s) hdBase
    exact Eq.mp (congrArg (fun f : F.boundary.subscheme ⟶ S ↦
      (f.stalkMap (a' y)).hom.FormallySmooth) hds) h
  · rw [I.comap_ker_blowupMap_subschemeι_blowupIso P F.iso hI, F.comap_boundary_iso_hom,
      ← ker_blowupMap_eq_ker_blowupMap_subschemeι, WithBoundary.ker_boundaryι_snoc]
  · rw [← hdBase]
    simp [a']

end OrderedFactorization

/-- Factor a specified logarithmic point blowup tower into corner blowups followed by
the ordered internal blowups, identifying the final schemes and their boundary ideals. -/
theorem nonempty_orderedFactorization [IsReduced D.subscheme]
    {c : Fin m → Over X} (h : IsLogarithmicBoundaryTower D s T P c) :
    Nonempty (OrderedFactorization D s T P c) := by
  induction h with
  | nil => exact OrderedFactorization.nonempty_nil _ _
  | @node _ _ _ _ _ I _ _ p hp hI hn ih =>
    subst I
    obtain ⟨F⟩ := ih
    exact F.exists_node hp hn
  | internal _ p hp hC hs ih =>
    obtain ⟨F⟩ := ih
    exact F.exists_internal p hp hC hs

end IsLogarithmicBoundaryTower

namespace IsClosedPointTower

variable {X Y : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y} {D : X.IdealSheafData}
  {k : Type u} [Field k] [X.Over (Spec (.of k))]

private theorem exists_internal_of_not_isNodeOfReducedBoundary {P : Y.IdealSheafData}
    {I : Y.IdealSheafData} {m : ℕ} {c : Fin m → Over X}
    (h : IsLogarithmicBoundaryTower D (X ↘ Spec (.of k)) T P c)
    (hnodal : AtWorstNodalOfRelativeDimensionOne (P.subschemeι ≫ T.toBase ≫ X ↘ Spec (.of k)))
    (p : Y) (hp : IsClosed ({p} : Set Y)) (hI : I = (Y.fromSpecResidueField p).ker)
    (hpP : p ∈ P.support)
    (hn : ¬ P.IsNodeOfReducedBoundary (T.toBase ≫ X ↘ Spec (.of k)) p)
    (hC : (I.comap P.subschemeι).IsEffectiveCartier) :
    ∃ c' : Fin (m + 1) → Over X,
      IsLogarithmicBoundaryTower D (X ↘ Spec (.of k)) (T.snoc I) (I.blowupMap P.subschemeι).ker
        c' := by
  have : IsReduced P.subscheme := hnodal.isReduced
  have hPNodal : AtWorstNodalOfRelativeDimensionOne
      (P.subschemeι ≫ (T.toBase ≫ X ↘ Spec (.of k))) := hnodal
  obtain ⟨q, hq, hqSmooth⟩ := P.exists_mem_smoothLocus_of_mem_support_of_not_isNodeOfReducedBoundary
    (T.toBase ≫ X ↘ Spec (.of k)) hPNodal hpP hn
  have hqClosed := P.subschemeι.isClosedEmbedding.isClosed_iff_image_isClosed.mpr (by
    simpa only [Set.image_singleton, hq] using hp : IsClosed (P.subschemeι '' {q}))
  have hker : I = (P.subscheme.fromSpecResidueField q ≫ P.subschemeι).ker := by
    rw [Scheme.Hom.ker_comp, P.subschemeι.map_ker_fromSpecResidueField, hq, hI]
  have hCartier : (P.subscheme.fromSpecResidueField q).ker.IsEffectiveCartier := by
    simpa only [hker, Scheme.Hom.comap_ker_comp_of_isClosedImmersion] using hC
  have := hnodal.syntomic
  have hSmooth := Scheme.Hom.mem_smoothLocus.mp hqSmooth
  clear hI
  subst I
  exact ⟨_, h.internal q hqClosed hCartier hSmooth⟩

variable [PerfectField k] [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [IsIntegral X] [IsNoetherian X]

private theorem exists_logarithmicBoundaryTower_of_totalTransform_le_ramification
    (hD : D.IsEffectiveCartier) (hT : IsClosedPointTower X T)
    (h : D.comap T.toBase ≤ hT.ramificationIdealSheafToBase k)
    (hnodal : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ Spec (.of k))) :
    let P := (D.comap T.toBase).colon (hT.ramificationIdealSheafToBase k)
    AtWorstNodalOfRelativeDimensionOne (P.subschemeι ≫ T.toBase ≫ X ↘ Spec (.of k)) ∧
      ∃ (m : ℕ) (c : Fin m → Over X), IsLogarithmicBoundaryTower D (X ↘ Spec (.of k)) T P c := by
  induction hT with
  | nil =>
    dsimp only
    have hP : (D.comap (BlowupTower.nil (X := X)).toBase).colon
        ((IsClosedPointTower.nil (X := X)).ramificationIdealSheafToBase k) = D := by
      rw [toBase_nil, comap_id, ramificationIdealSheafToBase_nil, colon_top]
    rw [hP, toBase_nil, Category.id_comp]
    exact ⟨hnodal, 0, Fin.elim0, .nil⟩
  | @snoc n Y T I hT p hp hI ih =>
    -- The no-zero inequality descends to the prefix, where the induction proves nodality.
    let V := BlowupTower.nil.snoc I
    have hV : IsClosedPointTower Y V := IsClosedPointTower.nil.snoc p hp hI
    have hpre := hT.totalTransform_le_ramification_of_append k hD hV
      (by simpa only [V, append_snoc, append_nil] using h)
    obtain ⟨hn, m, c, hc⟩ := ih hpre
    obtain ⟨hpP, _, hstep⟩ := hT.poleIdeal_snoc_of_nodal_boundary hD p hp hI h hn
    -- A node contributes the reduced total transform, and a smooth center the strict transform.
    rcases hstep with ⟨hnode, heq⟩ | ⟨hsm, heq, hC⟩
    · let P := (D.comap T.toBase).colon (hT.ramificationIdealSheafToBase k)
      let s := T.toBase ≫ X ↘ Spec (.of k)
      let : Y.Over (Spec (.of k)) := ⟨s⟩
      have : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k)) := hT.smoothOfRelativeDimension _
      have : IsIntegral Y := hT.isIntegral (X ↘ Spec (.of k))
      have : IsNoetherian Y := T.isNoetherian
      have : QuasiCompact (Y ↘ Spec (.of k)) := inferInstance
      have hs : Y ↘ Spec (.of k) = T.toBase ≫ X ↘ Spec (.of k) := rfl
      have hP := (hT.poleIdeal_snoc_of_totalTransform_le_ramification k hD p hp hI h).1
      obtain ⟨q, hq⟩ := P.range_subschemeι.ge hpP
      subst p
      subst I
      dsimp only at heq ⊢
      rw [heq]
      refine ⟨?_, m, c, hc.node _ hp rfl hnode⟩
      simp only [toBase_snoc, Category.assoc]
      rw [Y.ker_fromSpecResidueField_eq_vanishingIdeal (P.subschemeι q)]
      simpa only [hs, P] using
        atWorstNodalOfRelativeDimensionOne_radical_comap_blowupToBase_of_node
          (k := k) hn hP hp hnode
    · dsimp only at heq ⊢
      rw [heq]
      obtain ⟨c', hc'⟩ := exists_internal_of_not_isNodeOfReducedBoundary hc hn p hp hI hpP hsm hC
      refine ⟨?_, m + 1, c', hc'⟩
      simpa only [toBase_snoc, Category.assoc] using
        atWorstNodalOfRelativeDimensionOne_strictTransform_of_isEffectiveCartier_comap
          (T.toBase ≫ X ↘ Spec (.of k)) hn hC

/-- On a smooth integral surface, if the total transform of a nodal Cartier boundary
is bounded by the ramification ideal, the final pole divisor is again nodal. -/
theorem atWorstNodalOfRelativeDimensionOne_poleIdeal
    (hD : D.IsEffectiveCartier) (hT : IsClosedPointTower X T)
    (h : D.comap T.toBase ≤ hT.ramificationIdealSheafToBase k)
    (hnodal : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ Spec (.of k))) :
    let P := (D.comap T.toBase).colon (hT.ramificationIdealSheafToBase k)
    AtWorstNodalOfRelativeDimensionOne (P.subschemeι ≫ T.toBase ≫ X ↘ Spec (.of k)) :=
  (exists_logarithmicBoundaryTower_of_totalTransform_le_ramification hD hT h hnodal).1

/-- If the pullback of a logarithmic form has no zeros and the initial boundary is nodal,
the specified point blowup projection factors into a nodal tower followed by the ordered
internal blowups. The comparison identifies the final pole ideal with the strict boundary
of the internal tower. -/
theorem exists_orderedFactorization_of_totalTransform_le_ramification
    (hD : D.IsEffectiveCartier) (hT : IsClosedPointTower X T)
    (h : D.comap T.toBase ≤ hT.ramificationIdealSheafToBase k)
    (hnodal : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ Spec (.of k))) :
    let P := (D.comap T.toBase).colon (hT.ramificationIdealSheafToBase k)
    ∃ (m : ℕ) (c : Fin m → Over X),
      IsLogarithmicBoundaryTower D (X ↘ Spec (.of k)) T P c ∧
      Nonempty (IsLogarithmicBoundaryTower.OrderedFactorization D (X ↘ Spec (.of k)) T P c) := by
  have : IsReduced D.subscheme := hnodal.isReduced
  obtain ⟨m, c, hc⟩ :=
    (exists_logarithmicBoundaryTower_of_totalTransform_le_ramification hD hT h hnodal).2
  exact ⟨m, c, hc, hc.nonempty_orderedFactorization⟩

end IsClosedPointTower

end QPainleve.BlowupTower
