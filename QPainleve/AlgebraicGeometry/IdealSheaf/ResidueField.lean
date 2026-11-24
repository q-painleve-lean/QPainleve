/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.ResidueField
public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus

import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import TauCeti.AlgebraicGeometry.ResidueField

/-!
# The ideal sheaf of the closure of a point

A morphism from a reduced scheme gives its schematic image the reduced structure.
The kernel of a field-valued point thus defines the reduced closure of the point.
This identifies the reduced-center and residue-field descriptions of point blowups.
The reduced closed point ideal pulls back to a reduced closed point ideal along a
morphism that is an isomorphism over a neighborhood of the point.
-/

public section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- A reduced source determines the reduced scheme structure on its schematic image. -/
theorem Hom.ker_eq_vanishingIdeal_support {X Y : Scheme} (f : X ⟶ Y) [IsReduced X] :
    f.ker = IdealSheafData.vanishingIdeal f.ker.support :=
  le_antisymm (by rw [IdealSheafData.vanishingIdeal_support]; exact f.ker.le_radical)
    (IdealSheafData.vanishingIdeal_le_ker_of_range_subset f f.range_subset_ker_support)

/-- A map from a reduced scheme with image in a reduced closed section factors
as its map to the base followed by the section. -/
theorem Hom.eq_comp_of_range_subset_of_section {C T S : Scheme} [IsReduced C] [IsReduced S]
    (a : C ⟶ T) (q : T ⟶ S) (r : S ⟶ T) [IsClosedImmersion r] (hr : r ≫ q = 𝟙 S)
    (ha : Set.range a ⊆ Set.range r) : a = a ≫ q ≫ r := by
  have hker : r.ker ≤ a.ker := by
    rw [r.ker_eq_vanishingIdeal_support]
    exact IdealSheafData.vanishingIdeal_le_ker_of_range_subset a
      (ha.trans r.range_subset_ker_support)
  let b := IsClosedImmersion.lift r a hker
  have hba : b ≫ r = a := IsClosedImmersion.lift_fac _ _ _
  have hb : b = a ≫ q := by simp only [← hba, Category.assoc, hr, Category.comp_id]
  simpa only [Category.assoc] using hba.symm.trans (congrArg (· ≫ r) hb)

/-- The kernel of a residue-field morphism is the vanishing ideal of the closure of its point. -/
theorem ker_fromSpecResidueField_eq_vanishingIdeal {X : Scheme} (p : X) :
    (X.fromSpecResidueField p).ker =
      IdealSheafData.vanishingIdeal ⟨closure {p}, isClosed_closure⟩ := by
  have : QuasiCompact (X.fromSpecResidueField p) :=
    ⟨fun U _ _ ↦ (Set.toFinite ((X.fromSpecResidueField p) ⁻¹' U)).isCompact⟩
  rw [Hom.ker_eq_vanishingIdeal_support]
  congr 1
  apply SetLike.coe_injective
  rw [Hom.support_ker, range_fromSpecResidueField]
  rfl

/-- The residue-field kernel of a closed point is supported exactly at that point. -/
theorem support_ker_fromSpecResidueField_of_isClosed {X : Scheme} {p : X}
    (hp : IsClosed ({p} : Set X)) : ((X.fromSpecResidueField p).ker.support : Set X) = {p} := by
  rw [ker_fromSpecResidueField_eq_vanishingIdeal, IdealSheafData.coe_support_vanishingIdeal,
    Closeds.coe_mk, hp.closure_eq]

/-- A field-valued point has the same kernel ideal as the map from its residue field. -/
theorem Hom.ker_eq_ker_fromSpecResidueField {k : Type*} [Field k]
    {X : Scheme} (s : Spec (.of k) ⟶ X) :
    s.ker = (X.fromSpecResidueField (s (IsLocalRing.closedPoint k))).ker := by
  have : QuasiCompact s := ⟨fun U _ _ ↦ (Set.toFinite (s ⁻¹' U)).isCompact⟩
  have hrange : Set.range s = {s (IsLocalRing.closedPoint k)} :=
    Set.range_eq_singleton fun z ↦ congrArg s (Subsingleton.elim z _)
  rw [s.ker_eq_vanishingIdeal_support, ker_fromSpecResidueField_eq_vanishingIdeal]
  congr 1
  apply SetLike.coe_injective
  rw [s.support_ker, hrange]
  rfl

/-- Reduced point ideals distinguish points of a scheme. -/
@[simp]
theorem ker_fromSpecResidueField_inj {X : Scheme} {p q : X} :
    (X.fromSpecResidueField p).ker = (X.fromSpecResidueField q).ker ↔ p = q := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  have hs := congrArg (fun I : X.IdealSheafData ↦ (I.support : Set X)) h
  simp only [ker_fromSpecResidueField_eq_vanishingIdeal, IdealSheafData.coe_support_vanishingIdeal,
    Closeds.coe_mk] at hs
  exact ((specializes_iff_closure_subset.mpr hs.ge).antisymm
    (specializes_iff_closure_subset.mpr hs.le)).eq

/-- A closed immersion maps a reduced point ideal to the reduced ideal of its image point. -/
@[simp]
theorem Hom.map_ker_fromSpecResidueField {X Y : Scheme} (i : X ⟶ Y) [IsClosedImmersion i]
    (p : X) : (X.fromSpecResidueField p).ker.map i = (Y.fromSpecResidueField (i p)).ker := by
  rw [IdealSheafData.map_ker, ← i.SpecMap_residueFieldMap_fromSpecResidueField p,
    Hom.ker_comp_of_isIso]

/-- Pulling back a reduced point ideal along the closed immersion containing the point
recovers the reduced point ideal on the closed subscheme. -/
@[simp]
theorem Hom.comap_ker_fromSpecResidueField_apply {X Y : Scheme} (i : X ⟶ Y) [IsClosedImmersion i]
    (p : X) : (Y.fromSpecResidueField (i p)).ker.comap i = (X.fromSpecResidueField p).ker := by
  rw [← i.map_ker_fromSpecResidueField, IdealSheafData.comap_map_of_isClosedImmersion]

/-- Over an open on which a morphism is an isomorphism, the inverse image of a reduced
closed point is a reduced closed point, with its residue-field ideal. -/
theorem Hom.exists_comap_ker_fromSpecResidueField_of_isIso_morphismRestrict
    {X Y : Scheme} (f : Y ⟶ X) (p : X) (hp : IsClosed ({p} : Set X))
    (U : X.Opens) (hU : p ∈ U) [IsIso (f ∣_ U)] :
    ∃ q : Y, IsClosed ({q} : Set Y) ∧ f q = p ∧
      (X.fromSpecResidueField p).ker.comap f = (Y.fromSpecResidueField q).ker := by
  let s := X.fromSpecResidueField p
  have : IsClosedImmersion s := isClosed_singleton_iff_isClosedImmersion.mp hp
  let t := IsOpenImmersion.lift U.ι s (by
    simpa [s, Scheme.range_fromSpecResidueField, hp.closure_eq, Scheme.Opens.range_ι] using hU)
  let g := f ∣_ U
  let a := t ≫ inv g ≫ (f ⁻¹ᵁ U).ι
  have hsmall : IsPullback (t ≫ inv g) (𝟙 _) g t :=
    .of_vert_isIso ⟨by simp⟩
  have hpb : IsPullback a (𝟙 _) f s := by
    simpa only [a, Category.assoc, IsOpenImmersion.lift_fac, t] using
      hsmall.paste_horiz (isPullback_morphismRestrict f U).flip
  have : IsClosedImmersion a := MorphismProperty.of_isPullback hpb.flip inferInstance
  let x := IsLocalRing.closedPoint (X.residueField p)
  let q := a x
  have hrange : Set.range a = {q} := Set.range_eq_singleton fun y ↦
    congrArg a (Subsingleton.elim y x)
  refine ⟨q, hrange ▸ a.isClosedEmbedding.isClosed_range, ?_, ?_⟩
  · calc
      f q = (a ≫ f) x := (Hom.comp_apply _ _ _).symm
      _ = (𝟙 _ ≫ s) x := congrArg (fun m : _ ⟶ X ↦ m x) hpb.w
      _ = p := by
        rw [Category.id_comp]
        exact fromSpecResidueField_apply p x
  · rw [← IdealSheafData.ker_fst_of_isClosedImmersion s f]
    calc
      (pullback.fst f s).ker = (hpb.isoPullback.hom ≫ pullback.fst f s).ker :=
        (Hom.ker_comp_of_isIso _ _).symm
      _ = a.ker := congrArg Hom.ker hpb.isoPullback_hom_fst
      _ = _ := a.ker_eq_ker_fromSpecResidueField

/-- If a point lies over a closed point in the isomorphism locus, its residue-field
ideal is the inverse image of the ideal of that closed point. -/
theorem Hom.comap_ker_fromSpecResidueField_of_mem_isoLocus {X Y : Scheme}
    (f : Y ⟶ X) {q : Y} (hq : IsClosed ({f q} : Set X)) (hqU : f q ∈ f.isoLocus) :
    (X.fromSpecResidueField (f q)).ker.comap f = (Y.fromSpecResidueField q).ker := by
  have : IsIso (f ∣_ f.isoLocus) := f.le_isoLocus_iff.mp le_rfl
  obtain ⟨q', -, hq', hker⟩ := f.exists_comap_ker_fromSpecResidueField_of_isIso_morphismRestrict
    (f q) hq _ hqU
  have hx' : f q' ∈ f.isoLocus := hq'.symm ▸ hqU
  have heq : q' = q := f.injOn_preimage_isoLocus hx' hqU hq'
  subst q'
  exact hker

/-- An ideal vanishes on a closed point exactly when its support contains that point. -/
theorem IdealSheafData.le_ker_fromSpecResidueField_iff_mem_support {X : Scheme}
    (D : X.IdealSheafData) {p : X}
    (hp : IsClosed ({p} : Set X)) :
    D ≤ (X.fromSpecResidueField p).ker ↔ p ∈ D.support := by
  rw [ker_fromSpecResidueField_eq_vanishingIdeal, ← IdealSheafData.le_support_iff_le_vanishingIdeal]
  rw [← SetLike.coe_subset_coe, Closeds.coe_mk, hp.closure_eq, Set.singleton_subset_iff]
  rfl

end AlgebraicGeometry.Scheme
