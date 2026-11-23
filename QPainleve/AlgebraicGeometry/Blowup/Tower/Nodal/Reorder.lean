/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Pullback
public import QPainleve.AlgebraicGeometry.Curves.Node.Locus

import QPainleve.AlgebraicGeometry.Blowup.Pullback
import QPainleve.AlgebraicGeometry.IdealSheaf.BaseChange
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import TauCeti.AlgebraicGeometry.Blowup.Restriction

/-!
# Moving a nodal blowup before an ordered boundary tower

A node of the strict boundary survives every blowup at a smooth point of the
fixed boundary. Its blowup can be performed first. The reordered tower uses
the same ordered center schemes and identifies the reduced boundary on the
common final scheme, even when a smooth center occurs more than once.

These are the two types of blowup in the logarithmic surface factorization of
[Lutz, Definition 8.1 and Theorem 8.4][Lutz].

[Lutz]: https://arxiv.org/pdf/2005.05010v3#page=68
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower

variable {X X' S : Scheme.{u}} {D : X.IdealSheafData} [IsReduced D.subscheme]

private theorem formallySmooth_stalkMap_lifted_center (s : X ⟶ S) (f : X' ⟶ X)
    {Z : Scheme.{u}} (a : Z ⟶ D.subscheme) (ha : Set.range (a ≫ D.subschemeι) ⊆ f.isoLocus)
    (b : Z ⟶ (D.comap f).radical.subscheme)
    (hb : b ≫ subschemeMap (D.comap f).radical D f
      (le_map_iff_comap_le.mpr (le_radical _)) = a) (x : Z)
    (hs : ((D.subschemeι ≫ s).stalkMap (a x)).hom.FormallySmooth) :
    (((D.comap f).radical.subschemeι ≫ f ≫ s).stalkMap (b x)).hom.FormallySmooth := by
  let d := subschemeMap (D.comap f).radical D f (le_map_iff_comap_le.mpr (le_radical _))
  have hpoint : d (b x) = a x := by rw [← Scheme.Hom.comp_apply, hb]
  have hloc : d (b x) ∈ d.isoLocus := by
    rw [hpoint]
    exact D.preimage_isoLocus_le_subschemeMap_radical f
      (D.subschemeι.mem_preimage.mpr (ha ⟨x, Scheme.Hom.comp_apply _ _ _⟩))
  have : IsIso (d.stalkMap (b x)) := d.isIso_stalkMap_of_mem_isoLocus hloc
  rw [← subschemeMap_subschemeι_assoc ((D.comap f).radical) D f _ s, Scheme.Hom.stalkMap_comp]
  exact (RingHom.FormallySmooth.respectsIso.cancel_right_isIso _ _).mpr (hpoint.symm ▸ hs)

/-- A closed node of the strict boundary after an ordered sequence of smooth
boundary blowups is the lift of a closed node on the original boundary. Blowing
up that original node first and transporting the ordered centers gives a
cartesian comparison with the original tower. Each transported center is
smooth on the reduced total boundary and has its original residue scheme.
The comparison matches the final reduced boundary ideals. -/
theorem exists_iso_nodal_blowup_alongBoundary (s : X ⟶ S) {n : ℕ}
    (p : Fin n → D.subscheme) (hp : ∀ j, IsClosed ({p j} : Set D.subscheme))
    (hC : ∀ j, (D.subscheme.fromSpecResidueField (p j)).ker.IsEffectiveCartier)
    (hs : ∀ j, ((D.subschemeι ≫ s).stalkMap (p j)).hom.FormallySmooth) :
    let a := fun j ↦ D.subscheme.fromSpecResidueField (p j)
    let A := alongBoundary D.subschemeι (fun j ↦ ⟨(a j).ker, hC j⟩)
    ∀ q : A.1, IsClosed ({q} : Set A.1) →
      A.2.boundaryι.ker.IsNodeOfReducedBoundary (A.2.toTower.toBase ≫ s) q →
      let x := A.2.toTower.toBase q
      let I := (X.fromSpecResidueField x).ker
      let J := (A.1.fromSpecResidueField q).ker
      let E := (D.comap I.blowupToBase).radical
      let d := subschemeMap E D I.blowupToBase (le_map_iff_comap_le.mpr (le_radical _))
      IsClosed ({x} : Set X) ∧ D.IsNodeOfReducedBoundary s x ∧
      ∃ (a' : ∀ j, Spec (D.subscheme.residueField (p j)) ⟶ E.subscheme)
        (hC' : ∀ j, (a' j).ker.IsEffectiveCartier),
        (∀ j, IsPullback (a' j) (𝟙 _) d (a j)) ∧
        (∀ j y, ((E.subschemeι ≫ I.blowupToBase ≫ s).stalkMap (a' j y)).hom.FormallySmooth) ∧
        let B := alongBoundary E.subschemeι (fun j ↦ ⟨(a' j).ker, hC' j⟩)
        ∃ e : B.1 ≅ J.blowup,
          IsPullback (e.hom ≫ J.blowupToBase) B.2.toTower.toBase
            A.2.toTower.toBase I.blowupToBase ∧
          ((A.2.boundaryι.ker.comap J.blowupToBase).radical).comap e.hom = B.2.boundaryι.ker := by
  intro a A q hq hnode
  let π := A.2.toTower.toBase
  let x := π q
  let I := (X.fromSpecResidueField x).ker
  let J := (A.1.fromSpecResidueField q).ker
  let f := I.blowupToBase
  have ha (j : Fin n) : IsClosedImmersion (a j) :=
    isClosed_singleton_iff_isClosedImmersion.mp (hp j)
  obtain ⟨z, hz, hn⟩ := (A.2.boundaryι.isNodeOfReducedBoundary_ker_iff _ q).mp hnode
  rw [WithBoundary.boundaryι_toBase_assoc] at hn
  have hx : D.subschemeι z = x := by rw [← A.2.boundaryι_toBase, Scheme.Hom.comp_apply, hz]
  have hxclosed : IsClosed ({x} : Set X) := by
    have hzclosed := A.2.boundaryι.isClosedEmbedding.isClosed_iff_image_isClosed.mpr
      (by simpa only [Set.image_singleton, hz] using hq : IsClosed (A.2.boundaryι '' {z}))
    simpa only [Set.image_singleton, hx] using
      D.subschemeι.isClosedEmbedding.isClosedMap _ hzclosed
  have hxnode : D.IsNodeOfReducedBoundary s x := by
    rw [← ker_subschemeι D]
    exact (D.subschemeι.isNodeOfReducedBoundary_ker_iff _ _).mpr ⟨z, hx, hn⟩
  have hne (j : Fin n) : D.subschemeι (p j) ≠ x := by
    intro he
    have hj := D.subschemeι.isClosedEmbedding.injective (he.trans hx.symm)
    exact hn.not_formallySmooth_stalkMap (hj ▸ hs j)
  have hI : (I.support : Set X) = {x} :=
    Scheme.support_ker_fromSpecResidueField_of_isClosed hxclosed
  have hg (j : Fin n) : Set.range (a j ≫ D.subschemeι) ⊆ f.isoLocus := by
    rintro _ ⟨y, rfl⟩
    apply f.le_isoLocus_iff.mpr I.isIso_blowupToBase_restrict_compl_support
    simpa only [Scheme.Hom.comp_apply, a, Scheme.fromSpecResidueField_apply,
      ← SetLike.mem_coe, Closeds.coe_compl, hI,
      Set.mem_compl_iff, Set.mem_singleton_iff] using hne j
  have hπ : x ∈ π.isoLocus := mem_isoLocus_toBase_alongBoundary _ _ fun j ↦ by
    rw [Scheme.support_ker_fromSpecResidueField_of_isClosed (hp j), Set.image_singleton]
    exact fun h ↦ hne j h.symm
  have hJ : I.comap π = J := π.comap_ker_fromSpecResidueField_of_mem_isoLocus hxclosed hπ
  have hpb := I.isPullback_blowupMap_of_support_subset_isoLocus π
    (by simpa only [hI, Set.singleton_subset_iff, SetLike.mem_coe] using hπ)
  obtain ⟨a', hC', ha', g, hg', -, hboundary⟩ := exists_isPullback_alongBoundary_radical D f a hC hg
  let e := hg'.isoIsPullback _ _ hpb ≪≫
    J.blowupIso (Iso.refl _) (by simpa only [Iso.refl_hom, comap_id] using hJ.symm)
  have he : e.hom ≫ J.blowupToBase = g := by
    simp only [e, Iso.trans_hom, Category.assoc, blowupIso_hom_blowupToBase, Iso.refl_hom,
      Category.comp_id]
    exact hg'.isoIsPullback_hom_fst _ _ hpb
  refine ⟨hxclosed, hxnode, a', hC', ha', fun j y ↦ ?_, e, he.symm ▸ hg', ?_⟩
  · have hy : a j y = p j := Scheme.fromSpecResidueField_apply (p j) y
    exact formallySmooth_stalkMap_lifted_center s f (a j) (hg j) (a' j)
      (by simpa only [Category.id_comp] using (ha' j).w) y (hy.symm ▸ hs j)
  · rw [← radical_comap_of_isOpenImmersion, ← comap_comp, he]
    exact hboundary

end QPainleve.BlowupTower
