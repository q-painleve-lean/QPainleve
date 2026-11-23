/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Branches.Basic
public import QPainleve.AlgebraicGeometry.IdealSheaf.Stalk

import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.AlgebraicGeometry.ResidueField

/-!
# The intersection of the strict transform with the exceptional divisor

At a closed node, the scheme-theoretic intersection of the strict transform with
the exceptional divisor is finite étale over the residue field of the center.
This provides the reduced intersection used when the exceptional divisor is
included in the transformed boundary.
-/

public section

open CategoryTheory Limits TopologicalSpace TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The intersection of the strict transform of a nodal curve with the exceptional
divisor at a closed node is finite étale over the residue field of the center.
Its structure map factors the ambient blowup projection to the original scheme. -/
theorem exists_finite_etale_strictTransform_exceptional_intersection
    {k : Type u} [Field k] {D X : Scheme.{u}} [D.Over (Spec (.of k))]
    (i : D ⟶ X) [IsClosedImmersion i]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (D ↘ Spec (.of k))) {p : D}
    (hp : (let := hnodal.syntomic; p ∈ (D.singularLocus k).support))
    (hc : IsClosed ({i p} : Set X)) :
    let I := vanishingIdeal (Closeds.closure ({i p} : Set X))
    let j := I.blowupMap i
    let J := j.ker ⊔ I.comap I.blowupToBase
    ∃ g : J.subscheme ⟶ Spec (X.residueField (i p)),
      IsFinite g ∧ Etale g ∧
        g ≫ X.fromSpecResidueField (i p) = J.subschemeι ≫ I.blowupToBase := by
  let := hnodal.syntomic
  let q := i p
  let I := vanishingIdeal (Closeds.closure ({q} : Set X))
  let j := I.blowupMap i
  let π := I.blowupToBase
  let s := X.fromSpecResidueField q
  let f := j ≫ π
  let J := j.ker ⊔ I.comap π
  let b := f.fiberι q
  have : IsClosedImmersion s := isClosed_singleton_iff_isClosedImmersion.mp hc
  have : IsClosedImmersion b := MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback f s).flip inferInstance
  have hb : b.ker = s.ker.comap f := ker_fst_of_isClosedImmersion s f
  have hf : f = j ≫ π := rfl
  have hs : s.ker = I := X.ker_fromSpecResidueField_eq_vanishingIdeal q
  have hker : (b ≫ j).ker = J := by
    rw [Scheme.Hom.ker_comp, hb, hf, hs, comap_comp, map_comap_of_isClosedImmersion, sup_comm]
  let e := asIso (b ≫ j).toImage
  let e' : f.fiber q ≅ J.subscheme :=
    e ≪≫ eqToIso (congrArg subscheme hker)
  have he : e'.hom ≫ J.subschemeι = b ≫ j := by
    dsimp only [e', Iso.trans_hom, eqToIso.hom]
    rw [Category.assoc, ← eqToHom_naturality IdealSheafData.subschemeι hker]
    simp [e]
  obtain ⟨hfin, het⟩ :=
    D.isFinite_etale_fiberToSpecResidueField_blowup_singularLocus_of_node hnodal hp
  obtain ⟨a⟩ := nonempty_fiberToSpecResidueFieldIso_strictTransform_of_node i hnodal hp
  let t := (D.singularLocus k).blowupToBase.fiberToSpecResidueField p
  have : IsFinite t := hfin
  have : Etale t := het
  let a' : f.fiber q ≅ (D.singularLocus k).blowupToBase.fiber p :=
    (Over.forget _).mapIso a
  have hw : a'.hom ≫ t ≫ Spec.map (i.residueFieldMap p) = f.fiberToSpecResidueField q :=
    Over.w a.hom
  have : IsFinite (f.fiberToSpecResidueField q) := hw ▸ inferInstance
  have : Etale (f.fiberToSpecResidueField q) := hw ▸ inferInstance
  refine ⟨e'.inv ≫ f.fiberToSpecResidueField q, inferInstance, inferInstance, ?_⟩
  calc
    (e'.inv ≫ f.fiberToSpecResidueField q) ≫ s = e'.inv ≫ (b ≫ f) := by
      rw [Category.assoc, f.fiber_fac]
    _ = e'.inv ≫ (b ≫ j) ≫ π := by rw [Category.assoc]
    _ = J.subschemeι ≫ π := by
      rw [← he, ← Category.assoc, e'.inv_hom_id_assoc]

/-- Each attachment point is closed, and its strict and exceptional ideals generate
the ambient maximal ideal. In a smooth surface this is the transversality of the
two branches of the reduced total transform. -/
theorem stalkIdeal_sup_eq_maximalIdeal_strictTransform_exceptional
    {k : Type u} [Field k] {D X : Scheme.{u}} [D.Over (Spec (.of k))]
    (i : D ⟶ X) [IsClosedImmersion i]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (D ↘ Spec (.of k))) {p : D}
    (hp : (let := hnodal.syntomic; p ∈ (D.singularLocus k).support))
    (hc : IsClosed ({i p} : Set X)) :
    let I := vanishingIdeal (Closeds.closure ({i p} : Set X))
    let S := (I.blowupMap i).ker
    let E := I.comap I.blowupToBase
    ∀ x : I.blowup, x ∈ (S ⊔ E).support →
      IsClosed ({x} : Set I.blowup) ∧
        S.stalkIdeal x ⊔ E.stalkIdeal x = IsLocalRing.maximalIdeal (I.blowup.presheaf.stalk x) := by
  let I := vanishingIdeal (Closeds.closure ({i p} : Set X))
  let S := (I.blowupMap i).ker
  let E := I.comap I.blowupToBase
  let J := S ⊔ E
  obtain ⟨g, _, _, _⟩ := exists_finite_etale_strictTransform_exceptional_intersection i hnodal hp hc
  have : IsLocallyArtinian J.subscheme := .of_locallyQuasiFinite g
  have : IsRegular J.subscheme := IsRegular.of_smooth g
  dsimp only
  intro x hx
  obtain ⟨z, rfl⟩ := J.range_subschemeι.ge hx
  refine ⟨?_, (stalkIdeal_sup _ _ _).symm.trans
    (J.stalkIdeal_eq_maximalIdeal_of_isLocallyArtinian hx)⟩
  simpa only [Set.image_singleton] using
    J.subschemeι.isClosedEmbedding.isClosedMap {z} (isClosed_discrete _)

end AlgebraicGeometry.Scheme.IdealSheafData
