/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.Basic
public import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme

import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.RegularCurve
import QPainleve.AlgebraicGeometry.Blowup.Tower.IsoLocus
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Stalk
import QPainleve.AlgebraicGeometry.IdealSheaf.ClosedImmersion
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange

/-!
# Strict transforms of regular curves in point blowup towers

The iterated strict transform of a regular irreducible curve is isomorphic to
the original curve. Isomorphisms of the final surfaces over the original smooth
surface identify their strict transforms. On a smooth surface the strict
transform has stalk order one on its support.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {X Y Z : Scheme.{u}} {n m : ℕ} {T : BlowupTower X n Y} {U : BlowupTower X m Z}
  {C : X.IdealSheafData} {k : Type u} [Field k] [PerfectField k]
  (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 f]
  [IrreducibleSpace C.subscheme] [TauCeti.AlgebraicGeometry.IsRegular C.subscheme]

/-- The projection of a closed point blowup tower induces an isomorphism from the
iterated strict transform of a regular irreducible curve to the original curve. -/
theorem exists_iso_strictTransform_regularCurve (hT : IsClosedPointTower X T)
    (hdim : topologicalKrullDim C.subscheme = 1) :
    ∃ e : (T.strictTransform C).subscheme ≅ C.subscheme,
      e.hom ≫ C.subschemeι = (T.strictTransform C).subschemeι ≫ T.toBase := by
  induction hT with
  | nil =>
    rw [strictTransform_nil, toBase_nil, Category.comp_id]
    exact ⟨Iso.refl _, Category.id_comp _⟩
  | @snoc d W U I hU p hp hI ih =>
    obtain ⟨e, he⟩ := ih
    have : IrreducibleSpace (U.strictTransform C).subscheme :=
      e.hom.homeomorph.irreducibleSpace_iff.mpr inferInstance
    have : TauCeti.AlgebraicGeometry.IsRegular (U.strictTransform C).subscheme :=
      IsRegular.of_isOpenImmersion e.hom
    have hdim' : topologicalKrullDim (U.strictTransform C).subscheme = 1 :=
      e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq.trans hdim
    subst I
    obtain ⟨g, hg⟩ := (U.strictTransform C).exists_iso_strictTransform_of_regularCurve hdim' hp
    rw [strictTransform_snoc]
    refine ⟨g ≪≫ e, ?_⟩
    rw [Iso.trans_hom, Category.assoc, he, reassoc_of% hg, toBase_snoc]

omit [TauCeti.AlgebraicGeometry.IsRegular C.subscheme] in
include f in
private theorem genericPoint_mem_isoLocus (hU : IsClosedPointTower X U)
    (hdim : topologicalKrullDim C.subscheme = 1) :
    C.subschemeι (genericPoint C.subscheme) ∈ U.toBase.isoLocus := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  by_contra h
  have hm : C.subschemeι (genericPoint C.subscheme) ∈ U.toBase.centre := by
    simpa only [Scheme.Hom.centre_def, Set.mem_compl_iff, SetLike.mem_coe] using h
  rw [hU.centre_toBase_eq_range_baseCenter f] at hm
  obtain ⟨j, hj⟩ := hm
  have hclosed : IsClosed ({genericPoint C.subscheme} : Set C.subscheme) := by
    rw [← Set.preimage_image_eq {genericPoint C.subscheme} C.subschemeι.isClosedEmbedding.injective,
      Set.image_singleton, ← hj]
    exact (hU.isClosed_baseCenter j).preimage C.subschemeι.continuous
  have hsingle : ({genericPoint C.subscheme} : Set C.subscheme) = Set.univ :=
    hclosed.closure_eq.symm.trans (genericPoint_spec C.subscheme).def
  have : Subsingleton C.subscheme := Set.subsingleton_univ_iff.mp
    (hsingle ▸ Set.subsingleton_singleton)
  have hzero := TauCeti.topologicalKrullDim_eq_zero_iff_subsingleton.mpr this
  exact zero_ne_one (hzero.symm.trans hdim)

open Scheme.IdealSheafData in
include f in
/-- An isomorphism between the final surfaces of two closed point towers over the
same smooth surface identifies the strict transforms of a regular irreducible
curve as closed subschemes. -/
theorem comap_strictTransform_eq_of_iso_over
    (hT : IsClosedPointTower X T) (hU : IsClosedPointTower X U) (e : Y ≅ Z)
    (he : e.hom ≫ U.toBase = T.toBase) (hdim : topologicalKrullDim C.subscheme = 1) :
    (U.strictTransform C).comap e.hom = T.strictTransform C := by
  obtain ⟨a, ha⟩ := hT.exists_iso_strictTransform_regularCurve hdim
  obtain ⟨b, hb⟩ := hU.exists_iso_strictTransform_regularCurve hdim
  let s := a.inv ≫ (T.strictTransform C).subschemeι ≫ e.hom
  let t := b.inv ≫ (U.strictTransform C).subschemeι
  have hs : s ≫ U.toBase = C.subschemeι := by
    simp only [s, Category.assoc, he, ← ha, Iso.inv_hom_id_assoc]
  have ht : t ≫ U.toBase = C.subschemeι := by
    simp only [t, Category.assoc, ← hb, Iso.inv_hom_id_assoc]
  have hx := genericPoint_mem_isoLocus f hU hdim
  have hsη : U.toBase (s (genericPoint C.subscheme)) = C.subschemeι (genericPoint C.subscheme) :=
    congrArg (fun g : C.subscheme ⟶ X ↦ g (genericPoint C.subscheme)) hs
  have htη : U.toBase (t (genericPoint C.subscheme)) = C.subschemeι (genericPoint C.subscheme) :=
    congrArg (fun g : C.subscheme ⟶ X ↦ g (genericPoint C.subscheme)) ht
  have hsU : s (genericPoint C.subscheme) ∈ U.toBase ⁻¹' (U.toBase.isoLocus : Set X) := by
    rwa [Set.mem_preimage, hsη]
  have htU : t (genericPoint C.subscheme) ∈ U.toBase ⁻¹' (U.toBase.isoLocus : Set X) := by
    rwa [Set.mem_preimage, htη]
  have hη := U.toBase.injOn_preimage_isoLocus hsU htU (hsη.trans htη.symm)
  have : IsIntegral C.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have : IsClosedImmersion s := inferInstanceAs (IsClosedImmersion
    (a.inv ≫ (T.strictTransform C).subschemeι ≫ e.hom))
  have : IsClosedImmersion t := inferInstanceAs (IsClosedImmersion
    (b.inv ≫ (U.strictTransform C).subschemeι))
  have hk : s.ker = t.ker := by
    rw [s.ker_eq_vanishingIdeal_closure_genericPoint,
      t.ker_eq_vanishingIdeal_closure_genericPoint, hη]
  have hk' : ((T.strictTransform C).subschemeι ≫ e.hom).ker = U.strictTransform C := by
    simpa only [s, t, Scheme.Hom.ker_comp_of_isIso, ker_subschemeι] using hk
  rw [← hk', Scheme.Hom.comap_ker_comp_of_isClosedImmersion, ker_subschemeι]

variable [IsIntegral X] [IsNoetherian X]

/-- At each point of its support, the strict transform of a regular curve has
stalk order one on the smooth blown-up surface. -/
theorem stalkOrder_strictTransform_eq_one_of_mem_support
    (hT : IsClosedPointTower X T) (g : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 g]
    (hC : C.IsEffectiveCartier) (hdim : topologicalKrullDim C.subscheme = 1)
    {p : Y} (hp : p ∈ ((T.strictTransform C).support : Set Y)) :
    (T.strictTransform C).stalkOrder p = 1 := by
  let C' := T.strictTransform C
  have h := hT.isEffectiveCartier_strictTransform g hC
  obtain ⟨e, -⟩ := hT.exists_iso_strictTransform_regularCurve hdim
  have : TauCeti.AlgebraicGeometry.IsRegular C'.subscheme := IsRegular.of_isOpenImmersion e.hom
  have : Smooth (T.toBase ≫ g) := (hT.smoothOfRelativeDimension g).smooth
  obtain ⟨q, hq⟩ := C'.range_subschemeι.symm ▸ hp
  have := isRegularLocalRing_stalk_of_smooth (T.toBase ≫ g) (C'.subschemeι q)
  rw [← hq]
  exact (h.stalkOrder_eq_one_iff_isRegularLocalRing q).mpr inferInstance

end QPainleve.BlowupTower.IsClosedPointTower
