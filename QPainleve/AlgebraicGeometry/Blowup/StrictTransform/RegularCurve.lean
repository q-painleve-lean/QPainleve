/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform
public import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.ClosedImmersion
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Stalk
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Strict transforms of regular curves

The strict transform of a regular integral curve in a point blowup maps
isomorphically onto the curve. The center restricts either to the unit ideal
or to the ideal of a reduced closed point of the curve. Iterating gives the
same comparison for a tower of point blowups.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The blowup projection induces an isomorphism from the strict transform of
a regular irreducible curve to that curve. -/
theorem exists_iso_strictTransform_of_regularCurve
    {X : Scheme.{u}} (C : X.IdealSheafData)
    [IrreducibleSpace C.subscheme] [TauCeti.AlgebraicGeometry.IsRegular C.subscheme]
    (hdim : topologicalKrullDim C.subscheme = 1)
    {p : X} (hp : IsClosed ({p} : Set X)) :
    let I := (X.fromSpecResidueField p).ker
    let C' := (I.blowupMap C.subschemeι).ker
    ∃ e : C'.subscheme ≅ C.subscheme, e.hom ≫ C.subschemeι = C'.subschemeι ≫ I.blowupToBase := by
  let I := (X.fromSpecResidueField p).ker
  have hcart := C.subschemeι.isEffectiveCartier_comap_ker_fromSpecResidueField hdim hp
  have : IsIso (I.comap C.subschemeι).blowupToBase :=
    (isIso_blowupToBase_iff _).mpr hcart
  let j := I.blowupMap C.subschemeι
  refine ⟨(asIso j.toImage).symm ≪≫ asIso (I.comap C.subschemeι).blowupToBase, ?_⟩
  have hj : (I.comap C.subschemeι).blowupToBase ≫ C.subschemeι = j ≫ I.blowupToBase :=
    (I.blowupMap_blowupToBase C.subschemeι).symm
  calc
    _ = inv j.toImage ≫ (j ≫ I.blowupToBase) := by
      rw [Iso.trans_hom, Category.assoc, asIso_hom, hj]
      rfl
    _ = inv j.toImage ≫ (j.toImage ≫ j.ker.subschemeι) ≫ I.blowupToBase :=
      congrArg (fun g ↦ inv j.toImage ≫ g ≫ I.blowupToBase) j.toImage_imageι.symm
    _ = _ := by rw [Category.assoc, IsIso.inv_hom_id_assoc]

end AlgebraicGeometry.Scheme.IdealSheafData

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {X Y : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y} {C : X.IdealSheafData}
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

variable {k : Type u} [Field k] [PerfectField k] [IsIntegral X] [IsNoetherian X]

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
