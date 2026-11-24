/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.StrictTransform
public import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.ClosedImmersion

/-!
# Strict transforms of regular curves

The strict transform of a regular integral curve in a point blowup maps
isomorphically onto the curve. The center restricts either to the unit ideal
or to the ideal of a reduced closed point of the curve.
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
