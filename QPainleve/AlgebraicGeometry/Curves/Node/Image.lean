/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Prestable
public import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.Basic

/-!
# Nodal images of prestable families

When the schematic image is nodal, properness and geometric connectedness
descend from a prestable source along the surjective map to the image.
-/

public section

open CategoryTheory Limits TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The nodal schematic image of a prestable family in a separated scheme over
the same base is prestable. -/
theorem prestableFamily_image {C Y S : Scheme.{u}} (f : C ⟶ Y) (s : Y ⟶ S)
    [IsSeparated s] [PrestableFamily (f ≫ s)]
    (hN : AtWorstNodalOfRelativeDimensionOne (f.imageι ≫ s)) :
    PrestableFamily (f.imageι ≫ s) := by
  have : IsProper f := .of_comp f s
  have : Surjective f.toImage :=
    ⟨f.toImage_surjective_of_isClosed_range f.isClosedMap.isClosed_range⟩
  have hcomp := f.toImage_imageι_assoc s
  have : IsProper (f.toImage ≫ f.imageι ≫ s) := hcomp.symm ▸ inferInstance
  have : UniversallyClosed (f.imageι ≫ s) := .of_comp_surjective f.toImage _
  have : LocallyOfFinitePresentation (f.imageι ≫ s) := hN.syntomic.locallyOfFinitePresentation
  refine { toIsProper := {}
           toGeometricallyConnected := ⟨?_⟩
           atWorstNodalOfRelativeDimensionOne := hN }
  have hconn : GeometricallyConnected (f.toImage ≫ f.imageι ≫ s) := hcomp.symm ▸ inferInstance
  intro K _ x P p q h
  let a := pullback.snd f.toImage p
  have : ConnectedSpace ↥(pullback f.toImage p) :=
    hconn.geometrically_connectedSpace x _ _ ((IsPullback.of_hasPullback _ _).paste_vert h)
  exact a.surjective.connectedSpace a.continuous

end AlgebraicGeometry.Scheme.Hom
