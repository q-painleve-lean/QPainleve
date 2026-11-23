/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Dual
public import TauCeti.AlgebraicGeometry.IdealSheaf.Image

/-!
# Zero ideals of maps of line bundles

The zero ideal of a map of line bundles is the image ideal after twisting by the
dual of the target. It is invariant under an isomorphic change of the source.
-/

public section

open AlgebraicGeometry CategoryTheory MonoidalCategory

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

universe u

/-- An isomorphic change of the source line bundle preserves the zero ideal of a map. -/
@[simp]
theorem imageIdealSheaf_twistedToUnit_comp_iso {X : Scheme.{u}} {L M N : InvertibleSheaf X}
    (e : L.obj ≅ M.obj) (f : M.obj ⟶ N.obj) :
    (L.twistedToUnit N (e.hom ≫ f)).imageIdealSheaf = (M.twistedToUnit N f).imageIdealSheaf := by
  let t := tensorRight (dual N).obj
  let e' := tensorProductObjIso L (dual N) ≪≫ t.mapIso e ≪≫
    (tensorProductObjIso M (dual N)).symm
  have he' : L.twistedToUnit N (e.hom ≫ f) = e'.hom ≫ M.twistedToUnit N f := by
    simp [e', t, twistedToUnit_def, comp_whiskerRight]
  rw [he']
  exact (M.twistedToUnit N f).imageIdealSheaf_comp_iso e'

end TauCeti.AlgebraicGeometry.InvertibleSheaf
