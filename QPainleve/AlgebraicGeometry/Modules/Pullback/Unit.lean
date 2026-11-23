/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic

/-!
# Pullback of morphisms into the structure sheaf

The pullback of a morphism into the structure sheaf uses the canonical unit
identification and is compatible with composition of scheme maps.
-/

public section

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}}

/-- The identification of the structure sheaf converts iterated pullback of a
morphism into the structure sheaf to pullback along the composite. -/
@[reassoc]
theorem pullbackComp_inv_app_map_toUnit (f : X ⟶ Y) (g : Y ⟶ Z)
    {M : Z.Modules} (φ : M ⟶ 𝟙_ Z.Modules) :
    (pullbackComp f g).inv.app M ≫
      (pullback f).map ((pullback g).map φ ≫ (pullbackObjUnitIso g).hom) ≫
        (pullbackObjUnitIso f).hom =
      (pullback (f ≫ g)).map φ ≫ (pullbackObjUnitIso (f ≫ g)).hom := by
  simp only [Functor.map_comp, Category.assoc, ← Functor.comp_map,
    ← (pullbackComp f g).inv.naturality_assoc φ, pullbackObjUnitIso_comp]

end AlgebraicGeometry.Scheme.Modules
