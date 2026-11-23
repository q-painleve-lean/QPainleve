/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Quasicoherent

/-!
# Tensor products of pullback trivializations

The tensor comparison for pullback combines two trivializations over the same base.
It is compatible with pulling back the tensor of two morphisms to the structure sheaf.
-/

public noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {M N : Y.Modules}

/-- The tensor product of two trivializations of pulled-back modules. -/
def pullbackTensorTrivialization [M.IsQuasicoherent]
    (e : (pullback f).obj M ≅ 𝟙_ X.Modules) (d : (pullback f).obj N ≅ 𝟙_ X.Modules) :
    (pullback f).obj (M ⊗ N) ≅ 𝟙_ X.Modules :=
  asIso (Functor.OplaxMonoidal.δ (pullback f) M N) ≪≫ tensorIso e d ≪≫ λ_ _

/-- The forward morphism of the tensor product trivialization. -/
@[simp]
theorem pullbackTensorTrivialization_hom [M.IsQuasicoherent]
    (e : (pullback f).obj M ≅ 𝟙_ X.Modules) (d : (pullback f).obj N ≅ 𝟙_ X.Modules) :
    (pullbackTensorTrivialization f e d).hom =
      Functor.OplaxMonoidal.δ (pullback f) M N ≫ (e.hom ⊗ₘ d.hom) ≫ (λ_ _).hom :=
  (rfl)

open Functor.OplaxMonoidal in
/-- Pulling back a tensor of morphisms to the structure sheaf agrees with tensoring
the pulled-back morphisms and applying the structure-sheaf comparison. -/
theorem pullback_tensorFrame {W T : Scheme.{u}} (p : T ⟶ W)
    {A B : W.Modules} (e : A ⟶ 𝟙_ W.Modules) (d : B ⟶ 𝟙_ W.Modules) :
    (pullback p).map ((e ⊗ₘ d) ≫ (λ_ _).hom) ≫ (pullbackObjUnitIso p).hom =
      δ (pullback p) A B ≫
        (((pullback p).map e ≫ (pullbackObjUnitIso p).hom) ⊗ₘ
          ((pullback p).map d ≫ (pullbackObjUnitIso p).hom)) ≫ (λ_ _).hom := by
  simp only [← tensorHom_comp_tensorHom, δ_natural_assoc, Functor.map_comp, Category.assoc]
  rw [← pullback_η]
  rw [δ_comp_η_tensorHom_assoc, leftUnitor_naturality, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Scheme.Modules
