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

section RightTrivialization

variable {X Y Z : Scheme.{u}}

/-- Tensor a comparison of two pulled-back modules with a common factor, then evaluate
the target tensor product using a trivialization on the base. -/
def pullbackTensorRightTrivialization (f : Y ⟶ X) {L M K : X.Modules}
    [L.IsQuasicoherent] [M.IsQuasicoherent]
    (a : (pullback f).obj L ≅ (pullback f).obj M) (e : M ⊗ K ≅ 𝟙_ X.Modules) :
    (pullback f).obj (L ⊗ K) ≅ 𝟙_ Y.Modules :=
  asIso (Functor.OplaxMonoidal.δ (pullback f) L K) ≪≫
    tensorIso a (Iso.refl _) ≪≫ (asIso (Functor.OplaxMonoidal.δ (pullback f) M K)).symm ≪≫
    (pullback f).mapIso e ≪≫ pullbackObjUnitIso f

/-- The tensor comparison in a pulled-back right tensor trivialization. -/
@[simp]
theorem pullbackTensorRightTrivialization_hom (f : Y ⟶ X) {L M K : X.Modules}
    [L.IsQuasicoherent] [M.IsQuasicoherent]
    (a : (pullback f).obj L ≅ (pullback f).obj M) (e : M ⊗ K ≅ 𝟙_ X.Modules) :
    (pullbackTensorRightTrivialization f a e).hom =
      Functor.OplaxMonoidal.δ (pullback f) L K ≫ (a.hom ▷ (pullback f).obj K) ≫
        inv (Functor.OplaxMonoidal.δ (pullback f) M K) ≫
          (pullback f).map e.hom ≫ (pullbackObjUnitIso f).hom := by
  simp [pullbackTensorRightTrivialization, tensorHom_def]

open Functor.OplaxMonoidal in
/-- Pulling back a tensor trivialization from a comparison on an intermediate scheme. -/
theorem pullbackTensorRightTrivialization_comp_hom (g : Z ⟶ Y) (f : Y ⟶ X)
    {L M K : X.Modules} [L.IsQuasicoherent] [M.IsQuasicoherent]
    (a : (pullback f).obj L ≅ (pullback f).obj M) (e : M ⊗ K ≅ 𝟙_ X.Modules) :
    (pullbackComp g f).inv.app (L ⊗ K) ≫
      (pullback g).map (pullbackTensorRightTrivialization f a e).hom ≫
        (pullbackObjUnitIso g).hom =
    (pullbackTensorRightTrivialization (g ≫ f)
      (((pullbackComp g f).app L).symm ≪≫ (pullback g).mapIso a ≪≫
        (pullbackComp g f).app M) e).hom := by
  let c := pullbackComp g f
  have hunit : (pullback g).map (pullbackObjUnitIso f).hom ≫ (pullbackObjUnitIso g).hom =
      c.hom.app (𝟙_ X.Modules) ≫ (pullbackObjUnitIso (g ≫ f)).hom := by
    rw [← pullbackObjUnitIso_comp]
    simp [c]
  have hnat := c.hom.naturality_assoc e.hom (pullbackObjUnitIso (g ≫ f)).hom
  simp only [Functor.comp_map] at hnat
  simp only [pullbackTensorRightTrivialization_hom, Iso.trans_hom, Iso.symm_hom,
    Iso.app_inv, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [hunit, hnat]
  simp only [← Category.assoc, cancel_mono]
  -- Compose both sides with the target tensor comparison to remove its inverse.
  apply (cancel_mono (δ (pullback (g ≫ f)) M K)).mp
  have hc := inv_δ_comp_pullbackComp_hom_app g f M K
  have hc' : (pullback g).map (inv (δ (pullback f) M K)) ≫
      c.hom.app (M ⊗ K) ≫ δ (pullback (g ≫ f)) M K =
        δ (pullback g) _ _ ≫ (c.hom.app M ⊗ₘ c.hom.app K) := by
    apply (cancel_epi (inv (δ (pullback g) ((pullback f).obj M) ((pullback f).obj K)))).mp
    simpa only [Category.assoc, IsIso.inv_hom_id, IsIso.inv_hom_id_assoc,
      Category.comp_id, c] using congrArg (· ≫ δ (pullback (g ≫ f)) M K) hc
  simp only [Category.assoc]
  rw [hc', pullback_comp_δ]
  simp only [← tensorHom_id, ← δ_natural_assoc, Category.assoc]
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom_assoc]
  simp [c]

/-- A change of the morphism by equality transports tensor trivializations along the
canonical comparison of the pullback functors. -/
theorem pullbackTensorRightTrivialization_congr_hom {f f' : Y ⟶ X} (h : f = f')
    {L M K : X.Modules} [L.IsQuasicoherent] [M.IsQuasicoherent]
    (a : (pullback f').obj L ≅ (pullback f').obj M) (e : M ⊗ K ≅ 𝟙_ X.Modules) :
    (pullbackCongr h).hom.app (L ⊗ K) ≫ (pullbackTensorRightTrivialization f' a e).hom =
      (pullbackTensorRightTrivialization f
        ((pullbackCongr h).app L ≪≫ a ≪≫ ((pullbackCongr h).app M).symm) e).hom := by
  subst f'
  simp [pullbackCongr]

end RightTrivialization

end AlgebraicGeometry.Scheme.Modules
