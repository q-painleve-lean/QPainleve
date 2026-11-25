/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.VectorBundle.OpenCover

import QPainleve.AlgebraicGeometry.Modules.Pushforward.BaseChange
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Recovering finite locally free sheaves from their pullbacks

If pullback identifies regular functions on each open with those on its inverse image,
the unit of pullback and pushforward is an isomorphism on finite locally free sheaves.
The unit gives a comparison natural in maps of the sheaves. The local reduction
to finite free sheaves follows the degree-zero projection argument in the
[Stacks Project, Lemma 20.54.2](https://stacks.math.columbia.edu/tag/01E8).
-/

public section

open CategoryTheory MonoidalCategory TopologicalSpace
open CategoryTheory.Limits (isIso_app_coconePt_of_preservesColimit)

namespace AlgebraicGeometry.Scheme.Hom

open Scheme.Modules

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism that preserves regular functions over every open identifies the structure
sheaf of the base with the direct image of the structure sheaf of the source. -/
theorem isIso_unitToPushforwardObjUnit_of_isIso_app (hf : ∀ U, IsIso (f.app U)) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
  apply Hom.isIso_iff_isIso_app.mpr
  intro U
  let := hf U
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    (ConcreteCategory.bijective_of_isIso (f.app U))

private theorem isIso_unit_app_unit_of_isIso_app (hf : ∀ U, IsIso (f.app U)) :
    IsIso ((pullbackPushforwardAdjunction f).unit.app (𝟙_ Y.Modules)) := by
  have h := f.isIso_unitToPushforwardObjUnit_of_isIso_app hf
  have hunit := (Adjunction.homEquiv_unit (pullbackPushforwardAdjunction f) _ _
    (pullbackObjUnitIso f).hom).symm.trans
    (pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom f)
  exact (isIso_comp_right_iff _ _).mp (hunit.symm ▸ h : IsIso
    (((pullbackPushforwardAdjunction f).unit.app (𝟙_ Y.Modules)) ≫
      (pushforward f).map (pullbackObjUnitIso f).hom))

private theorem isIso_unit_app_free_of_isIso_app (hf : ∀ U, IsIso (f.app U))
    (I : Type u) [Finite I] :
    IsIso ((pullbackPushforwardAdjunction f).unit.app (SheafOfModules.free I)) := by
  let K : Discrete I ⥤ Y.Modules := (Functor.const _).obj (𝟙_ Y.Modules)
  let η := (pullbackPushforwardAdjunction f).unit
  have : IsIso (Functor.whiskerLeft K η) := (NatTrans.isIso_iff_isIso_app _).mpr
    fun _ ↦ isIso_unit_app_unit_of_isIso_app f hf
  exact isIso_app_coconePt_of_preservesColimit K η _ (SheafOfModules.isColimitFreeCofan I)

private theorem isIso_app_morphismRestrict (hf : ∀ U, IsIso (f.app U))
    (U : Y.Opens) (V : U.toScheme.Opens) : IsIso ((f ∣_ U).app V) := by
  let h := image_morphismRestrict_preimage f U V
  have hf' := hf (U.ι ''ᵁ V)
  have : IsIso (X.presheaf.map (eqToHom h).op) := inferInstance
  exact (morphismRestrict_app f U V).symm ▸
    (inferInstance : IsIso (f.app (U.ι ''ᵁ V) ≫ X.presheaf.map (eqToHom h).op))

/-- If f induces an isomorphism on regular functions over every open, the adjunction unit
E ⟶ f_* f^* E is an isomorphism for every finite locally free sheaf E. -/
theorem isIso_unit_app_of_isFiniteLocallyFree (hf : ∀ U, IsIso (f.app U))
    (E : TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf Y) :
    IsIso ((pullbackPushforwardAdjunction f).unit.app E.obj) := by
  have hlocal := SheafOfModules.isFiniteLocallyFree_iff_exists_isLocallyFreeData_isFiniteType E.obj
  obtain ⟨q, hq, hq'⟩ := hlocal.mp E.property
  apply (isIso_iff_of_isOpenCover ((Opens.coversTop_iff _ q.X).mp q.coversTop) _).mpr
  intro i
  let U : Y.Opens := q.X i
  let := (hq'.isFiniteType i).finite
  have := hq.isIso i
  let t : (pullback U.ι).obj E.obj ≅ SheafOfModules.free (q.generators i).I :=
    ((restrictFunctorIsoPullback U.ι).app E.obj).symm ≪≫
      restrictIsoFreeOfOverIsoFree E.obj U (asIso (q.generators i).π).symm
  let η := (pullbackPushforwardAdjunction (f ∣_ U)).unit
  have hη : IsIso (η.app ((pullback U.ι).obj E.obj)) := by
    have := isIso_unit_app_free_of_isIso_app (f ∣_ U)
      (isIso_app_morphismRestrict f hf U) (q.generators i).I
    exact (NatTrans.isIso_app_iff_of_iso η t).mpr inferInstance
  let w := (isPullback_morphismRestrict f U).flip.toCommSq
  have hbc : IsIso ((pushforwardBaseChange w).app ((pullback f).obj E.obj)) :=
    isIso_pushforwardBaseChange_morphismRestrict f U ((pullback f).obj E.obj)
  have h := pullback_map_unit_comp_pushforwardBaseChange_app w E.obj
  refine (isIso_comp_right_iff _ ((pushforwardBaseChange w).app ((pullback f).obj E.obj))).mp ?_
  rw [h]
  infer_instance

end AlgebraicGeometry.Scheme.Hom
