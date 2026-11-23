/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Pullback
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Monoidal.Basic
import Mathlib.CategoryTheory.Yoneda
import TauCeti.AlgebraicGeometry.LineBundle.Dual

/-!
# The canonical projection morphism for a line bundle

The morphism `L ⊗ f_* N ⟶ f_* (f^* L ⊗ N)` is the transpose of the pullback
tensor comparison followed by the counit on `N`. Its explicit description relates
the ideal-sheaf quotient of a line bundle to actual restriction to a closed subscheme.

For the projection formula, see Hartshorne, *Algebraic Geometry*, Exercise II.5.1(d),
and the [Stacks Project, Lemma 20.54.2](https://stacks.math.columbia.edu/tag/01E8).
Tau Ceti's `FiniteLocallyFreeSheaf.pushforwardTensorLeftIso` proves the projection formula
using the dual adjunction. The unit and counit equations below describe the canonical map.
-/

public noncomputable section

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal Functor.LaxMonoidal
open TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

open Scheme.Modules

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The canonical map from tensoring a direct image to the direct image of the tensor product. -/
def tensorPushforwardHom (M : Y.Modules) (N : X.Modules) :
    M ⊗ (pushforward f).obj N ⟶ (pushforward f).obj ((pullback f).obj M ⊗ N) :=
  (pullbackPushforwardAdjunction f).unit.app M ▷ (pushforward f).obj N ≫
    μ (pushforward f) ((pullback f).obj M) N

/-- The projection morphism is obtained from the adjunction unit and the tensor
map of direct image. -/
theorem tensorPushforwardHom_def (M : Y.Modules) (N : X.Modules) :
    f.tensorPushforwardHom M N =
      (pullbackPushforwardAdjunction f).unit.app M ▷ (pushforward f).obj N ≫
        μ (pushforward f) ((pullback f).obj M) N := (rfl)

/-- Under the pullback–pushforward adjunction, the projection morphism is the pullback tensor
comparison followed by the counit. -/
@[simp]
theorem tensorPushforwardHom_transpose (M : Y.Modules) (N : X.Modules) :
    ((pullbackPushforwardAdjunction f).homEquiv _ _).symm (f.tensorPushforwardHom M N) =
      δ (pullback f) M ((pushforward f).obj N) ≫
        (pullback f).obj M ◁ (pullbackPushforwardAdjunction f).counit.app N := by
  let adj := pullbackPushforwardAdjunction f
  rw [tensorPushforwardHom, Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_counit, Adjunction.map_μ_comp_counit_app_tensor]
  refine (δ_natural_left_assoc (pullback f) (adj.unit.app M) ((pushforward f).obj N)
    (adj.counit.app ((pullback f).obj M) ⊗ₘ adj.counit.app N)).symm.trans ?_
  rw [tensorHom_def, ← comp_whiskerRight_assoc]
  dsimp only [Functor.id_obj]
  have h := congrArg (fun a : (pullback f).obj M ⟶ (pullback f).obj M ↦
    δ (pullback f) M ((pushforward f).obj N) ≫
      a ▷ (pullback f).obj ((pushforward f).obj N) ≫
        (pullback f).obj M ◁ adj.counit.app N) (adj.left_triangle_components M)
  simpa only [id_whiskerRight, Category.id_comp] using h

/-- The canonical projection morphism commutes with a map of the tensor factors on the base. -/
@[reassoc]
theorem tensorPushforwardHom_naturality_left {M P : Y.Modules} (a : M ⟶ P) (N : X.Modules) :
    a ▷ (pushforward f).obj N ≫ f.tensorPushforwardHom P N =
      f.tensorPushforwardHom M N ≫ (pushforward f).map ((pullback f).map a ▷ N) := by
  apply ((pullbackPushforwardAdjunction f).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm]
  simp only [tensorPushforwardHom_transpose, Category.assoc]
  rw [← δ_natural_left_assoc]
  exact congrArg (δ (pullback f) M ((pushforward f).obj N) ≫ ·)
    (whisker_exchange ((pullback f).map a) ((pullbackPushforwardAdjunction f).counit.app N)).symm

/-- On an invertible sheaf, the canonical projection morphism is an isomorphism. -/
theorem isIso_tensorPushforwardHom (M : InvertibleSheaf Y) (N : X.Modules) :
    IsIso (f.tensorPushforwardHom M.obj N) := by
  let F := pullback f
  let G := pushforward f
  let adj := pullbackPushforwardAdjunction f
  let L := tensorLeft M.obj
  let K := tensorLeft (F.obj M.obj)
  have hL : (tensorRight M.obj).IsEquivalence := by
    rw [← InvertibleSheaf.tensorRightDualEquivalence_inverse]
    infer_instance
  let : L.IsEquivalence :=
    Functor.isEquivalence_of_iso (BraidedCategory.tensorLeftIsoTensorRight M.obj).symm
  have hK : (tensorRight (F.obj M.obj)).IsEquivalence := by
    rw [← InvertibleSheaf.pullback_obj_obj, ← InvertibleSheaf.tensorRightDualEquivalence_inverse]
    infer_instance
  let : K.IsEquivalence :=
    Functor.isEquivalence_of_iso (BraidedCategory.tensorLeftIsoTensorRight (F.obj M.obj)).symm
  let e := pullbackTensorLeftIso f M.obj
  apply isIso_of_yoneda_map_bijective
  intro T
  let A := L.objPreimage T
  let i := L.objObjPreimageIso T
  let P : (A ⟶ G.obj N) ≃ (T ⟶ L.obj (G.obj N)) :=
    (Functor.FullyFaithful.ofFullyFaithful L).homEquiv.trans (i.homCongr (Iso.refl _))
  let Q : (A ⟶ G.obj N) ≃ (T ⟶ G.obj (K.obj N)) :=
    ((adj.homEquiv _ _).symm.trans
      ((Functor.FullyFaithful.ofFullyFaithful K).homEquiv.trans
        ((e.app A).symm.homCongr (Iso.refl _)))).trans
      ((adj.homEquiv _ _).trans (i.homCongr (Iso.refl _)))
  have h (g : A ⟶ G.obj N) : P g ≫ f.tensorPushforwardHom M.obj N = Q g := by
    simp only [P, Q, Equiv.trans_apply, Functor.FullyFaithful.homEquiv_apply,
      Iso.homCongr, Equiv.coe_fn_mk, Iso.refl_hom, Category.comp_id]
    rw [Category.assoc]
    congr 1
    apply (adj.homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_naturality_left_symm]
    -- Expose the source and target of both adjunction equivalences so that cancellation
    -- uses the same objects, independently of the tensor functor wrappers.
    change F.map (M.obj ◁ g) ≫ (adj.homEquiv _ _).symm (f.tensorPushforwardHom M.obj N) =
      (adj.homEquiv (L.obj A) (K.obj N)).symm ((adj.homEquiv (L.obj A) (K.obj N))
        ((e.app A).hom ≫ F.obj M.obj ◁ (adj.homEquiv A N).symm g))
    rw [Equiv.symm_apply_apply]
    simp only [e, Iso.app_hom, pullbackTensorLeftIso_hom_app]
    rw [tensorPushforwardHom_transpose f M.obj N]
    exact (δ_natural_right_assoc F M.obj g _).symm.trans
      (congrArg (δ F M.obj A ≫ ·) ((whiskerLeft_comp _ _ _).symm.trans
        (congrArg (F.obj M.obj ◁ ·) (Adjunction.homEquiv_counit adj A N g).symm)))
  have hcomp : (fun x : T ⟶ L.obj (G.obj N) ↦ x ≫ f.tensorPushforwardHom M.obj N) =
      Q ∘ P.symm := by
    funext x
    simpa only [Equiv.apply_symm_apply, Function.comp_apply] using h (P.symm x)
  exact hcomp.symm ▸ (Q.bijective.comp P.symm.bijective)

end AlgebraicGeometry.Scheme.Hom
