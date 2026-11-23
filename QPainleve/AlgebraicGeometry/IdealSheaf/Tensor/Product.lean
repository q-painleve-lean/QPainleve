/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Modules.Dual
public import TauCeti.AlgebraicGeometry.IdealSheaf.TensorProduct
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Invertible
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Sections
import TauCeti.AlgebraicGeometry.Modules.Sheaf

/-!
# Sections with values in a tensor ideal

A section of a finite locally free sheaf lifts through its tensor product with an ideal
sheaf exactly when the ideal contains the image of evaluation on the dual sheaf.
Multiplication of ideal sheaves induces an isomorphism from their tensor product
whenever one factor is the ideal of an effective Cartier divisor.
-/

public noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed
open TauCeti

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

variable (M : X.Modules) [M.IsLocallyFree] [M.IsFiniteType]

/-- A section lifts through the tensor product with an ideal sheaf if and only if its
dual evaluation takes values in that ideal. -/
theorem exists_tensorLift_iff (I : X.IdealSheafData)
    (φ : (ihom M).obj (𝟙_ X.Modules) ⟶ 𝟙_ X.Modules) :
    (∃ t : 𝟙_ X.Modules ⟶ I.sheaf ⊗ M,
      t ≫ I.sheafι ▷ M ≫ (λ_ M).hom = dualHomUnitEquiv M φ) ↔
      φ.imageIdealSheaf ≤ I := by
  let i : I.sheaf ⟶ 𝟙_ X.Modules := I.sheafι
  constructor
  · rintro ⟨t, ht⟩
    let ψ := (dualHomTensorEquiv M I.sheaf).symm t
    apply φ.imageIdealSheaf_le_of_factor I ψ
    apply (dualHomTensorEquiv M (𝟙_ X.Modules)).injective
    rw [dualHomTensorEquiv_comp M ψ i, Equiv.apply_symm_apply]
    exact (cancel_mono (λ_ M).hom).mp
      (ht.trans (dualHomTensorEquiv_comp_leftUnitor M φ).symm)
  · intro h
    let ψ := I.sheafLift φ fun U s ↦
      IdealSheafData.sections_mono h U (φ.app_mem_imageIdealSheaf_sections U s)
    have hψ : ψ ≫ i = φ := I.sheafLift_ι _ _
    refine ⟨dualHomTensorEquiv M I.sheaf ψ, ?_⟩
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (λ_ M).hom) ((dualHomTensorEquiv_comp M ψ i).symm.trans
        (congrArg (dualHomTensorEquiv M _) hψ))).trans (dualHomTensorEquiv_comp_leftUnitor M φ))

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.IdealSheafData

open Opposite Scheme.Modules

variable {X : Scheme.{u}} (I J : X.IdealSheafData)

/-- Multiplication of ideals sends a pure tensor of sections to their product as functions. -/
@[simp]
theorem sheafMul_app_tmulRight {U : X.Opens} (s : Γ(I.sheaf, U)) (t : Γ(J.sheaf, U)) :
    (I.sheafMul J).app U (tmulRight I.sheaf t s) = I.sectionsMul J U s t := by
  apply (I * J).sheafι_app_injective U
  let i : I.sheaf ⟶ 𝟙_ X.Modules := I.sheafι
  let j : J.sheaf ⟶ 𝟙_ X.Modules := J.sheafι
  let k : (I * J).sheaf ⟶ 𝟙_ X.Modules := (I * J).sheafι
  let O := 𝟙_ X.Modules
  let F := sectionsFunctor U
  have h : Functor.LaxMonoidal.μ F I.sheaf J.sheaf ≫ F.map (I.sheafMul J) ≫ F.map k =
      (F.map i ⊗ₘ F.map j) ≫ Functor.LaxMonoidal.μ F O O ≫ F.map (λ_ O).hom := by
    erw [← Functor.map_comp, sheafMul_sheafι, Functor.map_comp,
      ← Functor.LaxMonoidal.μ_natural_assoc]
    rfl
  have hun := Functor.LaxMonoidal.left_unitality (F := F) O
  erw [sectionsFunctor_ε, id_whiskerRight, Category.id_comp] at hun
  have happ := congrArg (fun f : F.obj I.sheaf ⊗ F.obj J.sheaf ⟶ F.obj O ↦ f.hom (s ⊗ₜ t))
    (h.trans (congrArg (_ ≫ ·) hun.symm))
  rw [tmulRight_apply]
  exact happ.trans (I.sheafι_app_sectionsMul J U s t).symm

/-- Multiplication from the tensor product of two ideal sheaves to their product is surjective
on every affine open. -/
theorem surjective_app_sheafMul (U : X.affineOpens) :
    Function.Surjective ((I.sheafMul J).app U.val) := by
  intro w
  let a : Γ(X, U) := (I * J).sheafι.app U.val w
  have ha : a ∈ I.ideal U * J.ideal U := by
    have h := (I * J).sheafι_app_mem U.val w
    rw [sections_eq_ideal, ideal_mul, Pi.mul_apply] at h
    exact h
  suffices hex : ∃ z : Γ(I.sheaf ⊗ J.sheaf, U.val),
      (I * J).sheafι.app U.val ((I.sheafMul J).app U.val z) = a by
    obtain ⟨z, hz⟩ := hex
    exact ⟨z, (I * J).sheafι_app_injective U.val hz⟩
  refine Submodule.mul_induction_on ha (fun x hx y hy ↦ ?_) ?_
  · let s := I.sectionMk x ((I.sections_eq_ideal U).symm ▸ hx)
    let t := J.sectionMk y ((J.sections_eq_ideal U).symm ▸ hy)
    refine ⟨tmulRight I.sheaf t s, ?_⟩
    rw [sheafMul_app_tmulRight, sheafι_app_sectionsMul, sheafι_app_sectionMk, sheafι_app_sectionMk]
  · rintro x y ⟨z, hz⟩ ⟨w', hw'⟩
    exact ⟨z + w', by rw [map_add, map_add, hz, hw']; rfl⟩

/-- Multiplication identifies the tensor product with the product ideal when the second factor
is effective Cartier. -/
theorem isIso_sheafMul_of_isEffectiveCartier (hJ : J.IsEffectiveCartier) :
    IsIso (I.sheafMul J) := by
  let i : I.sheaf ⟶ 𝟙_ X.Modules := I.sheafι
  let j : J.sheaf ⟶ 𝟙_ X.Modules := J.sheafι
  have hR := (TauCeti.AlgebraicGeometry.InvertibleSheaf.tensorRightDualEquivalence
    hJ.toInvertibleSheaf).inverse.map_mono i
  rw [TauCeti.AlgebraicGeometry.InvertibleSheaf.tensorRightDualEquivalence_inverse,
    hJ.toInvertibleSheaf_obj] at hR
  have h₁ : Mono (i ▷ J.sheaf) := hR
  have hc : (𝟙_ X.Modules) ◁ j = (λ_ J.sheaf).hom ≫ j ≫ (λ_ (𝟙_ X.Modules)).inv :=
    ((λ_ (𝟙_ X.Modules)).eq_comp_inv).mpr (leftUnitor_naturality j)
  have h₂ : Mono ((𝟙_ X.Modules) ◁ j) := by rw [hc]; infer_instance
  have hprod : Mono ((i ⊗ₘ j) ≫ (λ_ (𝟙_ X.Modules)).hom) := by
    rw [tensorHom_def]
    infer_instance
  have : Mono (I.sheafMul J) := mono_of_mono_fac (I.sheafMul_sheafι J)
  have : Epi (I.sheafMul J) :=
    Scheme.Modules.Hom.epi_of_surjective_on_affineOpens _ fun U hU ↦
      I.surjective_app_sheafMul J ⟨U, hU⟩
  exact isIso_of_mono_of_epi _

/-- The inclusion of a product of ideal sheaves after tensoring with a module is the
successive inclusion of the two ideals. -/
@[reassoc]
theorem sheafMul_whiskerRight_comp_sheafι (M : X.Modules) :
    (α_ I.sheaf J.sheaf M).inv ≫ I.sheafMul J ▷ M ≫
        (I * J).sheafι ▷ M ≫ (λ_ M).hom =
      I.sheafι ▷ (J.sheaf ⊗ M) ≫ (λ_ (J.sheaf ⊗ M)).hom ≫
        J.sheafι ▷ M ≫ (λ_ M).hom := by
  let O := 𝟙_ X.Modules
  let i : J.sheaf ⟶ O := J.sheafι
  let j : I.sheaf ⟶ O := I.sheafι
  let k : (I * J).sheaf ⟶ O := (I * J).sheafι
  have hm : I.sheafMul J ≫ k = (j ⊗ₘ i) ≫ (λ_ O).hom :=
    I.sheafMul_sheafι J
  have h :=
    congrArg (fun g ↦ g ▷ M) hm
  simp only [comp_whiskerRight] at h
  calc
    _ = (α_ I.sheaf J.sheaf M).inv ≫ ((j ⊗ₘ i) ▷ M) ≫
          (λ_ O).hom ▷ M ≫ (λ_ M).hom := by
      exact congrArg ((α_ I.sheaf J.sheaf M).inv ≫ · ≫ (λ_ M).hom) h
    _ = _ := by
      simp only [tensorHom_def, comp_whiskerRight]
      monoidal

end AlgebraicGeometry.Scheme.IdealSheafData
