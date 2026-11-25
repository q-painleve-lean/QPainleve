/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.IdealSheaf.Tensor.Restriction

/-!
# Inclusion of the ideal-sheaf twist

Tensoring the ideal inclusion with a module gives the morphism from its ideal-sheaf
twist. For a line bundle, this morphism is the kernel of restriction to the closed
subscheme, expressed as a factorization criterion for maps into the line bundle.
-/

public noncomputable section

open CategoryTheory Limits MonoidalCategory
open TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}}

/-- The morphism from the ideal-sheaf twist of a module to the module itself. -/
def tensorIdealInclusion (I : X.IdealSheafData) (M : X.Modules) : M ⊗ I.sheaf ⟶ M :=
  M ◁ I.sheafι ≫ (ρ_ M).hom

/-- The tensor ideal inclusion is induced by the inclusion into the structure sheaf. -/
theorem tensorIdealInclusion_def (I : X.IdealSheafData) (M : X.Modules) :
    I.tensorIdealInclusion M = M ◁ I.sheafι ≫ (ρ_ M).hom :=
  (rfl)

/-- A morphism into a line bundle restricts to zero on a closed subscheme exactly
when it factors through the ideal-sheaf twist of its target. -/
theorem pullback_map_eq_zero_iff_exists_comp_tensorIdealInclusion
    (I : X.IdealSheafData) {M : X.Modules} (N : InvertibleSheaf X) (b : M ⟶ N.obj) :
    (Scheme.Modules.pullback I.subschemeι).map b = 0 ↔
      ∃ a : M ⟶ N.obj ⊗ I.sheaf, b = a ≫ I.tensorIdealInclusion N.obj := by
  let S := (ShortComplex.mk _ _ I.sheafι_toPushforwardSubscheme).map (tensorLeft N.obj)
  have hS : S.ShortExact := I.shortExact_tensor_toPushforwardSubscheme N.obj
  have hIso := I.isIso_tensorRestrictionHom N
  have hunit : b ≫ (pullbackPushforwardAdjunction I.subschemeι).unit.app N.obj =
      (b ≫ (ρ_ N.obj).inv ≫ S.g) ≫ I.tensorRestrictionHom N := by
    rw [← I.tensorRestrictionHom_unit N]
    simp only [Category.assoc]
    rfl
  have hzero : (Scheme.Modules.pullback I.subschemeι).map b = 0 ↔
      (b ≫ (ρ_ N.obj).inv) ≫ S.g = 0 := by
    let adj := pullbackPushforwardAdjunction I.subschemeι
    rw [← (adj.homEquiv M ((Scheme.Modules.pullback I.subschemeι).obj N.obj)).injective.eq_iff]
    simp only [Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
    have hn := adj.unit.naturality b
    simp only [Functor.id_map, Functor.comp_map] at hn
    rw [← hn, hunit, ← cancel_mono (I.tensorRestrictionHom N), zero_comp]
    simp only [Category.assoc]
  rw [hzero]
  constructor
  · intro h
    let a := hS.fIsKernel.lift (KernelFork.ofι (b ≫ (ρ_ N.obj).inv) h)
    have ha : a ≫ S.f = b ≫ (ρ_ N.obj).inv :=
      hS.fIsKernel.fac (KernelFork.ofι (b ≫ (ρ_ N.obj).inv) h) WalkingParallelPair.zero
    refine ⟨a, ?_⟩
    exact (by rw [← Category.assoc, ha, Category.assoc, Iso.inv_hom_id, Category.comp_id] :
      a ≫ S.f ≫ (ρ_ N.obj).hom = b).symm
  · rintro ⟨a, rfl⟩
    calc
      (a ≫ I.tensorIdealInclusion N.obj ≫ (ρ_ N.obj).inv) ≫ S.g = a ≫ S.f ≫ S.g := by
        simp only [tensorIdealInclusion_def, Category.assoc, Iso.hom_inv_id_assoc]
        rfl
      _ = 0 := by simp only [S.zero, comp_zero]

/-- The inclusion from the ideal-sheaf twist is natural in the coefficient module. -/
@[reassoc]
theorem tensorIdealInclusion_naturality (I : X.IdealSheafData) {M N : X.Modules} (b : M ⟶ N) :
    I.tensorIdealInclusion M ≫ b = b ▷ I.sheaf ≫ I.tensorIdealInclusion N := by
  simp only [tensorIdealInclusion_def]
  calc
    (M ◁ I.sheafι ≫ (ρ_ M).hom) ≫ b = M ◁ I.sheafι ≫ b ▷ (𝟙_ X.Modules) ≫ (ρ_ N).hom :=
      (Category.assoc _ _ _).trans (congrArg (M ◁ I.sheafι ≫ ·) (rightUnitor_naturality b).symm)
    _ = b ▷ I.sheaf ≫ N ◁ I.sheafι ≫ (ρ_ N).hom := whisker_exchange_assoc b I.sheafι _

/-- For a finite locally free module the tensor ideal inclusion is a monomorphism. -/
theorem mono_tensorIdealInclusion (I : X.IdealSheafData) (M : X.Modules)
    [M.IsLocallyFree] [M.IsFiniteType] : Mono (I.tensorIdealInclusion M) := by
  have : Mono (M ◁ I.sheafι) := (I.shortExact_tensor_toPushforwardSubscheme M).mono_f
  rw [tensorIdealInclusion_def]
  infer_instance

end AlgebraicGeometry.Scheme.IdealSheafData
