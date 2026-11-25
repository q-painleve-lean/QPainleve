/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections
import QPainleve.AlgebraicGeometry.Modules.Pullback.Sections
import TauCeti.AlgebraicGeometry.Modules.Pullback.Quasicoherent

/-!
# Transporting products of sections

Surjectivity of the tensor map on sections can be tested after pulling back along
an open immersion whose image contains the open of sections.
-/

public section

open CategoryTheory Functor.LaxMonoidal MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.Hom

open Modules

variable {X Y : Scheme.{u}} {U : X.Opens} {M N : X.Modules}

/-- Over an open contained in the image of an open immersion, products of sections
generate after pullback if they generate before pullback, and conversely. -/
theorem surjective_sectionsFunctor_μ_iff_pullback (f : Y ⟶ X) [IsOpenImmersion f]
    (hU : U ≤ f.opensRange) :
    Function.Surjective (μ (sectionsFunctor U) M N) ↔
      Function.Surjective
        (μ (sectionsFunctor (f ⁻¹ᵁ U)) ((pullback f).obj M) ((pullback f).obj N)) := by
  let F := sectionsFunctor U
  let G := sectionsFunctor (f ⁻¹ᵁ U)
  let μ₀ := (μ F M N).hom.toAddMonoidHom
  let μ₁ := (μ G ((pullback f).obj M) ((pullback f).obj N)).hom.toAddMonoidHom
  have hpb (P : X.Modules) := f.bijective_pullbackSections_of_isOpenImmersion P U hU
  let δ := (Functor.OplaxMonoidal.δ (pullback f) M N).app (f ⁻¹ᵁ U)
  let a := δ.hom.comp (f.pullbackSections (M ⊗ N) U).toAddMonoidHom
  have ha : Function.Bijective a :=
    (ConcreteCategory.bijective_of_isIso δ).comp (hpb (M ⊗ N))
  have ht (x : Γ(M, U)) (y : Γ(N, U)) :
      a (μ₀ (TensorProduct.tmul _ x y)) =
        μ₁ (TensorProduct.tmul _ (f.pullbackSections M U x) (f.pullbackSections N U y)) :=
    f.δ_app_pullbackSections_μ M U N x y
  suffices Function.Surjective μ₀ ↔ Function.Surjective μ₁ from this
  constructor
  · intro h t
    obtain ⟨s, rfl⟩ := ha.surjective t
    obtain ⟨v, rfl⟩ := h s
    induction v using TensorProduct.inductionOn with
    | tmul x y => exact ⟨_, (ht x y).symm⟩
    | add x y hx hy =>
      obtain ⟨r, hr⟩ := hx
      obtain ⟨s, hs⟩ := hy
      refine ⟨r + s, ?_⟩
      exact (map_add μ₁ r s).trans ((congrArg₂ (· + ·) hr hs).trans
        ((map_add a (μ₀ x) (μ₀ y)).symm.trans (congrArg a (map_add μ₀ x y).symm)))
  · intro h t
    obtain ⟨s, hs⟩ := h (a t)
    suffices ∃ v, a (μ₀ v) = μ₁ s from
      this.imp fun v hv ↦ ha.injective (hv.trans hs)
    clear hs
    induction s using TensorProduct.inductionOn with
    | tmul x y =>
      obtain ⟨x, rfl⟩ := (hpb M).surjective x
      obtain ⟨y, rfl⟩ := (hpb N).surjective y
      exact ⟨_, ht x y⟩
    | add x y hx hy =>
      obtain ⟨r, hr⟩ := hx
      obtain ⟨s, hs⟩ := hy
      refine ⟨r + s, ?_⟩
      exact (congrArg a (map_add μ₀ r s)).trans ((map_add a (μ₀ r) (μ₀ s)).trans
        ((congrArg₂ (· + ·) hr hs).trans (map_add μ₁ x y).symm))

end AlgebraicGeometry.Scheme.Hom
