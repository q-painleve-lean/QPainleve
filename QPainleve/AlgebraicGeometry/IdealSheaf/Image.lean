/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.Image
public import TauCeti.AlgebraicGeometry.IdealSheaf.Sequence
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Invertible
import TauCeti.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.Noetherian.Orzech

/-!
# Factorization through an image ideal

Two embeddings into the structure sheaf identify their domains with the same ideal sheaf
exactly when there is an isomorphism between the embeddings.
An invertible sheaf mapping to the structure sheaf is already isomorphic to its image
whenever the image ideal is effective Cartier.
-/

public section

open AlgebraicGeometry CategoryTheory MonoidalCategory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The image of the inclusion of an ideal sheaf into the structure sheaf is that ideal. -/
@[simp]
lemma imageIdealSheaf_sheafι {X : Scheme.{u}} (I : X.IdealSheafData) :
    I.sheafι.imageIdealSheaf = I := by
  refine le_antisymm (I.sheafι.imageIdealSheaf_le_of_factor I (𝟙 _) (Category.id_comp _)) ?_
  intro U a ha
  rw [Modules.Hom.imageIdealSheaf_ideal, Modules.Hom.mem_imageIdeal]
  have ha' : a ∈ I.sections U.val := (I.sections_eq_ideal U).symm ▸ ha
  exact ⟨I.sectionMk a ha', I.sheafι_app_sectionMk a ha'⟩

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.Modules.Hom

/-- If the image ideal of a functional on an invertible sheaf is effective Cartier,
the canonical map to that ideal sheaf is an isomorphism. -/
theorem isIso_toImageIdealSheaf_of_isEffectiveCartier {X : Scheme.{u}} {M : X.Modules}
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M] (φ : M ⟶ 𝟙_ X.Modules)
    (h : φ.imageIdealSheaf.IsEffectiveCartier) : IsIso φ.toImageIdealSheaf := by
  classical
  let J := φ.imageIdealSheaf
  have := h.isInvertible_sheaf
  let B := {U : X.Opens | IsAffineOpen U ∧
    Nonempty (Γ(M, U) ≃ₗ[Γ(X, U)] Γ(X, U)) ∧
    Nonempty (Γ(J.sheaf, U) ≃ₗ[Γ(X, U)] Γ(X, U))}
  have hB : TopologicalSpace.Opens.IsBasis B := by
    apply TopologicalSpace.Opens.isBasis_iff_nbhd.mpr
    intro W x hx
    obtain ⟨V, eM, hxV⟩ := Scheme.Modules.exists_mem_trivialization M x
    obtain ⟨V', eJ, hxV'⟩ := Scheme.Modules.exists_mem_trivialization J.sheaf x
    have hx' : x ∈ V ⊓ V' ⊓ W := ⟨⟨hxV, hxV'⟩, hx⟩
    obtain ⟨U, hU, hxU, hle⟩ := exists_isAffineOpen_mem_and_subset hx'
    exact ⟨U, ⟨hU,
      ⟨M.trivializationCoordinate eM (homOfLE (hle.trans (inf_le_left.trans inf_le_left)))⟩,
      ⟨J.sheaf.trivializationCoordinate eJ
        (homOfLE (hle.trans (inf_le_left.trans inf_le_right)))⟩⟩, hxU, hle.trans inf_le_right⟩
  refine φ.toImageIdealSheaf.isIso_of_isBasis
    (B := fun U : B ↦ U.val) (by rwa [Subtype.range_coe]) ?_
  rintro ⟨U, hU, ⟨eM⟩, ⟨eJ⟩⟩
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  have hs : Function.Surjective (φ.toImageIdealSheaf.app U) := by
    intro s
    have hs := J.sheafι_app_mem U s
    rw [J.sections_eq_ideal ⟨U, hU⟩, imageIdealSheaf_ideal] at hs
    obtain ⟨t, ht⟩ := (mem_imageIdeal φ (U := U)).mp hs
    exact ⟨t, J.sheafι_app_injective U ((φ.toImageIdealSheaf_app_sheafι U t).trans ht)⟩
  let g : Γ(M, U) →ₗ[Γ(X, U)] Γ(J.sheaf, U) := (φ.toImageIdealSheaf.val.app (.op U)).hom
  have := Module.Finite.equiv eJ.symm
  exact OrzechProperty.bijective_of_surjective_of_injective
    (eM.trans eJ.symm).toLinearMap g (eM.trans eJ.symm).injective hs

/-- Monomorphisms into the structure sheaf have the same image ideal exactly when their
sources are isomorphic over the structure sheaf. -/
theorem imageIdealSheaf_eq_iff_exists_iso_comp_eq {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ 𝟙_ X.Modules) (ψ : N ⟶ 𝟙_ X.Modules)
    [Mono φ] [Mono ψ] :
    φ.imageIdealSheaf = ψ.imageIdealSheaf ↔ ∃ e : M ≅ N, e.hom ≫ ψ = φ := by
  constructor
  · intro h
    let e : φ.imageIdealSheaf.sheaf ≅ ψ.imageIdealSheaf.sheaf :=
      eqToIso (congrArg Scheme.IdealSheafData.sheaf h)
    have he : e.hom ≫ ψ.imageIdealSheaf.sheafι = φ.imageIdealSheaf.sheafι := by
      simpa [e] using (eqToHom_naturality (g := fun _ ↦ 𝟙_ X.Modules)
        (fun I : X.IdealSheafData ↦ I.sheafι) h).symm
    have hψ : ψ.imageIdealSheafIso.inv ≫ ψ = ψ.imageIdealSheaf.sheafι :=
      ψ.imageIdealSheafIso.inv_comp_eq.mpr ψ.imageIdealSheafIso_hom_ι.symm
    let α := φ.imageIdealSheafIso ≪≫ e ≪≫ ψ.imageIdealSheafIso.symm
    refine ⟨α, ?_⟩
    calc
      α.hom ≫ ψ = φ.imageIdealSheafIso.hom ≫ e.hom ≫ ψ.imageIdealSheafIso.inv ≫ ψ :=
        (Category.assoc _ _ _).trans (congrArg (φ.imageIdealSheafIso.hom ≫ ·)
          (Category.assoc _ _ _))
      _ = φ.imageIdealSheafIso.hom ≫ φ.imageIdealSheaf.sheafι :=
        congrArg (φ.imageIdealSheafIso.hom ≫ ·) ((congrArg (e.hom ≫ ·) hψ).trans he)
      _ = φ := φ.imageIdealSheafIso_hom_ι
  · rintro ⟨e, rfl⟩
    exact ψ.imageIdealSheaf_comp_iso e

end AlgebraicGeometry.Scheme.Modules.Hom
