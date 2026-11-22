/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.Image
public import TauCeti.AlgebraicGeometry.IdealSheaf.Sequence

/-!
# Factorization through an image ideal

Two embeddings into the structure sheaf identify their domains with the same ideal sheaf
exactly when there is an isomorphism between the embeddings.
-/

public section

open AlgebraicGeometry CategoryTheory MonoidalCategory

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
