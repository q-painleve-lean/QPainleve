/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Invertible
public import TauCeti.AlgebraicGeometry.LineBundle.Class
import QPainleve.AlgebraicGeometry.IdealSheaf.Image
import TauCeti.AlgebraicGeometry.LineBundle.Endomorphisms

/-!
# Effective Cartier divisors with trivial ideal bundle

When the global functions on a scheme form a field, an effective Cartier divisor
with trivial ideal bundle is empty.
-/

public section

open CategoryTheory MonoidalCategory
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

variable {X : Scheme.{u}} {I : X.IdealSheafData}

/-- An effective Cartier divisor with trivial ideal class on a scheme with a field of global
functions has unit ideal. -/
theorem eq_top_of_isField_of_mk_toInvertibleSheaf_eq_one (hI : I.IsEffectiveCartier)
    (hX : IsField Γ(X, ⊤)) (hL : LineBundleClass.mk hI.toInvertibleSheaf = 1) :
    I = ⊤ := by
  obtain ⟨e⟩ := LineBundleClass.mk_eq_one_iff.mp hL
  let j : 𝟙_ X.Modules ≅ I.sheaf := e.symm ≪≫ eqToIso hI.toInvertibleSheaf_obj
  let φ : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules := j.hom ≫ I.sheafι
  have : Mono φ := mono_comp _ _
  have hφ : φ ≠ 0 := by
    intro hz
    have hid : 𝟙 (𝟙_ X.Modules) = 0 := (cancel_mono φ).mp (by simp [hz])
    let _ := hX.toField
    let E := Scheme.Modules.globalSectionsActionRingEquiv (𝟙_ X.Modules)
    apply one_ne_zero (α := Γ(X, ⊤))
    apply E.injective
    rw [map_one, map_zero]
    exact congrArg End.of hid
  have : IsIso φ := Scheme.Modules.Hom.isIso_of_ne_zero_of_isField_of_isInvertible φ hX hφ
  have ht := (⊤ : X.IdealSheafData).imageIdealSheaf_sheafι
  let e' : I.sheaf ≅ (⊤ : X.IdealSheafData).sheaf :=
    j.symm ≪≫ asIso φ ≪≫ (asIso (⊤ : X.IdealSheafData).sheafι).symm
  have he' : e'.hom ≫ (⊤ : X.IdealSheafData).sheafι = I.sheafι := by
    simp only [e', Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, Category.assoc,
      φ, Iso.inv_hom_id_assoc]
    let ι : (⊤ : X.IdealSheafData).sheaf ⟶ 𝟙_ X.Modules := (⊤ : X.IdealSheafData).sheafι
    exact (Category.assoc I.sheafι (inv ι) ι).trans <|
      (congrArg (I.sheafι ≫ ·) (IsIso.inv_hom_id ι)).trans (Category.comp_id _)
  rw [← I.imageIdealSheaf_sheafι, ← he']
  exact ((⊤ : X.IdealSheafData).sheafι.imageIdealSheaf_comp_iso e').trans ht

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
