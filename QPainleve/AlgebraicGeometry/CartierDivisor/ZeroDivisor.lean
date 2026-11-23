/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.IdealSheaf

import QPainleve.AlgebraicGeometry.IdealSheaf.Image
import QPainleve.AlgebraicGeometry.IdealSheaf.Image.Basic
import TauCeti.AlgebraicGeometry.LineBundle.Endomorphisms

/-!
# Zero divisors of sections

Evaluation of a section on the dual line bundle defines the ideal of its zero scheme.
On an integral scheme a nonzero section cuts out an effective Cartier divisor with the
class of its line bundle. Two nonzero sections define the same divisor exactly when
they differ by a global unit.

## References

* The Stacks Project, [Lemma 31.15.10](https://stacks.math.columbia.edu/tag/01X0).
-/

public section

open AlgebraicGeometry CategoryTheory MonoidalCategory
open Scheme.Modules

universe u

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

noncomputable section

variable {X : Scheme.{u}} (L : InvertibleSheaf X)

/-- Evaluation identifies sections of a line bundle with functionals on its bundled dual. -/
def dualSectionEquiv : ((dual L).obj ⟶ 𝟙_ X.Modules) ≃ Γ(L.obj, ⊤) :=
  ((eqToIso (dual_obj L)).homCongr (Iso.refl _)).trans
    ((dualHomUnitEquiv L.obj).trans L.obj.unitHomEquivTop)

/-- The bundled dual section correspondence evaluates the same internal-Hom functional. -/
lemma dualSectionEquiv_apply (φ : (dual L).obj ⟶ 𝟙_ X.Modules) :
    L.dualSectionEquiv φ =
      L.obj.unitHomEquivTop (dualHomUnitEquiv L.obj ((eqToIso (dual_obj L)).inv ≫ φ)) :=
  (rfl)

/-- The zero functional corresponds to the zero section. -/
@[simp]
lemma dualSectionEquiv_zero : L.dualSectionEquiv 0 = 0 := by
  rw [dualSectionEquiv_apply]
  have h := Limits.comp_zero (f := (eqToIso (dual_obj L)).inv) (Z := 𝟙_ X.Modules)
  exact (congrArg (L.obj.unitHomEquivTop ∘ dualHomUnitEquiv L.obj) h).trans
    ((congrArg L.obj.unitHomEquivTop (dualHomUnitEquiv_zero L.obj)).trans
      (unitHomEquivTop_zero L.obj))

/-- Scaling a functional on the dual scales its associated section by the same function. -/
@[simp]
lemma dualSectionEquiv_comp_globalSectionsSmul
    (φ : (dual L).obj ⟶ 𝟙_ X.Modules) (a : Γ(X, ⊤)) :
    L.dualSectionEquiv (φ ≫ globalSectionsSmul (𝟙_ X.Modules) a) =
      a • L.dualSectionEquiv φ := by
  let ψ := (eqToIso (dual_obj L)).inv ≫ φ
  let mul := globalSectionsSmul (𝟙_ X.Modules) a
  have h := Category.assoc (eqToIso (dual_obj L)).inv φ mul
  calc
    L.dualSectionEquiv (φ ≫ mul) =
        L.obj.unitHomEquivTop (dualHomUnitEquiv L.obj (ψ ≫ mul)) :=
      (L.dualSectionEquiv_apply _).trans
        (congrArg (L.obj.unitHomEquivTop ∘ dualHomUnitEquiv L.obj) h.symm)
    _ = (globalSectionsSmul L.obj a).app ⊤ (L.dualSectionEquiv φ) :=
      (congrArg L.obj.unitHomEquivTop
        (dualHomUnitEquiv_comp_globalSectionsSmul L.obj ψ a)).trans
        ((unitHomEquivTop_comp L.obj _ _).trans
          (congrArg ((globalSectionsSmul L.obj a).app ⊤) (L.dualSectionEquiv_apply φ).symm))
    _ = a • L.dualSectionEquiv φ := by
      rw [globalSectionsSmul_app, Scheme.Modules.smul_apply,
        Subsingleton.elim ((⊤ : X.Opens).leTop.op) (𝟙 _), X.presheaf.map_id]
      rfl

/-- The ideal sheaf of the zero scheme of a section, obtained by evaluation on the dual. -/
def zeroIdeal (s : Γ(L.obj, ⊤)) : X.IdealSheafData :=
  (L.dualSectionEquiv.symm s).imageIdealSheaf

/-- The zero section cuts out the entire scheme. -/
@[simp]
theorem zeroIdeal_zero : L.zeroIdeal 0 = ⊥ := by
  rw [zeroIdeal, Hom.imageIdealSheaf_eq_bot_iff, Equiv.symm_apply_eq, dualSectionEquiv_zero]

/-- On an affine open, the zero ideal is the image of the evaluation map on sections. -/
@[simp]
lemma zeroIdeal_ideal (s : Γ(L.obj, ⊤)) (U : X.affineOpens) :
    (L.zeroIdeal s).ideal U = (L.dualSectionEquiv.symm s).imageIdeal U :=
  Hom.imageIdealSheaf_ideal _ _

/-- The zero ideal is the image ideal of evaluation on the internal-Hom dual. -/
theorem zeroIdeal_eq_imageIdealSheaf_evaluation (s : Γ(L.obj, ⊤)) :
    L.zeroIdeal s = ((dualHomUnitEquiv L.obj).symm
      (L.obj.unitHomEquivTop.symm s)).imageIdealSheaf := by
  let φ := L.dualSectionEquiv.symm s
  let e : (ihom L.obj).obj (𝟙_ X.Modules) ≅ (dual L).obj := eqToIso (dual_obj L).symm
  have hφ : (dualHomUnitEquiv L.obj).symm (L.obj.unitHomEquivTop.symm s) = e.hom ≫ φ := by
    apply (dualHomUnitEquiv L.obj).injective
    apply L.obj.unitHomEquivTop.injective
    exact (congrArg L.obj.unitHomEquivTop ((dualHomUnitEquiv L.obj).apply_symm_apply _)).trans
      ((L.obj.unitHomEquivTop.apply_symm_apply s).trans
        ((L.dualSectionEquiv.apply_symm_apply s).symm.trans (L.dualSectionEquiv_apply φ)))
  rw [hφ, Hom.imageIdealSheaf_comp_iso]
  rfl

/-- Transporting a section through an isomorphism of line bundles preserves its zero ideal. -/
@[simp]
theorem zeroIdeal_hom_app {K : InvertibleSheaf X} (e : L.obj ≅ K.obj) (s : Γ(L.obj, ⊤)) :
    K.zeroIdeal (e.hom.app ⊤ s) = L.zeroIdeal s := by
  let eL := eqToIso (dual_obj L)
  let eK := eqToIso (dual_obj K)
  let d := (SheafOfModules.dualIso (R := X.sheaf) e).symm
  let d' : (dual K).obj ≅ (dual L).obj := eK ≪≫ d ≪≫ eL.symm
  let φ := L.dualSectionEquiv.symm s
  have hcompose : eK.inv ≫ (d'.hom ≫ φ) = d.hom ≫ (eL.inv ≫ φ) := calc
    _ = eK.inv ≫ eK.hom ≫ d.hom ≫ eL.inv ≫ φ :=
      congrArg (eK.inv ≫ ·) <|
        (Category.assoc _ _ _).trans (congrArg (eK.hom ≫ ·) (Category.assoc _ _ _))
    _ = _ := eK.inv_hom_id_assoc _
  have hd : d.hom = (MonoidalClosed.pre e.hom).app (𝟙_ X.Modules) :=
    SheafOfModules.dualIso_inv (R := X.sheaf) e
  have hsection :
      K.dualSectionEquiv (d'.hom ≫ φ) = e.hom.app ⊤ s := calc
    _ = K.obj.unitHomEquivTop (dualHomUnitEquiv K.obj (d.hom ≫ eL.inv ≫ φ)) :=
      (K.dualSectionEquiv_apply _).trans
        (congrArg (K.obj.unitHomEquivTop ∘ dualHomUnitEquiv K.obj) hcompose)
    _ = K.obj.unitHomEquivTop (dualHomUnitEquiv L.obj (eL.inv ≫ φ) ≫ e.hom) :=
      congrArg K.obj.unitHomEquivTop <|
        (congrArg (fun f ↦ dualHomUnitEquiv K.obj (f ≫ eL.inv ≫ φ)) hd).trans
          (dualHomUnitEquiv_pre_comp (eL.inv ≫ φ) e.hom)
    _ = e.hom.app ⊤ s :=
      (unitHomEquivTop_comp L.obj _ e.hom).trans
        (congrArg (e.hom.app ⊤) ((L.dualSectionEquiv_apply φ).symm.trans
          (L.dualSectionEquiv.apply_symm_apply s)))
  have hφ : K.dualSectionEquiv.symm (e.hom.app ⊤ s) = d'.hom ≫ φ :=
    (K.dualSectionEquiv.symm_apply_eq).mpr hsection.symm
  rw [zeroIdeal, zeroIdeal, hφ]
  exact φ.imageIdealSheaf_comp_iso d'

variable [IsIntegral X]

private lemma dualSectionEquiv_symm_mono {s : Γ(L.obj, ⊤)} (hs : s ≠ 0) :
    Mono (L.dualSectionEquiv.symm s) := by
  apply (dual L).mono_of_ne_zero_to_unit
  intro h
  apply hs
  rw [← L.dualSectionEquiv.apply_symm_apply s, h, dualSectionEquiv_zero]

/-- The zero ideal of a nonzero section is effective Cartier. -/
theorem isEffectiveCartier_zeroIdeal {s : Γ(L.obj, ⊤)} (hs : s ≠ 0) :
    (L.zeroIdeal s).IsEffectiveCartier :=
  letI := L.dualSectionEquiv_symm_mono hs
  (dual L).isEffectiveCartier_imageIdealSheaf _

/-- The effective Cartier divisor cut out by a nonzero section. -/
def zeroDivisor {s : Γ(L.obj, ⊤)} (hs : s ≠ 0) : Scheme.CartierDivisor X :=
  (L.isEffectiveCartier_zeroIdeal hs).toCartierDivisor

/-- The zero divisor of a nonzero section is effective. -/
theorem isEffective_zeroDivisor {s : Γ(L.obj, ⊤)} (hs : s ≠ 0) :
    (L.zeroDivisor hs).IsEffective :=
  (L.isEffectiveCartier_zeroIdeal hs).isEffective_toCartierDivisor

/-- The divisor recovers the scheme-theoretic zero ideal. -/
@[simp]
lemma idealSheaf_zeroDivisor {s : Γ(L.obj, ⊤)} (hs : s ≠ 0) :
    (L.isEffective_zeroDivisor hs).idealSheaf = L.zeroIdeal s :=
  (L.isEffectiveCartier_zeroIdeal hs).idealSheaf_toCartierDivisor

/-- Isomorphic line bundles give the same divisor for corresponding nonzero sections. -/
@[simp]
theorem zeroDivisor_hom_app {K : InvertibleSheaf X} (e : L.obj ≅ K.obj)
    {s : Γ(L.obj, ⊤)} (ht : e.hom.app ⊤ s ≠ 0) :
    K.zeroDivisor ht = L.zeroDivisor (s := s) (fun hs ↦ ht (by rw [hs, map_zero])) := by
  have hs : s ≠ 0 := fun h ↦ ht (by rw [h, map_zero])
  exact ((K.isEffectiveCartier_zeroIdeal ht).toCartierDivisor_eq_iff
    (L.isEffectiveCartier_zeroIdeal hs)).mpr (L.zeroIdeal_hom_app e s)

/-- The zero divisor has the class of the original bundle. -/
@[simp]
lemma toLineBundleClass_zeroDivisor {s : Γ(L.obj, ⊤)} (hs : s ≠ 0) :
    (L.zeroDivisor hs).toLineBundleClass = LineBundleClass.mk L := by
  have := L.dualSectionEquiv_symm_mono hs
  rw [zeroDivisor, Scheme.IdealSheafData.IsEffectiveCartier.toLineBundleClass_toCartierDivisor]
  exact (congrArg Inv.inv ((dual L).mk_toInvertibleSheaf_imageIdealSheaf _)).trans
    (by rw [← LineBundleClass.inv_mk, inv_inv])

/-- Sections cutting out the same divisor differ by multiplication by a global unit. -/
theorem zeroDivisor_eq_iff_exists_smul {s t : Γ(L.obj, ⊤)} (hs : s ≠ 0) (ht : t ≠ 0) :
    L.zeroDivisor hs = L.zeroDivisor ht ↔ ∃ a : Γ(X, ⊤)ˣ, (a : Γ(X, ⊤)) • t = s := by
  rw [zeroDivisor, zeroDivisor, Scheme.IdealSheafData.IsEffectiveCartier.toCartierDivisor_eq_iff,
    zeroIdeal, zeroIdeal]
  let φ := L.dualSectionEquiv.symm s
  let ψ := L.dualSectionEquiv.symm t
  have : Mono φ := L.dualSectionEquiv_symm_mono hs
  have : Mono ψ := L.dualSectionEquiv_symm_mono ht
  have : TauCeti.SheafOfModules.IsInvertible (R := X.ringCatSheaf) (dual L).obj := (dual L).property
  let unitAut := unitsGlobalSectionsMulEquivAut (dual L).obj
  -- Apply the image comparison to the evaluations on the dual bundle.
  change φ.imageIdealSheaf = ψ.imageIdealSheaf ↔ _
  rw [φ.imageIdealSheaf_eq_iff_exists_iso_comp_eq ψ]
  constructor
  · rintro ⟨α, hα⟩
    let a := unitAut.symm (Aut.of α)
    have ha := (globalSectionsSmul_unitsGlobalSectionsMulEquivAut_symm (dual L).obj (Aut.of α))
    refine ⟨a, ?_⟩
    rw [← L.dualSectionEquiv.apply_symm_apply t, ← L.dualSectionEquiv.apply_symm_apply s,
      ← L.dualSectionEquiv_comp_globalSectionsSmul, ← globalSectionsSmul_naturality ψ]
    exact congrArg L.dualSectionEquiv (ha ▸ hα)
  · rintro ⟨a, ha⟩
    refine ⟨(unitAut a).asIso, L.dualSectionEquiv.injective ?_⟩
    rw [unitsGlobalSectionsMulEquivAut_apply_hom, globalSectionsSmul_naturality,
      dualSectionEquiv_comp_globalSectionsSmul]
    simpa only [ψ, φ, Equiv.apply_symm_apply] using ha

/-- Every effective Cartier divisor with the class of the bundle is the zero divisor of a
nonzero section of that bundle. -/
theorem exists_zeroDivisor_eq {D : Scheme.CartierDivisor X} (hD : D.IsEffective)
    (hL : D.toLineBundleClass = LineBundleClass.mk L) :
    ∃ (s : Γ(L.obj, ⊤)) (hs : s ≠ 0), L.zeroDivisor hs = D := by
  let I := hD.idealSheaf
  let hI := hD.isEffectiveCartier_idealSheaf
  have hclass : LineBundleClass.mk (dual L) = LineBundleClass.mk hI.toInvertibleSheaf := by
    rw [hD.mk_idealSheaf_eq_inv, hL, ← LineBundleClass.inv_mk]
  obtain ⟨e⟩ := LineBundleClass.mk_eq_mk_iff.mp hclass
  let e' : (dual L).obj ≅ I.sheaf :=
    e ≪≫ eqToIso (Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheaf_obj hI)
  let φ : (dual L).obj ⟶ 𝟙_ X.Modules := e'.hom ≫ I.sheafι
  have hφ : φ.imageIdealSheaf = I := by
    exact (I.sheafι.imageIdealSheaf_comp_iso e').trans I.imageIdealSheaf_sheafι
  have : Mono φ := mono_comp _ _
  have hφne : φ ≠ 0 := by
    intro hz
    have hzero := Limits.IsZero.of_mono_eq_zero φ hz
    have : TauCeti.SheafOfModules.IsInvertible (R := X.ringCatSheaf) (dual L).obj :=
      (dual L).property
    exact one_ne_zero <| globalSectionsSmul_injective (dual L).obj <| hzero.eq_of_src _ _
  let s := L.dualSectionEquiv φ
  have hs : s ≠ 0 := fun h ↦
    hφne (L.dualSectionEquiv.injective (h.trans L.dualSectionEquiv_zero.symm))
  refine ⟨s, hs, ?_⟩
  rw [← hD.toCartierDivisor_idealSheaf, zeroDivisor,
    Scheme.IdealSheafData.IsEffectiveCartier.toCartierDivisor_eq_iff, zeroIdeal,
    Equiv.symm_apply_apply]
  exact hφ

end

end TauCeti.AlgebraicGeometry.InvertibleSheaf
