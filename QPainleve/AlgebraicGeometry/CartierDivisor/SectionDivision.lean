/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.CartierDivisor.ZeroDivisor
import QPainleve.AlgebraicGeometry.IdealSheaf.TensorProduct
import QPainleve.AlgebraicGeometry.IdealSheaf.Image
import TauCeti.AlgebraicGeometry.IdealSheaf.Colon

/-!
# Dividing sections by an effective Cartier divisor

If a section of a line bundle vanishes along an effective Cartier divisor, it comes from a
unique section of the line bundle twisted by the divisor's ideal sheaf. The inclusion is
the tensor product of the ideal inclusion with the identity on the original line bundle.
This is the section form of the effective Cartier divisor correspondence in the Stacks
Project, [Lemma 31.15.10](https://stacks.math.columbia.edu/tag/01X0).
-/

public noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

variable {X : Scheme.{u}} (L : InvertibleSheaf X) {I : X.IdealSheafData}

/-- The underlying sheaf of the Cartier twist is the ideal tensored with the line bundle. -/
def idealTwistIso (hI : I.IsEffectiveCartier) :
    (hI.toInvertibleSheaf.tensorProduct L).obj ≅ I.sheaf ⊗ L.obj :=
  tensorProductObjIso hI.toInvertibleSheaf L ≪≫
    eqToIso (congrArg (· ⊗ L.obj) hI.toInvertibleSheaf_obj)

/-- The canonical inclusion of the twist by the ideal of an effective Cartier divisor. -/
def idealTwistInclusion (hI : I.IsEffectiveCartier) :
    (hI.toInvertibleSheaf.tensorProduct L).obj ⟶ L.obj :=
  (L.idealTwistIso hI).hom ≫ I.sheafι ▷ L.obj ≫ (λ_ L.obj).hom

/-- The inclusion is induced by the ideal inclusion on the first tensor factor. -/
@[reassoc]
theorem idealTwistInclusion_eq (hI : I.IsEffectiveCartier) :
    idealTwistInclusion L hI =
      (L.idealTwistIso hI).hom ≫ I.sheafι ▷ L.obj ≫ (λ_ L.obj).hom :=
  (rfl)

instance (hI : I.IsEffectiveCartier) : Mono (L.idealTwistInclusion hI) := by
  have h := L.tensorRightDualEquivalence.inverse.map_mono I.sheafι
  rw [tensorRightDualEquivalence_inverse] at h
  have : Mono (I.sheafι ▷ L.obj) := h
  rw [idealTwistInclusion_eq]
  infer_instance

-- Use the dual sheaf in the monoidal category of scheme modules.
private def sectionToFunctional :
    Γ(L.obj, ⊤) ≃ ((ihom L.obj).obj (𝟙_ X.Modules) ⟶ 𝟙_ X.Modules) :=
  L.obj.unitHomEquivTop.symm.trans (dualHomUnitEquiv L.obj).symm

/-- A section lies in the effective Cartier twist exactly when its zero ideal is contained
in the divisor ideal. The section of the twist is unique. -/
theorem existsUnique_idealTwist_section_iff (hI : I.IsEffectiveCartier)
    (s : Γ(L.obj, ⊤)) :
    (∃! t : Γ((hI.toInvertibleSheaf.tensorProduct L).obj, ⊤),
        (L.idealTwistInclusion hI).app ⊤ t = s) ↔ L.zeroIdeal s ≤ I := by
  let K := hI.toInvertibleSheaf.tensorProduct L
  let e := L.idealTwistIso hI
  let i := L.idealTwistInclusion hI
  let φ := sectionToFunctional L s
  have hs : dualHomUnitEquiv L.obj φ = L.obj.unitHomEquivTop.symm s :=
    (dualHomUnitEquiv L.obj).apply_symm_apply _
  have hzero : L.zeroIdeal s = φ.imageIdealSheaf := L.zeroIdeal_eq_imageIdealSheaf_evaluation s
  rw [hzero, ← exists_tensorLift_iff, hs]
  constructor
  · rintro ⟨t, ht, -⟩
    let τ : 𝟙_ X.Modules ⟶ K.obj := K.obj.unitHomEquivTop.symm t
    have hh : τ ≫ i = L.obj.unitHomEquivTop.symm s := by
      apply L.obj.unitHomEquivTop.injective
      exact (unitHomEquivTop_comp K.obj τ i).trans
        ((congrArg (i.app ⊤) (K.obj.unitHomEquivTop.apply_symm_apply t)).trans
          (ht.trans (L.obj.unitHomEquivTop.apply_symm_apply s).symm))
    exact ⟨τ ≫ e.hom, (Category.assoc _ _ _).trans (by
      simpa only [i, e, idealTwistInclusion_eq] using hh)⟩
  · rintro ⟨t, ht⟩
    let τ : 𝟙_ X.Modules ⟶ K.obj := t ≫ e.inv
    have hcomp : τ ≫ i = L.obj.unitHomEquivTop.symm s :=
      (Category.assoc t e.inv i).trans (by
        simpa only [i, e, idealTwistInclusion_eq, Iso.inv_hom_id_assoc] using ht)
    let t' := K.obj.unitHomEquivTop τ
    have ht' : i.app ⊤ t' = s :=
      (unitHomEquivTop_comp K.obj τ i).symm.trans
        ((congrArg L.obj.unitHomEquivTop hcomp).trans (Equiv.apply_symm_apply _ _))
    refine ⟨t', ht', fun y hy ↦ ?_⟩
    apply K.obj.unitHomEquivTop.symm.injective
    apply (cancel_mono i).mp
    let σ : 𝟙_ X.Modules ⟶ K.obj := K.obj.unitHomEquivTop.symm y
    have hσ : σ ≫ i = L.obj.unitHomEquivTop.symm s := by
      apply L.obj.unitHomEquivTop.injective
      exact (unitHomEquivTop_comp K.obj σ i).trans
        ((congrArg (i.app ⊤) (K.obj.unitHomEquivTop.apply_symm_apply y)).trans
          (hy.trans (L.obj.unitHomEquivTop.apply_symm_apply s).symm))
    exact hσ.trans (hcomp.symm.trans
      (congrArg (· ≫ i) (K.obj.unitHomEquivTop.symm_apply_apply τ).symm))

private theorem exists_iso_tensorLift_iff (φ : (ihom L.obj).obj (𝟙_ X.Modules) ⟶ 𝟙_ X.Modules)
    [Mono φ] :
    (∃ e : 𝟙_ X.Modules ≅ I.sheaf ⊗ L.obj,
      e.hom ≫ I.sheafι ▷ L.obj ≫ (λ_ L.obj).hom = dualHomUnitEquiv L.obj φ) ↔
        φ.imageIdealSheaf = I := by
  let M := L.obj
  let i : I.sheaf ⟶ 𝟙_ X.Modules := I.sheafι
  let E := dualHomTensorEquiv M I.sheaf
  have heval (ψ : (ihom M).obj (𝟙_ X.Modules) ⟶ I.sheaf) :
      dualHomUnitEquiv M (ψ ≫ i) = E ψ ≫ i ▷ M ≫ (λ_ M).hom := by
    rw [← dualHomTensorEquiv_comp_leftUnitor, dualHomTensorEquiv_comp, Category.assoc]
  constructor
  · rintro ⟨e, he⟩
    let ψ := E.symm e.hom
    have hψ : E ψ = e.hom := E.apply_symm_apply _
    have : IsIso (E ψ) := hψ ▸ inferInstance
    have hIso : IsIso ψ := (isIso_dualHomTensorEquiv_iff L ψ).mp ‹_›
    have hφ : ψ ≫ i = φ := (dualHomUnitEquiv M).injective (by rw [heval, hψ]; exact he)
    have hImg : (ψ ≫ i).imageIdealSheaf = i.imageIdealSheaf :=
      i.imageIdealSheaf_comp_iso (asIso ψ)
    rw [← hφ, hImg]
    exact I.imageIdealSheaf_sheafι
  · intro h
    subst I
    let ψ := φ.toImageIdealSheaf
    have hIso : IsIso (dualHomTensorEquiv M φ.imageIdealSheaf.sheaf ψ) :=
      (isIso_dualHomTensorEquiv_iff L ψ).mpr inferInstance
    exact ⟨asIso _, (heval ψ).symm.trans
      (congrArg (dualHomUnitEquiv M) φ.toImageIdealSheaf_ι)⟩

private theorem sectionToFunctional_mono [IsIntegral X] {s : Γ(L.obj, ⊤)} (hs : s ≠ 0) :
    Mono (sectionToFunctional L s) := by
  let D : InvertibleSheaf X := dual L
  let e : D.obj ≅ (ihom L.obj).obj (𝟙_ X.Modules) := eqToIso (dual_obj L)
  let f := e.hom ≫ sectionToFunctional L s
  have h : f ≠ 0 := by
    intro hf
    apply hs
    have hz : sectionToFunctional L s = 0 :=
      (cancel_epi e.hom).mp (hf.trans (Limits.comp_zero (f := e.hom)).symm)
    apply L.obj.unitHomEquivTop.symm.injective
    exact ((dualHomUnitEquiv L.obj).apply_symm_apply _).symm.trans
      ((congrArg (dualHomUnitEquiv L.obj) hz).trans
        ((dualHomUnitEquiv_zero L.obj).trans
          (L.obj.unitHomEquivTop.symm_apply_eq.mpr (unitHomEquivTop_zero L.obj).symm).symm))
  have : Mono f := D.mono_of_ne_zero_to_unit f h
  have hfac : e.inv ≫ f = sectionToFunctional L s := e.inv_hom_id_assoc _
  rw [← hfac]
  infer_instance

/-- The zero ideal of a nonzero section is the ideal for which division yields a frame
of the twisted line bundle. -/
theorem zeroIdeal_eq_iff_exists_iso_tensorLift [IsIntegral X]
    {s : Γ(L.obj, ⊤)} (hs : s ≠ 0) :
    L.zeroIdeal s = I ↔
      ∃ e : 𝟙_ X.Modules ≅ I.sheaf ⊗ L.obj,
        e.hom ≫ I.sheafι ▷ L.obj ≫ (λ_ L.obj).hom = L.obj.unitHomEquivTop.symm s := by
  let φ := sectionToFunctional L s
  have : Mono φ := sectionToFunctional_mono L hs
  have heval : dualHomUnitEquiv L.obj φ = L.obj.unitHomEquivTop.symm s :=
    (dualHomUnitEquiv L.obj).apply_symm_apply _
  have hzero : L.zeroIdeal s = φ.imageIdealSheaf := L.zeroIdeal_eq_imageIdealSheaf_evaluation s
  rw [hzero, ← heval]
  exact (exists_iso_tensorLift_iff L φ).symm

/-- The zero ideal of a section mapped through the Cartier twist inclusion is the
product of its original zero ideal with the divisor ideal. -/
theorem zeroIdeal_idealTwistInclusion [IsIntegral X] (hI : I.IsEffectiveCartier)
    (t : Γ((hI.toInvertibleSheaf.tensorProduct L).obj, ⊤)) :
    L.zeroIdeal ((L.idealTwistInclusion hI).app ⊤ t) =
      ((hI.toInvertibleSheaf.tensorProduct L).zeroIdeal t) * I := by
  let H := hI.toInvertibleSheaf.tensorProduct L
  let s := (L.idealTwistInclusion hI).app ⊤ t
  by_cases hs : s = 0
  · have hLift := (L.existsUnique_idealTwist_section_iff hI 0).mpr (by simp)
    have ht : t = 0 := hLift.unique hs (map_zero _)
    have ht' : L.zeroIdeal s = ⊥ := hs ▸ L.zeroIdeal_zero
    calc
      _ = ⊥ := ht'
      _ = _ := by
        rw [ht, zeroIdeal_zero]
        ext U a
        simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply,
          Scheme.IdealSheafData.ideal_bot, Pi.bot_apply, Ideal.bot_mul]
  have ht : t ≠ 0 := fun h ↦ hs
    ((congrArg ((L.idealTwistInclusion hI).app ⊤) h).trans (map_zero _))
  let J := H.zeroIdeal t
  obtain ⟨e, he⟩ := (H.zeroIdeal_eq_iff_exists_iso_tensorLift (I := J) ht).mp rfl
  let i := L.idealTwistIso hI
  have := J.isIso_sheafMul_of_isEffectiveCartier I hI
  let d := e ≪≫ whiskerLeftIso J.sheaf i ≪≫ (α_ J.sheaf I.sheaf L.obj).symm ≪≫
    whiskerRightIso (asIso (J.sheafMul I)) L.obj
  refine (L.zeroIdeal_eq_iff_exists_iso_tensorLift (I := J * I) hs).mpr ⟨d, ?_⟩
  have hs' : (H.obj.unitHomEquivTop.symm t : 𝟙_ X.Modules ⟶ H.obj) ≫
      L.idealTwistInclusion hI = L.obj.unitHomEquivTop.symm s := by
    apply L.obj.unitHomEquivTop.injective
    rw [unitHomEquivTop_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rw [← hs', ← he]
  simp only [d, Iso.trans_hom, whiskerLeftIso_hom, whiskerRightIso_hom, Iso.symm_hom,
    asIso_hom, Category.assoc]
  erw [J.sheafMul_whiskerRight_comp_sheafι I L.obj]
  simp only [idealTwistInclusion_eq, i]
  -- The ideal inclusions have target the structure sheaf, presented here as the tensor unit.
  erw [whisker_exchange_assoc, leftUnitor_naturality_assoc]
  let j : J.sheaf ⟶ 𝟙_ X.Modules := J.sheafι
  exact ((Category.assoc e.hom (j ▷ H.obj ≫ (λ_ H.obj).hom) _).trans
    (congrArg (e.hom ≫ ·) (Category.assoc (j ▷ H.obj) (λ_ H.obj).hom _))).symm

/-- If the common zero ideal of a family of sections is effective Cartier, dividing
by that ideal gives sections whose nonvanishing loci cover the scheme. -/
theorem exists_idealTwist_sections_of_cartier_base_ideal [IsIntegral X] {ι : Type*}
    (s : ι → Γ(L.obj, ⊤)) (hI : (⨆ i, L.zeroIdeal (s i)).IsEffectiveCartier) :
    let K := hI.toInvertibleSheaf.tensorProduct L
    ∃ t : ι → Γ(K.obj, ⊤),
      (∀ i, (L.idealTwistInclusion hI).app ⊤ (t i) = s i) ∧
      (⨆ i, Scheme.Modules.nonvanishingLocus K.obj (t i)) = ⊤ := by
  let J := ⨆ i, L.zeroIdeal (s i)
  let K := hI.toInvertibleSheaf.tensorProduct L
  choose t ht using fun i ↦
    ((L.existsUnique_idealTwist_section_iff hI (s i)).mpr
      (le_iSup (fun j ↦ L.zeroIdeal (s j)) i)).exists
  refine ⟨t, ht, (K.iSup_nonvanishingLocus_eq_top_iff t).mpr ?_⟩
  have hmul : (⨆ i, K.zeroIdeal (t i)) * J = J := by
    rw [(J.gc_mul_colon).l_iSup]
    exact iSup_congr fun i ↦ (L.zeroIdeal_idealTwistInclusion hI (t i)).symm.trans
      (congrArg L.zeroIdeal (ht i))
  exact hI.mul_left_cancel (by simpa only [mul_comm, Scheme.IdealSheafData.top_mul] using hmul)

end TauCeti.AlgebraicGeometry.InvertibleSheaf
