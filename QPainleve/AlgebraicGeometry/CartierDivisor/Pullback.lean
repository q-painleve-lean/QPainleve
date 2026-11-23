/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.CartierDivisor.ZeroDivisor
public import TauCeti.AlgebraicGeometry.LineBundle.Pullback
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections
public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import QPainleve.AlgebraicGeometry.IdealSheaf.Image
import QPainleve.AlgebraicGeometry.IdealSheaf.Image.Basic
import QPainleve.AlgebraicGeometry.Modules.Pullback.Sections
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import TauCeti.AlgebraicGeometry.Modules.Pullback.InternalHom.Coherence
import QPainleve.AlgebraicGeometry.VectorBundle.SectionZeroLocus

/-!
# Pullback of zero schemes of line bundle sections

The zero ideal of a line bundle section commutes with arbitrary scheme pullback.
This identifies the ideal of a pulled-back section with the total transform of
its zero divisor in applications to blowups. The comparison specializes
`FiniteLocallyFreeSheaf.imageIdealSheaf_evaluation_pullback_section` to line bundles.
-/

public section

open AlgebraicGeometry CategoryTheory MonoidalCategory MonoidalClosed
open Scheme.Modules

universe u

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

noncomputable section

variable {X Y : Scheme.{u}}

local instance (L : InvertibleSheaf X) :
    ((ihom L.obj).obj (𝟙_ X.Modules)).IsQuasicoherent := by
  let e : (dual L).obj ≅ (ihom L.obj).obj (𝟙_ X.Modules) := eqToIso (dual_obj L)
  let : TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X
      ((ihom L.obj).obj (𝟙_ X.Modules)) :=
    (TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X).prop_of_iso e (dual L).property
  infer_instance

private theorem zeroIdeal_eq_evaluation_image (L : InvertibleSheaf X) (s : Γ(L.obj, ⊤)) :
    L.zeroIdeal s =
      ((L.obj.dualHomUnitEquiv).symm (L.obj.unitHomEquivTop.symm s)).imageIdealSheaf := by
  let φ := L.dualSectionEquiv.symm s
  let e : (dual L).obj ≅ (ihom L.obj).obj (𝟙_ X.Modules) := eqToIso (dual_obj L)
  have hsec : L.obj.unitHomEquivTop (L.obj.dualHomUnitEquiv (e.inv ≫ φ)) = s :=
    (L.dualSectionEquiv_apply φ).symm.trans (L.dualSectionEquiv.apply_symm_apply s)
  have hφ : (L.obj.dualHomUnitEquiv).symm (L.obj.unitHomEquivTop.symm s) = e.inv ≫ φ := by
    rw [L.obj.unitHomEquivTop.symm_apply_eq.mpr hsec.symm, Equiv.symm_apply_apply]
  rw [hφ]
  refine Eq.trans ?_ (φ.imageIdealSheaf_comp_iso e.symm).symm
  ext U x
  rw [zeroIdeal_ideal, Scheme.Modules.Hom.imageIdealSheaf_ideal]

/-- The ideal sheaf of the zero scheme of a section pulls back with the section. -/
theorem zeroIdeal_pullbackSections (L : InvertibleSheaf Y) (g : X ⟶ Y)
    (s : Γ(L.obj, ⊤)) :
    ((pullback g).obj L).zeroIdeal (g.pullbackSections L.obj ⊤ s) =
      (L.zeroIdeal s).comap g := by
  let E := (toFiniteLocallyFree Y).obj L
  let L' := (pullback g).obj L
  let t : Γ(L'.obj, ⊤) := g.pullbackSections L.obj ⊤ s
  exact (zeroIdeal_eq_evaluation_image L' t).trans
    ((E.imageIdealSheaf_evaluation_pullback_section s g).trans
      (congrArg (·.comap g) (zeroIdeal_eq_evaluation_image L s)).symm)

/-- When a pulled-back Cartier ideal is the zero ideal of a nonzero section on an
integral scheme, the dual line bundle identifies with that pulled-back ideal.
The identification intertwines evaluation and the ideal inclusion. -/
theorem exists_iso_pullbackSheaf_of_zeroIdeal [IsIntegral X]
    (L : InvertibleSheaf X) (f : X ⟶ Y) {I : Y.IdealSheafData} (hI : I.IsEffectiveCartier)
    {s : Γ(L.obj, ⊤)} (hs : s ≠ 0) (h : L.zeroIdeal s = I.comap f) :
    ∃ e : (dual L).obj ≅ (Scheme.Modules.pullback f).obj I.sheaf,
      e.hom ≫ (Scheme.Modules.pullback f).map I.sheafι ≫ (pullbackObjUnitIso f).hom =
        L.dualSectionEquiv.symm s := by
  let φ := L.dualSectionEquiv.symm s
  have : Mono φ := L.dualSectionEquiv_symm_mono hs
  have : IsIso (I.pullbackSheafHom f) :=
    I.isIso_pullbackSheafHom f hI (h ▸ L.isEffectiveCartier_zeroIdeal hs)
  have hφ : φ.imageIdealSheaf = I.comap f := by
    simpa only [φ, Equiv.apply_symm_apply, h] using (L.zeroIdeal_dualSectionEquiv φ).symm
  have himage : φ.imageIdealSheaf = (I.comap f).sheafι.imageIdealSheaf :=
    hφ.trans (I.comap f).imageIdealSheaf_sheafι.symm
  obtain ⟨e, he⟩ := (φ.imageIdealSheaf_eq_iff_exists_iso_comp_eq (I.comap f).sheafι).mp himage
  refine ⟨e ≪≫ (asIso (I.pullbackSheafHom f)).symm, ?_⟩
  rw [← I.pullbackSheafHom_sheafι f]
  simpa only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc,
    IsIso.inv_hom_id_assoc] using he

/-- A scalar comparison of pulled-back sections is the same scalar comparison of
their pulled-back evaluations on the dual. -/
theorem pullback_map_dualSectionEquiv_symm_eq_smul (L : InvertibleSheaf Y)
    (f : X ⟶ Y) {s t : Γ(L.obj, ⊤)} (a : Γ(X, ⊤))
    (h : f.pullbackSections L.obj ⊤ s = a • f.pullbackSections L.obj ⊤ t) :
    (Scheme.Modules.pullback f).map (L.dualSectionEquiv.symm s) ≫ (pullbackObjUnitIso f).hom =
      (Scheme.Modules.pullback f).map (L.dualSectionEquiv.symm t) ≫ (pullbackObjUnitIso f).hom ≫
        globalSectionsSmul (𝟙_ X.Modules) a := by
  let P := Scheme.Modules.pullback f
  let K := (InvertibleSheaf.pullback f).obj L
  let e := eqToIso (dual_obj L)
  let e' := eqToIso (dual_obj K)
  let b := (pullbackIhomComparison L.obj f).app (𝟙_ Y.Modules) ≫
    (ihom K.obj).map (pullbackObjUnitIso f).hom
  let c := (P.map e.hom ≫ b) ≫ e'.inv
  let pb (r : Γ(L.obj, ⊤)) : Γ(K.obj, ⊤) :=
    f.pullbackSectionsLE L.obj ⊤ ⊤ f.preimage_top.ge r
  have he (r : Γ(L.obj, ⊤)) :
      P.map (L.dualSectionEquiv.symm r) ≫ (pullbackObjUnitIso f).hom =
        c ≫ K.dualSectionEquiv.symm (pb r) := by
    have hr : K.obj.unitHomEquivTop.symm (pb r) =
        (pullbackObjUnitIso f).inv ≫ P.map (L.obj.unitHomEquivTop.symm r) :=
      (congrArg K.obj.unitHomEquivTop.symm (f.pullbackSectionsLE_top r)).trans
        (f.unitHomEquivTop_symm_pullbackSections r)
    let sy : 𝟙_ Y.Modules ⟶ L.obj := L.obj.unitHomEquivTop.symm r
    let sx : 𝟙_ X.Modules ⟶ K.obj := K.obj.unitHomEquivTop.symm (pb r)
    let vy := (dualHomUnitEquiv L.obj).symm sy
    let vx := (dualHomUnitEquiv K.obj).symm sx
    have hv : P.map vy ≫ (pullbackObjUnitIso f).hom = b ≫ vx := by
      have hy := Scheme.Modules.dualHomUnitEquiv_symm_apply L.obj sy
      let ev (t : 𝟙_ X.Modules ⟶ K.obj) :=
        (λ_ _).inv ≫ t ▷ (ihom K.obj).obj (𝟙_ X.Modules) ≫
          (ihom.ev K.obj).app (𝟙_ X.Modules)
      have hx : vx = ev sx := Scheme.Modules.dualHomUnitEquiv_symm_apply K.obj sx
      have hsx : sx = (pullbackObjUnitIso f).inv ≫ P.map sy := hr
      have hxe := hx.trans (congrArg ev hsx)
      refine (congrArg (fun t ↦ P.map t ≫ (pullbackObjUnitIso f).hom) hy).trans
        ((f.pullback_map_evaluation_comp_pullbackObjUnitIso_hom L.obj sy).trans ?_)
      exact (Category.assoc _ _ _).symm.trans (congrArg (b ≫ ·) hxe.symm)
    calc
      _ = P.map (e.hom ≫ vy) ≫ (pullbackObjUnitIso f).hom :=
        congrArg (fun v ↦ P.map v ≫ (pullbackObjUnitIso f).hom) (L.dualSectionEquiv_symm_apply r)
      _ = P.map e.hom ≫ P.map vy ≫ (pullbackObjUnitIso f).hom :=
        (congrArg (· ≫ (pullbackObjUnitIso f).hom) (P.map_comp e.hom vy)).trans
          (Category.assoc _ _ _)
      _ = P.map e.hom ≫ b ≫ vx := congrArg (P.map e.hom ≫ ·) hv
      _ = (P.map e.hom ≫ b) ≫ vx := (Category.assoc _ _ _).symm
      _ = (P.map e.hom ≫ b) ≫ e'.inv ≫ e'.hom ≫ vx :=
        congrArg ((P.map e.hom ≫ b) ≫ ·) (e'.inv_hom_id_assoc vx).symm
      _ = c ≫ (e'.hom ≫ vx) := (Category.assoc _ _ _).symm
      _ = _ := (congrArg (c ≫ ·) (K.dualSectionEquiv_symm_apply (pb r))).symm
  have ha : X.presheaf.map (f ⁻¹ᵁ (⊤ : Y.Opens)).leTop.op a = a :=
    (congrArg (fun g : Γ(X, ⊤) ⟶ Γ(X, ⊤) ↦ g a)
      (X.presheaf.map_id (Opposite.op ⊤))).trans (id_apply a)
  have h' : pb s = a • pb t := by
    simpa only [pb, Scheme.Hom.pullbackSectionsLE_top, ha] using!
      h.trans (K.obj.sectionsGlobal_smul (f ⁻¹ᵁ (⊤ : Y.Opens)) a (f.pullbackSections L.obj ⊤ t))
  have hscalar : K.dualSectionEquiv.symm (pb s) =
      K.dualSectionEquiv.symm (pb t) ≫ globalSectionsSmul (𝟙_ X.Modules) a := by
    apply K.dualSectionEquiv.injective
    simpa only [dualSectionEquiv_comp_globalSectionsSmul, Equiv.apply_symm_apply] using h'
  exact (he s).trans ((congrArg (c ≫ ·) hscalar).trans
    ((reassoc_of% (he t)) _).symm)

/-- The sum of the zero ideals of a family of sections pulls back with the family. -/
theorem iSup_zeroIdeal_pullbackSections (L : InvertibleSheaf Y) (g : X ⟶ Y) {ι : Sort*}
    (s : ι → Γ(L.obj, ⊤)) :
    (⨆ i, ((pullback g).obj L).zeroIdeal (g.pullbackSections L.obj ⊤ (s i))) =
      (⨆ i, L.zeroIdeal (s i)).comap g := by
  exact (congrArg iSup (funext fun i ↦ L.zeroIdeal_pullbackSections g (s i))).trans
    ((Scheme.IdealSheafData.map_gc g).l_iSup (f := fun i ↦ L.zeroIdeal (s i))).symm

/-- Pullback along a dominant morphism to a reduced scheme is injective on
global sections of a line bundle. -/
theorem pullbackSections_injective_of_isDominant [IsReduced Y] (L : InvertibleSheaf Y)
    (g : X ⟶ Y) [IsDominant g] : Function.Injective (g.pullbackSections L.obj ⊤) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro s hs'
  by_contra hs
  let L' := (pullback g).obj L
  have hz : L'.zeroIdeal 0 = ⊥ := by
    rw [zeroIdeal_eq_evaluation_image, Scheme.Modules.Hom.imageIdealSheaf_eq_bot_iff]
    have hunit := L'.obj.unitHomEquivTop.symm_apply_eq.mpr
      (Scheme.Modules.unitHomEquivTop_zero L'.obj).symm
    exact L'.obj.dualHomUnitEquiv.symm_apply_eq.mpr
      (hunit.trans (Scheme.Modules.dualHomUnitEquiv_zero L'.obj).symm)
  let I := L.zeroIdeal s
  let v : 𝟙_ Y.Modules ⟶ L.obj := L.obj.unitHomEquivTop.symm s
  let φ := L.obj.dualHomUnitEquiv.symm v
  have hv : v ≠ 0 := fun h ↦ hs ((L.obj.unitHomEquivTop.symm_apply_eq.mp h).trans
    (Scheme.Modules.unitHomEquivTop_zero L.obj))
  have hφ : φ ≠ 0 := fun h ↦ hv ((L.obj.dualHomUnitEquiv.symm_apply_eq.mp h).trans
    (Scheme.Modules.dualHomUnitEquiv_zero L.obj))
  have hproper : ((I.support : Set Y)ᶜ).Nonempty := by
    dsimp only [I]
    rw [zeroIdeal_eq_evaluation_image]
    exact φ.nonempty_compl_support_imageIdealSheaf hφ
  obtain ⟨x, hx⟩ := g.denseRange.exists_mem_open I.support.isClosed.isOpen_compl hproper
  have h : (⊥ : X.IdealSheafData) = I.comap g :=
    hz.symm.trans ((congrArg L'.zeroIdeal hs').symm.trans (L.zeroIdeal_pullbackSections g s))
  apply hx
  have heq := congrArg Scheme.IdealSheafData.support h
  rw [Scheme.IdealSheafData.support_bot, Scheme.IdealSheafData.support_comap] at heq
  have hx_top : x ∈ (⊤ : TopologicalSpace.Closeds X) := Set.mem_univ x
  exact (heq ▸ hx_top : x ∈ (I.support.preimage g.continuous : Set X))

end

end TauCeti.AlgebraicGeometry.InvertibleSheaf
