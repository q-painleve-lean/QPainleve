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
import QPainleve.AlgebraicGeometry.IdealSheaf.Image.Basic
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
