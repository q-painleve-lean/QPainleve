/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections
public import TauCeti.AlgebraicGeometry.Modules.Sections

/-!
# Pullback of global sections as morphisms

The equivalence between global sections of a sheaf of modules and morphisms from
the structure sheaf commutes with pullback.
-/

public section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Pulling a global section back to the top open agrees with its canonical pullback. -/
theorem pullbackSectionsLE_top {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules} (s : Γ(M, ⊤)) :
    f.pullbackSectionsLE M ⊤ ⊤ f.preimage_top.ge s = f.pullbackSections M ⊤ s := by
  let N := (Modules.pullback f).obj M
  let a : Γ(N, ⊤) := f.pullbackSections M ⊤ s
  refine (f.pullbackSectionsLE_apply M ⊤ ⊤ f.preimage_top.ge s).trans ?_
  exact (congrArg (fun h : Γ(N, ⊤) ⟶ Γ(N, ⊤) ↦ h a)
    (N.presheaf.map_id (Opposite.op ⊤))).trans (id_apply a)

/-- Comparing canonical pullbacks by a scalar also compares the pullbacks
viewed as sections over the top open. -/
theorem pullbackSectionsLE_top_eq_smul {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Y.Modules} {s t : Γ(M, ⊤)} (a : Γ(X, ⊤))
    (h : f.pullbackSections M ⊤ s = a • f.pullbackSections M ⊤ t) :
    f.pullbackSectionsLE M ⊤ ⊤ f.preimage_top.ge s =
      a • f.pullbackSectionsLE M ⊤ ⊤ f.preimage_top.ge t := by
  let N := (Modules.pullback f).obj M
  let l := N.sectionsRestrictionLinear (homOfLE f.preimage_top.ge)
  let v := f.pullbackSections M ⊤ t
  have hl := by
    letI := N.sectionsGlobalModule (⊤ : X.Opens)
    exact _root_.map_smul l a v
  have ha : X.presheaf.map (⊤ : X.Opens).leTop.op a = a :=
    (congrArg (fun g : Γ(X, ⊤) ⟶ Γ(X, ⊤) ↦ g a)
      (X.presheaf.map_id (Opposite.op ⊤))).trans (id_apply a)
  have hv := N.sectionsGlobal_smul ⊤ a (l v)
  have hb (r : Γ(M, ⊤)) :
      f.pullbackSectionsLE M ⊤ ⊤ f.preimage_top.ge r = l (f.pullbackSections M ⊤ r) :=
    (f.pullbackSectionsLE_apply M ⊤ ⊤ f.preimage_top.ge r).trans
      ((N.sectionsRestrictionLinear_apply _ _).symm)
  exact (hb s).trans ((congrArg l h).trans (hl.trans (hv.trans
    ((congrArg (· • l v) ha).trans (congrArg (a • ·) (hb t).symm)))))

/-- Pulling back the morphism of a global section gives the morphism of its pullback. -/
theorem unitHomEquivTop_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Y.Modules} (s : 𝟙_ Y.Modules ⟶ M) :
    ((Modules.pullback f).obj M).unitHomEquivTop
        ((Modules.pullbackObjUnitIso f).inv ≫ (Modules.pullback f).map s) =
      f.pullbackSections M ⊤ (M.unitHomEquivTop s) := by
  have h := (congrArg (((Modules.pullback f).map s).app (f ⁻¹ᵁ ⊤) ·)
    (f.pullbackObjUnitIso_inv_app_one)).trans
    (f.pullbackSections_naturality _ ⊤ s (1 : Γ(Y, ⊤)))
  exact (Modules.unitHomEquivTop_apply _ _).trans
    (h.trans (congrArg (f.pullbackSections M ⊤) (Modules.unitHomEquivTop_apply M s).symm))

/-- The morphism of the pulled-back section is the pullback of the morphism of the section. -/
theorem unitHomEquivTop_symm_pullbackSections {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Y.Modules} (s : Γ(M, ⊤)) :
    (((Modules.pullback f).obj M).unitHomEquivTop).symm (f.pullbackSections M ⊤ s) =
      (Modules.pullbackObjUnitIso f).inv ≫
        (Modules.pullback f).map (M.unitHomEquivTop.symm s) := by
  let t : 𝟙_ Y.Modules ⟶ M := M.unitHomEquivTop.symm s
  exact ((Modules.pullback f).obj M).unitHomEquivTop.symm_apply_eq.mpr
    ((f.unitHomEquivTop_pullback t).trans
      (congrArg (f.pullbackSections M ⊤) (M.unitHomEquivTop.apply_symm_apply s))).symm

end AlgebraicGeometry.Scheme.Hom
