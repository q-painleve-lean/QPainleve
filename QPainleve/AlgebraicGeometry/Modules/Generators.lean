/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GeneratingSections
import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Colimits

/-!
# Generating sections on affine opens

The restrictions of generating sections of a quasicoherent sheaf span its module of
sections over each affine open. This uses Tau Ceti's preservation of quasicoherent
coproducts by sections on affine opens.
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A generating family of a quasicoherent sheaf spans the sections on each affine open. -/
theorem _root_.SheafOfModules.GeneratingSections.span_restrict_eq_top_of_isAffineOpen
    {X : Scheme.{u}} {M : X.Modules}
    [M.IsQuasicoherent] (G : M.GeneratingSections) {U : X.Opens} (hU : IsAffineOpen U) :
    Submodule.span Γ(X, U) (Set.range fun i ↦ M.presheaf.map U.leTop.op
      (M.sectionsEquivTop (G.s i))) = ⊤ := by
  classical
  let F := sectionsFunctor U
  let P : X.Modules := SheafOfModules.free G.I
  let π : P ⟶ M := G.π
  have hπ : Epi π := G.epi
  let g (i : G.I) : 𝟙_ X.Modules ⟶ P := SheafOfModules.ιFree i
  let S := Submodule.span Γ(X, U) (Set.range fun i ↦ M.presheaf.map U.leTop.op
    (M.sectionsEquivTop (G.s i)))
  have hc : IsColimit (Cofan.mk P g) := SheafOfModules.isColimitFreeCofan G.I
  have hF := isColimitMapCoconeCofanMkEquiv F _ g
    (isColimitMapCoconeSectionsFunctor
      (fun _ ↦ inferInstanceAs (𝟙_ X.Modules).IsQuasicoherent) hc hU)
  have happ (i : G.I) (r : Γ(X, U)) :
      (g i ≫ π).app U r = r • M.presheaf.map U.leTop.op (M.sectionsEquivTop (G.s i)) := by
    have h := SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply G.π i
    rw [Equiv.apply_symm_apply] at h
    have htop : M.unitHomEquivTop (g i ≫ π) = M.sectionsEquivTop (G.s i) := by
      rw [M.unitHomEquivTop_apply, M.sectionsEquivTop_apply]
      exact (SheafOfModules.unitHomEquiv_apply_coe M (g i ≫ π) (op ⊤)).symm.trans
        (congrArg (fun s : M.sections ↦ s.val (op ⊤))
          ((Equiv.eq_symm_apply _).mp h.symm))
    have hf := congrArg (fun φ : 𝟙_ X.Modules ⟶ M ↦ φ.app U r)
      (M.unitHomEquivTop.symm_apply_apply (g i ≫ π))
    refine hf.symm.trans ((M.unitHomEquivTop_symm_val_app _ U r).trans ?_)
    exact congrArg (fun z : Γ(M, ⊤) ↦ r • M.presheaf.map U.leTop.op z) htop
  let a (i : G.I) : F.obj (𝟙_ X.Modules) ⟶ ModuleCat.of Γ(X, U) S :=
    ModuleCat.ofHom (((F.map (g i ≫ π)).hom).codRestrict S fun r ↦
      (happ i r).symm ▸ S.smul_mem r (Submodule.subset_span ⟨i, rfl⟩))
  let f := Cofan.IsColimit.desc hF a
  have hf : f ≫ ModuleCat.ofHom S.subtype = F.map π := by
    apply Cofan.IsColimit.hom_ext hF
    intro i
    -- The coprojections in the image cofan are the section maps of `g i`.
    change F.map (g i) ≫ f ≫ ModuleCat.ofHom S.subtype = F.map (g i) ≫ F.map π
    have hi : F.map (g i) ≫ f = a i := Cofan.IsColimit.fac hF a i
    rw [← Category.assoc, hi]
    exact (F.map_comp (g i) π).symm
  apply top_unique
  intro m _
  obtain ⟨x, rfl⟩ := Hom.app_surjective_of_epi_of_isAffineOpen π U hU m
  exact (ConcreteCategory.congr_hom hf x) ▸ (f x).property

end AlgebraicGeometry.Scheme.Modules
