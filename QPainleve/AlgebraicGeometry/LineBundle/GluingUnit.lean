/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Endomorphisms
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic

/-!
# Gluing units for line bundle trivializations

In a commutative square of schemes, two side trivializations of a module pull back to
trivializations on the overlap. Their comparison is multiplication by a global unit.
The gluing compatibility criterion describes how rescaling the side trivializations
affects this comparison.
-/

public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry
open Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {P Y Z : Scheme.{u}}

/-- The change in an overlap unit under rescaling of the two trivializations. -/
def lineGluingCoboundary (j : P ⟶ Y) (g : P ⟶ Z) :
    (Γ(Y, ⊤)ˣ × Γ(Z, ⊤)ˣ) →* Γ(P, ⊤)ˣ :=
  ((Units.map j.appTop.hom.toMonoidHom).comp (MonoidHom.fst _ _)) /
    ((Units.map g.appTop.hom.toMonoidHom).comp (MonoidHom.snd _ _))

@[simp]
theorem lineGluingCoboundary_apply (j : P ⟶ Y) (g : P ⟶ Z)
    (u : Γ(Y, ⊤)ˣ) (v : Γ(Z, ⊤)ˣ) :
    j.lineGluingCoboundary g (u, v) =
      Units.map j.appTop.hom.toMonoidHom u / Units.map g.appTop.hom.toMonoidHom v :=
  (rfl)

end AlgebraicGeometry.Scheme.Hom

namespace CategoryTheory.CommSq

variable {P Y Z X : Scheme.{u}} {j : P ⟶ Y} {g : P ⟶ Z} {f : Y ⟶ X} {i : Z ⟶ X}
  (h : CommSq j g f i)

private abbrev leftFrame {M : X.Modules} (e : (pullback f).obj M ≅ 𝟙_ Y.Modules) :
    (pullback (j ≫ f)).obj M ≅ 𝟙_ P.Modules :=
  ((pullbackComp j f).app M).symm ≪≫ (pullback j).mapIso e ≪≫ pullbackObjUnitIso j

private abbrev rightFrame {M : X.Modules} (d : (pullback i).obj M ≅ 𝟙_ Z.Modules) :
    (pullback (j ≫ f)).obj M ≅ 𝟙_ P.Modules :=
  ((pullbackComp g i ≪≫ pullbackCongr h.w.symm).app M).symm ≪≫
    (pullback g).mapIso d ≪≫ pullbackObjUnitIso g

/-- The unit taking the right trivialization to the left trivialization on the overlap. -/
def lineGluingUnit {M : X.Modules} (e : (pullback f).obj M ≅ 𝟙_ Y.Modules)
    (d : (pullback i).obj M ≅ 𝟙_ Z.Modules) : Γ(P, ⊤)ˣ :=
  (unitsGlobalSectionsMulEquivAut (𝟙_ P.Modules)).symm
    (Aut.of ((h.rightFrame d).symm ≪≫ leftFrame (j := j) e))

/-- A trivialization on one side of a commutative square induces a trivialization
of the iterated pullback along the other side. -/
@[simps! hom]
def pullbackTrivialization {M : X.Modules} (d : (pullback i).obj M ≅ 𝟙_ Z.Modules) :
    (pullback j).obj ((pullback f).obj M) ≅ 𝟙_ P.Modules :=
  (pullbackComp j f).app M ≪≫ (pullbackCongr h.w).app M ≪≫
    ((pullbackComp g i).app M).symm ≪≫ (pullback g).mapIso d ≪≫ pullbackObjUnitIso g

private theorem leftFrame_eq_rightFrame {M : X.Modules}
    (e : (pullback f).obj M ≅ 𝟙_ Y.Modules) (d : (pullback i).obj M ≅ 𝟙_ Z.Modules) :
    (leftFrame (j := j) e).hom =
      (h.rightFrame d).hom ≫ globalSectionsSmul (𝟙_ P.Modules) (h.lineGluingUnit e d) := by
  rw [lineGluingUnit, globalSectionsSmul_unitsGlobalSectionsMulEquivAut_symm]
  exact ((h.rightFrame d).hom_inv_id_assoc (leftFrame (j := j) e).hom).symm

/-- The left trivialization on the overlap is the right one followed by multiplication
by the gluing unit. -/
theorem lineGluingUnit_spec {M : X.Modules} (e : (pullback f).obj M ≅ 𝟙_ Y.Modules)
    (d : (pullback i).obj M ≅ 𝟙_ Z.Modules) :
    (pullbackComp j f).inv.app M ≫ (pullback j).map e.hom ≫ (pullbackObjUnitIso j).hom =
      (pullbackCongr h.w.symm).inv.app M ≫ (pullbackComp g i).inv.app M ≫
        (pullback g).map d.hom ≫ (pullbackObjUnitIso g).hom ≫
          globalSectionsSmul (𝟙_ P.Modules) (h.lineGluingUnit e d : Γ(P, ⊤)) := by
  simpa only [leftFrame, rightFrame, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    Iso.trans_inv, NatTrans.comp_app, Functor.mapIso_hom, Category.assoc] using
    h.leftFrame_eq_rightFrame e d

/-- A unit is the gluing unit precisely when its multiplication converts the right
trivialization on the overlap to the left trivialization. -/
theorem lineGluingUnit_eq_iff {M : X.Modules} (e : (pullback f).obj M ≅ 𝟙_ Y.Modules)
    (d : (pullback i).obj M ≅ 𝟙_ Z.Modules) (a : Γ(P, ⊤)ˣ) :
    h.lineGluingUnit e d = a ↔
      (pullbackComp j f).inv.app M ≫ (pullback j).map e.hom ≫ (pullbackObjUnitIso j).hom =
        (pullbackCongr h.w.symm).inv.app M ≫ (pullbackComp g i).inv.app M ≫
          (pullback g).map d.hom ≫ (pullbackObjUnitIso g).hom ≫
            globalSectionsSmul (𝟙_ P.Modules) (a : Γ(P, ⊤)) := by
  constructor
  · rintro rfl
    exact h.lineGluingUnit_spec e d
  · intro ha
    apply Units.ext
    apply (globalSectionsAction_bijective (𝟙_ P.Modules)).injective
    have hw := (h.lineGluingUnit_spec e d).symm.trans ha
    -- The common prefix is the right trivialization and therefore cancels.
    have hw' : (h.rightFrame d).hom ≫ globalSectionsSmul (𝟙_ P.Modules) (h.lineGluingUnit e d) =
        (h.rightFrame d).hom ≫ globalSectionsSmul (𝟙_ P.Modules) a := by
      simpa only [rightFrame, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.trans_inv,
        NatTrans.comp_app, Functor.mapIso_hom, Category.assoc] using hw
    simp only [globalSectionsAction_apply]
    exact congrArg End.of ((cancel_epi (h.rightFrame d).hom).mp hw')

private abbrev unitAut {W : Scheme.{u}} (u : Γ(W, ⊤)ˣ) :
    (𝟙_ W.Modules) ≅ (𝟙_ W.Modules) :=
  (unitsGlobalSectionsMulEquivAut (𝟙_ W.Modules) u).asIso

private theorem scalar_frame_transport {W T : Scheme.{u}} (p : T ⟶ W)
    {M N : W.Modules} (s : M ≅ 𝟙_ W.Modules) (t : N ≅ 𝟙_ W.Modules) (v : Γ(W, ⊤)ˣ) :
    (pullback p).mapIso (s ≪≫ unitAut v ≪≫ t.symm) =
      ((pullback p).mapIso s ≪≫ pullbackObjUnitIso p) ≪≫
        unitAut (Units.map p.appTop.hom.toMonoidHom v) ≪≫
          ((pullback p).mapIso t ≪≫ pullbackObjUnitIso p).symm := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_comp, unitsGlobalSectionsMulEquivAut_apply_hom, pullback_map_globalSectionsSmul,
    Units.coe_map, RingHom.toMonoidHom_eq_coe, Category.assoc,
    ← globalSectionsSmul_naturality_assoc, Iso.hom_inv_id_assoc]
  rfl

section Pullback

variable {P' Y' Z' X' : Scheme.{u}} {j' : P' ⟶ Y'} {g' : P' ⟶ Z'}
  {f' : Y' ⟶ X'} {i' : Z' ⟶ X'} {p : P' ⟶ P} {y : Y' ⟶ Y} {z : Z' ⟶ Z} {x : X' ⟶ X}

private theorem pullbackComp_inv_app_map_frame_hom {A B C D : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) {M : D.Modules}
    (e : (pullback c).obj M ≅ 𝟙_ C.Modules) :
    (pullbackComp a (b ≫ c)).inv.app M ≫
        (pullback a).map (leftFrame (j := b) e).hom ≫ (pullbackObjUnitIso a).hom =
      eqToHom (by rw [Category.assoc]) ≫ (leftFrame (j := a ≫ b) e).hom := by
  simp only [leftFrame, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc,
    pullbackComp_inv_app_comp_pullback_map_pullbackComp_inv_app_assoc]
  have hn := (pullbackComp a b).inv.naturality_assoc e.hom
    ((pullback a).map (pullbackObjUnitIso b).hom ≫ (pullbackObjUnitIso a).hom)
  simp only [Functor.comp_map] at hn
  rw [← hn, pullbackObjUnitIso_comp]

@[reassoc]
private theorem leftFrame_pullbackTrivialization
    (hf : CommSq f' y x f) (hj : CommSq j' p y j)
    {M : X.Modules} (e : (pullback f).obj M ≅ 𝟙_ Y.Modules) :
    (leftFrame (j := j') (hf.pullbackTrivialization e)).hom =
      (pullbackComp (j' ≫ f') x).hom.app M ≫
        eqToHom (by rw [Category.assoc, hf.w, ← Category.assoc, hj.w, Category.assoc]) ≫
        (pullbackComp p (j ≫ f)).inv.app M ≫
        (pullback p).map (leftFrame (j := j) e).hom ≫ (pullbackObjUnitIso p).hom := by
  rw [pullbackComp_inv_app_map_frame_hom]
  simp only [leftFrame, pullbackTrivialization, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, Functor.mapIso_hom, Functor.map_comp, Category.assoc,
    pullbackComp_inv_app_comp_pullback_map_pullbackComp_hom_app_assoc,
    pullbackComp_inv_app_comp_pullback_map_pullbackCongr_hom_app_assoc,
    pullbackComp_inv_app_comp_pullback_map_pullbackComp_inv_app_assoc, eqToHom_trans_assoc]
  have hn := (pullbackComp j' y).inv.naturality_assoc e.hom
    ((pullback j').map (pullbackObjUnitIso y).hom ≫ (pullbackObjUnitIso j').hom)
  simp only [Functor.comp_map] at hn
  rw [← hn, pullbackObjUnitIso_comp]
  have ht (b c : P' ⟶ Y) (hbc : b = c) :
      (leftFrame (j := b) e).hom =
        eqToHom (by rw [hbc]) ≫ (leftFrame (j := c) e).hom := by
    subst c
    simp
  -- The source changes with the composite, so the frame comparison includes its transport.
  rw [show (pullbackComp (j' ≫ y) f).inv.app M ≫
      (pullback (j' ≫ y)).map e.hom ≫ (pullbackObjUnitIso (j' ≫ y)).hom =
      eqToHom (by rw [hj.w]) ≫ (pullbackComp (p ≫ j) f).inv.app M ≫
        (pullback (p ≫ j)).map e.hom ≫ (pullbackObjUnitIso (p ≫ j)).hom from ht _ _ hj.w]
  simp only [eqToHom_trans_assoc]

/-- In a commuting cube, the gluing unit of the induced trivializations is the pullback
of the original gluing unit along the map of overlaps. -/
theorem lineGluingUnit_pullback (h' : CommSq j' g' f' i') (hf : CommSq f' y x f)
    (hi : CommSq i' z x i) (hj : CommSq j' p y j) (hg : CommSq g' p z g)
    {M : X.Modules} (e : (pullback f).obj M ≅ 𝟙_ Y.Modules)
    (d : (pullback i).obj M ≅ 𝟙_ Z.Modules) :
    h'.lineGluingUnit (hf.pullbackTrivialization e) (hi.pullbackTrivialization d) =
      Units.map p.appTop.hom (h.lineGluingUnit e d) := by
  have hframe := congrArg ((pullback p).map · ≫ (pullbackObjUnitIso p).hom)
    (h.leftFrame_eq_rightFrame e d)
  rw [Functor.map_comp, Category.assoc, pullback_map_globalSectionsSmul,
    globalSectionsSmul_naturality] at hframe
  apply (h'.lineGluingUnit_eq_iff _ _ _).mpr
  have hleft := leftFrame_pullbackTrivialization hf hj e
  have hright := leftFrame_pullbackTrivialization_assoc hi hg d
    (globalSectionsSmul (𝟙_ P'.Modules)
      (p.appTop (h.lineGluingUnit e d : Γ(P, ⊤))))
  -- Both pulled-back frames use the comparison for the same composite to X.
  simp only [leftFrame, rightFrame, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.trans_inv,
    NatTrans.comp_app, Functor.mapIso_hom, Category.assoc] at hleft hright hframe
  have happ (a : Γ(P, ⊤)) : (p.appTop.hom : Γ(P, ⊤) →* Γ(P', ⊤)) a =
      p.appTop a := rfl
  simp only [Units.coe_map, happ]
  rw [hleft, hright]
  rw [hframe]
  have hcongr {A B : Scheme.{u}} {a b : A ⟶ B} (hab : a = b) :
      (pullbackCongr hab).inv = (pullbackCongr hab.symm).hom := by
    subst b
    rfl
  simp only [Functor.map_comp, Category.assoc, hcongr,
    pullbackComp_inv_app_comp_pullback_map_pullbackCongr_hom_app_assoc,
    pullbackCongr_hom_app_comp_pullbackComp_hom_app_assoc, eqToHom_trans_assoc]

end Pullback

variable {M N : X.Modules}
  (e : (pullback f).obj M ≅ 𝟙_ Y.Modules) (d : (pullback i).obj M ≅ 𝟙_ Z.Modules)
  (e' : (pullback f).obj N ≅ 𝟙_ Y.Modules) (d' : (pullback i).obj N ≅ 𝟙_ Z.Modules)

/-- The isomorphisms obtained by rescaling the side trivializations agree on the overlap
exactly when the restricted units relate the two gluing units. -/
theorem lineGluingUnit_compatibility_iff (u : Γ(Y, ⊤)ˣ) (v : Γ(Z, ⊤)ˣ) :
    let a := e ≪≫ (unitsGlobalSectionsMulEquivAut (𝟙_ Y.Modules) u).asIso ≪≫ e'.symm
    let b := d ≪≫ (unitsGlobalSectionsMulEquivAut (𝟙_ Z.Modules) v).asIso ≪≫ d'.symm
    let c := pullbackComp g i ≪≫ pullbackCongr h.w.symm
    ((pullbackComp j f).app M).symm ≪≫ (pullback j).mapIso a ≪≫
        (pullbackComp j f).app N =
      (c.app M).symm ≪≫ (pullback g).mapIso b ≪≫ c.app N ↔
      Units.map j.appTop.hom.toMonoidHom u * h.lineGluingUnit e d =
        h.lineGluingUnit e' d' * Units.map g.appTop.hom.toMonoidHom v := by
  dsimp only
  rw [scalar_frame_transport, scalar_frame_transport]
  let F := leftFrame (j := j) e
  let F' := leftFrame (j := j) e'
  let G := h.rightFrame d
  let G' := h.rightFrame d'
  let U := unitAut (Units.map j.appTop.hom.toMonoidHom u)
  let V := unitAut (Units.map g.appTop.hom.toMonoidHom v)
  have hleft :
      ((pullbackComp j f).app M).symm ≪≫
          (((pullback j).mapIso e ≪≫ pullbackObjUnitIso j) ≪≫
            U ≪≫ ((pullback j).mapIso e' ≪≫ pullbackObjUnitIso j).symm) ≪≫
          (pullbackComp j f).app N = F ≪≫ U ≪≫ F'.symm := by
    simp only [F, F', Iso.trans_assoc, Iso.trans_symm]
    rfl
  have hright :
      ((pullbackComp g i ≪≫ pullbackCongr h.w.symm).app M).symm ≪≫
          (((pullback g).mapIso d ≪≫ pullbackObjUnitIso g) ≪≫
            V ≪≫ ((pullback g).mapIso d' ≪≫ pullbackObjUnitIso g).symm) ≪≫
          (pullbackComp g i ≪≫ pullbackCongr h.w.symm).app N = G ≪≫ V ≪≫ G'.symm := by
    simp only [G, G', Iso.trans_assoc, Iso.trans_symm]
    rfl
  rw [hleft, hright, Iso.ext_iff, ← cancel_mono F'.hom]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hF : F.hom = G.hom ≫ globalSectionsSmul (𝟙_ P.Modules) (h.lineGluingUnit e d) :=
    h.leftFrame_eq_rightFrame e d
  have hF' : F'.hom = G'.hom ≫ globalSectionsSmul (𝟙_ P.Modules) (h.lineGluingUnit e' d') :=
    h.leftFrame_eq_rightFrame e' d'
  rw [hF, hF']
  simp only [Category.assoc, Iso.inv_hom_id_assoc, cancel_epi, U, V,
    unitsGlobalSectionsMulEquivAut_apply_hom, ← globalSectionsSmul_mul, ← Units.val_mul]
  constructor
  · intro hs
    apply Units.ext
    apply (globalSectionsActionRingEquiv (𝟙_ P.Modules)).injective
    simpa only [globalSectionsActionRingEquiv_apply] using congrArg End.of hs
  · intro hs
    rw [hs]

end CategoryTheory.CommSq

namespace CategoryTheory.Iso

/-- In two chosen trivializations, an isomorphism is multiplication by a unit. -/
theorem exists_eq_trivialization_rescaling {W : Scheme.{u}} {A B : W.Modules}
    (c : A ≅ B) (s : A ≅ 𝟙_ W.Modules) (t : B ≅ 𝟙_ W.Modules) :
    ∃ u : Γ(W, ⊤)ˣ, c = s ≪≫ (unitsGlobalSectionsMulEquivAut (𝟙_ W.Modules) u).asIso ≪≫ t.symm := by
  let a : Aut (𝟙_ W.Modules) := Aut.of (s.symm ≪≫ c ≪≫ t)
  refine ⟨(unitsGlobalSectionsMulEquivAut (𝟙_ W.Modules)).symm a, ?_⟩
  simp only [MulEquiv.apply_symm_apply]
  have ha : a.asIso = s.symm ≪≫ c ≪≫ t := rfl
  rw [ha]
  simp [Iso.trans_assoc]

end CategoryTheory.Iso
