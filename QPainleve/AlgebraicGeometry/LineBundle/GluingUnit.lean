/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Modules.Pullback.Tensor
public import TauCeti.AlgebraicGeometry.LineBundle.Endomorphisms

/-!
# Gluing units for line bundle trivializations

In a commutative square of schemes, two side trivializations of a module pull back to
trivializations on the overlap. Their comparison is multiplication by a global unit.
The gluing compatibility criterion describes how rescaling the side trivializations
affects this comparison. Tensor product of trivializations multiplies the
overlap units.
-/

public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry TauCeti.AlgebraicGeometry
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

open Functor.OplaxMonoidal in
private theorem leftFrame_tensor {M N : X.Modules} [M.IsQuasicoherent]
    (e : (pullback f).obj M ≅ 𝟙_ Y.Modules) (e' : (pullback f).obj N ≅ 𝟙_ Y.Modules) :
    (leftFrame (j := j) (pullbackTensorTrivialization f e e')).hom =
      δ (pullback (j ≫ f)) M N ≫
        ((leftFrame (j := j) e).hom ⊗ₘ (leftFrame (j := j) e').hom) ≫ (λ_ _).hom := by
  simp only [leftFrame, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom,
    pullbackTensorTrivialization_hom]
  rw [Functor.map_comp, Category.assoc, pullback_tensorFrame, pullback_comp_δ]
  simp only [Category.assoc, tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id_app_assoc]

open Functor.OplaxMonoidal in
private theorem rightFrame_tensor {M N : X.Modules} [M.IsQuasicoherent]
    (d : (pullback i).obj M ≅ 𝟙_ Z.Modules) (d' : (pullback i).obj N ≅ 𝟙_ Z.Modules) :
    (h.rightFrame (pullbackTensorTrivialization i d d')).hom =
      δ (pullback (j ≫ f)) M N ≫
        ((h.rightFrame d).hom ⊗ₘ (h.rightFrame d').hom) ≫ (λ_ _).hom := by
  simp only [rightFrame, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.trans_inv,
    NatTrans.comp_app, Functor.mapIso_hom, Category.assoc]
  -- First tensor the two frames over `g ≫ i`, then transport to `j ≫ f`.
  have ht := leftFrame_tensor (j := g) d d'
  simp only [leftFrame, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom] at ht
  have hc {a b : P ⟶ X} (hab : a = b) :
      (pullbackCongr hab.symm).inv = (pullbackCongr hab).hom := by
    subst b
    rfl
  rw [hc h.w, ht, pullbackCongr_hom_app_comp_δ_assoc]
  simp only [tensorHom_comp_tensorHom_assoc]

/-- Tensoring the side trivializations multiplies their gluing units on the overlap. -/
theorem lineGluingUnit_tensor {M N : X.Modules} [M.IsQuasicoherent]
    (e : (pullback f).obj M ≅ 𝟙_ Y.Modules) (d : (pullback i).obj M ≅ 𝟙_ Z.Modules)
    (e' : (pullback f).obj N ≅ 𝟙_ Y.Modules) (d' : (pullback i).obj N ≅ 𝟙_ Z.Modules) :
    h.lineGluingUnit (pullbackTensorTrivialization f e e') (pullbackTensorTrivialization i d d') =
      h.lineGluingUnit e d * h.lineGluingUnit e' d' := by
  apply (h.lineGluingUnit_eq_iff ..).mpr
  simp only [← Category.assoc]
  -- Use the frames so that both overlap trivializations have the same source.
  exact (show
    (leftFrame (j := j) (pullbackTensorTrivialization f e e')).hom =
      (h.rightFrame (pullbackTensorTrivialization i d d')).hom ≫
        globalSectionsSmul (𝟙_ P.Modules) ↑(h.lineGluingUnit e d * h.lineGluingUnit e' d') from by
    rw [leftFrame_tensor, rightFrame_tensor, h.leftFrame_eq_rightFrame e d,
      h.leftFrame_eq_rightFrame e' d', ← tensorHom_comp_tensorHom]
    -- Use the unitor calculation from
    -- `Scheme.Hom.pushforward_map_globalSectionsSmul_tensorHom_mul` in Tau Ceti.
    have hs (a b : Γ(P, ⊤)) :
        (globalSectionsSmul (𝟙_ P.Modules) a ⊗ₘ globalSectionsSmul (𝟙_ P.Modules) b) ≫
            (λ_ _).hom =
          (λ_ (𝟙_ P.Modules)).hom ≫ globalSectionsSmul (𝟙_ P.Modules) (a * b) := by
      rw [tensorHom_def, Category.assoc, leftUnitor_naturality, ← Category.assoc, unitors_equal,
        rightUnitor_naturality, Category.assoc, ← unitors_equal, mul_comm, globalSectionsSmul_mul]
    simp only [Category.assoc, Units.val_mul, hs])

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
