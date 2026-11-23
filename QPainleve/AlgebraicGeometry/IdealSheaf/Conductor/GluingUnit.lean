/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Defs
public import QPainleve.AlgebraicGeometry.IdealSheaf.Conductor.Modules
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality

import TauCeti.AlgebraicGeometry.LineBundle.Endomorphisms

/-!
# Gluing units and line bundle classes

Two trivializations of the restrictions of a line bundle in a conductor square
differ on the overlap by a global unit. The Picard class determines this unit
up to a rescaling by units on the two sides. This gives the equivalence relation
on gluing units needed to use overlap coordinates on Picard classes.

The proof uses descent of compatible bundle isomorphisms across the conductor
square and the identification of automorphisms of the trivial line with global
units. See the [Stacks Project, Lemma 15.6.9](https://stacks.math.columbia.edu/tag/0D2J)
for the affine projective-module patching result.
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

private theorem gluing_compatibility_iff (u : Γ(Y, ⊤)ˣ) (v : Γ(Z, ⊤)ˣ) :
    let a := e ≪≫ unitAut u ≪≫ e'.symm
    let b := d ≪≫ unitAut v ≪≫ d'.symm
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

private theorem exists_eq_frame_rescaling {W : Scheme.{u}} {A B : W.Modules}
    (s : A ≅ 𝟙_ W.Modules) (t : B ≅ 𝟙_ W.Modules) (c : A ≅ B) :
    ∃ u : Γ(W, ⊤)ˣ, c = s ≪≫ unitAut u ≪≫ t.symm := by
  let a : Aut (𝟙_ W.Modules) := Aut.of (s.symm ≪≫ c ≪≫ t)
  refine ⟨(unitsGlobalSectionsMulEquivAut (𝟙_ W.Modules)).symm a, ?_⟩
  simp only [unitAut, MulEquiv.apply_symm_apply]
  have ha : a.asIso = s.symm ≪≫ c ≪≫ t := rfl
  rw [ha]
  simp [Iso.trans_assoc]

end CategoryTheory.CommSq

namespace CategoryTheory.IsPullback

variable {P Y Z X : Scheme.{u}} {j : P ⟶ Y} {g : P ⟶ Z} {f : Y ⟶ X} {i : Z ⟶ X}
  (h : IsPullback j g f i)

open CategoryTheory.CommSq

variable [IsFinite f] [IsSchemeTheoreticallyDominant f] [IsClosedImmersion i]

/-- Two line bundles trivialized on both sides of a conductor square have the same Picard
class exactly when units on the two sides rescale their gluing units into one another. -/
theorem gluingUnits_picardClass_iff (hi : i.ker = f.conductor) {L K : InvertibleSheaf X}
    (eL : (pullback f).obj L.obj ≅ 𝟙_ Y.Modules) (dL : (pullback i).obj L.obj ≅ 𝟙_ Z.Modules)
    (eK : (pullback f).obj K.obj ≅ 𝟙_ Y.Modules) (dK : (pullback i).obj K.obj ≅ 𝟙_ Z.Modules) :
    LineBundleClass.mk L = LineBundleClass.mk K ↔
      ∃ (u : Γ(Y, ⊤)ˣ) (v : Γ(Z, ⊤)ˣ),
        Units.map j.appTop.hom.toMonoidHom u * h.toCommSq.lineGluingUnit eL dL =
          h.toCommSq.lineGluingUnit eK dK * Units.map g.appTop.hom.toMonoidHom v := by
  rw [LineBundleClass.mk_eq_mk_iff]
  constructor
  · rintro ⟨c⟩
    obtain ⟨u, hu⟩ := exists_eq_frame_rescaling eL eK ((pullback f).mapIso c)
    obtain ⟨v, hv⟩ := exists_eq_frame_rescaling dL dK ((pullback i).mapIso c)
    refine ⟨u, v, (h.toCommSq.gluing_compatibility_iff eL dL eK dK u v).mp ?_⟩
    rw [← hu, ← hv]
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
      Functor.mapIso_hom, ← Functor.comp_map, NatIso.naturality_1]
    exact (NatIso.naturality_1 (pullbackComp g i ≪≫ pullbackCongr h.w.symm) c.hom).symm
  · rintro ⟨u, v, huv⟩
    let A := (InvertibleSheaf.toFiniteLocallyFree X).obj L
    let B := (InvertibleSheaf.toFiniteLocallyFree X).obj K
    obtain ⟨c, -, -⟩ := h.existsUnique_iso_of_ker_eq_conductor hi A B
      (eL ≪≫ unitAut u ≪≫ eK.symm) (dL ≪≫ unitAut v ≪≫ dK.symm)
      ((h.toCommSq.gluing_compatibility_iff eL dL eK dK u v).mpr huv)
    exact ⟨c⟩

/-- Equality of the classes of overlap units modulo rescaling detects equality
of the Picard classes of the trivialized line bundles. -/
theorem picardClass_eq_iff_gluingUnit_quotient_eq (hi : i.ker = f.conductor)
    {L K : InvertibleSheaf X}
    (eL : (pullback f).obj L.obj ≅ 𝟙_ Y.Modules) (dL : (pullback i).obj L.obj ≅ 𝟙_ Z.Modules)
    (eK : (pullback f).obj K.obj ≅ 𝟙_ Y.Modules) (dK : (pullback i).obj K.obj ≅ 𝟙_ Z.Modules) :
    LineBundleClass.mk L = LineBundleClass.mk K ↔
      (QuotientGroup.mk (h.toCommSq.lineGluingUnit eL dL) :
        Γ(P, ⊤)ˣ ⧸ (j.lineGluingCoboundary g).range) =
          QuotientGroup.mk (h.toCommSq.lineGluingUnit eK dK) := by
  rw [h.gluingUnits_picardClass_iff hi eL dL eK dK]
  symm
  rw [eq_comm, QuotientGroup.eq_iff_div_mem, MonoidHom.mem_range, Prod.exists]
  simp only [Scheme.Hom.lineGluingCoboundary_apply, div_eq_div_iff_mul_eq_mul]

omit [IsFinite f] [IsSchemeTheoreticallyDominant f] [IsClosedImmersion i] in
private theorem exists_trivialized_representative
    (a : ((LineBundleClass.pullbackHom f).ker ⊓ (LineBundleClass.pullbackHom i).ker :
      Subgroup (LineBundleClass X))) :
    ∃ L : InvertibleSheaf X, Nonempty ((pullback f).obj L.obj ≅ 𝟙_ Y.Modules) ∧
      Nonempty ((pullback i).obj L.obj ≅ 𝟙_ Z.Modules) ∧ LineBundleClass.mk L = a.val := by
  obtain ⟨L, hL⟩ := LineBundleClass.mk_surjective a.val
  have hf : LineBundleClass.pullback f a.val = 1 := by
    simpa only [LineBundleClass.pullbackHom_apply] using
      MonoidHom.mem_ker.mp (a.property.1 : a.val ∈ (LineBundleClass.pullbackHom f).ker)
  have hi : LineBundleClass.pullback i a.val = 1 := by
    simpa only [LineBundleClass.pullbackHom_apply] using
      MonoidHom.mem_ker.mp (a.property.2 : a.val ∈ (LineBundleClass.pullbackHom i).ker)
  rw [← hL, LineBundleClass.pullback_mk, LineBundleClass.mk_eq_one_iff] at hf hi
  exact ⟨L, hf, hi, hL⟩

private theorem exists_gluingUnitClass (hi : i.ker = f.conductor)
    (a : ((LineBundleClass.pullbackHom f).ker ⊓ (LineBundleClass.pullbackHom i).ker :
      Subgroup (LineBundleClass X))) :
    ∃ t : (Γ(P, ⊤)ˣ ⧸ (j.lineGluingCoboundary g).range), ∀ (L : InvertibleSheaf X)
      (e : (pullback f).obj L.obj ≅ 𝟙_ Y.Modules) (d : (pullback i).obj L.obj ≅ 𝟙_ Z.Modules),
      LineBundleClass.mk L = a.val → t = QuotientGroup.mk (h.toCommSq.lineGluingUnit e d) := by
  obtain ⟨L, ⟨e⟩, ⟨d⟩, hL⟩ := exists_trivialized_representative a
  refine ⟨QuotientGroup.mk (h.toCommSq.lineGluingUnit e d), fun K e' d' hK ↦ ?_⟩
  exact (h.picardClass_eq_iff_gluingUnit_quotient_eq hi e d e' d').mp (hL.trans hK.symm)

/-- The Picard classes whose restrictions to both sides of the conductor square are trivial
embed into the quotient of overlap units by changes of trivializations. -/
def lineGluingClassEmbedding (hi : i.ker = f.conductor) :
    ((LineBundleClass.pullbackHom f).ker ⊓ (LineBundleClass.pullbackHom i).ker :
      Subgroup (LineBundleClass X)) ↪ (Γ(P, ⊤)ˣ ⧸ (j.lineGluingCoboundary g).range) where
  toFun a := (h.exists_gluingUnitClass hi a).choose
  inj' := by
    intro a b hab
    obtain ⟨L, ⟨e⟩, ⟨d⟩, hL⟩ := exists_trivialized_representative a
    obtain ⟨K, ⟨e'⟩, ⟨d'⟩, hK⟩ := exists_trivialized_representative b
    have ha := (h.exists_gluingUnitClass hi a).choose_spec L e d hL
    have hb := (h.exists_gluingUnitClass hi b).choose_spec K e' d' hK
    have hLK := (h.picardClass_eq_iff_gluingUnit_quotient_eq hi e d e' d').mpr
      (ha.symm.trans (hab.trans hb))
    exact Subtype.ext (hL.symm.trans (hLK.trans hK))

/-- Compute the gluing class from any representative and any pair of trivializations. -/
theorem lineGluingClassEmbedding_apply (hi : i.ker = f.conductor)
    (a : ((LineBundleClass.pullbackHom f).ker ⊓ (LineBundleClass.pullbackHom i).ker :
      Subgroup (LineBundleClass X)))
    (L : InvertibleSheaf X) (e : (pullback f).obj L.obj ≅ 𝟙_ Y.Modules)
    (d : (pullback i).obj L.obj ≅ 𝟙_ Z.Modules) (hL : LineBundleClass.mk L = a.val) :
    h.lineGluingClassEmbedding hi a = QuotientGroup.mk (h.toCommSq.lineGluingUnit e d) :=
  (h.exists_gluingUnitClass hi a).choose_spec L e d hL

end CategoryTheory.IsPullback
