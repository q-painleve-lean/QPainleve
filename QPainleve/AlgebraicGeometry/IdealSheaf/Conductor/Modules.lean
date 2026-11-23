/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.IdealSheaf.Conductor.Pullback
public import TauCeti.AlgebraicGeometry.VectorBundle.TotalSpace.PullbackHom
import Mathlib.Algebra.Category.Ring.Limits

/-!
# Module maps across a conductor square

The conductor square of a finite scheme-theoretically dominant morphism gives a pullback
of the direct images of the structure sheaves in the category of modules. The
pullback–pushforward adjunction gives descent for linear functionals. The symmetric-algebra
universal property and Tau Ceti's `totalSpaceIhomHomEquiv` then give descent for maps and
isomorphisms of finite locally free sheaves.

See the Stacks Project, Tag 0E25, for the structure sheaf pullback, and Tag 0D2J for
finite projective module patching over fiber products of rings.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed
open CategoryTheory.Limits hiding pullback
open AlgebraicGeometry

universe u

namespace CategoryTheory.IsPullback

open Scheme.Modules TauCeti.AlgebraicGeometry

variable {P Y Z X : Scheme.{u}} {j : P ⟶ Y} {g : P ⟶ Z} {f : Y ⟶ X} {i : Z ⟶ X}
  [IsFinite f] [IsSchemeTheoreticallyDominant f] [IsClosedImmersion i]

/-- The structure sheaf is the module pullback of the direct images from the finite source
and the conductor subscheme over their common closed subscheme. -/
theorem isPullback_structureModules_of_ker_eq_conductor
    (h : IsPullback j g f i) (hi : i.ker = f.conductor) :
    IsPullback (C := X.Modules)
      (MonObj.one (X := f.pushforwardStructureAlgebra.toMon.X))
      (MonObj.one (X := i.pushforwardStructureAlgebra.toMon.X))
      (Scheme.Hom.pushforwardStructureAlgebraMap j (rfl : j ≫ f = j ≫ f)).hom.hom
      (Scheme.Hom.pushforwardStructureAlgebraMap g h.w.symm).hom.hom := by
  let F := Scheme.Modules.toPresheaf X
  let : ReflectsLimitsOfShape WalkingCospan F := reflectsLimitsOfShape_of_reflectsIsomorphisms
  apply IsPullback.of_map_of_faithful F
  apply IsPullback.of_forall_isPullback_app
  intro U
  let forgetRing := forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat.{u} Ab
  have hU := ((h.isPullback_presheaf_of_ker_eq_conductor hi).app U).map forgetRing
  have hm {V W : Scheme.{u}} {p : V ⟶ X} {q : W ⟶ X} (a : V ⟶ W) (ha : a ≫ q = p)
      (x : Γ(q.pushforwardStructureAlgebra.X, U.unop)) :
      (((Scheme.Hom.pushforwardStructureAlgebraMap a ha).hom.hom).app U.unop) x =
        a.appLE (q ⁻¹ᵁ U.unop) (p ⁻¹ᵁ U.unop) (by subst p; rfl) x := by
    have hs := Scheme.Hom.sectionsAlgHom_pushforwardStructureAlgebraMap_apply a ha U.unop x
    simp only [CommMon.sectionsAlgHom_apply,
      Scheme.Hom.pushforwardStructureAlgebraSectionsRingEquiv_apply,
      Scheme.Hom.pushforwardStructureAlgebraSectionsRingEquiv_symm_apply] at hs
    exact hs
  have hu {W : Scheme.{u}} (q : W ⟶ X) :
      forgetRing.map (q.c.app U) =
        (F.map (MonObj.one (X := q.pushforwardStructureAlgebra.toMon.X))).app U := by
    exact congrArg (fun α : 𝟙_ X.Modules ⟶ q.pushforwardStructureAlgebra.toMon.X ↦
      (F.map α).app U) (Scheme.Hom.pushforwardStructureAlgebra_one q).symm
  refine hU.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.comp_id _).trans ((hu f).trans (Category.id_comp _).symm))
    ((Category.comp_id _).trans ((hu i).trans (Category.id_comp _).symm)) ?_ ?_
  · refine (Category.comp_id _).trans ?_
    refine Eq.trans ?_ (Category.id_comp _).symm
    apply ConcreteCategory.hom_ext
    intro x
    exact ((hm j rfl x).trans
      (ConcreteCategory.congr_hom (Scheme.Hom.appLE_eq_app j) x)).symm
  · refine (Category.comp_id _).trans ?_
    refine Eq.trans ?_ (Category.id_comp _).symm
    apply ConcreteCategory.hom_ext
    intro x
    exact (hm g h.w.symm x).symm

/-- A pair of linear functionals on the two restrictions of an arbitrary module descends
uniquely if the functionals agree on the common closed subscheme. -/
theorem existsUnique_functional_of_ker_eq_conductor
    (h : IsPullback j g f i) (hi : i.ker = f.conductor) {M : X.Modules}
    (a : (pullback f).obj M ⟶ 𝟙_ Y.Modules)
    (b : (pullback i).obj M ⟶ 𝟙_ Z.Modules)
    (hab : (pullbackComp j f).inv.app M ≫ (pullback j).map a ≫ (pullbackObjUnitIso j).hom =
      (pullbackCongr h.w.symm).inv.app M ≫ (pullbackComp g i).inv.app M ≫
        (pullback g).map b ≫ (pullbackObjUnitIso g).hom) :
    ∃! c : M ⟶ 𝟙_ X.Modules,
      (pullback f).map c ≫ (pullbackObjUnitIso f).hom = a ∧
        (pullback i).map c ≫ (pullbackObjUnitIso i).hom = b := by
  let A := (pullbackPushforwardAdjunction f).homEquiv M (𝟙_ Y.Modules)
  let B := (pullbackPushforwardAdjunction i).homEquiv M (𝟙_ Z.Modules)
  let C := (pullbackPushforwardAdjunction (j ≫ f)).homEquiv M (𝟙_ P.Modules)
  have hj : C ((pullbackComp j f).inv.app M ≫ (pullback j).map a ≫
      (pullbackObjUnitIso j).hom) = A a ≫
        (Scheme.Hom.pushforwardStructureAlgebraMap j (rfl : j ≫ f = j ≫ f)).hom.hom := by
    simpa only [pullbackCongr, eqToIso_refl, Iso.refl_inv, NatTrans.id_app, Category.id_comp] using
      Scheme.Hom.pullbackPushforwardAdjunction_homEquiv_pullback_map j (rfl : j ≫ f = j ≫ f) M a
  have hw := hj.symm.trans ((congrArg C hab).trans
    (Scheme.Hom.pullbackPushforwardAdjunction_homEquiv_pullback_map g h.w.symm M b))
  let H := h.isPullback_structureModules_of_ker_eq_conductor hi
  have ha (c : M ⟶ 𝟙_ X.Modules) :
      A ((pullback f).map c ≫ (pullbackObjUnitIso f).hom) =
        c ≫ MonObj.one (X := f.pushforwardStructureAlgebra.toMon.X) := by
    dsimp only [A]
    rw [Adjunction.homEquiv_naturality_left,
      pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom]
    exact congrArg (fun α : 𝟙_ X.Modules ⟶ f.pushforwardStructureAlgebra.toMon.X ↦ c ≫ α)
      (Scheme.Hom.pushforwardStructureAlgebra_one f).symm
  have hb (c : M ⟶ 𝟙_ X.Modules) :
      B ((pullback i).map c ≫ (pullbackObjUnitIso i).hom) =
        c ≫ MonObj.one (X := i.pushforwardStructureAlgebra.toMon.X) := by
    dsimp only [B]
    rw [Adjunction.homEquiv_naturality_left,
      pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom]
    exact congrArg (fun α : 𝟙_ X.Modules ⟶ i.pushforwardStructureAlgebra.toMon.X ↦ c ≫ α)
      (Scheme.Hom.pushforwardStructureAlgebra_one i).symm
  let c := H.lift (A a) (B b) hw
  have hfa : c ≫ MonObj.one (X := f.pushforwardStructureAlgebra.toMon.X) = A a :=
    H.lift_fst _ _ _
  have hib : c ≫ MonObj.one (X := i.pushforwardStructureAlgebra.toMon.X) = B b :=
    H.lift_snd _ _ _
  refine ⟨c, ⟨A.injective ((ha c).trans hfa), B.injective ((hb c).trans hib)⟩, ?_⟩
  rintro d ⟨hd, he⟩
  exact H.hom_ext ((ha d).symm.trans ((congrArg A hd).trans hfa.symm))
    ((hb d).symm.trans ((congrArg B he).trans hib.symm))

/-- Compatible points of the relative spectrum of a symmetric algebra descend across a
conductor square. -/
theorem existsUnique_hom_relativeSpecSymmetricAlgebra_of_ker_eq_conductor
    (h : IsPullback j g f i) (hi : i.ker = f.conductor) (M : QuasicoherentSheaf X) :
    let S := (MorphismProperty.Over.forget _ _ X).obj
      ((relativeSpec X).obj (Opposite.op ((symmetricAlgebra X).obj M)))
    ∀ (a : Over.mk f ⟶ S) (b : Over.mk i ⟶ S),
      Over.homMk (U := Over.mk (j ≫ f)) (V := Over.mk f) j rfl ≫ a =
        Over.homMk (U := Over.mk (j ≫ f)) (V := Over.mk i) g h.w.symm ≫ b →
      ∃! c : Over.mk (𝟙 X) ⟶ S,
        Over.homMk (U := Over.mk f) (V := Over.mk (𝟙 X)) f (Category.comp_id f) ≫ c = a ∧
          Over.homMk (U := Over.mk i) (V := Over.mk (𝟙 X)) i (Category.comp_id i) ≫ c = b := by
  intro S a b hab
  let e (T : Over X) := relativeSpecSymmetricAlgebraPullbackHomEquiv M T
  have hj := relativeSpecSymmetricAlgebraPullbackHomEquiv_comp M
    (Over.homMk (U := Over.mk (j ≫ f)) (V := Over.mk f) j rfl) a
  have hg := relativeSpecSymmetricAlgebraPullbackHomEquiv_comp M
    (Over.homMk (U := Over.mk (j ≫ f)) (V := Over.mk i) g h.w.symm) b
  have he := hj.symm.trans ((congrArg (e (Over.mk (j ≫ f))) hab).trans hg)
  -- The left restriction is already written over the chosen composite `j ≫ f`.
  dsimp only [Over.homMk_left, Over.mk_hom, pullbackCongr] at he
  let E := (e (Over.mk (𝟙 X))).trans
    (((pullbackId X).app M.obj).homCongr (Iso.refl _))
  apply (E.existsUnique_congr ?_).mpr (h.existsUnique_functional_of_ker_eq_conductor hi _ _ he)
  intro c
  have hr {W : Scheme.{u}} (q : W ⟶ X) :
      e (Over.mk q) (Over.homMk (U := Over.mk q) (V := Over.mk (𝟙 X)) q (Category.comp_id q) ≫ c) =
        (pullback q).map (E c) ≫ (pullbackObjUnitIso q).hom := by
    have hq (N : X.Modules) :
        (pullbackComp q (𝟙 X) ≪≫ pullbackCongr (Category.comp_id q)).app N =
          (pullback q).mapIso ((pullbackId X).app N) :=
      Iso.ext (pullbackComp_id_hom q N)
    let m := e (Over.mk (𝟙 X)) c
    let α := (pullbackComp q (𝟙 X) ≪≫ pullbackCongr (Category.comp_id q)).app M.obj
    have hh : e (Over.mk q) (Over.homMk (U := Over.mk q) (V := Over.mk (𝟙 X))
        q (Category.comp_id q) ≫ c) =
          α.inv ≫ (pullback q).map m ≫ (pullbackObjUnitIso q).hom :=
      (relativeSpecSymmetricAlgebraPullbackHomEquiv_comp M
        (Over.homMk (U := Over.mk q) (V := Over.mk (𝟙 X)) q (Category.comp_id q)) c).trans
        (Category.assoc _ _ _).symm
    refine hh.trans ((congrArg (· ≫ (pullback q).map m ≫ (pullbackObjUnitIso q).hom)
      (congrArg Iso.inv (hq M.obj))).trans ?_)
    simp only [E, Equiv.trans_apply, Iso.homCongr, Equiv.coe_fn_mk, Iso.refl_hom,
      Category.comp_id, Functor.mapIso_inv, Functor.map_comp, Category.assoc, m]
  exact and_congr (by rw [← hr]; exact (e _).injective.eq_iff.symm)
    (by rw [← hr]; exact (e _).injective.eq_iff.symm)

/-- Compatible morphisms between the restrictions of two finite locally free modules descend
uniquely across a conductor square. The compatibility compares both restrictions on the
common closed subscheme using the composition isomorphisms of pullback. -/
theorem existsUnique_hom_of_ker_eq_conductor
    (h : IsPullback j g f i) (hi : i.ker = f.conductor)
    (E F : FiniteLocallyFreeSheaf X)
    (a : (pullback f).obj E.obj ⟶ (pullback f).obj F.obj)
    (b : (pullback i).obj E.obj ⟶ (pullback i).obj F.obj)
    (hab :
      let e := pullbackComp g i ≪≫ pullbackCongr h.w.symm
      (pullbackComp j f).inv.app E.obj ≫ (pullback j).map a ≫
          (pullbackComp j f).hom.app F.obj =
        e.inv.app E.obj ≫ (pullback g).map b ≫ e.hom.app F.obj) :
    ∃! c : E.obj ⟶ F.obj, (pullback f).map c = a ∧ (pullback i).map c = b := by
  let S := (MorphismProperty.Over.forget _ _ X).obj
    ((totalSpaceScheme X).obj ((ihom E).obj F))
  let e {W : Scheme.{u}} (q : W ⟶ X) := totalSpaceIhomHomEquiv E F (Over.mk q)
  let a' : Over.mk f ⟶ S := (e f).symm a
  let b' : Over.mk i ⟶ S := (e i).symm b
  have hcompat : Over.homMk (U := Over.mk (j ≫ f)) (V := Over.mk f) j rfl ≫ a' =
      Over.homMk (U := Over.mk (j ≫ f)) (V := Over.mk i) g h.w.symm ≫ b' := by
    apply (e (j ≫ f)).injective
    rw [totalSpaceIhomHomEquiv_comp E F f j rfl a',
      totalSpaceIhomHomEquiv_comp E F i g h.w.symm b']
    simpa only [a', b', e, Equiv.apply_symm_apply, Iso.trans_inv, Iso.trans_hom,
      NatTrans.comp_app, pullbackCongr, eqToIso_refl, Iso.refl_hom,
      Iso.refl_inv, NatTrans.id_app, Category.id_comp, Category.comp_id, Over.mk_hom] using hab
  have hpoints := h.existsUnique_hom_relativeSpecSymmetricAlgebra_of_ker_eq_conductor hi
    ((FiniteLocallyFreeSheaf.toQuasicoherent X).obj (FiniteLocallyFreeSheaf.dual ((ihom E).obj F)))
    a' b' hcompat
  let E₀ := (e (𝟙 X)).trans
    (((pullbackId X).app E.obj).homCongr ((pullbackId X).app F.obj))
  apply (E₀.existsUnique_congr ?_).mp hpoints
  intro c
  have hr {W : Scheme.{u}} (q : W ⟶ X) :
      e q (Over.homMk (U := Over.mk q) (V := Over.mk (𝟙 X)) q (Category.comp_id q) ≫ c) =
        (pullback q).map (E₀ c) := by
    have hq (N : X.Modules) :
        (pullbackComp q (𝟙 X) ≪≫ pullbackCongr (Category.comp_id q)).app N =
          (pullback q).mapIso ((pullbackId X).app N) :=
      Iso.ext (pullbackComp_id_hom q N)
    have hc := totalSpaceIhomHomEquiv_comp E F (𝟙 X) q (Category.comp_id q) c
    have hinv := congrArg (fun α ↦ α.inv) (hq E.obj)
    have hhom := congrArg (fun α ↦ α.hom) (hq F.obj)
    simp only [Iso.app_inv, Iso.app_hom, Functor.mapIso_inv, Functor.mapIso_hom] at hinv hhom
    exact hc.trans (by
      simp only [hinv, hhom, E₀, Equiv.trans_apply, Iso.homCongr, Equiv.coe_fn_mk,
        Iso.app_inv, Iso.app_hom, Functor.map_comp, e])
  refine and_congr ((e f).injective.eq_iff.symm.trans ?_)
    ((e i).injective.eq_iff.symm.trans ?_)
  · exact Iff.of_eq (congrArg₂ (· = ·) (hr f) ((e f).apply_symm_apply a))
  · exact Iff.of_eq (congrArg₂ (· = ·) (hr i) ((e i).apply_symm_apply b))

/-- Compatible isomorphisms of finite locally free sheaves descend to a unique isomorphism
across a conductor square. -/
theorem existsUnique_iso_of_ker_eq_conductor
    (h : IsPullback j g f i) (hi : i.ker = f.conductor)
    (E F : FiniteLocallyFreeSheaf X)
    (a : (pullback f).obj E.obj ≅ (pullback f).obj F.obj)
    (b : (pullback i).obj E.obj ≅ (pullback i).obj F.obj)
    (hab :
      let e := pullbackComp g i ≪≫ pullbackCongr h.w.symm
      ((pullbackComp j f).app E.obj).symm ≪≫ (pullback j).mapIso a ≪≫
          (pullbackComp j f).app F.obj =
        (e.app E.obj).symm ≪≫ (pullback g).mapIso b ≪≫ e.app F.obj) :
    ∃! c : E.obj ≅ F.obj, (pullback f).mapIso c = a ∧ (pullback i).mapIso c = b := by
  obtain ⟨c, ⟨hcf, hci⟩, hc⟩ := h.existsUnique_hom_of_ker_eq_conductor hi E F a.hom b.hom
    (by simpa only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
      Category.assoc] using congrArg Iso.hom hab)
  obtain ⟨d, ⟨hdf, hdi⟩, _⟩ := h.existsUnique_hom_of_ker_eq_conductor hi F E a.inv b.inv
    (by simpa only [Iso.trans_inv, Iso.symm_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_inv,
      Category.assoc] using congrArg Iso.inv hab)
  have hId (V : FiniteLocallyFreeSheaf X) {m : V.obj ⟶ V.obj}
      (hf : (pullback f).map m = 𝟙 _) (hi' : (pullback i).map m = 𝟙 _) : m = 𝟙 _ := by
    obtain ⟨e, _, he⟩ :=
      h.existsUnique_hom_of_ker_eq_conductor hi V V (𝟙 _) (𝟙 _) (by simp)
    exact (he m ⟨hf, hi'⟩).trans (he (𝟙 _) ⟨(pullback f).map_id _, (pullback i).map_id _⟩).symm
  let e : E.obj ≅ F.obj :=
    { hom := c
      inv := d
      hom_inv_id := hId E (by rw [Functor.map_comp, hcf, hdf, a.hom_inv_id])
        (by rw [Functor.map_comp, hci, hdi, b.hom_inv_id])
      inv_hom_id := hId F (by rw [Functor.map_comp, hdf, hcf, a.inv_hom_id])
        (by rw [Functor.map_comp, hdi, hci, b.inv_hom_id]) }
  refine ⟨e, ⟨Iso.ext hcf, Iso.ext hci⟩, ?_⟩
  rintro r ⟨hrf, hri⟩
  exact Iso.ext (hc r.hom ⟨congrArg Iso.hom hrf, congrArg Iso.hom hri⟩)

end CategoryTheory.IsPullback
