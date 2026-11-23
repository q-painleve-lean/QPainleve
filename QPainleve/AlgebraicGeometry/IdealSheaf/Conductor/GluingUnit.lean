/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Defs
public import QPainleve.AlgebraicGeometry.IdealSheaf.Conductor.Modules
public import QPainleve.AlgebraicGeometry.LineBundle.GluingUnit
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality

import QPainleve.AlgebraicGeometry.IdealSheaf.Conductor.LineBundle
import TauCeti.AlgebraicGeometry.LineBundle.Monoidal

/-!
# Gluing units and line bundle classes

Two trivializations of the restrictions of a line bundle in a conductor square
differ on the overlap by a global unit. The Picard class determines this unit
up to a rescaling by units on the two sides. The quotient of overlap units is
isomorphic to the subgroup of Picard classes trivial on both sides. Tensor
product multiplies the overlap units.

The proof uses descent of compatible bundle isomorphisms across the conductor
square and the identification of automorphisms of the trivial line with global
units. See the [Stacks Project, Lemma 15.6.9](https://stacks.math.columbia.edu/tag/0D2J)
for the affine projective-module patching result.
-/

public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry TauCeti.AlgebraicGeometry
open Scheme.Modules

universe u

namespace CategoryTheory.IsPullback

variable {P Y Z X : Scheme.{u}} {j : P ⟶ Y} {g : P ⟶ Z} {f : Y ⟶ X} {i : Z ⟶ X}
  (h : IsPullback j g f i)

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
    obtain ⟨u, hu⟩ := ((pullback f).mapIso c).exists_eq_trivialization_rescaling eL eK
    obtain ⟨v, hv⟩ := ((pullback i).mapIso c).exists_eq_trivialization_rescaling dL dK
    refine ⟨u, v, (h.toCommSq.lineGluingUnit_compatibility_iff eL dL eK dK u v).mp ?_⟩
    rw [← hu, ← hv]
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
      Functor.mapIso_hom, ← Functor.comp_map, NatIso.naturality_1]
    exact (NatIso.naturality_1 (pullbackComp g i ≪≫ pullbackCongr h.w.symm) c.hom).symm
  · rintro ⟨u, v, huv⟩
    let A := (InvertibleSheaf.toFiniteLocallyFree X).obj L
    let B := (InvertibleSheaf.toFiniteLocallyFree X).obj K
    obtain ⟨c, -, -⟩ := h.existsUnique_iso_of_ker_eq_conductor hi A B
      (eL ≪≫ (unitsGlobalSectionsMulEquivAut (𝟙_ Y.Modules) u).asIso ≪≫ eK.symm)
      (dL ≪≫ (unitsGlobalSectionsMulEquivAut (𝟙_ Z.Modules) v).asIso ≪≫ dK.symm)
      ((h.toCommSq.lineGluingUnit_compatibility_iff eL dL eK dK u v).mpr huv)
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

private theorem exists_gluingUnitClass (hi : i.ker = f.conductor)
    (a : ((LineBundleClass.pullbackHom f).ker ⊓ (LineBundleClass.pullbackHom i).ker :
      Subgroup (LineBundleClass X))) :
    ∃ t : (Γ(P, ⊤)ˣ ⧸ (j.lineGluingCoboundary g).range), ∀ (L : InvertibleSheaf X)
      (e : (pullback f).obj L.obj ≅ 𝟙_ Y.Modules) (d : (pullback i).obj L.obj ≅ 𝟙_ Z.Modules),
      LineBundleClass.mk L = a.val → t = QuotientGroup.mk (h.toCommSq.lineGluingUnit e d) := by
  obtain ⟨L, ⟨e⟩, ⟨d⟩, hL⟩ := LineBundleClass.exists_trivialized_representative a
  refine ⟨QuotientGroup.mk (h.toCommSq.lineGluingUnit e d), fun K e' d' hK ↦ ?_⟩
  exact (h.picardClass_eq_iff_gluingUnit_quotient_eq hi e d e' d').mp (hL.trans hK.symm)

private theorem gluingUnitClass_mul (hi : i.ker = f.conductor)
    (a b : ((LineBundleClass.pullbackHom f).ker ⊓ (LineBundleClass.pullbackHom i).ker :
      Subgroup (LineBundleClass X))) :
    (h.exists_gluingUnitClass hi (a * b)).choose =
      (h.exists_gluingUnitClass hi a).choose * (h.exists_gluingUnitClass hi b).choose := by
  obtain ⟨L, ⟨e⟩, ⟨d⟩, hL⟩ := LineBundleClass.exists_trivialized_representative a
  obtain ⟨K, ⟨e'⟩, ⟨d'⟩, hK⟩ := LineBundleClass.exists_trivialized_representative b
  have hLK : LineBundleClass.mk (L ⊗ K) = (a * b).val := by
    rw [Subgroup.coe_mul, ← hL, ← hK, ← LineBundleClass.mk_tensorProduct]
    exact LineBundleClass.mk_eq_mk_iff.mpr ⟨(InvertibleSheaf.tensorProductObjIso L K).symm⟩
  rw [(h.exists_gluingUnitClass hi a).choose_spec L e d hL,
    (h.exists_gluingUnitClass hi b).choose_spec K e' d' hK,
    (h.exists_gluingUnitClass hi (a * b)).choose_spec (L ⊗ K)
      (pullbackTensorTrivialization f e e') (pullbackTensorTrivialization i d d') hLK,
    h.toCommSq.lineGluingUnit_tensor, QuotientGroup.mk_mul]

private theorem gluingUnitClass_surjective (hi : i.ker = f.conductor) :
    Function.Surjective (fun a ↦ (h.exists_gluingUnitClass hi a).choose) := by
  intro q
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨L, e, d, hu⟩ := h.exists_glued_line_of_conductor_square u hi
  have hker {T : Scheme.{u}} (p : T ⟶ X)
      (t : (pullback p).obj L.obj ≅ 𝟙_ T.Modules) :
      LineBundleClass.mk L ∈ (LineBundleClass.pullbackHom p).ker := by
    rw [MonoidHom.mem_ker, LineBundleClass.pullbackHom_apply,
      LineBundleClass.pullback_mk, LineBundleClass.mk_eq_one_iff]
    exact ⟨t⟩
  let a : ((LineBundleClass.pullbackHom f).ker ⊓ (LineBundleClass.pullbackHom i).ker :
      Subgroup (LineBundleClass X)) := ⟨LineBundleClass.mk L, hker f e, hker i d⟩
  refine ⟨a, ((h.exists_gluingUnitClass hi a).choose_spec L e d rfl).trans ?_⟩
  rw [(h.toCommSq.lineGluingUnit_eq_iff e d u).mpr hu]

/-- Picard classes trivial on both sides of a conductor square are identified with
overlap units modulo rescaling by units on the two sides. -/
def lineGluingClassMulEquiv (hi : i.ker = f.conductor) :
    ((LineBundleClass.pullbackHom f).ker ⊓ (LineBundleClass.pullbackHom i).ker :
      Subgroup (LineBundleClass X)) ≃* (Γ(P, ⊤)ˣ ⧸ (j.lineGluingCoboundary g).range) :=
  MulEquiv.ofBijective
    (⟨fun a ↦ (h.exists_gluingUnitClass hi a).choose, h.gluingUnitClass_mul hi⟩ : _ →ₙ* _)
    ⟨by
      intro a b hab
      obtain ⟨L, ⟨e⟩, ⟨d⟩, hL⟩ := LineBundleClass.exists_trivialized_representative a
      obtain ⟨K, ⟨e'⟩, ⟨d'⟩, hK⟩ := LineBundleClass.exists_trivialized_representative b
      have ha := (h.exists_gluingUnitClass hi a).choose_spec L e d hL
      have hb := (h.exists_gluingUnitClass hi b).choose_spec K e' d' hK
      have hLK := (h.picardClass_eq_iff_gluingUnit_quotient_eq hi e d e' d').mpr
        (ha.symm.trans (hab.trans hb))
      exact Subtype.ext (hL.symm.trans (hLK.trans hK)),
    h.gluingUnitClass_surjective hi⟩

/-- Compute the gluing class from any representative and any pair of trivializations. -/
theorem lineGluingClassMulEquiv_apply (hi : i.ker = f.conductor)
    (a : ((LineBundleClass.pullbackHom f).ker ⊓ (LineBundleClass.pullbackHom i).ker :
      Subgroup (LineBundleClass X)))
    (L : InvertibleSheaf X) (e : (pullback f).obj L.obj ≅ 𝟙_ Y.Modules)
    (d : (pullback i).obj L.obj ≅ 𝟙_ Z.Modules) (hL : LineBundleClass.mk L = a.val) :
    h.lineGluingClassMulEquiv hi a = QuotientGroup.mk (h.toCommSq.lineGluingUnit e d) :=
  (h.exists_gluingUnitClass hi a).choose_spec L e d hL

end CategoryTheory.IsPullback
