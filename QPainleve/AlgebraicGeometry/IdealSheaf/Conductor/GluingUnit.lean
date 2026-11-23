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
