/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
public import TauCeti.AlgebraicGeometry.Birational.RationalMap.ValuationRing
public import TauCeti.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Basic
import QPainleve.AlgebraicGeometry.Morphisms.Separated
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced

/-!
# Isomorphisms onto exceptional curves

A proper morphism to a curve of the first kind that induces an isomorphism of
function fields is an isomorphism. In the comparison of two point blowups,
a dominant restriction to the target exceptional curve induces such an
isomorphism of function fields as soon as the ambient map is an isomorphism
near the generic point of that curve.

## References

* [The Stacks Project, Lemma 54.17.1](https://stacks.math.columbia.edu/tag/0C5R)
-/

public section

open CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind

variable {X Y : Scheme.{u}} {I : X.IdealSheafData} {J : Y.IdealSheafData}

/-- Every local ring of an exceptional curve of the first kind is a valuation ring. -/
theorem valuationRing_stalk (hJ : J.IsExceptionalCurveOfFirstKind) (y : J.subscheme) :
    let _ := hJ.isIntegral_subscheme
    ValuationRing (J.subscheme.presheaf.stalk y) := by
  let := hJ.isIntegral_subscheme
  obtain ⟨k, _, e, -⟩ := hJ.exists_iso
  have := Scheme.IsCurveOver.valuationRing_stalk k (projectiveLine k) (e.inv y)
  let a := (asIso (e.inv.stalkMap y)).commRingCatIsoToRingEquiv
  exact Function.Surjective.valuationRing a.toRingHom a.surjective

/-- A proper dominant morphism from an integral scheme to an exceptional curve is an
isomorphism if it induces an isomorphism of function fields. -/
theorem isIso_of_isIso_functionFieldMap (hJ : J.IsExceptionalCurveOfFirstKind)
    [IsIntegral X] [IsIntegral J.subscheme] (g : X ⟶ J.subscheme)
    [IsProper g] [IsDominant g] [IsIso g.functionFieldMap] : IsIso g := by
  let t := J.subscheme.fromSpecStalk (genericPoint J.subscheme)
  let s := X.fromSpecStalk (genericPoint X)
  let a := Spec.map (inv g.functionFieldMap)
  have hgen : s ≫ g = Spec.map g.functionFieldMap ≫ t :=
    g.SpecMap_functionFieldMap_fromSpecStalk.symm
  have ha : (a ≫ s) ≫ g = t := by
    rw [Category.assoc, hgen, ← Spec.map_comp_assoc, IsIso.hom_inv_id, Spec.map_id,
      Category.id_comp]
  obtain ⟨σ, ⟨hσ, hσgen⟩, -⟩ :=
    g.existsUnique_section_of_valuationRing hJ.valuationRing_stalk (a ≫ s) ha
  have : IsDominant (t ≫ σ) := hσgen.symm ▸ inferInstanceAs (IsDominant (a ≫ s))
  have : IsDominant σ := IsDominant.of_comp t σ
  exact g.isIso_of_dominant_section σ hσ

/-- Suppose a proper morphism restricts to a dominant morphism from an integral closed subscheme
onto an exceptional curve of the first kind. If the target curve meets the ambient isomorphism
locus, the restriction is an isomorphism. -/
theorem isIso_of_dominant_over_isoLocus (hJ : J.IsExceptionalCurveOfFirstKind)
    (f : X ⟶ Y) [IsProper f] [IsIntegral I.subscheme]
    (g : I.subscheme ⟶ J.subscheme) [IsDominant g]
    (hg : g ≫ J.subschemeι = I.subschemeι ≫ f)
    (y : J.subscheme) (hy : J.subschemeι y ∈ f.isoLocus) : IsIso g := by
  let := hJ.isIntegral_subscheme
  let η := genericPoint I.subscheme
  have hη : f (I.subschemeι η) ∈ f.isoLocus :=
    have hyη : J.subschemeι (genericPoint J.subscheme) ∈ f.isoLocus :=
      ((genericPoint_specializes y).map J.subschemeι.continuous).mem_open f.isoLocus.isOpen hy
    have hηeq : f (I.subschemeι η) = J.subschemeι (genericPoint J.subscheme) := calc
      f (I.subschemeι η) = J.subschemeι (g η) :=
        (congrArg (fun m : I.subscheme ⟶ Y ↦ m η) hg).symm
      _ = _ := congrArg J.subschemeι g.genericPoint_eq_of_isDominant
    hηeq.symm ▸ hyη
  have hfη := f.isIso_stalkMap_of_mem_isoLocus hη
  have hproper : IsProper (g ≫ J.subschemeι) := hg.symm ▸ inferInstanceAs
    (IsProper (I.subschemeι ≫ f))
  have := IsProper.of_comp g J.subschemeι
  have compApply {W : Scheme.{u}} (a : I.subscheme ⟶ W) (b : W ⟶ Y)
      (c : Y.presheaf.stalk ((a ≫ b) η)) :
      ((a ≫ b).stalkMap η).hom c = a.stalkMap η (b.stalkMap (a η) c) :=
    congrArg (fun m ↦ m.hom c) (Scheme.Hom.stalkMap_comp a b η)
  have hsurj : Function.Surjective (((g ≫ J.subschemeι).stalkMap η).hom) := by
    rw [hg]
    intro c
    obtain ⟨a, rfl⟩ := I.subschemeι.stalkMap_surjective η c
    obtain ⟨b, rfl⟩ :=
      (ConcreteCategory.bijective_of_isIso (f.stalkMap (I.subschemeι η))).surjective a
    exact ⟨b, compApply I.subschemeι f b⟩
  let : IsSimpleRing (J.subscheme.presheaf.stalk (g η)) :=
    g.genericPoint_eq_of_isDominant.symm ▸ inferInstanceAs (IsSimpleRing J.subscheme.functionField)
  have : IsIso (g.stalkMap η) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    refine ⟨(g.stalkMap η).hom.injective, fun a ↦ ?_⟩
    obtain ⟨b, hb⟩ := hsurj a
    exact ⟨J.subschemeι.stalkMap (g η) b, (compApply g J.subschemeι b).symm.trans hb⟩
  exact hJ.isIso_of_isIso_functionFieldMap g

/-- A proper morphism that sends an integral closed subscheme nonconstantly into an exceptional
curve meeting the isomorphism locus induces an isomorphism onto that curve. -/
theorem exists_iso_of_nonconstant_over_isoLocus (hJ : J.IsExceptionalCurveOfFirstKind)
    (f : X ⟶ Y) [IsProper f] [IsIntegral I.subscheme]
    (hmap : Set.MapsTo f (I.support : Set X) (J.support : Set Y))
    (hnc : ¬ (Set.range (I.subschemeι ≫ f)).Subsingleton)
    (y : J.subscheme) (hy : J.subschemeι y ∈ f.isoLocus) :
    ∃ e : I.subscheme ≅ J.subscheme, e.hom ≫ J.subschemeι = I.subschemeι ≫ f := by
  let := hJ.isIntegral_subscheme
  have hle : J.comap f ≤ I := by
    have hrad := I.isReduced_subscheme_iff_radical_eq.mp inferInstance
    rw [← hrad, ← vanishingIdeal_support, ← le_support_iff_le_vanishingIdeal, support_comap]
    exact hmap
  let H := le_map_iff_comap_le.mpr hle
  let g := subschemeMap I J f H
  have hg : g ≫ J.subschemeι = I.subschemeι ≫ f := subschemeMap_subschemeι I J f H
  have : IsDominant g := by
    rw [isDominant_iff_genericPoint_eq]
    by_contra hη
    have hclosed := Scheme.isClosed_singleton_of_ne_genericPoint
      hJ.topologicalKrullDim_subscheme.le hη
    have hc (x : I.subscheme) : g x = g (genericPoint I.subscheme) := by
      have hs := specializes_iff_mem_closure.mp ((genericPoint_specializes x).map g.continuous)
      rwa [hclosed.closure_eq, Set.mem_singleton_iff] at hs
    apply hnc
    rintro _ ⟨x, rfl⟩ _ ⟨x', rfl⟩
    simp only [← hg, Scheme.Hom.comp_apply, hc x, hc x']
  have := hJ.isIso_of_dominant_over_isoLocus f g hg y hy
  exact ⟨asIso g, hg⟩

end AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind
