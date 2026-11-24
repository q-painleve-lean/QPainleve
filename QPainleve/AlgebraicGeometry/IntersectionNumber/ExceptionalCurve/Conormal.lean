/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Basic
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct
import QPainleve.AlgebraicGeometry.IdealSheaf.Tensor.Product
import QPainleve.AlgebraicGeometry.Modules.Pullback.SectionProducts
import QPainleve.AlgebraicGeometry.Modules.TensorProduct
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Multiplication

/-!
# Products of conormal sections of an exceptional curve

The conormal line bundle of an exceptional curve of the first kind is the degree-one
twist on the projective line. Products of sections generate the sections of every pair
of conormal powers. In particular, multiplying by conormal sections generates the
successive layers used to compute the ring of functions on the formal neighborhood.

## References

* The Stacks Project, [Lemma 54.16.3](https://stacks.math.columbia.edu/tag/0C2K).
-/

public section

open CategoryTheory Functor.LaxMonoidal MonoidalCategory
open TauCeti (isEffectiveCartier_pow)
open TauCeti.AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

private theorem surjective_sectionsFunctor_μ_conormalPowers
    {X : Scheme.{u}} {E : X.IdealSheafData} (hE : E.IsExceptionalCurveOfFirstKind) (m n : ℕ) :
    let C j := (pullback E.subschemeι).obj (E ^ j).sheaf
    Function.Surjective (μ (sectionsFunctor ⊤) (C m) (C n)) := by
  intro C
  obtain ⟨k, _, e, ⟨a⟩⟩ := hE.exists_iso
  have hopen : (⊤ : E.subscheme.Opens) ≤ e.hom.opensRange :=
    (e.hom.opensRange_of_isIso).ge
  apply (e.hom.surjective_sectionsFunctor_μ_iff_pullback hopen).mpr
  let f := e.hom ≫ E.subschemeι
  let I j := (isEffectiveCartier_pow hE.isEffectiveCartier j).toInvertibleSheaf
  let A := TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Fin 2 → k)
  let L j := (InvertibleSheaf.pullback f).obj (I j)
  let conormal := (InvertibleSheaf.pullback f).obj hE.isEffectiveCartier.toInvertibleSheaf
  have hdeg : conormal.eulerDegree k = 1 :=
    (projectiveLine.nonempty_iso_twistingSheaf_iff k _ 1).mp ⟨a⟩
  have hi (j : ℕ) : Nonempty ((pullback e.hom).obj (C j) ≅ Proj.twistingSheaf A j) := by
    have hpow : LineBundleClass.mk (L j) = LineBundleClass.mk conormal ^ j := by
      dsimp only [L, I, conormal]
      rw [← LineBundleClass.pullback_mk, LineBundleClass.mk_toInvertibleSheaf_pow,
        LineBundleClass.pullback_pow, LineBundleClass.pullback_mk]
    have : IsNoetherian (projectiveLine k) :=
      isNoetherian_of_finiteType (projectiveLine k ↘ Spec (.of k))
    have : Fact (∀ x : projectiveLine k, Order.coheight x ≤ 1) :=
      ⟨Scheme.IsCurveOver.coheight_le_one (k := k)⟩
    have hd : (L j).eulerDegree k = j := by
      rw [← LineBundleClass.eulerDegree_mk, hpow, ← zpow_natCast,
        LineBundleClass.eulerDegree_zpow k, LineBundleClass.eulerDegree_mk, hdeg, mul_one]
    obtain ⟨d⟩ := (projectiveLine.nonempty_iso_twistingSheaf_iff k (L j) j).mpr hd
    let hI := (isEffectiveCartier_pow hE.isEffectiveCartier j).toInvertibleSheaf_obj
    exact ⟨(pullbackComp e.hom E.subschemeι).app (E ^ j).sheaf ≪≫
      (pullback f).mapIso (eqToIso hI.symm) ≪≫
      eqToIso (InvertibleSheaf.pullback_obj_obj f (I j)).symm ≪≫ d⟩
  obtain ⟨hm⟩ := hi m
  obtain ⟨hn⟩ := hi n
  exact (surjective_sectionsFunctor_μ_iff_of_iso hm hn).mpr
    ((Pi.basisFun k (Fin 2)).surjective_sectionsFunctor_μ_twistingSheaf m n)

/-- Multiplication of the conormal powers of an exceptional curve of the first kind is
surjective on global sections. The multiplication morphism is the restriction to the
curve of the multiplication of its Cartier ideal powers. -/
theorem IsExceptionalCurveOfFirstKind.surjective_conormalPowerMultiplication
    {X : Scheme.{u}} {E : X.IdealSheafData} (hE : E.IsExceptionalCurveOfFirstKind) (m n : ℕ) :
    let P := pullback E.subschemeι
    let S := sectionsFunctor (⊤ : E.subscheme.Opens)
    let A := (E ^ m).sheaf
    let B := (E ^ n).sheaf
    Function.Surjective
      (μ S (P.obj A) (P.obj B) ≫ S.map
        (inv (Functor.OplaxMonoidal.δ (pullback E.subschemeι) A B) ≫
          P.map ((E ^ m).sheafMul (E ^ n) ≫ eqToHom (congrArg sheaf (pow_add E m n).symm)))) := by
  intro P S A B
  have h := surjective_sectionsFunctor_μ_conormalPowers hE m n
  have := (E ^ m).isIso_sheafMul_of_isEffectiveCartier _
    (isEffectiveCartier_pow hE.isEffectiveCartier n)
  let t := (E ^ m).sheafMul (E ^ n) ≫ eqToHom (congrArg sheaf (pow_add E m n).symm)
  let s := S.map (inv (Functor.OplaxMonoidal.δ (pullback E.subschemeι) A B) ≫ P.map t)
  have : IsIso t := inferInstanceAs (IsIso (_ ≫ _))
  have hs : Function.Surjective s := (ConcreteCategory.bijective_of_isIso s).surjective
  exact hs.comp h

end AlgebraicGeometry.Scheme.IdealSheafData
