/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Contraction
public import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
public import QPainleve.AlgebraicGeometry.Normalization.Proper
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Basic

import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Comparison
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections.Ample
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Proper
import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.Basic

/-!
# A normal model collapsing an exceptional curve

A morphism collapsing an exceptional curve of the first kind factors through the
relative normalization of its scheme-theoretic image. The new target is normal and
finite over projective space, and the morphism to it is an isomorphism away from the
curve. The new target is projective, and the scheme-theoretic fiber over the
collapsed point is the exceptional curve.
This gives the normal model in the contraction argument of the
[Stacks Project, Lemma 54.16.4](https://stacks.math.columbia.edu/tag/0C2L).
-/

public section

open CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} {E : X.IdealSheafData}

variable [IsIntegral X] [IsNormalScheme X]

/-- An exceptional curve of the first kind on a normal integral projective scheme is the
scheme-theoretic fiber of a modification to a normal integral scheme finite over projective
space. The target is projective over the coefficient field. The contracted point is the entire
non-isomorphism locus. Pullback induces an isomorphism on sections over every open of the target. -/
theorem IsExceptionalCurveOfFirstKind.exists_normal_model_collapsing_exceptional_curve
    (hE : E.IsExceptionalCurveOfFirstKind)
    (k : Type u) [Field k] [X.Over (Spec (.of k))] [X.IsProjectiveOver k] :
    ∃ (ι : Type u) (_ : Finite ι) (Z : Scheme.{u})
      (j : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule ι k)) (f : X ⟶ Z) (p : Z),
      IsIntegral Z ∧ IsNormalScheme Z ∧ IsFinite j ∧
      f ≫ j ≫ Proj.toSpecCoeff (MvPolynomial.homogeneousSubmodule ι k) = X ↘ Spec (.of k) ∧
      IsModification f ∧ IsClosed ({p} : Set Z) ∧ f ⁻¹' {p} = (E.support : Set X) ∧
      (Z.fromSpecResidueField p).ker.comap f = E ∧
      f.centre = {p} ∧ (∀ U : Z.Opens, IsIso (f.app U)) ∧
      (letI : Z.Over (Spec (.of k)) :=
        ⟨j ≫ Proj.toSpecCoeff (MvPolynomial.homogeneousSubmodule ι k)⟩
       Z.IsProjectiveOver k) := by
  obtain ⟨ι, hι, g, p, hg, hproper, hp, hpre, hideal, hq⟩ :=
    hE.exists_projective_morphism_with_exceptional_fiber k
  let g' := g.toImage
  have : IsProper (g' ≫ g.imageι) := g.toImage_imageι.symm ▸ hproper
  have : IsProper g' := IsProper.of_comp g' g.imageι
  let s := g.imageι ≫ Proj.toSpecCoeff (MvPolynomial.homogeneousSubmodule ι k)
  have : LocallyOfFiniteType s := by dsimp [s]; infer_instance
  have hq' {x : X} (hx : x ∉ (E.support : Set X)) : g'.QuasiFiniteAt x :=
    (Scheme.Hom.quasiFiniteAt_comp_iff (g := g.imageι)).mp
      (by simpa only [g', Scheme.Hom.toImage_imageι] using hq x hx)
  have hη := hq' hE.isEffectiveCartier.genericPoint_notMem_support
  have : IsFinite g'.fromNormalization :=
    g'.isFinite_fromNormalization_of_quasiFiniteAt_genericPoint s hη
  let f := g'.toNormalization
  let j := g'.fromNormalization ≫ g.imageι
  have hf : f ≫ j = g := by simp [f, j, g']
  have hI := hE.isIntegral_subscheme
  let x := E.subschemeι (genericPoint E.subscheme)
  have hx : x ∈ (E.support : Set X) := E.range_subschemeι ▸ Set.mem_range_self _
  let p' := g' x
  have hp' : g.imageι p' = p := by
    rw [← Scheme.Hom.comp_apply, g.toImage_imageι]
    exact (Set.ext_iff.mp hpre x).mpr hx
  have hpre' : g' ⁻¹' {p'} = (E.support : Set X) := by
    rw [← hpre]
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [← g.imageι.injective.eq_iff, hp', ← Scheme.Hom.comp_apply, g.toImage_imageι]
  have hconnected : _root_.IsConnected (g' ⁻¹' {p'}) := by
    rw [hpre', ← E.range_subschemeι]
    exact isConnected_range E.subschemeι.continuous
  obtain ⟨q, hfiber, hcentre⟩ := g'.exists_centre_eq_singleton_toNormalization hconnected
    (hpre'.symm ▸ hE.not_subsingleton_support) (fun _ hx ↦ hq' (by rwa [← hpre']))
  have hF : f ⁻¹' {q} = (E.support : Set X) := hfiber.trans hpre'
  have hclosed : IsClosed ({q} : Set g'.normalization) := hcentre ▸ f.isClosed_centre
  have hjq : j q = p := by
    have hxq : f x = q := (Set.ext_iff.mp hF x).mpr hx
    rw [← hxq, ← Scheme.Hom.comp_apply, hf]
    exact (Set.ext_iff.mp hpre x).mpr hx
  have hideal' : (Scheme.fromSpecResidueField _ (j q)).ker.comap (f ≫ j) = E :=
    (congrArg₂ (fun z a ↦ (Scheme.fromSpecResidueField _ z).ker.comap a) hjq hf).trans hideal
  have : IsReduced ((Scheme.fromSpecResidueField _ (j q)).ker.comap (f ≫ j)).subscheme :=
    hideal' ▸ (inferInstance : IsReduced E.subscheme)
  have heq := f.comap_ker_fromSpecResidueField_eq_of_comp j hclosed (hjq.symm ▸ hp)
    (hF.trans (by rw [hjq, hf]; exact hpre.symm))
  refine ⟨ι, hι, g'.normalization, j, f, q, inferInstance,
    g'.isNormalScheme_normalization_of_isNormalScheme, inferInstance, ?_,
    g'.isModification_toNormalization_of_quasiFiniteAt hη, hclosed, hF, heq.trans hideal', hcentre,
    g'.isIso_app_toNormalization, ?_⟩
  · rwa [← Category.assoc, hf]
  · let : g'.normalization.Over (Spec (.of k)) :=
      ⟨j ≫ Proj.toSpecCoeff (MvPolynomial.homogeneousSubmodule ι k)⟩
    have : j.IsOver (Spec (.of k)) := ⟨rfl⟩
    exact Scheme.IsProjectiveOver.of_isFinite k j

end AlgebraicGeometry.Scheme.IdealSheafData
