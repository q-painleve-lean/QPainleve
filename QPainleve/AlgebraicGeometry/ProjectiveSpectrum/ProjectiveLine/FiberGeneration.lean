/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.LineBundle.RelativeGeneration
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
public import TauCeti.AlgebraicGeometry.IntersectionNumber.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.ProjectiveLine
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.ClosedImmersion
import QPainleve.AlgebraicGeometry.IdealSheaf.Tensor.SectionLifting
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.Cohomology
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.GlobalGeneration
import TauCeti.AlgebraicGeometry.Curves.ProjectiveLine
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct
import TauCeti.AlgebraicGeometry.LineBundle.GlobalGeneration.Basic

/-!
# Surjectivity of evaluation on a projective-line ruling

For a line bundle of nonnegative degree on the closed fibers, a generating section on
a fiber lifts after a positive twist along that fiber. The twist comes from the base,
so it can be removed locally. In particular a degree-one bundle supplies the quotient
of the pullback of its direct image used in the projective bundle description of the ruling.

See [Vakil, *Complex Algebraic Surfaces*, Class 17, §2][Vakil].
The section-lifting argument uses the Cartier twist comparison in the proof of
[Debarre, *Introduction to Mori Theory*, Theorem 4.1][Debarre].

[Vakil]: https://math.stanford.edu/~vakil/02-245/sclass17A.pdf#page=4
[Debarre]: https://perso.imj-prg.fr/wp-content/uploads/debarre-pub/M22.pdf#page=42
-/

public section

open CategoryTheory Filter Limits
open TauCeti.AlgebraicGeometry LineBundleClass

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k]

local notation "class(" L ")" => LineBundleClass.mk L
local notation "I[" h "]" => Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheaf h

private theorem exists_twist_section_of_cartier_fiber (f : X ⟶ Y) (L : InvertibleSheaf X)
    (K : InvertibleSheaf Y) (J : X.IdealSheafData) (hJ : J.IsEffectiveCartier)
    (hclass : pullback f (class(K)) = class(I[hJ]))
    (htriv : pullback J.subschemeι (class(I[hJ])) = 1)
    (e : projectiveLine k ≅ J.subscheme)
    (hdeg : 0 ≤ intersectionNumber k (e.hom ≫ J.subschemeι) (class(L)))
    (z : J.subscheme) :
    ∃ (N : InvertibleSheaf Y)
      (s : Γ((L.tensorProduct ((InvertibleSheaf.pullback f).obj N)).obj, ⊤)),
      J.subschemeι z ∈
        (L.tensorProduct ((InvertibleSheaf.pullback f).obj N)).obj.nonvanishingLocus s := by
  have hcoh := J.subsingleton_cohomology_one_tensor_pushforwardSubscheme_of_projectiveLine
    L e ((by decide : (-1 : ℤ) ≤ 0).trans hdeg)
  obtain ⟨n, hn⟩ := (hJ.eventually_surjective_pullbackSectionsLE_of_trivial_conormal
    (k := k) L htriv hcoh).exists
  let M := L.tensorProduct (I[hJ].dual.tensorPow n)
  have hM : class(M) = class(L) * class(I[hJ])⁻¹ ^ n := by
    simp only [M, mk_tensorProduct, mk_tensorPow, ← inv_mk]
  let i := J.subschemeι
  have hres : class((InvertibleSheaf.pullback i).obj M) =
      class((InvertibleSheaf.pullback i).obj L) := by
    simp only [i, ← pullback_mk, hM, pullback_mul, pullback_pow, pullback_inv, htriv,
      inv_one, one_pow, mul_one]
  have hglob : ((InvertibleSheaf.pullback i).obj L).IsGloballyGenerated := by
    apply InvertibleSheaf.isGloballyGenerated_of_nonneg_eulerDegree_projectiveLine _ e
    simpa only [i, ← eulerDegree_mk, ← pullback_mk, ← pullback_comp, intersectionNumber_def] using
      hdeg
  obtain ⟨r⟩ := mk_eq_mk_iff.mp hres
  let ri := eqToIso (InvertibleSheaf.pullback_obj_obj i M)
  have hG := (InvertibleSheaf.isGloballyGenerated_iff_of_iso r).mpr hglob
  obtain ⟨t, ht⟩ := InvertibleSheaf.isGloballyGenerated_iff.mp hG z
  obtain ⟨s, hs⟩ := hn (ri.hom.app ⊤ t)
  have hz : i z ∈ M.obj.nonvanishingLocus s := by
    rw [← Scheme.Modules.nonvanishingLocus_hom_app ri, ← hs,
      Scheme.Modules.nonvanishingLocus_pullbackSectionsLE, top_inf_eq] at ht
    exact ht
  let N := K.dual.tensorPow n
  let Q := L.tensorProduct ((InvertibleSheaf.pullback f).obj N)
  have hQ : class(Q) = class(M) := by
    simp only [Q, N, hM, mk_tensorProduct, ← pullback_mk, mk_tensorPow, ← inv_mk,
      pullback_pow, pullback_inv, hclass]
  obtain ⟨q⟩ := mk_eq_mk_iff.mp hQ
  refine ⟨N, q.symm.hom.app ⊤ s, ?_⟩
  exact (Scheme.Modules.nonvanishingLocus_hom_app q.symm s).symm ▸ hz

private theorem exists_twist_section_of_projectiveLine_fiber
    (f : X ⟶ Y) [Flat f] (L : InvertibleSheaf X) {y : Y} (hy : IsClosed ({y} : Set Y))
    (hP : (Y.fromSpecResidueField y).ker.IsEffectiveCartier)
    (e : projectiveLine k ≅ f.fiber y)
    (hdeg : 0 ≤ intersectionNumber k (e.hom ≫ f.fiberι y) (class(L)))
    (z : f.fiber y) :
    ∃ (N : InvertibleSheaf Y)
      (s : Γ((L.tensorProduct ((InvertibleSheaf.pullback f).obj N)).obj, ⊤)),
      f.fiberι y z ∈
        (L.tensorProduct ((InvertibleSheaf.pullback f).obj N)).obj.nonvanishingLocus s := by
  let j := Y.fromSpecResidueField y
  let i := f.fiberι y
  let J := i.ker
  have : IsClosedImmersion j := isClosed_singleton_iff_isClosedImmersion.mp hy
  have : IsClosedImmersion i :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f j).flip inferInstance
  have hJP : j.ker.comap f = J :=
    (IdealSheafData.ker_fst_of_isClosedImmersion j f).symm
  have hJ : J.IsEffectiveCartier := hJP ▸ hP.comap f
  let a : f.fiber y ≅ J.subscheme := asIso i.toImage
  have ha : a.hom ≫ J.subschemeι = i := i.toImage_imageι
  have hclass : pullback f (class(I[hP])) = class(I[hJ]) :=
    (hP.pullback_mk_toInvertibleSheaf (hJP.symm ▸ hJ)).trans (mk_toInvertibleSheaf_congr _ _ hJP)
  have htriv : pullback J.subschemeι (class(I[hJ])) = 1 := by
    apply (pullbackEquiv a).injective
    simp only [pullbackEquiv_apply, pullback_one]
    rw [pullback_comp, ha, ← hclass, pullback_comp, f.fiber_fac, ← pullback_comp,
      Subsingleton.elim (pullback j (class(I[hP]))) 1, pullback_one]
  have hdeg' : 0 ≤ intersectionNumber k ((e ≪≫ a).hom ≫ J.subschemeι) (class(L)) := by
    rw [Iso.trans_hom, Category.assoc, ha]
    exact hdeg
  obtain ⟨N, s, hs⟩ := exists_twist_section_of_cartier_fiber (k := k)
    f L I[hP] J hJ hclass htriv (e ≪≫ a) hdeg' (a.hom z)
  exact ⟨N, s, by simpa only [← Scheme.Hom.comp_apply, ha] using hs⟩

/-- If the closed fibers of a flat closed morphism are projective lines and
their base points are effective Cartier divisors, evaluation is surjective for
every line bundle of nonnegative degree on these fibers. -/
theorem epi_counit_of_projectiveLine_fibers (f : X ⟶ Y) [Flat f]
    (hf : IsClosedMap f) (L : InvertibleSheaf X)
    (hP : ∀ y : Y, IsClosed ({y} : Set Y) → (Y.fromSpecResidueField y).ker.IsEffectiveCartier)
    (hF : ∀ y : Y, IsClosed ({y} : Set Y) →
      ∃ e : projectiveLine k ≅ f.fiber y,
        0 ≤ intersectionNumber k (e.hom ≫ f.fiberι y) (class(L))) :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app L.obj) := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of k))
  apply f.epi_counit_of_exists_twist_section L
  intro x hx
  have hy : IsClosed ({f x} : Set Y) := by simpa only [Set.image_singleton] using hf _ hx
  obtain ⟨e, he⟩ := hF (f x) hy
  obtain ⟨N, s, hs⟩ := exists_twist_section_of_projectiveLine_fiber (k := k)
    f L hy (hP (f x) hy) e he (f.asFiber x)
  exact ⟨N, s, by simpa only [f.fiberι_asFiber] using hs⟩

/-- For a proper flat morphism to the projective line with projective-line closed
fibers, the evaluation of every line bundle of nonnegative fiber degree is surjective. -/
theorem epi_ruling_evaluation (f : X ⟶ projectiveLine k) [IsProper f] [Flat f]
    (L : InvertibleSheaf X)
    (hF : ∀ y : projectiveLine k, IsClosed ({y} : Set (projectiveLine k)) →
      ∃ e : projectiveLine k ≅ f.fiber y,
        0 ≤ intersectionNumber k (e.hom ≫ f.fiberι y) (class(L))) :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app L.obj) := by
  have : TauCeti.AlgebraicGeometry.IsRegular (projectiveLine k) := ⟨fun _ ↦ inferInstance⟩
  exact f.epi_counit_of_projectiveLine_fibers f.isClosedMap L
    (fun _ hy ↦ (projectiveLine k).isEffectiveCartier_ker_fromSpecResidueField_of_dim_eq_one
      hy (Scheme.IsCurveOver.topologicalKrullDim_eq_one k)) hF

end AlgebraicGeometry.Scheme.Hom
