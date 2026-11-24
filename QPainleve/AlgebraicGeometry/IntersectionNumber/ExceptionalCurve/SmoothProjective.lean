/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Blowup
public import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.NormalModel
public import TauCeti.AlgebraicGeometry.IdealSheaf.Over
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension

import QPainleve.AlgebraicGeometry.Curves.GenusZero
import QPainleve.AlgebraicGeometry.IdealSheaf.Stalk
import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.CompletedStalk
import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Localization
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Smooth projective contractions of exceptional curves

An exceptional curve of the first kind on a smooth integral projective surface over
an algebraically closed field can be contracted to a point on a smooth projective
surface. The contraction exhibits the original surface as the blowup of that point.

The argument uses the completed-local-ring and blowup comparisons in the
[Stacks Project, Lemma 54.16.4](https://stacks.math.columbia.edu/tag/0C2L).
The projective case is [Lemma 54.16.9(1)](https://stacks.math.columbia.edu/tag/0C2N).
-/

public section

open CategoryTheory Limits TopologicalSpace
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {E : X.IdealSheafData}

section Local

variable [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [IsLocallyNoetherian Y]

local notation "A[" p "]" => Y.presheaf.stalk p
local notation "s[" p "]" => Y.fromSpecStalk p
local notation "I[" p "]" => Scheme.Hom.ker (Spec.map (Y.residue p))

/-- A proper contraction whose scheme-theoretic fiber is an exceptional projective line
over the ground field has a regular two-dimensional local ring at its contracted point,
provided pullback identifies functions and the morphism is an isomorphism off the point. -/
theorem isRegularLocalRing_and_ringKrullDim_eq_of_contraction
    (hE : E.IsExceptionalCurveOfFirstKind) (e : projectiveLine k ≅ E.subscheme)
    [e.hom.IsOver (Spec (.of k))] (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f] {p : Y}
    (hp : IsClosed ({p} : Set Y)) (hF : (Y.fromSpecResidueField p).ker.comap f = E)
    (hU : ((Y.fromSpecResidueField p).ker.support).compl ≤ f.isoLocus)
    (hf : ∀ V : Y.affineOpens, IsIso (f.app V)) :
    IsRegularLocalRing A[p] ∧ ringKrullDim A[p] = 2 := by
  let a := pullback.fst f s[p]
  let g := pullback.snd f s[p]
  let J := I[p].comap g
  -- Use the algebra structure induced by the target scheme at the contracted point.
  let : Algebra k A[p] := (Spec.preimage (s[p] ≫ (Y ↘ Spec (.of k)))).hom.toAlgebra
  let : (pullback f s[p]).Over (Spec (.of k)) := ⟨a ≫ (X ↘ Spec (.of k))⟩
  have ha : a.IsOver (Spec (.of k)) := ⟨rfl⟩
  have hg : g.IsOver (Spec (.of k)) := by
    constructor
    rw [specOverSpec_over]
    have h : Spec.map (CommRingCat.ofHom (algebraMap k A[p])) =
        s[p] ≫ (Y ↘ Spec (.of k)) := Spec.map_preimage _
    rw [h, ← Category.assoc, ← pullback.condition, Category.assoc, comp_over f]
    exact ha.comp_over
  obtain ⟨_, hΓ, hJ, hloc⟩ := hE.localize_contraction hp hF hU hf
  have : IsIso g.appTop := hΓ ⊤
  -- The closed fiber of the localization is the original curve over the ground field.
  have hJE : J = E.comap a := f.comap_ker_residue_pullback_snd_fromSpecStalk hp hF
  let j := subschemeMap J E a (hJE ▸ E.le_map_comap a)
  have : IsIso j := f.isIso_subschemeMap_comap_pullback_fst_of_support_le hp hF E le_rfl hJE
  have hj : j.IsOver (Spec (.of k)) := by
    constructor
    rw [J.over_eq_subschemeι_comp, E.over_eq_subschemeι_comp, ← ha.comp_over]
    exact (reassoc_of% (subschemeMap_subschemeι J E a (hJE ▸ E.le_map_comap a))) (X ↘ Spec (.of k))
  let e' := e ≪≫ (asIso j).symm
  have : e'.hom.IsOver (Spec (.of k)) := by
    dsimp only [e', Iso.trans_hom, Iso.symm_hom]
    infer_instance
  have hI := Scheme.Hom.ker_Spec_map (Y.residue p)
  have hker : RingHom.ker (Y.residue p).hom = IsLocalRing.maximalIdeal A[p] :=
    IsLocalRing.ker_residue
  rw [hker] at hI
  exact hJ.isRegularLocalRing_and_ringKrullDim_eq_of_exceptional_thickenings e' g
    (congrArg (fun K ↦ K.comap g) hI.symm) (hI ▸ hloc)

end Local

section Projective

attribute [local instance] MvPolynomial.gradedAlgebra

variable [IsAlgClosed k] [X.Over (Spec (.of k))]

/-- Over an algebraically closed ground field, an exceptional curve on a proper scheme
is isomorphic to the projective line over that field. -/
theorem exists_iso_projectiveLine_over [IsProper (X ↘ Spec (.of k))]
    (hE : E.IsExceptionalCurveOfFirstKind) :
    ∃ e : projectiveLine k ≅ E.subscheme, e.hom.IsOver (Spec (.of k)) := by
  have : E.subscheme.IsCurveOver k := Scheme.isCurveOver_iff.mpr
    ⟨hE.isIntegral_subscheme, inferInstanceAs (IsProper (E.subschemeι ≫ (X ↘ Spec (.of k)))),
      hE.topologicalKrullDim_subscheme⟩
  have hgen : E.subscheme.genus k = 0 := by
    simpa only [Scheme.genus_def] using hE.finrank_cohomology_one_trivial_eq_zero k
  obtain ⟨e, he⟩ := Scheme.genus_eq_zero_iff_exists_iso_projectiveLine.mp hgen
  have : e.hom.IsOver (Spec (.of k)) := he
  exact ⟨e.symm, by simpa only [Iso.symm_hom] using
    (inferInstance : e.inv.IsOver (Spec (.of k)))⟩

variable [IsIntegral X] [X.IsProjectiveOver k] [Smooth (X ↘ Spec (.of k))]

/-- Castelnuovo contraction of an exceptional curve on a smooth integral projective scheme
over an algebraically closed field. The target is a smooth integral projective surface.
Pullback identifies functions on every target open with those on its inverse image. The
exceptional curve is the scheme-theoretic fiber, and the contraction is the blowup of the point. -/
theorem exists_smooth_projective_contraction (hE : E.IsExceptionalCurveOfFirstKind) :
    ∃ (Z : Scheme.{u}) (t : Z ⟶ Spec (.of k)) (f : X ⟶ Z) (p : Z),
      letI : Z.Over (Spec (.of k)) := ⟨t⟩
      IsIntegral Z ∧ Z.IsProjectiveOver k ∧ SmoothOfRelativeDimension 2 t ∧
        f.IsOver (Spec (.of k)) ∧ IsModification f ∧ IsClosed ({p} : Set Z) ∧ f.centre = {p} ∧
        (Z.fromSpecResidueField p).ker.comap f = E ∧ (∀ U : Z.Opens, IsIso (f.app U)) ∧
        ∃ e : X ≅ (Z.fromSpecResidueField p).ker.blowup,
          e.hom ≫ (Z.fromSpecResidueField p).ker.blowupToBase = f := by
  have : IsRegular X := IsRegular.of_smooth (X ↘ Spec (.of k))
  obtain ⟨ι, _, Z, j, f, p, hZ, _, _, hs, hmod, hp, _, hF, hc, hΓ, hproj⟩ :=
    hE.exists_normal_model_collapsing_exceptional_curve k
  let t := j ≫ Proj.toSpecCoeff (MvPolynomial.homogeneousSubmodule ι k)
  let : Z.Over (Spec (.of k)) := ⟨t⟩
  have : f.IsOver (Spec (.of k)) := ⟨hs⟩
  have : IsNoetherian Z := isNoetherian_of_finiteType (Z ↘ Spec (.of k))
  have : LocallyOfFiniteType t := inferInstanceAs (LocallyOfFiniteType (Z ↘ Spec (.of k)))
  have hU : ((Z.fromSpecResidueField p).ker.support).compl ≤ f.isoLocus := by
    rw [← SetLike.coe_subset_coe, Closeds.coe_compl,
      support_ker_fromSpecResidueField_of_isClosed hp, ← hc, Scheme.Hom.compl_centre]
  obtain ⟨e, he⟩ := hE.exists_iso_projectiveLine_over (k := k)
  obtain ⟨hr, hd⟩ := hE.isRegularLocalRing_and_ringKrullDim_eq_of_contraction e f hp hF hU
    (fun V ↦ hΓ V.val)
  have : IsRegular Z := f.isRegular_of_isRegularLocalRing_of_mem_centre fun y hy ↦ by
    rw [hc, Set.mem_singleton_iff] at hy
    exact hy ▸ hr
  have : Smooth t := t.smooth_of_isRegularLocalRing_stalk
  have hdim : SmoothOfRelativeDimension 2 t := smoothOfRelativeDimension_of_topologicalKrullDim_eq t
    ((ringKrullDim_stalk_eq_topologicalKrullDim_of_isClosed t hp).symm.trans hd)
  let I := (Z.fromSpecResidueField p).ker
  have := hE.isIso_blowupLift_of_regular_contraction_point f hc hd hF
  exact ⟨Z, t, f, p, hZ, hproj, hdim, inferInstance, hmod, hp, hc, hF, hΓ,
    asIso (I.blowupLift f (hF.symm ▸ hE.isEffectiveCartier)),
    I.blowupLift_blowupToBase f _⟩

end Projective

end AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind
