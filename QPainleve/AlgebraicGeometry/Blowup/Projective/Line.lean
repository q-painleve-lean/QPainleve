/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.ElementaryTransform
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.Basic
public import TauCeti.AlgebraicGeometry.Blowup.IdealSheaf
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Polynomial.Ideal
import QPainleve.AlgebraicGeometry.Blowup.Affine
import QPainleve.AlgebraicGeometry.Gluing
import TauCeti.AlgebraicGeometry.Blowup.BaseChange
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.AffineLine
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.Extension
import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import TauCeti.Data.Fin.Rev
import TauCeti.RingTheory.Node.CoordinateOpen
import TauCeti.RingTheory.Node.Reduced

/-!
# Blowup charts for an elementary transformation of the projective line

Over an affine base, blow up the part of one of the two coordinate sections lying above
a principal divisor. The polynomial chart of the base equation and the node chart are supplied by
`elementaryTransformOuterChart` and `elementaryTransformNodeChart`. Together
with the unchanged opposite chart they give an isomorphism between the two blowups
of opposite sections.

See Gross, Hacking and Keel, [*Birational geometry of cluster algebras*][GHK], §3.1.

[GHK]: https://arxiv.org/html/1309.2573v2#S3.SS1
-/

public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory
open Polynomial reesAlgebra TauCeti.NodeAlgebra QPainleve

namespace TauCeti.AlgebraicGeometry.projectiveLine

universe u

variable {R : Type u} [CommRing R] (f : R) (i : Fin 2)

local notation "P" => R[X]
local notation "A" => (Spec (CommRingCat.of P))
local notation "J" => (Ideal.span {(X : P), C f})
local notation "N" => NodeAlgebra R f
local notation "Node" => (Spec (CommRingCat.of N))
local notation "Specₐ" g:max => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom g))

private abbrev affineCenter : (A).IdealSheafData :=
  IdealSheafData.ofIdealTop ((J).map (Scheme.ΓSpecIso (.of P)).inv.hom)

/-- The center on coordinate section `i` over the base divisor `f = 0`, as an ideal
sheaf on the projective line. -/
def coordinateSectionCenter : (projectiveLine R).IdealSheafData :=
  (affineCenter f).map (polynomialChartι R i)

/-- The center is the scheme-theoretic image of the zero point of the chosen chart
over `R/(f)`. In particular the ideal records the scheme structure of the base divisor. -/
theorem coordinateSectionCenter_eq_ker_polynomialPoint :
    coordinateSectionCenter f i =
      (polynomialPoint R (Ideal.Quotient.mk (Ideal.span {f})) i 0).ker := by
  let I : Ideal R := Ideal.span {f}
  let q := Ideal.Quotient.mk I
  let ev := evalRingHom (0 : R)
  have hq : eval₂RingHom q 0 = q.comp ev := by
    apply Polynomial.ringHom_ext <;> simp [ev, coe_eval₂RingHom, coe_evalRingHom]
  have hmap : Ideal.map ev J = I := by
    rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
    simp [ev, I]
  have hker_ev : RingHom.ker ev = Ideal.span {(X : P)} := by simp [ev, ker_evalRingHom]
  have hker : RingHom.ker (q.comp ev) = J := by
    rw [← RingHom.comap_ker, Ideal.mk_ker, ← hmap, Ideal.comap_map_of_surjective ev
      (fun r ↦ ⟨C r, eval_C⟩), ← RingHom.ker_eq_comap_bot, hker_ev, sup_eq_left]
    exact Ideal.span_mono (by simp)
  rw [coordinateSectionCenter, polynomialPoint_def, hq, ← IdealSheafData.map_ker,
    Scheme.Hom.ker_Spec_map, CommRingCat.hom_ofHom, hker]

/-- A surjective evaluation with kernel `(f)` gives the same coordinate-section
center as the quotient by `(f)`. -/
theorem coordinateSectionCenter_eq_ker_polynomialPoint_of_surjective
    {B : Type u} [CommRing B] (ev : R →+* B) (hsurj : Function.Surjective ev)
    (hker : RingHom.ker ev = Ideal.span {f}) :
    coordinateSectionCenter f i = (polynomialPoint R ev i 0).ker := by
  let e := RingHom.quotientKerEquivOfSurjective hsurj
  have hq : e.symm.toRingHom.comp ev = Ideal.Quotient.mk (RingHom.ker ev) :=
    RingHom.quotientKerEquivOfSurjective_symm_comp hsurj
  have he : IsIso (Spec.map (CommRingCat.ofHom e.symm.toRingHom)) :=
    inferInstanceAs (IsIso (Spec.map e.toCommRingCatIso.inv))
  have hcomp : Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
      polynomialPoint R ev i (0 : B) =
      polynomialPoint R (Ideal.Quotient.mk (RingHom.ker ev)) i 0 := by
    rw [SpecMap_polynomialPoint, hq, map_zero]
  rw [coordinateSectionCenter_eq_ker_polynomialPoint, ← hker, ← hcomp,
    Scheme.Hom.ker_comp_of_isIso]

/-- In the chart containing the chosen section, the center has ideal `(X, C f)`. -/
@[simp]
theorem coordinateSectionCenter_comap_polynomialChartι :
    (coordinateSectionCenter f i).comap (polynomialChartι R i) =
      IdealSheafData.ofIdealTop ((J).map (Scheme.ΓSpecIso (.of P)).inv.hom) :=
  (affineCenter f).comap_map_of_isOpenImmersion _

/-- The center is disjoint from the opposite chart. -/
@[simp]
theorem coordinateSectionCenter_comap_polynomialChartι_rev :
    (coordinateSectionCenter f i).comap (polynomialChartι R i.rev) = ⊤ := by
  let a := polynomialChartι R i
  let b := polynomialChartι R i.rev
  apply (IdealSheafData.comap_eq_top_iff _ b).mpr
  apply top_unique
  intro y _
  rw [Scheme.Hom.mem_preimage]
  refine fun hy ↦ ?_
  have hdis := ((affineCenter f).disjoint_support_map_iff a b.opensRange).mpr ?_
  · exact Set.disjoint_left.mp hdis (Scheme.Hom.mem_opensRange.mpr ⟨y, rfl⟩) hy
  · simp only [Set.disjoint_left]
    intro x hx hcenter
    have hx' := (polynomialChartι_mem_range_iff R i x).mp (Scheme.Hom.mem_opensRange.mp hx)
    apply hx'
    let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
    have : IsClosedImmersion q :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have hq : q.ker = affineCenter f := by
      rw [Scheme.Hom.ker_Spec_map, CommRingCat.hom_ofHom, Ideal.mk_ker]
    rw [← hq, Scheme.Hom.support_ker, q.isClosedEmbedding.isClosed_range.closure_eq] at hcenter
    obtain ⟨z, rfl⟩ := hcenter
    -- The prime ideal at a point of a spectrum pulls back under `Spec.map`.
    change Ideal.Quotient.mk J (X : P) ∈ z.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))]
    exact z.asIdeal.zero_mem

local notation "𝓘(" a ")" =>
  IdealSheafData.ofIdealTop
    (Ideal.map (CommRingCat.Hom.hom (Iso.inv (Scheme.ΓSpecIso (CommRingCat.of _))))
      (Ideal.span (singleton a)))
local notation "D(" i ")" => coordinateSectionCenter (0 : R) i

/-- The ideal of the full coordinate section is the kernel of its zero point. -/
theorem ker_coordinateSection (j : Fin 2) :
    (polynomialPoint R (RingHom.id R) j (0 : R)).ker = D(j) := by
  symm
  apply coordinateSectionCenter_eq_ker_polynomialPoint_of_surjective
  · exact Function.surjective_id
  · rw [Ideal.span_singleton_zero]
    exact (RingHom.injective_iff_ker_eq_bot (RingHom.id R)).mp Function.injective_id

/-- The full coordinate section embeds the base as a closed subscheme. -/
theorem isClosedImmersion_coordinateSection (j : Fin 2) :
    IsClosedImmersion (polynomialPoint R (RingHom.id R) j (0 : R)) :=
  (polynomialPoint R (RingHom.id R) j (0 : R)).isClosedImmersion_of_comp_eq_id
    (f := projectiveLine R ↘ Spec (.of R)) (by simp [polynomialPoint_over])

/-- Over a reduced base the full coordinate section is a reduced closed subscheme. -/
theorem isReduced_subscheme_coordinateSectionCenter_zero [IsReduced (Spec (.of R))]
    (j : Fin 2) : IsReduced (D(j)).subscheme := by
  have := isClosedImmersion_coordinateSection (R := R) j
  rw [← ker_coordinateSection (R := R) j]
  exact isReduced_of_isOpenImmersion (inv (polynomialPoint R (RingHom.id R) j (0 : R)).toImage)

/-- The ideal of a coordinate section pulls back to the same coordinate section
under extension of the coefficient ring. -/
theorem comap_coordinateSectionCenter_zero_baseChangeProjection
    (S : Type u) [CommRing S] [Algebra R S] (j : Fin 2) :
    (D(j)).comap (baseChangeProjection R S) = coordinateSectionCenter (0 : S) j := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let s := polynomialPoint R (RingHom.id R) j 0
  let t := polynomialPoint S (RingHom.id S) j 0
  have h₀ : IsPullback (𝟙 _) g g (𝟙 _) := IsPullback.of_id_fst
  have h₁ : t ≫ baseChangeProjection R S = g ≫ s := by
    simp [g, s, t, polynomialPoint_comp_baseChangeProjection, SpecMap_polynomialPoint]
  have h₂ : IsPullback t g (baseChangeProjection R S) s := by
    apply IsPullback.of_right _ h₁ (isPullback_baseChangeProjection R S).flip
    have hid (B : Type u) [CommRing B] :
        Spec.map (CommRingCat.ofHom (RingHom.id B)) = 𝟙 (Spec (.of B)) := by
      exact Scheme.Spec.map_id _
    simpa only [s, t, polynomialPoint_over, hid] using h₀
  have := isClosedImmersion_coordinateSection (R := R) j
  rw [← ker_coordinateSection (R := R) j, ← ker_coordinateSection (R := S) j]
  exact (IdealSheafData.ker_eq_comap_of_isPullback _ h₂).symm

/-- On its own chart, the full coordinate section has ideal `(X)`. -/
theorem coordinateSectionCenter_zero_comap_polynomialChartι :
    (D(i)).comap (polynomialChartι R i) = 𝓘((X : P)) := by
  rw [coordinateSectionCenter_comap_polynomialChartι, map_zero, Ideal.span_pair_zero]

/-- Pulling the full coordinate section back along a point of its chart gives the ideal `(a)`. -/
theorem comap_coordinateSectionCenter_zero_polynomialPoint {S : Type u} [CommRing S]
    (g : R →+* S) (a : S) : (D(i)).comap (polynomialPoint R g i a) = 𝓘(a) := by
  rw [polynomialPoint_def, IdealSheafData.comap_comp,
    coordinateSectionCenter_zero_comap_polynomialChartι,
    IdealSheafData.comap_ofIdealTop_map_ΓSpecIso_inv, Ideal.map_span, Set.image_singleton,
    CommRingCat.hom_ofHom, coe_eval₂RingHom, eval₂_X]

/-- The full coordinate section pulls back to the empty subscheme at an opposite-chart point. -/
theorem comap_coordinateSectionCenter_zero_polynomialPoint_rev {S : Type u}
    [CommRing S] (g : R →+* S) (a : S) :
    (D(i)).comap (polynomialPoint R g i.rev a) = ⊤ := by
  rw [polynomialPoint_def, IdealSheafData.comap_comp,
    coordinateSectionCenter_comap_polynomialChartι_rev, IdealSheafData.comap_top]

/-- At a point of chart `i`, the section indexed by `i.rev` pulls back to the empty subscheme. -/
theorem comap_coordinateSectionCenter_zero_rev_polynomialPoint {S : Type u}
    [CommRing S] (g : R →+* S) (a : S) :
    (D(i.rev)).comap (polynomialPoint R g i a) = ⊤ := by
  simpa only [Fin.rev_rev] using
    comap_coordinateSectionCenter_zero_polynomialPoint_rev i.rev g a

private theorem isEffectiveCartier_polynomialVariable : (𝓘((X : P))).IsEffectiveCartier := by
  rw [← Polynomial.zeroIdealSheaf_eq_ofIdealTop]
  exact (Polynomial.monic_X (R := R)).isRelativeEffectiveCartier_zeroIdealSheaf.isEffectiveCartier

/-- The section of the projective line over the whole base is an effective Cartier divisor. -/
theorem isEffectiveCartier_coordinateSectionCenter_zero : (D(i)).IsEffectiveCartier := by
  apply (D(i)).isEffectiveCartier_of_forall_exists_isOpenImmersion
  intro x
  obtain ⟨j, y, rfl⟩ := exists_eq_awayι R x
  have hy : awayι R j y ∈ Set.range (polynomialChartι R j) := by
    rw [← Scheme.Hom.coe_opensRange, opensRange_polynomialChartι,
      ← Proj.opensRange_awayι, Scheme.Hom.coe_opensRange]
    exact Set.mem_range_self y
  refine ⟨_, polynomialChartι R j, inferInstance, hy, ?_⟩
  rcases Fin.fin_two_eq_or_eq_rev i j with rfl | rfl
  · rw [coordinateSectionCenter_zero_comap_polynomialChartι]
    exact isEffectiveCartier_polynomialVariable (R := R)
  · rw [coordinateSectionCenter_comap_polynomialChartι_rev]
    exact IdealSheafData.isEffectiveCartier_top _

local notation "Z" => coordinateSectionCenter f i

private def reesBlowupι : Proj (reesAlgebra.grade J) ⟶ (Z).blowup :=
  ((Z).exists_isPullback_toSpecCoeff_reesAlgebra (polynomialChartι R i) J
    (coordinateSectionCenter_comap_polynomialChartι f i)).choose

private theorem isPullback_reesBlowupι :
    IsPullback (reesBlowupι f i) (Proj.toSpecCoeff (reesAlgebra.grade J))
      (Z).blowupToBase (polynomialChartι R i) :=
  ((Z).exists_isPullback_toSpecCoeff_reesAlgebra (polynomialChartι R i) J
    (coordinateSectionCenter_comap_polynomialChartι f i)).choose_spec

private instance : IsOpenImmersion (reesBlowupι f i) :=
  MorphismProperty.of_isPullback (isPullback_reesBlowupι f i).flip inferInstance

private theorem opensRange_reesBlowupι :
    (reesBlowupι f i).opensRange = (Z).blowupToBase ⁻¹ᵁ (polynomialChartι R i).opensRange := by
  let h := isPullback_reesBlowupι f i
  rw [← Scheme.Hom.opensRange_pullbackFst]
  refine Eq.trans ?_ (Scheme.Hom.opensRange_comp_of_isIso h.isoPullback.hom _)
  apply SetLike.coe_injective
  simp only [Scheme.Hom.coe_opensRange, h.isoPullback_hom_fst]

private instance : IsIso (((Z).comap (polynomialChartι R i.rev)).blowupToBase) :=
  (Scheme.IdealSheafData.isIso_blowupToBase_iff _).mpr (by
    rw [coordinateSectionCenter_comap_polynomialChartι_rev]
    exact Scheme.IdealSheafData.isEffectiveCartier_top _)

/-- The unchanged opposite polynomial chart in the blowup along the chosen section. -/
def sectionBlowupOppositeChartι : A ⟶ (Z).blowup :=
  inv (((Z).comap (polynomialChartι R i.rev)).blowupToBase) ≫
    (Z).blowupMap (polynomialChartι R i.rev)

/-- Projection of the unchanged chart is the opposite polynomial chart of the projective line. -/
@[reassoc]
theorem sectionBlowupOppositeChartι_blowupToBase :
    sectionBlowupOppositeChartι f i ≫ (Z).blowupToBase = polynomialChartι R i.rev := by
  rw [sectionBlowupOppositeChartι, Category.assoc, Scheme.IdealSheafData.blowupMap_blowupToBase,
    IsIso.inv_hom_id_assoc]

/-- The node chart of the section blowup. Coordinate `i` of the node `xy = f`
is the coordinate of the original affine chart. -/
def sectionBlowupNodeChartι (hf : IsSMulRegular R f) : Node ⟶ (Z).blowup :=
  elementaryTransformNodeChart f hf i ≫ reesBlowupι f i

/-- Projection of the node chart uses coordinate `i` of the node. -/
@[reassoc]
theorem sectionBlowupNodeChartι_blowupToBase (hf : IsSMulRegular R f) :
    sectionBlowupNodeChartι f i hf ≫ (Z).blowupToBase =
      polynomialPoint R (algebraMap R N) i (TauCeti.NodeAlgebra.coord f i) := by
  rw [sectionBlowupNodeChartι, Category.assoc, (isPullback_reesBlowupι f i).w, ← Category.assoc,
    elementaryTransformNodeChart_toSpec, polynomialPoint_def]
  rfl

/-- The chart of the base equation `f` in the section blowup, with polynomial coordinate `X/f`. -/
def sectionBlowupDivisorChartι (hf : IsSMulRegular R f) : A ⟶ (Z).blowup :=
  elementaryTransformOuterChart f hf ≫ reesBlowupι f i

/-- Projection of the divisor chart sends the original section coordinate to `f * X`. -/
@[reassoc]
theorem sectionBlowupDivisorChartι_blowupToBase (hf : IsSMulRegular R f) :
    sectionBlowupDivisorChartι f i hf ≫ (Z).blowupToBase =
      polynomialPoint R C i (C f * X) := by
  rw [sectionBlowupDivisorChartι, Category.assoc, (isPullback_reesBlowupι f i).w,
    ← Category.assoc, elementaryTransformOuterChart_toSpec, polynomialPoint_def]
  rfl

instance isOpenImmersion_sectionBlowupNodeChartι (hf : IsSMulRegular R f) :
    IsOpenImmersion (sectionBlowupNodeChartι f i hf) := by
  unfold sectionBlowupNodeChartι
  infer_instance

instance isOpenImmersion_sectionBlowupDivisorChartι (hf : IsSMulRegular R f) :
    IsOpenImmersion (sectionBlowupDivisorChartι f i hf) := by
  unfold sectionBlowupDivisorChartι
  infer_instance

instance isOpenImmersion_sectionBlowupOppositeChartι :
    IsOpenImmersion (sectionBlowupOppositeChartι f i) := by
  unfold sectionBlowupOppositeChartι
  infer_instance

/-- The image of the unchanged chart is the preimage of the opposite base chart. -/
theorem opensRange_sectionBlowupOppositeChartι :
    (sectionBlowupOppositeChartι f i).opensRange =
      (Z).blowupToBase ⁻¹ᵁ (polynomialChartι R i.rev).opensRange :=
  (Scheme.Hom.opensRange_comp_of_isIso _ _).trans ((Z).opensRange_blowupMap _)

private theorem opensRange_node_sup_divisor (hf : IsSMulRegular R f) :
    (sectionBlowupNodeChartι f i hf).opensRange ⊔ (sectionBlowupDivisorChartι f i hf).opensRange =
      (reesBlowupι f i).opensRange := by
  let g := reesBlowupι f i
  -- Expose the compositions to use the open-immersion instances of both Rees charts.
  change (elementaryTransformNodeChart f hf i ≫ g).opensRange ⊔
    (elementaryTransformOuterChart f hf ≫ g).opensRange = g.opensRange
  rw [Scheme.Hom.opensRange_comp, Scheme.Hom.opensRange_comp]
  have h := congrArg (g ''ᵁ ·) (sup_opensRange_elementaryTransformCharts f hf i)
  apply SetLike.coe_injective
  simpa only [TopologicalSpace.Opens.coe_sup, Scheme.Hom.coe_image, Set.image_union,
    Scheme.Hom.image_top_eq_opensRange] using congrArg SetLike.coe h

/-- The node, divisor, and opposite charts cover the section blowup. -/
theorem opensRange_sectionBlowupCharts_sup_eq_top (hf : IsSMulRegular R f) :
    (sectionBlowupNodeChartι f i hf).opensRange ⊔ (sectionBlowupDivisorChartι f i hf).opensRange ⊔
      (sectionBlowupOppositeChartι f i).opensRange = ⊤ := by
  have h : (polynomialChartι R i).opensRange ⊔ (polynomialChartι R i.rev).opensRange = ⊤ := by
    simp_rw [opensRange_polynomialChartι]
    fin_cases i
    · exact basicOpen_coord_sup_eq_top R
    · rw [sup_comm]
      exact basicOpen_coord_sup_eq_top R
  rw [opensRange_node_sup_divisor, opensRange_reesBlowupι, opensRange_sectionBlowupOppositeChartι,
    ← Scheme.Hom.preimage_sup, h, Scheme.Hom.preimage_top]

-- Middle chart, divisor chart, and unchanged opposite chart, respectively.
private abbrev chartScheme : Option Bool → Scheme.{u}
  | none => Node
  | some _ => A

private def chartι (hf : IsSMulRegular R f) : (j : Option Bool) → chartScheme f j ⟶ (Z).blowup
  | none => sectionBlowupNodeChartι f i hf
  | some false => sectionBlowupDivisorChartι f i hf
  | some true => sectionBlowupOppositeChartι f i

private instance (hf : IsSMulRegular R f) (j : Option Bool) :
    IsOpenImmersion (chartι f i hf j) := by
  rcases j with _ | (_ | _)
  · exact isOpenImmersion_sectionBlowupNodeChartι f i hf
  · exact isOpenImmersion_sectionBlowupDivisorChartι f i hf
  · exact isOpenImmersion_sectionBlowupOppositeChartι f i

private def sectionBlowupCover (hf : IsSMulRegular R f) : ((Z).blowup).OpenCover where
  I₀ := Option Bool
  X := chartScheme f
  f := chartι f i hf
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    have hx := TopologicalSpace.Opens.mem_sup.mp
      ((opensRange_sectionBlowupCharts_sup_eq_top f i hf).ge (show x ∈ ⊤ from trivial))
    rcases hx with hx | hx
    · rcases TopologicalSpace.Opens.mem_sup.mp hx with hx | hx
      · exact ⟨none, Scheme.Hom.mem_opensRange.mp hx⟩
      · exact ⟨some false, Scheme.Hom.mem_opensRange.mp hx⟩
    · exact ⟨some true, Scheme.Hom.mem_opensRange.mp hx⟩

/-- The three section blowup charts detect equality of ideal sheaves. -/
theorem sectionBlowup_idealSheaf_ext (hf : IsSMulRegular R f)
    {I K : (Z).blowup.IdealSheafData}
    (hn : I.comap (sectionBlowupNodeChartι f i hf) =
      K.comap (sectionBlowupNodeChartι f i hf))
    (hd : I.comap (sectionBlowupDivisorChartι f i hf) =
      K.comap (sectionBlowupDivisorChartι f i hf))
    (ho : I.comap (sectionBlowupOppositeChartι f i) =
      K.comap (sectionBlowupOppositeChartι f i)) : I = K := by
  apply IdealSheafData.ext_of_comap_openCover (sectionBlowupCover f i hf)
  rintro (_ | (_ | _))
  · exact hn
  · exact hd
  · exact ho

/-- An ideal sheaf on the section blowup is effective Cartier if it is effective
Cartier on the node, divisor, and opposite charts. -/
theorem isEffectiveCartier_of_sectionBlowupCharts (hf : IsSMulRegular R f)
    {I : (Z).blowup.IdealSheafData}
    (hn : (I.comap (sectionBlowupNodeChartι f i hf)).IsEffectiveCartier)
    (hd : (I.comap (sectionBlowupDivisorChartι f i hf)).IsEffectiveCartier)
    (ho : (I.comap (sectionBlowupOppositeChartι f i)).IsEffectiveCartier) :
    I.IsEffectiveCartier := by
  apply I.isEffectiveCartier_of_forall_exists_isOpenImmersion
  intro x
  obtain ⟨j, y, rfl⟩ := (sectionBlowupCover f i hf).exists_eq x
  rcases j with _ | (_ | _)
  · exact ⟨_, sectionBlowupNodeChartι f i hf, inferInstance, Set.mem_range_self y, hn⟩
  · exact ⟨_, sectionBlowupDivisorChartι f i hf, inferInstance, Set.mem_range_self y, hd⟩
  · exact ⟨_, sectionBlowupOppositeChartι f i, inferInstance, Set.mem_range_self y, ho⟩

private theorem exceptional_comap_reesBlowupι :
    ((Z).comap (Z).blowupToBase).comap (reesBlowupι f i) =
      affineBlowupExceptionalIdeal P J := by
  rw [← IdealSheafData.comap_comp, (isPullback_reesBlowupι f i).w,
    IdealSheafData.comap_comp, coordinateSectionCenter_comap_polynomialChartι,
    affineBlowupExceptionalIdeal_def, toSpecCoeff_reesAlgebra]

/-- On the node chart of the section blowup, the exceptional ideal is generated by the
original section coordinate. -/
@[simp]
theorem exceptional_comap_sectionBlowupNodeChartι (hf : IsSMulRegular R f) :
    ((Z).comap (Z).blowupToBase).comap (sectionBlowupNodeChartι f i hf) =
      IdealSheafData.ofIdealTop
        ((Ideal.span {TauCeti.NodeAlgebra.coord f i}).map (Scheme.ΓSpecIso (.of N)).inv.hom) := by
  rw [sectionBlowupNodeChartι, IdealSheafData.comap_comp, exceptional_comap_reesBlowupι]
  exact affineBlowupExceptionalIdeal_comap_elementaryTransformNodeChart f hf i

/-- On the divisor chart of the section blowup, the exceptional ideal is generated by the
base equation. -/
@[simp]
theorem exceptional_comap_sectionBlowupDivisorChartι (hf : IsSMulRegular R f) :
    ((Z).comap (Z).blowupToBase).comap (sectionBlowupDivisorChartι f i hf) =
      IdealSheafData.ofIdealTop ((Ideal.span {C f}).map (Scheme.ΓSpecIso (.of P)).inv.hom) := by
  rw [sectionBlowupDivisorChartι, IdealSheafData.comap_comp, exceptional_comap_reesBlowupι]
  exact affineBlowupExceptionalIdeal_comap_elementaryTransformOuterChart f hf

/-- The exceptional divisor is disjoint from the unchanged opposite chart. -/
@[simp]
theorem exceptional_comap_sectionBlowupOppositeChartι :
    ((Z).comap (Z).blowupToBase).comap (sectionBlowupOppositeChartι f i) = ⊤ := by
  rw [← IdealSheafData.comap_comp, sectionBlowupOppositeChartι_blowupToBase,
    coordinateSectionCenter_comap_polynomialChartι_rev]

private def switchedChartι (hf : IsSMulRegular R f) :
    (j : Option Bool) → chartScheme f j ⟶ (Z).blowup
  | none => sectionBlowupNodeChartι f i hf
  | some false => sectionBlowupOppositeChartι f i
  | some true => sectionBlowupDivisorChartι f i hf

private def blowupStructureMap : (Z).blowup ⟶ Spec (.of R) :=
  (Z).blowupToBase ≫ (projectiveLine R ↘ Spec (.of R))

private instance : IsSeparated (blowupStructureMap f i) := by
  unfold blowupStructureMap
  infer_instance

private def chartStructureMap : (j : Option Bool) → chartScheme f j ⟶ Spec (.of R)
  | none => Spec.map (CommRingCat.ofHom (algebraMap R N))
  | some _ => Spec.map (CommRingCat.ofHom (algebraMap R P))

private theorem chartι_over (hf : IsSMulRegular R f) (j : Option Bool) :
    chartι f i hf j ≫ blowupStructureMap f i = chartStructureMap f j := by
  rcases j with _ | (_ | _)
  · exact (sectionBlowupNodeChartι_blowupToBase_assoc _ _ _ _).trans
      (polynomialPoint_over _ _ _ _)
  · exact (sectionBlowupDivisorChartι_blowupToBase_assoc _ _ _ _).trans
      (polynomialPoint_over _ _ _ _)
  · exact (sectionBlowupOppositeChartι_blowupToBase_assoc _ _ _).trans (polynomialChartι_over _ _)

private theorem switchedChartι_over (hf : IsSMulRegular R f) (j : Option Bool) :
    switchedChartι f i hf j ≫ blowupStructureMap f i = chartStructureMap f j := by
  rcases j with _ | (_ | _)
  · exact chartι_over f i hf none
  · exact chartι_over f i hf (some true)
  · exact chartι_over f i hf (some false)

private theorem eq_of_blowupToBase_eq_polynomialPoint {D : Type u} [CommRing D]
    {g h : Spec (.of D) ⟶ (Z).blowup} {c : R →+* D} (a : Dˣ)
    (hg : g ≫ (Z).blowupToBase = polynomialPoint R c i (a : D))
    (hh : h ≫ (Z).blowupToBase = polynomialPoint R c i (a : D)) : g = h := by
  apply (Z).blowup_hom_ext (hg.trans hh.symm)
  rw [hg, polynomialPoint_rev, polynomialPoint_def, IdealSheafData.comap_comp,
    coordinateSectionCenter_comap_polynomialChartι_rev, IdealSheafData.comap_top]
  exact IdealSheafData.isEffectiveCartier_top _

section Generic

variable [IsDomain R]

local notation "F" => FractionRing P
local notation "x" => algebraMap P F (X : P)
local notation "s" => (algebraMap R F f / x)
local notation "c" => algebraMap R F
local notation "T" => Spec (CommRingCat.of F)

private theorem x_ne_zero : (x : F) ≠ 0 := by simp

private theorem s_ne_zero (hf : f ≠ 0) : (s : F) ≠ 0 :=
  div_ne_zero (by simpa using (FaithfulSMul.algebraMap_injective R F).ne hf) (x_ne_zero (R := R))

private theorem mul_s : (x : F) * s = c f := by
  rw [mul_div_cancel₀ _ (x_ne_zero (R := R))]

private theorem mul_inv_s (hf : f ≠ 0) : c f * (s : F)⁻¹ = x := by
  calc
    c f * (s : F)⁻¹ = (x * s) * s⁻¹ := congrArg (· * s⁻¹) (mul_s f).symm
    _ = x := by rw [mul_assoc, mul_inv_cancel₀ (s_ne_zero f hf), mul_one]

-- The common test scheme is the generic point of the polynomial chart. Invert
-- the first projection's node coordinate to identify the node algebra there.
private def nodeGenericHom : N →ₐ[R] F :=
  let L := Localization.Away (X : P)
  let g : L →ₐ[R] F := IsLocalization.Away.liftAlgHom X
    (f := IsScalarTower.toAlgHom R P F) (isUnit_iff_ne_zero.mpr (x_ne_zero (R := R)))
  (g.comp (localizationAwayCoordEquiv f i).toAlgHom).comp
    (IsScalarTower.toAlgHom R N (Localization.Away (TauCeti.NodeAlgebra.coord f i)))

private theorem nodeGenericHom_coord :
    nodeGenericHom f i (TauCeti.NodeAlgebra.coord f i) = x := by
  simp [nodeGenericHom]

private theorem nodeGenericHom_coord_rev :
    nodeGenericHom f i (TauCeti.NodeAlgebra.coord f i.rev) = s := by
  apply mul_left_cancel₀ (x_ne_zero (R := R))
  rw [mul_s, ← nodeGenericHom_coord f i, ← map_mul]
  have h : i.rev = 1 - i := by fin_cases i <;> decide
  rw [h, coord_mul_coord_one_sub, AlgHom.commutes]

private theorem nodeGenericHom_injective (hf : f ≠ 0) :
    Function.Injective (nodeGenericHom f i) := by
  let L := Localization.Away (X : P)
  have hu : IsUnit (IsScalarTower.toAlgHom R P F (X : P)) :=
    isUnit_iff_ne_zero.mpr (x_ne_zero (R := R))
  let g : L →ₐ[R] F := IsLocalization.Away.liftAlgHom X
    (f := IsScalarTower.toAlgHom R P F) hu
  have hg : Function.Injective g := by
    have hX : (X : P) ≠ 0 := Polynomial.X_ne_zero
    refine (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers (X : P))
      g.toRingHom).mpr fun a b ↦ ?_
    simp only [g, IsLocalization.Away.liftAlgHom_toRingHom, IsLocalization.Away.lift_eq]
    rw [(IsLocalization.injective L (powers_le_nonZeroDivisors_of_noZeroDivisors hX)).eq_iff]
    exact (IsFractionRing.injective P F).eq_iff.symm
  exact hg.comp ((localizationAwayCoordEquiv f i).injective.comp
    (IsLocalization.injective _
      (Submonoid.powers_le.mpr (TauCeti.NodeAlgebra.coord_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero hf) i))))

private def genericChart : (j : Option Bool) → T ⟶ chartScheme f j
  | none => Specₐ (nodeGenericHom f i)
  | some false => Spec.map (CommRingCat.ofHom (eval₂RingHom c s⁻¹))
  | some true => Spec.map (CommRingCat.ofHom (eval₂RingHom c x⁻¹))

private theorem genericChart_isDominant (hf : f ≠ 0) (j : Option Bool) :
    IsDominant (genericChart f i j) := by
  have hx : Transcendental R (x : F) :=
    (transcendental_algebraMap_iff (IsFractionRing.injective P F)).mpr
      (Polynomial.transcendental_X R)
  have hs : Transcendental R (s : F) := fun h ↦ hx (by
    simpa only [Algebra.smul_def, mul_inv_s f hf] using h.inv.smul f)
  have h (a : F) (ha : Transcendental R a) :
      IsDominant (Spec.map (CommRingCat.ofHom (eval₂RingHom c a))) := by
    have : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom (eval₂RingHom c a))) :=
      (isSchemeTheoreticallyDominant_SpecMap_iff _).mpr
        ((transcendental_iff_injective.mp ha) : Function.Injective (aeval a : P →ₐ[R] F))
    infer_instance
  rcases j with _ | (_ | _)
  · have : IsSchemeTheoreticallyDominant (genericChart f i none) :=
      (isSchemeTheoreticallyDominant_SpecMap_iff _).mpr (nodeGenericHom_injective f i hf)
    infer_instance
  · exact h _ fun ha ↦ hs (IsAlgebraic.inv_iff.mp ha)
  · exact h _ fun ha ↦ hx (IsAlgebraic.inv_iff.mp ha)

private theorem genericChart_comp_chartι_blowupToBase (hf : f ≠ 0) (j : Option Bool) :
    genericChart f i j ≫ chartι f i (IsRegular.of_ne_zero hf).left.isSMulRegular j ≫
      (Z).blowupToBase = polynomialPoint R c i x := by
  rcases j with _ | (_ | _)
  · dsimp only [chartι, genericChart]
    rw [sectionBlowupNodeChartι_blowupToBase, SpecMap_polynomialPoint]
    exact congrArg₂ (fun k a ↦ polynomialPoint R k i a)
      (RingHom.ext (nodeGenericHom f i).commutes) (nodeGenericHom_coord f i)
  · dsimp only [chartι, genericChart]
    rw [sectionBlowupDivisorChartι_blowupToBase, SpecMap_polynomialPoint]
    simp only [coe_eval₂RingHom, eval₂_C, eval₂_mul, eval₂_X, mul_inv_s f hf]
    congr 1
    ext r
    simp
  · dsimp only [chartι, genericChart]
    rw [sectionBlowupOppositeChartι_blowupToBase, ← polynomialPoint_X R i.rev,
      SpecMap_polynomialPoint]
    simpa using (polynomialPoint_rev c i (Units.mk0 x (x_ne_zero (R := R)))).symm

private theorem genericChart_comp_switchedChartι_blowupToBase (hf : f ≠ 0) (j : Option Bool) :
    genericChart f i j ≫ switchedChartι f i.rev (IsRegular.of_ne_zero hf).left.isSMulRegular j ≫
      (coordinateSectionCenter f i.rev).blowupToBase = polynomialPoint R c i.rev s := by
  rcases j with _ | (_ | _)
  · dsimp only [switchedChartι, genericChart]
    rw [sectionBlowupNodeChartι_blowupToBase, SpecMap_polynomialPoint]
    exact congrArg₂ (fun k a ↦ polynomialPoint R k i.rev a)
      (RingHom.ext (nodeGenericHom f i).commutes) (nodeGenericHom_coord_rev f i)
  · dsimp only [switchedChartι, genericChart]
    rw [sectionBlowupOppositeChartι_blowupToBase, Fin.rev_rev, ← polynomialPoint_X R i,
      SpecMap_polynomialPoint]
    simpa using (polynomialPoint_rev c i.rev (Units.mk0 s (s_ne_zero f hf))).symm
  · dsimp only [switchedChartι, genericChart]
    rw [sectionBlowupDivisorChartι_blowupToBase, SpecMap_polynomialPoint]
    simp [div_eq_mul_inv]

private instance isReduced_chartScheme (j : Option Bool) : IsReduced (chartScheme f j) := by
  rcases j with _ | _ <;> dsimp only [chartScheme] <;> infer_instance

private theorem isReduced_sectionBlowup (h : IsSMulRegular R f) : IsReduced (Z).blowup := by
  have : ∀ a, IsReduced ((sectionBlowupCover f i h).X a) := isReduced_chartScheme f
  exact IsReduced.of_openCover _ (sectionBlowupCover f i h)

private theorem genericChart_comp_chartι (hf : f ≠ 0) (a : Option Bool) :
    let h := (IsRegular.of_ne_zero hf).left.isSMulRegular
    genericChart f i a ≫ chartι f i h a = genericChart f i none ≫ chartι f i h none := by
  apply eq_of_blowupToBase_eq_polynomialPoint f i (Units.mk0 x (x_ne_zero (R := R)))
  · exact (Category.assoc _ _ _).trans (genericChart_comp_chartι_blowupToBase f i hf a)
  · exact (Category.assoc _ _ _).trans (genericChart_comp_chartι_blowupToBase f i hf none)

private theorem genericChart_comp_chartι_isDominant (hf : f ≠ 0) :
    IsDominant (genericChart f i none ≫ chartι f i (IsRegular.of_ne_zero hf).left.isSMulRegular
      none) := by
  let h := (IsRegular.of_ne_zero hf).left.isSMulRegular
  constructor
  intro p
  obtain ⟨a, q, rfl⟩ := (sectionBlowupCover f i h).exists_eq p
  rw [← genericChart_comp_chartι f i hf a]
  have := genericChart_isDominant f i hf a
  change chartι f i h a q ∈ closure (Set.range (genericChart f i a ≫ chartι f i h a))
  simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp] using
    (chartι f i h a).continuous.range_subset_closure_image_dense
      (genericChart f i a).denseRange ⟨q, rfl⟩

private def elementaryTransformHom (hf : f ≠ 0) (j : Fin 2) (hj : j = i.rev) :
    (Z).blowup ⟶ (coordinateSectionCenter f j).blowup := by
  subst j
  let h := (IsRegular.of_ne_zero hf).left.isSMulRegular
  have := isReduced_sectionBlowup f i h
  have := genericChart_comp_chartι_isDominant f i hf
  refine (sectionBlowupCover f i h).glueMorphismsOfDominant
    (genericChart f i none ≫ chartι f i h none) (genericChart f i)
    (genericChart_comp_chartι f i hf)
    (switchedChartι f i.rev h) (genericChart f i none ≫ switchedChartι f i.rev h none) ?_
    (blowupStructureMap f i.rev) (blowupStructureMap f i) ?_
  · intro a
    apply eq_of_blowupToBase_eq_polynomialPoint f i.rev (Units.mk0 s (s_ne_zero f hf))
    · exact Category.assoc _ _ _ |>.trans (genericChart_comp_switchedChartι_blowupToBase f i hf a)
    · exact (Category.assoc _ _ _).trans
        (genericChart_comp_switchedChartι_blowupToBase f i hf none)
  · intro a
    exact (switchedChartι_over f i.rev h a).trans (chartι_over f i h a).symm

private theorem chartι_elementaryTransformHom (hf : f ≠ 0) (j : Fin 2)
    (hj : j = i.rev) (a : Option Bool) :
    let h := (IsRegular.of_ne_zero hf).left.isSMulRegular
    chartι f i h a ≫ elementaryTransformHom f i hf j hj = switchedChartι f j h a := by
  subst j
  let h := (IsRegular.of_ne_zero hf).left.isSMulRegular
  have := isReduced_sectionBlowup f i h
  have := genericChart_comp_chartι_isDominant f i hf
  unfold elementaryTransformHom
  apply Scheme.Cover.ι_glueMorphismsOfDominant

private theorem elementaryTransformHom_comp (hf : f ≠ 0) (j : Fin 2)
    (hj : j = i.rev) (hi : i = j.rev) :
    elementaryTransformHom f i hf j hj ≫ elementaryTransformHom f j hf i hi = 𝟙 _ := by
  let h := (IsRegular.of_ne_zero hf).left.isSMulRegular
  apply (sectionBlowupCover f i h).hom_ext
  intro a
  -- Unfold the cover projections to apply the chart equations.
  change Option Bool at a
  change chartι f i h a ≫ _ = chartι f i h a ≫ _
  have h₁ := chartι_elementaryTransformHom f i hf j hj a
  rw [← Category.assoc, h₁, Category.comp_id]
  rcases a with _ | (_ | _)
  · exact chartι_elementaryTransformHom f j hf i hi none
  · exact chartι_elementaryTransformHom f j hf i hi (some true)
  · exact chartι_elementaryTransformHom f j hf i hi (some false)

/-- The opposite-section blowups above `V(f)` are isomorphic over `Spec R`.
Away from `V(f)`, the source affine coordinate `x` gives the target affine coordinate
`x/f` in the chart of the same index. -/
def elementaryTransform (hf : f ≠ 0) :
    (coordinateSectionCenter f i).blowup ≅ (coordinateSectionCenter f i.rev).blowup where
  hom := elementaryTransformHom f i hf i.rev rfl
  inv := elementaryTransformHom f i.rev hf i (Fin.rev_rev i).symm
  hom_inv_id := elementaryTransformHom_comp f i hf i.rev rfl (Fin.rev_rev i).symm
  inv_hom_id := elementaryTransformHom_comp f i.rev hf i (Fin.rev_rev i).symm rfl

/-- The common node chart identifies the section coordinates of the two blowups
with the two factors of `xy = f`. -/
@[reassoc]
theorem sectionBlowupNodeChartι_elementaryTransform_hom (hf : f ≠ 0) :
    sectionBlowupNodeChartι f i (IsRegular.of_ne_zero hf).left.isSMulRegular ≫
      (elementaryTransform f i hf).hom =
        sectionBlowupNodeChartι f i.rev (IsRegular.of_ne_zero hf).left.isSMulRegular :=
  chartι_elementaryTransformHom f i hf i.rev rfl none

/-- The polynomial chart with coordinate `x/f` becomes the unchanged target chart. -/
@[reassoc]
theorem sectionBlowupDivisorChartι_elementaryTransform_hom (hf : f ≠ 0) :
    sectionBlowupDivisorChartι f i (IsRegular.of_ne_zero hf).left.isSMulRegular ≫
        (elementaryTransform f i hf).hom = sectionBlowupOppositeChartι f i.rev :=
  chartι_elementaryTransformHom f i hf i.rev rfl (some false)

/-- The unchanged source chart becomes the target chart of the base equation. -/
@[reassoc]
theorem sectionBlowupOppositeChartι_elementaryTransform_hom (hf : f ≠ 0) :
    sectionBlowupOppositeChartι f i ≫ (elementaryTransform f i hf).hom =
      sectionBlowupDivisorChartι f i.rev (IsRegular.of_ne_zero hf).left.isSMulRegular :=
  chartι_elementaryTransformHom f i hf i.rev rfl (some true)

/-- The elementary transformation is over the original coefficient ring. -/
@[reassoc (attr := simp)]
theorem elementaryTransform_hom_over (hf : f ≠ 0) :
    (elementaryTransform f i hf).hom ≫ (coordinateSectionCenter f i.rev).blowupToBase ≫
        (projectiveLine R ↘ Spec (.of R)) =
      (coordinateSectionCenter f i).blowupToBase ≫ (projectiveLine R ↘ Spec (.of R)) := by
  let h := (IsRegular.of_ne_zero hf).left.isSMulRegular
  apply (sectionBlowupCover f i h).hom_ext
  intro j
  -- The structure maps of corresponding affine charts agree over the coefficient ring.
  change chartι f i h j ≫ (elementaryTransform f i hf).hom ≫ blowupStructureMap f i.rev =
    chartι f i h j ≫ blowupStructureMap f i
  rw [← Category.assoc]
  have hj := chartι_elementaryTransformHom f i hf i.rev rfl j
  exact (congrArg (· ≫ blowupStructureMap f i.rev) hj).trans
    ((switchedChartι_over f i.rev h j).trans (chartι_over f i h j).symm)

/-- On the opposite affine chart the elementary transformation multiplies the affine
coordinate by the base equation, with the same chart index on both projective lines. -/
theorem elementaryTransform_hom_blowupToBase_eq_polynomialPoint
    (hf : f ≠ 0) {D : Type u} [CommRing D] {k : R →+* D} {a : D}
    {g : Spec (.of D) ⟶ (coordinateSectionCenter f i).blowup}
    (hg : g ≫ (coordinateSectionCenter f i).blowupToBase = polynomialPoint R k i.rev a) :
    g ≫ (elementaryTransform f i hf).hom ≫
        (coordinateSectionCenter f i.rev).blowupToBase =
      polynomialPoint R k i.rev (k f * a) := by
  let h := Spec.map (CommRingCat.ofHom (eval₂RingHom k a))
  have hproj : h ≫ sectionBlowupOppositeChartι f i ≫ (Z).blowupToBase =
      polynomialPoint R k i.rev a := by
    rw [sectionBlowupOppositeChartι_blowupToBase, polynomialPoint_def]
  have hcomp : g = h ≫ sectionBlowupOppositeChartι f i := by
    apply (Z).blowup_hom_ext (hg.trans (by simpa only [Category.assoc] using hproj.symm))
    rw [hg, polynomialPoint_def, IdealSheafData.comap_comp,
      coordinateSectionCenter_comap_polynomialChartι_rev, IdealSheafData.comap_top]
    exact IdealSheafData.isEffectiveCartier_top _
  rw [hcomp, Category.assoc, sectionBlowupOppositeChartι_elementaryTransform_hom_assoc,
    sectionBlowupDivisorChartι_blowupToBase, SpecMap_polynomialPoint]
  simp

/-- Above a zero of `f`, the divisor chart maps to the center on the source and retains
its entire affine coordinate on the target of the elementary transformation. -/
theorem exists_elementaryTransform_lift_of_map_eq_zero (hf : f ≠ 0)
    {D : Type u} [CommRing D] (k : R →+* D) (hk : k f = 0) (a : D) :
    ∃ g : Spec (.of D) ⟶ (coordinateSectionCenter f i).blowup,
      g ≫ (coordinateSectionCenter f i).blowupToBase = polynomialPoint R k i 0 ∧
      g ≫ (elementaryTransform f i hf).hom ≫
        (coordinateSectionCenter f i.rev).blowupToBase = polynomialPoint R k i a := by
  let e := Spec.map (CommRingCat.ofHom (eval₂RingHom k a))
  refine ⟨e ≫ sectionBlowupDivisorChartι f i (IsRegular.of_ne_zero hf).left.isSMulRegular, ?_, ?_⟩
  · rw [Category.assoc, sectionBlowupDivisorChartι_blowupToBase,
      SpecMap_polynomialPoint]
    simp [hk]
  · rw [Category.assoc, sectionBlowupDivisorChartι_elementaryTransform_hom_assoc,
      sectionBlowupOppositeChartι_blowupToBase, Fin.rev_rev]
    exact (polynomialPoint_def R k i a).symm

end Generic

end TauCeti.AlgebraicGeometry.projectiveLine
