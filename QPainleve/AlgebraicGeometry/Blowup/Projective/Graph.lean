/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Projective.Coordinates
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.BaseChange
public import TauCeti.AlgebraicGeometry.Blowup.IdealSheaf
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.SchematicDensity
import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
import TauCeti.AlgebraicGeometry.Pullback.Carrier
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap
import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Segre

/-!
# Gluing projective presentations of blowups

Indexed affine Rees presentations that agree on the complement of the exceptional
divisor glue to a closed immersion into the product of the base with projective space.
The relevant density is scheme-theoretic, so this comparison works over nonreduced bases.

## References

* [The Stacks Project, Section 31.33](https://stacks.math.columbia.edu/tag/01OF).
* Tau Ceti's schematic density of the complement of an effective Cartier divisor
  and its Segre closed immersion.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open TauCeti

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}} (I : X.IdealSheafData)
  {R : Type u} [CommRing R] (f : X ⟶ Spec (.of R))
  {ι : Type u}

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "ℙ" => Proj (MvPolynomial.homogeneousSubmodule ι R)
local notation "q" => Proj.toSpecCoeff (MvPolynomial.homogeneousSubmodule ι R)

variable {V : X.Opens} (hV : IsAffineOpen V)
  (a : ι → I.ideal ⟨V, hV⟩)
  (ha : Ideal.span (Set.range fun j ↦ (a j : Γ(X, V))) = I.ideal ⟨V, hV⟩)

@[instance_reducible] private def chartAlgebra : Algebra R Γ(X, V) :=
  (Spec.preimage (hV.fromSpec ≫ f)).hom.toAlgebra

/-- An indexed set of generators on an affine open gives a map of the corresponding
Rees projective spectrum to projective space over the coefficient base. -/
def blowupChartToProjectiveSpace :
    Proj (reesAlgebra.grade (I.ideal ⟨V, hV⟩)) ⟶ ℙ :=
  letI := chartAlgebra f hV
  reesAlgebra.coordinateEmbedding a ha ≫ Proj.polynomialBaseChangeProjection ι

/-- The coefficient map of the chart presentation is the structure map of the blowup. -/
@[reassoc (attr := simp)]
theorem blowupChartToProjectiveSpace_toSpecCoeff :
    I.blowupChartToProjectiveSpace f hV a ha ≫ q = I.blowupChart hV ≫ I.blowupToBase ≫ f := by
  let := chartAlgebra f hV
  have hf : Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, V))) = hV.fromSpec ≫ f := by
    exact Spec.map_preimage _
  rw [blowupChartToProjectiveSpace, Category.assoc,
    Proj.polynomialBaseChangeProjection_toSpecCoeff, hf,
    reesAlgebra.coordinateEmbedding_toSpecCoeff_assoc, blowupChart_blowupToBase_assoc]

/-- Outside the center the affine chart map is evaluation on the chosen generators,
read over the original coefficient ring. -/
theorem comp_blowupChartToProjectiveSpace_eq_fromOfGlobalSections
    {T : Scheme.{u}} (b : Γ(X, V) →+* Γ(T, ⊤))
    (hb : (I.ideal ⟨V, hV⟩).map b = ⊤)
    (t : T ⟶ Proj (reesAlgebra.grade (I.ideal ⟨V, hV⟩)))
    (ht : t ≫ Proj.toSpecCoeff (reesAlgebra.grade (I.ideal ⟨V, hV⟩)) =
      T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom b)) :
    let p := MvPolynomial.eval₂Hom (b.comp (Spec.preimage (hV.fromSpec ≫ f)).hom)
      (fun i ↦ b (a i))
    ∃ hp : (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule ι R)).toIdeal.map
      p = ⊤, t ≫ I.blowupChartToProjectiveSpace f hV a ha =
        Proj.fromOfGlobalSections (MvPolynomial.homogeneousSubmodule ι R) p hp := by
  let := chartAlgebra f hV
  obtain ⟨_, he⟩ := reesAlgebra.comp_coordinateEmbedding_eq_fromOfGlobalSections a b ha hb t ht
  rw [blowupChartToProjectiveSpace, ← Category.assoc, he]
  exact Proj.fromOfGlobalSections_polynomialBaseChangeProjection ι b _ _

private def projectiveChartToProduct :
    Proj (MvPolynomial.homogeneousSubmodule ι Γ(X, V)) ⟶ pullback f q :=
  letI := chartAlgebra f hV
  pullback.lift (Proj.toSpecCoeff _ ≫ hV.fromSpec)
    (Proj.polynomialBaseChangeProjection ι) (by
      rw [Category.assoc, Proj.polynomialBaseChangeProjection_toSpecCoeff]
      congr 1
      exact (Spec.map_preimage _).symm)

private theorem isPullback_projectiveChartToProduct :
    IsPullback (projectiveChartToProduct (ι := ι) f hV)
      (Proj.toSpecCoeff (MvPolynomial.homogeneousSubmodule ι Γ(X, V))) (pullback.fst f q)
      hV.fromSpec := by
  let := chartAlgebra f hV
  have h := (Proj.isPullback_polynomialBaseChangeProjection
    (R := R) (S := Γ(X, V)) ι)
  have hf : Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, V))) = hV.fromSpec ≫ f :=
    Spec.map_preimage _
  have hp := IsPullback.of_right' (hf ▸ h) (IsPullback.of_hasPullback f q).flip
  convert hp using 1
  apply pullback.hom_ext
  · simp [projectiveChartToProduct]
  · simp [projectiveChartToProduct]

private theorem isPullback_coordinateEmbedding {m : I.blowup ⟶ ℙ}
    (hm : m ≫ q = I.blowupToBase ≫ f)
    (hchart : I.blowupChart hV ≫ m = I.blowupChartToProjectiveSpace f hV a ha) :
    IsPullback (reesAlgebra.coordinateEmbedding a ha) (I.blowupChart hV)
      (projectiveChartToProduct f hV) (pullback.lift I.blowupToBase m hm.symm) := by
  have hp := isPullback_projectiveChartToProduct (ι := ι) f hV
  have h := I.isPullback_blowupChart_fromSpec hV
  refine IsPullback.of_right (by simpa using h) ?_ hp.flip
  apply pullback.hom_ext
  · simpa [projectiveChartToProduct] using h.w
  · simpa [projectiveChartToProduct, blowupChartToProjectiveSpace] using hchart.symm

variable {τ : Type*} (U : τ → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
  (hcover : ⨆ i, U i = ⊤)

private def blowupProjectiveCover : I.blowup.OpenCover :=
  Scheme.Cover.mkOfCovers τ
    (fun i ↦ Proj (reesAlgebra.grade (I.ideal ⟨U i, hU i⟩)))
    (fun i ↦ I.blowupChart (hU i)) (by
      intro x
      obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover ▸ Opens.mem_top (I.blowupToBase x))
      exact ⟨i, by simpa [← Scheme.Hom.mem_opensRange, I.opensRange_blowupChart] using hi⟩)
    (fun _ ↦ inferInstance)

private def projectiveProductCover : (pullback f q).OpenCover :=
  Scheme.Cover.mkOfCovers τ
    (fun i ↦ Proj (MvPolynomial.homogeneousSubmodule ι Γ(X, U i)))
    (fun i ↦ projectiveChartToProduct f (hU i)) (by
      intro x
      obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover ▸ Opens.mem_top (pullback.fst f q x))
      refine ⟨i, ?_⟩
      -- Express the covering condition as membership in the range of the chart.
      change x ∈ Set.range (projectiveChartToProduct f (hU i))
      rw [Scheme.Pullback.range_fst_of_isPullback
        (isPullback_projectiveChartToProduct (ι := ι) f (hU i)), (hU i).range_fromSpec]
      exact hi)
    (fun i ↦ MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (isPullback_projectiveChartToProduct (ι := ι) f (hU i)).flip inferInstance)

variable (aU : ∀ i, ι → I.ideal ⟨U i, hU i⟩)
  (haU : ∀ i, Ideal.span (Set.range fun j ↦ (aU i j : Γ(X, U i))) = I.ideal ⟨U i, hU i⟩)

include hcover in
/-- If on an affine cover a morphism is given by the indexed Rees presentations of the
blowup, its graph over the original scheme is a closed immersion. -/
theorem isClosedImmersion_blowup_graph {m : I.blowup ⟶ ℙ}
    (hm : m ≫ q = I.blowupToBase ≫ f)
    (hchart : ∀ i, I.blowupChart (hU i) ≫ m =
      I.blowupChartToProjectiveSpace f (hU i) (aU i) (haU i)) :
    IsClosedImmersion (pullback.lift I.blowupToBase m hm.symm) := by
  let 𝒰 := projectiveProductCover (ι := ι) f U hU hcover
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) 𝒰
  intro i
  let hp := I.isPullback_coordinateEmbedding f (hU i) (aU i) (haU i) hm (hchart i)
  -- The cover pullback map is the second projection of this cartesian square.
  change IsClosedImmersion (pullback.snd (pullback.lift I.blowupToBase m hm.symm)
    (projectiveChartToProduct f (hU i)))
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion hp.flip.isoPullback.hom,
    hp.flip.isoPullback_hom_snd]
  infer_instance

/-- Two maps to projective space over the base agree on their entire chart overlap
if they agree on the complement of the exceptional divisor there. -/
theorem eq_on_blowupChart_overlap {V W : X.Opens} (hV : IsAffineOpen V)
    (hW : IsAffineOpen W)
    {m : Proj (reesAlgebra.grade (I.ideal ⟨V, hV⟩)) ⟶ ℙ}
    {n : Proj (reesAlgebra.grade (I.ideal ⟨W, hW⟩)) ⟶ ℙ}
    (hm : m ≫ q = I.blowupChart hV ≫ I.blowupToBase ≫ f)
    (hn : n ≫ q = I.blowupChart hW ≫ I.blowupToBase ≫ f)
    (h : let c := I.blowupChart hV
         let d := I.blowupChart hW
         let k := pullback.fst c d ≫ c
         let e := Scheme.Opens.ι (I.comap I.blowupToBase).support.compl
         pullback.snd e k ≫ pullback.fst c d ≫ m =
           pullback.snd e k ≫ pullback.snd c d ≫ n) :
    pullback.fst (I.blowupChart hV) (I.blowupChart hW) ≫ m =
      pullback.snd (I.blowupChart hV) (I.blowupChart hW) ≫ n := by
  let c := I.blowupChart hV
  let d := I.blowupChart hW
  let V₀ : I.blowup.Opens := (I.comap I.blowupToBase).support.compl
  let e := V₀.ι
  let k := pullback.fst c d ≫ c
  have : IsOpenImmersion k := inferInstanceAs (IsOpenImmersion (pullback.fst c d ≫ c))
  have : IsSchemeTheoreticallyDominant (pullback.snd e k) := by
    have hd := (I.isEffectiveCartier_comap_blowupToBase.comap k)
      |>.isSchemeTheoreticallyDominant_support_compl_ι
    rw [compl_support_comap] at hd
    have : IsSchemeTheoreticallyDominant (k ⁻¹ᵁ V₀).ι := hd
    rw [← (isPullback_morphismRestrict k V₀).isoPullback_inv_snd]
    infer_instance
  apply TauCeti.ext_of_isSchemeTheoreticallyDominant (pullback.snd e k) q
  · simpa only [Category.assoc, hm, hn] using
      (reassoc_of% (pullback.condition (f := c) (g := d))) (I.blowupToBase ≫ f)
  · simpa only [Category.assoc] using h

include hcover in
/-- Compatible indexed Rees presentations glue to a morphism whose graph over the base
is a closed immersion. -/
theorem exists_blowupToProjectiveSpace_of_compatible
    (h : ∀ i j, pullback.fst (I.blowupChart (hU i)) (I.blowupChart (hU j)) ≫
      I.blowupChartToProjectiveSpace f (hU i) (aU i) (haU i) =
      pullback.snd (I.blowupChart (hU i)) (I.blowupChart (hU j)) ≫
      I.blowupChartToProjectiveSpace f (hU j) (aU j) (haU j)) :
    ∃ (m : I.blowup ⟶ ℙ) (hm : m ≫ q = I.blowupToBase ≫ f),
      IsClosedImmersion (pullback.lift I.blowupToBase m hm.symm) ∧
        ∀ i, I.blowupChart (hU i) ≫ m =
          I.blowupChartToProjectiveSpace f (hU i) (aU i) (haU i) := by
  let 𝒰 := I.blowupProjectiveCover U hU hcover
  let c i := I.blowupChartToProjectiveSpace f (hU i) (aU i) (haU i)
  let m := 𝒰.glueMorphisms c h
  have hchart (i : τ) : I.blowupChart (hU i) ≫ m = c i :=
    𝒰.ι_glueMorphisms c h i
  have hm : m ≫ q = I.blowupToBase ≫ f := by
    apply 𝒰.hom_ext
    intro i
    -- The source cover maps are the native chart immersions.
    change I.blowupChart (hU i) ≫ m ≫ q = I.blowupChart (hU i) ≫ I.blowupToBase ≫ f
    rw [reassoc_of% (hchart i)]
    exact I.blowupChartToProjectiveSpace_toSpecCoeff f (hU i) (aU i) (haU i)
  exact ⟨m, hm, I.isClosedImmersion_blowup_graph f U hU hcover aU haU hm hchart, hchart⟩

variable
  (g : Scheme.Opens.toScheme (X := I.blowup) (I.comap I.blowupToBase).support.compl ⟶
    Proj (MvPolynomial.homogeneousSubmodule ι R))
  (hcompat : ∀ i,
    let e := Scheme.Opens.ι (I.comap I.blowupToBase).support.compl
    pullback.fst e (I.blowupChart (hU i)) ≫ g = pullback.snd e (I.blowupChart (hU i)) ≫
      I.blowupChartToProjectiveSpace f (hU i) (aU i) (haU i))

include hcompat in
private theorem compatible_blowupChartToProjectiveSpace (i j : τ) :
    pullback.fst (I.blowupChart (hU i)) (I.blowupChart (hU j)) ≫
        I.blowupChartToProjectiveSpace f (hU i) (aU i) (haU i) =
      pullback.snd (I.blowupChart (hU i)) (I.blowupChart (hU j)) ≫
        I.blowupChartToProjectiveSpace f (hU j) (aU j) (haU j) := by
  apply I.eq_on_blowupChart_overlap f (hU i) (hU j)
  · exact I.blowupChartToProjectiveSpace_toSpecCoeff f (hU i) (aU i) (haU i)
  · exact I.blowupChartToProjectiveSpace_toSpecCoeff f (hU j) (aU j) (haU j)
  · dsimp only
    let e := Scheme.Opens.ι (I.comap I.blowupToBase).support.compl
    let c := I.blowupChart (hU i)
    let d := I.blowupChart (hU j)
    let k := pullback.fst c d ≫ c
    let r := pullback.fst e k
    let s := pullback.snd e k
    have hk : r ≫ e = s ≫ k := pullback.condition
    let l₁ := pullback.lift r (s ≫ pullback.fst c d) (by simpa [k] using hk)
    let l₂ : pullback e k ⟶ pullback e d :=
      pullback.lift r (s ≫ pullback.snd c d) (by
        rw [hk, Category.assoc]
        exact congrArg (s ≫ ·) (pullback.condition (f := c) (g := d)))
    have hi : pullback.fst e c ≫ g = pullback.snd e c ≫
        I.blowupChartToProjectiveSpace f (hU i) (aU i) (haU i) := hcompat i
    have hj : pullback.fst e d ≫ g = pullback.snd e d ≫
        I.blowupChartToProjectiveSpace f (hU j) (aU j) (haU j) := hcompat j
    have h₁ : r ≫ g = s ≫ pullback.fst c d ≫
        I.blowupChartToProjectiveSpace f (hU i) (aU i) (haU i) := by
      simpa only [l₁, Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd_assoc] using
        congrArg (l₁ ≫ ·) hi
    have h₂ : r ≫ g = s ≫ pullback.snd c d ≫
        I.blowupChartToProjectiveSpace f (hU j) (aU j) (haU j) := by
      simpa only [l₂, Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd_assoc] using
        congrArg (l₂ ≫ ·) hj
    exact h₁.symm.trans h₂

include hcover hcompat in
/-- Indexed affine Rees presentations agreeing on the complement of the exceptional divisor
give a projective coordinate map on the blowup with closed graph over the original scheme. -/
theorem exists_blowupToProjectiveSpace :
    ∃ (m : I.blowup ⟶ ℙ) (hm : m ≫ q = I.blowupToBase ≫ f),
      IsClosedImmersion (pullback.lift I.blowupToBase m hm.symm) ∧
        Scheme.Opens.ι (I.comap I.blowupToBase).support.compl ≫ m = g ∧
        ∀ i, I.blowupChart (hU i) ≫ m =
          I.blowupChartToProjectiveSpace f (hU i) (aU i) (haU i) := by
  obtain ⟨m, hm, hclosed, hchart⟩ := I.exists_blowupToProjectiveSpace_of_compatible
    f U hU hcover aU haU (I.compatible_blowupChartToProjectiveSpace f U hU aU haU g hcompat)
  let 𝒰 := I.blowupProjectiveCover U hU hcover
  refine ⟨m, hm, hclosed, ?_, hchart⟩
  let e := Scheme.Opens.ι (I.comap I.blowupToBase).support.compl
  refine Scheme.Cover.hom_ext (𝒰.pullback₁ e) _ _ fun i ↦ ?_
  -- The pullback cover is indexed by the original charts.
  change pullback.fst e (I.blowupChart (hU i)) ≫ e ≫ m =
    pullback.fst e (I.blowupChart (hU i)) ≫ g
  rw [reassoc_of% (pullback.condition (f := e) (g := I.blowupChart (hU i))), hchart i]
  exact (hcompat i).symm

/-- A closed graph in the product of the base and a finite projective space gives
projectivity of the blowup over the coefficient ring when the base is projectively embedded. -/
theorem isProjectiveOver_blowup_of_closed_graph
    [Finite ι] {σ : Type u} [Finite σ]
    (j : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)) [IsClosedImmersion j]
    (hj : j ≫ Proj.toSpecCoeff (MvPolynomial.homogeneousSubmodule σ R) = f)
    (m : I.blowup ⟶ ℙ) (hm : m ≫ q = I.blowupToBase ≫ f)
    (hclosed : IsClosedImmersion (pullback.lift I.blowupToBase m hm.symm)) :
    let : I.blowup.Over (Spec (.of R)) := ⟨I.blowupToBase ≫ f⟩
    I.blowup.IsProjectiveOver R := by
  let p := Proj.toSpecCoeff (MvPolynomial.homogeneousSubmodule σ R)
  let v := pullback.lift I.blowupToBase m hm.symm
  have : IsClosedImmersion v := hclosed
  let w := pullback.map f q p q j (𝟙 _) (𝟙 _) (by simpa using hj.symm) (by simp)
  have : MorphismProperty.IsStableUnderComposition
      (@IsClosedImmersion : MorphismProperty Scheme.{u}) :=
    ⟨fun _ _ _ _ ↦ IsClosedImmersion.comp _ _⟩
  have : IsClosedImmersion w :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion) ‹IsClosedImmersion j›
      (inferInstance : IsClosedImmersion (𝟙 (Proj (MvPolynomial.homogeneousSubmodule ι R))))
      hj.symm (Category.id_comp q).symm
  let : I.blowup.Over (Spec (.of R)) := ⟨I.blowupToBase ≫ f⟩
  let b := v ≫ w ≫ Proj.segre (σ := σ) (τ := ι) R
  have : b.IsOver (Spec (.of R)) := ⟨by
    simp [b, v, w, p, pullback.map, Proj.segre_toSpecCoeff, hj]
    rfl⟩
  have : IsClosedImmersion b := inferInstanceAs (IsClosedImmersion (v ≫ w ≫ Proj.segre R))
  exact Scheme.IsProjectiveOver.of_isClosedImmersion R b

include hcover hcompat in
/-- A blowup with compatible finite coordinate presentations over a projectively embedded
base is projective over the coefficient ring. -/
theorem isProjectiveOver_blowup_of_local_coordinates
    [Finite ι] {σ : Type u} [Finite σ]
    (j : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)) [IsClosedImmersion j]
    (hj : j ≫ Proj.toSpecCoeff (MvPolynomial.homogeneousSubmodule σ R) = f) :
    let : I.blowup.Over (Spec (.of R)) := ⟨I.blowupToBase ≫ f⟩
    I.blowup.IsProjectiveOver R := by
  obtain ⟨m, hm, hclosed, -, -⟩ :=
    I.exists_blowupToProjectiveSpace f U hU hcover aU haU g hcompat
  exact I.isProjectiveOver_blowup_of_closed_graph f j hj m hm hclosed

end AlgebraicGeometry.Scheme.IdealSheafData
