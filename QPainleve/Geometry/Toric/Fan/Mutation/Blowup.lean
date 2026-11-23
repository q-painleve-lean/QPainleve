/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Mutation.Pivot
public import TauCeti.AlgebraicGeometry.Blowup.UniversalProperty

import QPainleve.AlgebraicGeometry.Blowup.Pullback
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap

/-!
# Toric mutation on the global pivot blowups

The elementary transformation over the base torus and the isomorphism away from the pivot
fiber give a single isomorphism of the two toric pivot blowups over the projective-line ruling.
The two restrictions specify the comparison used to transport further blowup centers and
to compute pullbacks of divisors.

The local elementary transformation is that of Gross, Hacking and Keel,
[*Birational geometry of cluster algebras*][GHK], §3.1.

[GHK]: https://arxiv.org/html/1309.2573v2#S3.SS1
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Limits Module PointedCone
open TauCeti.AlgebraicGeometry (projectiveLine)

namespace TauCeti.Toric.Fan

private abbrev RulingBase := projectiveLine ℂ

private abbrev rulingOpen (c : ℂ) : Bool → Scheme
  | false => projectiveLineTorusFan.algebraicRealization
  | true => (mutationRulingComplement c).toScheme

private abbrev rulingOpenι (c : ℂ) : (j : Bool) → rulingOpen c j ⟶ RulingBase
  | false => projectiveLineTorusι
  | true => (mutationRulingComplement c).ι

private theorem rulingOpen_covers (c : ℂˣ) (x : RulingBase) :
    ∃ j y, rulingOpenι (c : ℂ) j y = x := by
  by_cases hx : x ∈ mutationRulingComplement (c : ℂ)
  · exact ⟨true, ⟨x, hx⟩, rfl⟩
  · let p := projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) 0 (-(↑c⁻¹ : ℂ))
    have hp : x ∈ (p.ker.support : Set RulingBase) := by
      rw [mutationRulingComplement_eq_compl_support] at hx
      by_contra hn
      exact hx hn
    have : IsClosedImmersion p := isClosedImmersion_of_comp_eq_id
      (projectiveLine ℂ ↘ Spec (.of ℂ)) p (by simp [p, projectiveLine.polynomialPoint_over])
    have hsupport : (p.ker.support : Set RulingBase) = Set.range p :=
      p.support_ker.trans p.isClosedEmbedding.isClosed_range.closure_eq
    rw [hsupport] at hp
    obtain ⟨y, rfl⟩ := hp
    have hpoint : projectiveLineTorusPoint (-c⁻¹) ≫ projectiveLineTorusι = p := by
      rw [projectiveLineTorusPoint_comp_projectiveLineTorusι, Units.val_neg]
    exact ⟨false, projectiveLineTorusPoint (-c⁻¹) y, by
      simpa only [rulingOpenι, Scheme.Hom.comp_apply] using
        congrArg (fun (g : Spec (CommRingCat.of ℂ) ⟶ RulingBase) ↦ g y) hpoint⟩

private instance (c : ℂ) (j : Bool) : IsOpenImmersion (rulingOpenι c j) := by
  cases j
  · exact inferInstanceAs (IsOpenImmersion projectiveLineTorusι)
  · exact inferInstanceAs (IsOpenImmersion (mutationRulingComplement c).ι)

private structure RulingChart {X : Scheme} (r : X ⟶ RulingBase) (c : ℂ) (j : Bool) where
  scheme : Scheme
  ι : scheme ⟶ X
  toRuling : scheme ⟶ rulingOpen c j
  isPullback : IsPullback ι toRuling r (rulingOpenι c j)

private instance rulingChart_isOpenImmersion {X : Scheme} {r : X ⟶ RulingBase} {c : ℂ} {j : Bool}
    (chart : RulingChart r c j) : IsOpenImmersion chart.ι :=
  MorphismProperty.of_isPullback chart.isPullback.flip inferInstance

private abbrev rulingChartCover {X : Scheme} {r : X ⟶ RulingBase} (c : ℂˣ)
    (chart : (j : Bool) → RulingChart r (c : ℂ) j) : X.OpenCover :=
  Scheme.Cover.mkOfCovers Bool (fun j ↦ (chart j).scheme) (fun j ↦ (chart j).ι)
    (fun x ↦ by
      obtain ⟨j, y, hy⟩ := rulingOpen_covers c (r x)
      have hx : x ∈ Set.range (pullback.fst r (rulingOpenι (c : ℂ) j)) := by
        rw [Scheme.Pullback.range_fst]
        exact ⟨y, hy⟩
      obtain ⟨z, hz⟩ := hx
      let h := (chart j).isPullback
      exact ⟨j, h.isoPullback.inv z, by
        rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hz]⟩)
    (fun _ ↦ inferInstance)

section BlowupCharts

variable {X : Scheme} (I : X.IdealSheafData) {c : ℂ}

private abbrev complementBlowupChart {r : X ⟶ RulingBase} {U : X.Opens}
    {p : U.toScheme ⟶ (mutationRulingComplement c).toScheme}
    (hU : IsPullback p U.ι (mutationRulingComplement c).ι r)
    (hI : (I.comap U.ι).IsEffectiveCartier) :
    RulingChart (I.blowupToBase ≫ r) c true := by
  refine ⟨U.toScheme, I.blowupLift U.ι hI, p, ?_⟩
  simpa only [Category.id_comp] using
    ((I.isPullback_blowupLift U.ι hI).paste_horiz hU).flip

private abbrev torusBlowupChart {r : X ⟶ RulingBase} {T Y : Scheme} {g : T ⟶ X}
    {a : Y ⟶ T} {ι : Y ⟶ I.blowup} (h : IsPullback a ι g I.blowupToBase)
    {t : T ⟶ projectiveLineTorusFan.algebraicRealization}
    (ht : IsPullback t g projectiveLineTorusι r) :
    RulingChart (I.blowupToBase ≫ r) c false :=
  ⟨Y, ι, a ≫ t, (h.paste_horiz ht).flip⟩

end BlowupCharts

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (ρ : Φ.Ray)
  (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones) (c : ℂˣ)

local notation "v" => ρ.primitiveGenerator
local notation "hv" => Ray.primitiveGenerator_ne_zero ρ
local notation "hp" => Ray.hull_primitiveGenerator_mem ρ
local notation "Ψ" => Φ.mutationFan b hv hp hOpp
local notation "m" => LinearMap.toAddMonoidHom (Basis.detDualEquiv b v)
local notation "h₀" => detCharacter_nonneg_or_nonpos Φ b hv hp hOpp
local notation "h₁" => mutationDetCharacter_nonneg_or_nonpos Φ b hv hp hOpp
local notation "r₀" => Φ.characterRuling m h₀
local notation "r₁" => characterRuling Ψ m h₁
local notation "J₀" => Ray.mutationSourceCenterIdeal b ρ c
local notation "J₁" => Ray.mutationTargetCenterIdeal b ρ hOpp c
local notation "I₀" => Ray.mutationPivotSourceIdeal b ρ hOpp c
local notation "I₁" => Ray.mutationPivotTargetIdeal b ρ hOpp c
local notation "P₀" => Scheme.IdealSheafData.blowupToBase I₀ ≫ pullback.fst r₀ projectiveLineTorusι
local notation "P₁" => Scheme.IdealSheafData.blowupToBase I₁ ≫ pullback.fst r₁ projectiveLineTorusι
local notation "U₀" => mutationComplement Φ b h₀ (c : ℂ)
local notation "U₁" => mutationComplement Ψ b h₁ (c : ℂ)
local notation "R₀" => Scheme.IdealSheafData.blowupToBase J₀ ≫ r₀
local notation "R₁" => Scheme.IdealSheafData.blowupToBase J₁ ≫ r₁
local notation "eT" => Ray.mutationPivotIso b ρ hOpp c
local notation "eC" => Φ.mutationComplementIso b (c : ℂ) hv hp hOpp

private theorem sourceCenter_comap_complement_isEffectiveCartier :
    ((J₀).comap (U₀).ι).IsEffectiveCartier := by
  rw [ρ.mutationSourceCenterIdeal_comap_complement b hOpp c]
  exact Scheme.IdealSheafData.isEffectiveCartier_top _

private theorem targetCenter_comap_complement_isEffectiveCartier :
    ((J₁).comap (U₁).ι).IsEffectiveCartier := by
  rw [ρ.mutationTargetCenterIdeal_comap_complement b hOpp c]
  exact Scheme.IdealSheafData.isEffectiveCartier_top _

private abbrev mutationSourceChart : (j : Bool) → RulingChart R₀ (c : ℂ) j
  | false => torusBlowupChart J₀ (ρ.isPullback_mutationPivotSourceBlowupι b hOpp c)
      ((IsPullback.of_hasPullback r₀ projectiveLineTorusι).flip)
  | true => complementBlowupChart J₀ (Φ.isPullback_mutationComplementToRuling b h₀ (c : ℂ))
      (sourceCenter_comap_complement_isEffectiveCartier b ρ hOpp c)

private abbrev mutationTargetChart : (j : Bool) → RulingChart R₁ (c : ℂ) j
  | false => torusBlowupChart J₁ (ρ.isPullback_mutationPivotTargetBlowupι b hOpp c)
      ((IsPullback.of_hasPullback r₁ projectiveLineTorusι).flip)
  | true => complementBlowupChart J₁ ((Ψ).isPullback_mutationComplementToRuling b h₁ (c : ℂ))
      (targetCenter_comap_complement_isEffectiveCartier b ρ hOpp c)

local notation "S" => mutationSourceChart b ρ hOpp c
local notation "T" => mutationTargetChart b ρ hOpp c
local notation "𝒰" => rulingChartCover c S
local notation "𝒱" => rulingChartCover c T

private abbrev mutationBlowupChartIso : (j : Bool) → (S j).scheme ≅ (T j).scheme
  | false => eT
  | true => eC

local notation "E" => mutationBlowupChartIso b ρ hOpp c

private theorem mutationBlowupChartIso_hom_toRuling (j : Bool) :
    (E j).hom ≫ (T j).toRuling = (S j).toRuling := by
  apply (cancel_mono (rulingOpenι (c : ℂ) j)).mp
  simp only [Category.assoc, (T j).isPullback.w.symm, (S j).isPullback.w.symm]
  cases j
  · simpa only [mutationBlowupChartIso, mutationTargetChart, mutationSourceChart,
      torusBlowupChart, Category.assoc, ρ.mutationPivotSourceBlowupι_blowupToBase_assoc,
      ρ.mutationPivotTargetBlowupι_blowupToBase_assoc] using
      ρ.mutationPivotIso_hom_comp_ruling b hOpp c
  · dsimp only [mutationBlowupChartIso, mutationTargetChart, mutationSourceChart,
      complementBlowupChart]
    simpa only [Category.assoc, Scheme.IdealSheafData.blowupLift_blowupToBase_assoc] using
      ρ.mutationComplementIso_hom_comp_ruling b hOpp c

private theorem mutationBlowupHom_agrees_on_overlap :
    pullback.fst (S false).ι (S true).ι ≫ (E false).hom ≫ (T false).ι =
      pullback.snd (S false).ι (S true).ι ≫ (E true).hom ≫ (T true).ι := by
  let p := pullback.fst (S false).ι (S true).ι
  let q := pullback.snd (S false).ι (S true).ι
  have hsource : (S false).ι ≫ (J₀).blowupToBase = P₀ :=
    ρ.mutationPivotSourceBlowupι_blowupToBase b hOpp c
  have hq : (S true).ι ≫ (J₀).blowupToBase = (U₀).ι :=
    Scheme.IdealSheafData.blowupLift_blowupToBase _ _ _
  have hcompare : p ≫ P₀ = q ≫ (U₀).ι := by
    rw [← hsource, ← hq, ← Category.assoc, ← Category.assoc, pullback.condition]
  let l := pullback.lift p q hcompare
  let f := p ≫ (E false).hom ≫ (T false).ι
  let g := q ≫ (E true).hom
  have hproj : f ≫ (J₁).blowupToBase = g ≫ (U₁).ι := by
    have h := congrArg (l ≫ ·) (ρ.mutationPivotIso_hom_agrees_on_overlap b hOpp c)
    simpa only [f, g, Category.assoc, mutationBlowupChartIso, mutationTargetChart, torusBlowupChart,
      ρ.mutationPivotTargetBlowupι_blowupToBase, l, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc] using h
  have ht : (T true).ι ≫ (J₁).blowupToBase = (U₁).ι :=
    Scheme.IdealSheafData.blowupLift_blowupToBase _ _ _
  refine (J₁).blowup_hom_ext (g₁ := f) (g₂ := g ≫ (T true).ι) ?_ ?_
  · rw [Category.assoc g, ht]
    exact hproj
  · rw [hproj, Scheme.IdealSheafData.comap_comp,
      ρ.mutationTargetCenterIdeal_comap_complement b hOpp c, Scheme.IdealSheafData.comap_top]
    exact Scheme.IdealSheafData.isEffectiveCartier_top _

private theorem mutationBlowupHom_compatible (j k : Bool) :
    pullback.fst (S j).ι (S k).ι ≫ (E j).hom ≫ (T j).ι =
      pullback.snd (S j).ι (S k).ι ≫ (E k).hom ≫ (T k).ι := by
  cases j <;> cases k
  · have := rulingChart_isOpenImmersion (S false)
    rw [fst_eq_snd_of_mono_eq]
  · exact mutationBlowupHom_agrees_on_overlap b ρ hOpp c
  · rw [← cancel_epi (pullbackSymmetry _ _).hom]
    simpa only [pullbackSymmetry_hom_comp_fst_assoc, pullbackSymmetry_hom_comp_snd_assoc] using
      (mutationBlowupHom_agrees_on_overlap b ρ hOpp c).symm
  · have := rulingChart_isOpenImmersion (S true)
    rw [fst_eq_snd_of_mono_eq]

private def mutationBlowupHom : (J₀).blowup ⟶ (J₁).blowup :=
  (𝒰).glueMorphisms (fun j ↦ (E j).hom ≫ (T j).ι)
    (mutationBlowupHom_compatible b ρ hOpp c)

local notation "M" => mutationBlowupHom b ρ hOpp c

private theorem mutationChart_ι_mutationBlowupHom (j : Bool) :
    (S j).ι ≫ M = (E j).hom ≫ (T j).ι :=
  (𝒰).ι_glueMorphisms _ _ j

private theorem mutationBlowupHom_comp_ruling : M ≫ R₁ = R₀ := by
  refine (𝒰).hom_ext _ _ fun (j : Bool) ↦ ?_
  have H := mutationChart_ι_mutationBlowupHom b ρ hOpp c j
  -- The cover uses the two chosen representatives of the ruling pullbacks.
  change (S j).ι ≫ M ≫ R₁ = (S j).ι ≫ R₀
  rw [← Category.assoc, H, Category.assoc, (T j).isPullback.w, ← Category.assoc,
    mutationBlowupChartIso_hom_toRuling, ← (S j).isPullback.w]

private theorem isIso_mutationBlowupHom : IsIso M := by
  rw [← MorphismProperty.isomorphisms.iff]
  refine IsZariskiLocalAtTarget.of_openCover (P := MorphismProperty.isomorphisms Scheme) 𝒱
    fun (j : Bool) ↦ ?_
  rw [MorphismProperty.isomorphisms.iff]
  have htop : IsPullback (S j).ι (E j).hom M (T j).ι := by
    refine IsPullback.of_bot ?_ (mutationChart_ι_mutationBlowupHom b ρ hOpp c j)
      (T j).isPullback
    rw [mutationBlowupHom_comp_ruling, mutationBlowupChartIso_hom_toRuling]
    exact (S j).isPullback
  have heq : (𝒱).pullbackHom M j = (htop.isoPullback.inv ≫ (E j).hom) := by
    exact htop.isoPullback_inv_snd.symm
  rw [heq]
  exact IsIso.comp_isIso' htop.isoPullback.symm.isIso_hom (E j).isIso_hom

/-- The global isomorphism between the toric surfaces blown up at the original and mutated
pivot centers. The two blowups present the elementary transform over the same ruling. -/
def Ray.mutationBlowupIso : (J₀).blowup ≅ (J₁).blowup :=
  letI := isIso_mutationBlowupHom b ρ hOpp c
  asIso M

/-- The global mutation blowup isomorphism restricts to the elementary transformation
over the base torus. -/
@[reassoc (attr := simp)]
theorem Ray.mutationPivotSourceBlowupι_comp_mutationBlowupIso_hom :
    ρ.mutationPivotSourceBlowupι b hOpp c ≫ (ρ.mutationBlowupIso b hOpp c).hom =
      (eT).hom ≫ ρ.mutationPivotTargetBlowupι b hOpp c :=
  mutationChart_ι_mutationBlowupHom b ρ hOpp c false

/-- On the complement of the pivot fiber the blowups are unchanged and the global
isomorphism restricts to the toric mutation isomorphism there. -/
@[reassoc (attr := simp)]
theorem Ray.mutationComplementBlowupι_comp_mutationBlowupIso_hom :
    (J₀).blowupLift (U₀).ι (by
      rw [ρ.mutationSourceCenterIdeal_comap_complement b hOpp c]
      exact Scheme.IdealSheafData.isEffectiveCartier_top _) ≫
        (ρ.mutationBlowupIso b hOpp c).hom =
      (eC).hom ≫ (J₁).blowupLift (U₁).ι (by
        rw [ρ.mutationTargetCenterIdeal_comap_complement b hOpp c]
        exact Scheme.IdealSheafData.isEffectiveCartier_top _) :=
  mutationChart_ι_mutationBlowupHom b ρ hOpp c true

/-- The global mutation blowup isomorphism preserves the projective-line ruling. -/
@[reassoc]
theorem Ray.mutationBlowupIso_hom_comp_ruling :
    (ρ.mutationBlowupIso b hOpp c).hom ≫ R₁ = R₀ :=
  mutationBlowupHom_comp_ruling b ρ hOpp c

/-- The global mutation blowup isomorphism is over the complex field. -/
@[reassoc]
theorem Ray.mutationBlowupIso_hom_comp_toBase :
    (ρ.mutationBlowupIso b hOpp c).hom ≫ (J₁).blowupToBase ≫
        (Ψ).algebraicRealizationStructureMap =
      (J₀).blowupToBase ≫ Φ.algebraicRealizationStructureMap := by
  have h := congrArg (· ≫ (projectiveLine ℂ ↘ Spec (CommRingCat.of ℂ)))
    (ρ.mutationBlowupIso_hom_comp_ruling b hOpp c)
  simpa only [Category.assoc, CategoryTheory.comp_over r₀, CategoryTheory.comp_over r₁,
    algebraicRealization_over] using h

end TauCeti.Toric.Fan
