/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Mutation.Pivot
public import TauCeti.AlgebraicGeometry.Blowup.UniversalProperty

import QPainleve.AlgebraicGeometry.Blowup.Pullback
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Basic
import TauCeti.AlgebraicGeometry.IdealSheaf.Locality
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

variable {K : Type} [Field K]

local notation "RulingBase" => projectiveLine K

private abbrev rulingOpen (c : K) : Bool → Scheme
  | false => projectiveLineTorusFan.finiteFanScheme K
  | true => (mutationRulingComplement c).toScheme

private abbrev rulingOpenι (c : K) : (j : Bool) → rulingOpen c j ⟶ RulingBase
  | false => (projectiveLineTorusι K)
  | true => (mutationRulingComplement c).ι

private theorem rulingOpen_covers (c : Kˣ) (x : RulingBase) :
    ∃ j y, rulingOpenι (c : K) j y = x := by
  by_cases hx : x ∈ mutationRulingComplement (c : K)
  · exact ⟨true, ⟨x, hx⟩, rfl⟩
  · let p := projectiveLine.polynomialPoint K (RingHom.id K) 0 (-(↑c⁻¹ : K))
    have hp : x ∈ (p.ker.support : Set RulingBase) := by
      rw [mutationRulingComplement_eq_compl_support] at hx
      by_contra hn
      exact hx hn
    have : IsClosedImmersion p := isClosedImmersion_of_comp_eq_id
      (projectiveLine K ↘ Spec (.of K)) p (by simp [p, projectiveLine.polynomialPoint_over])
    have hsupport : (p.ker.support : Set RulingBase) = Set.range p :=
      p.support_ker.trans p.isClosedEmbedding.isClosed_range.closure_eq
    rw [hsupport] at hp
    obtain ⟨y, rfl⟩ := hp
    have hpoint : projectiveLineTorusPoint K (-c⁻¹) ≫ (projectiveLineTorusι K) = p := by
      rw [projectiveLineTorusPoint_comp_projectiveLineTorusι, Units.val_neg]
    exact ⟨false, projectiveLineTorusPoint K (-c⁻¹) y, by
      simpa only [rulingOpenι, Scheme.Hom.comp_apply] using
        congrArg (fun (g : Spec (CommRingCat.of K) ⟶ RulingBase) ↦ g y) hpoint⟩

private instance (c : K) (j : Bool) : IsOpenImmersion (rulingOpenι c j) := by
  cases j
  · exact inferInstanceAs (IsOpenImmersion (projectiveLineTorusι K))
  · exact inferInstanceAs (IsOpenImmersion (mutationRulingComplement c).ι)

private structure RulingChart {X : Scheme} (r : X ⟶ RulingBase) (c : K) (j : Bool) where
  scheme : Scheme
  ι : scheme ⟶ X
  toRuling : scheme ⟶ rulingOpen c j
  isPullback : IsPullback ι toRuling r (rulingOpenι c j)

private instance rulingChart_isOpenImmersion {X : Scheme} {r : X ⟶ RulingBase} {c : K} {j : Bool}
    (chart : RulingChart r c j) : IsOpenImmersion chart.ι :=
  MorphismProperty.of_isPullback chart.isPullback.flip inferInstance

private abbrev rulingChartCover {X : Scheme} {r : X ⟶ RulingBase} (c : Kˣ)
    (chart : (j : Bool) → RulingChart r (c : K) j) : X.OpenCover :=
  Scheme.Cover.mkOfCovers Bool (fun j ↦ (chart j).scheme) (fun j ↦ (chart j).ι)
    (fun x ↦ by
      obtain ⟨j, y, hy⟩ := rulingOpen_covers c (r x)
      have hx : x ∈ Set.range (pullback.fst r (rulingOpenι (c : K) j)) := by
        rw [Scheme.Pullback.range_fst]
        exact ⟨y, hy⟩
      obtain ⟨z, hz⟩ := hx
      let h := (chart j).isPullback
      exact ⟨j, h.isoPullback.inv z, by
        rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hz]⟩)
    (fun _ ↦ inferInstance)

section BlowupCharts

variable {X : Scheme} (I : X.IdealSheafData) {c : K}

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
    {t : T ⟶ projectiveLineTorusFan.finiteFanScheme K}
    (ht : IsPullback t g (projectiveLineTorusι K) r) :
    RulingChart (I.blowupToBase ≫ r) c false :=
  ⟨Y, ι, a ≫ t, (h.paste_horiz ht).flip⟩

end BlowupCharts

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (ρ : Φ.Ray)
  (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones) (c : Kˣ)

local notation "v" => ρ.primitiveGenerator
local notation "hv" => Ray.primitiveGenerator_ne_zero ρ
local notation "hp" => Ray.hull_primitiveGenerator_mem ρ
local notation "Ψ" => Φ.mutationFan b hv hp hOpp
local notation "m" => LinearMap.toAddMonoidHom (Basis.detDualEquiv b v)
local notation "h₀" => detCharacter_nonneg_or_nonpos Φ b hv hp hOpp
local notation "h₁" => mutationDetCharacter_nonneg_or_nonpos Φ b hv hp hOpp
local notation "r₀" => Φ.characterRuling K m h₀
local notation "r₁" => characterRuling K Ψ m h₁
local notation "J₀" => Ray.mutationSourceCenterIdeal b ρ c
local notation "J₁" => Ray.mutationTargetCenterIdeal b ρ hOpp c
local notation "I₀" => Ray.mutationPivotSourceIdeal b ρ hOpp c
local notation "I₁" => Ray.mutationPivotTargetIdeal b ρ hOpp c
local notation "P₀" =>
  Scheme.IdealSheafData.blowupToBase I₀ ≫ pullback.fst r₀ (projectiveLineTorusι K)
local notation "P₁" =>
  Scheme.IdealSheafData.blowupToBase I₁ ≫ pullback.fst r₁ (projectiveLineTorusι K)
local notation "U₀" => mutationComplement Φ b h₀ (c : K)
local notation "U₁" => mutationComplement Ψ b h₁ (c : K)
local notation "R₀" => Scheme.IdealSheafData.blowupToBase J₀ ≫ r₀
local notation "R₁" => Scheme.IdealSheafData.blowupToBase J₁ ≫ r₁
local notation "eT" => Ray.mutationPivotIso b ρ hOpp c
local notation "eC" => Φ.mutationComplementIso b (c : K) hv hp hOpp

private theorem sourceCenter_comap_complement_isEffectiveCartier :
    ((J₀).comap (U₀).ι).IsEffectiveCartier := by
  rw [ρ.mutationSourceCenterIdeal_comap_complement b hOpp c]
  exact Scheme.IdealSheafData.isEffectiveCartier_top _

private theorem targetCenter_comap_complement_isEffectiveCartier :
    ((J₁).comap (U₁).ι).IsEffectiveCartier := by
  rw [ρ.mutationTargetCenterIdeal_comap_complement b hOpp c]
  exact Scheme.IdealSheafData.isEffectiveCartier_top _

private abbrev mutationSourceChart : (j : Bool) → RulingChart R₀ (c : K) j
  | false => torusBlowupChart J₀ (ρ.isPullback_mutationPivotSourceBlowupι b hOpp c)
      ((IsPullback.of_hasPullback r₀ (projectiveLineTorusι K)).flip)
  | true => complementBlowupChart J₀ (Φ.isPullback_mutationComplementToRuling b h₀ (c : K))
      (sourceCenter_comap_complement_isEffectiveCartier b ρ hOpp c)

private abbrev mutationTargetChart : (j : Bool) → RulingChart R₁ (c : K) j
  | false => torusBlowupChart J₁ (ρ.isPullback_mutationPivotTargetBlowupι b hOpp c)
      ((IsPullback.of_hasPullback r₁ (projectiveLineTorusι K)).flip)
  | true => complementBlowupChart J₁ ((Ψ).isPullback_mutationComplementToRuling b h₁ (c : K))
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
  apply (cancel_mono (rulingOpenι (c : K) j)).mp
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

/-- A point on the common resolution above the complement of the pivot fiber projects on
the target to its image under the mutation isomorphism of the two complements. -/
theorem Ray.mutationBlowupIso_apply_over_complement (p : (J₀).blowup) (x : (U₀).toScheme)
    (hx : (J₀).blowupToBase p = (U₀).ι x) :
    (J₁).blowupToBase ((ρ.mutationBlowupIso b hOpp c).hom p) = (U₁).ι ((eC).hom x) := by
  let hI := sourceCenter_comap_complement_isEffectiveCartier b ρ hOpp c
  let j := (J₀).blowupLift (U₀).ι hI
  obtain ⟨y, hy, hproj⟩ := Scheme.exists_preimage_of_isPullback
    ((J₀).isPullback_blowupLift (U₀).ι hI) x p hx.symm
  change y = x at hy
  subst y
  change j x = p at hproj
  have hcomp : j ≫ (ρ.mutationBlowupIso b hOpp c).hom ≫ (J₁).blowupToBase =
      (eC).hom ≫ (U₁).ι := by
    rw [← Category.assoc, ρ.mutationComplementBlowupι_comp_mutationBlowupIso_hom b hOpp c,
      Category.assoc, Scheme.IdealSheafData.blowupLift_blowupToBase]
  rw [← hproj]
  exact congrArg (fun f ↦ f x) hcomp

/-- The global mutation blowup isomorphism preserves the projective-line ruling. -/
@[reassoc]
theorem Ray.mutationBlowupIso_hom_comp_ruling :
    (ρ.mutationBlowupIso b hOpp c).hom ≫ R₁ = R₀ :=
  mutationBlowupHom_comp_ruling b ρ hOpp c

/-- If the reference point projects off the pivot fiber, another point projects to the
same point on the source exactly when it projects to the same point on the target. -/
theorem Ray.mutationBlowupIso_projected_eq_iff (ρ : Φ.Ray) (b : Basis (Fin 2) ℤ N)
    (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones) (c : Kˣ)
    {p q : (ρ.mutationSourceCenterIdeal b c).blowup}
    (hq : (ρ.mutationSourceCenterIdeal b c).blowupToBase q ∈
      Φ.mutationComplement b
        (Φ.detCharacter_nonneg_or_nonpos b ρ.primitiveGenerator_ne_zero
          ρ.hull_primitiveGenerator_mem hOpp) (c : K)) :
    (ρ.mutationTargetCenterIdeal b hOpp c).blowupToBase ((ρ.mutationBlowupIso b hOpp c).hom p) =
      (ρ.mutationTargetCenterIdeal b hOpp c).blowupToBase ((ρ.mutationBlowupIso b hOpp c).hom q) ↔
        (ρ.mutationSourceCenterIdeal b c).blowupToBase p =
          (ρ.mutationSourceCenterIdeal b c).blowupToBase q := by
  let I := ρ.mutationSourceCenterIdeal b c
  let J := ρ.mutationTargetCenterIdeal b hOpp c
  let G := ρ.mutationBlowupIso b hOpp c
  let nonzero := ρ.primitiveGenerator_ne_zero
  let memCone := ρ.hull_primitiveGenerator_mem
  let hSource := Φ.detCharacter_nonneg_or_nonpos b nonzero memCone hOpp
  let hTarget := Φ.mutationDetCharacter_nonneg_or_nonpos b nonzero memCone hOpp
  let targetFan := Φ.mutationFan b nonzero memCone hOpp
  let U := Φ.mutationComplement b hSource (c : K)
  let W := mutationComplement targetFan b hTarget (c : K)
  let complementIso := Φ.mutationComplementIso b (c : K) nonzero memCone hOpp
  let character := LinearMap.toAddMonoidHom (b.detDualEquiv ρ.primitiveGenerator)
  let f := Φ.characterRuling K character hSource
  let g := targetFan.characterRuling K character hTarget
  let y : U.toScheme := ⟨I.blowupToBase q, hq⟩
  have hqy := ρ.mutationBlowupIso_apply_over_complement b hOpp c q y rfl
  have hr (z : I.blowup) : g (J.blowupToBase (G.hom z)) = f (I.blowupToBase z) :=
    congrArg (fun a ↦ a z) (ρ.mutationBlowupIso_hom_comp_ruling b hOpp c)
  constructor
  · intro he
    have hf := (hr p).symm.trans ((congrArg (fun z ↦ g z) he).trans (hr q))
    have hmem : I.blowupToBase p ∈ U := by
      dsimp only [U]
      rw [mutationComplement_eq, Scheme.Hom.mem_preimage] at hq ⊢
      exact hf ▸ hq
    let x : U.toScheme := ⟨I.blowupToBase p, hmem⟩
    have hpx := ρ.mutationBlowupIso_apply_over_complement b hOpp c p x rfl
    have e : W.ι (complementIso.hom x) = W.ι (complementIso.hom y) := hpx.symm.trans (he.trans hqy)
    exact congrArg Subtype.val (complementIso.hom.injective (W.ι.injective e))
  · intro he
    exact (ρ.mutationBlowupIso_apply_over_complement b hOpp c p y he).trans hqy.symm

section ExceptionalDivisor

open Scheme.IdealSheafData

local notation "p" =>
  projectiveLine.polynomialPoint K (RingHom.id K) 0 (-(Units.val c⁻¹))
local notation "G" => Ray.mutationBlowupIso b ρ hOpp c
local notation "ex" I:arg => comap I (blowupToBase I)

private theorem comap_pivotFiber_exceptional_at_torus :
    ((p).ker.comap R₀).comap (S false).ι =
      (ex(J₀) * (ex(J₁)).comap (G).hom).comap (S false).ι := by
  rw [comap_mul, ← comap_comp (ex(J₁)),
    ← comap_comp (p).ker, ← Category.assoc,
    ρ.mutationPivotSourceBlowupι_blowupToBase,
    ρ.mutationPivotSourceBlowupι_comp_mutationBlowupIso_hom, comap_comp (ex(J₁))]
  have hSourceExc : (ex(J₀)).comap (S false).ι = ex(I₀) :=
    ρ.comap_exceptionalIdeal_mutationPivotSourceBlowupι b hOpp c
  rw [hSourceExc, ρ.comap_exceptionalIdeal_mutationPivotTargetBlowupι b hOpp c]
  simpa only [Category.assoc, Units.val_mul, Units.val_neg, Units.val_one, neg_mul, one_mul] using
    ρ.comap_pivotFiber_mutationPivotIso b hOpp c

private theorem comap_pivotFiber_exceptional_at_complement :
    ((p).ker.comap R₀).comap (S true).ι =
      (ex(J₀) * (ex(J₁)).comap (G).hom).comap (S true).ι := by
  have hF : (p).ker.comap (rulingOpenι (c : K) true) = ⊤ := by
    apply (comap_eq_top_iff _ _).mpr
    rw [← mutationRulingComplement_eq_compl_support c]
    exact Scheme.Opens.ι_preimage_self _
  have hSourceExc : (ex(J₀)).comap (S true).ι = ⊤ := by
    rw [← comap_comp, blowupLift_blowupToBase,
      ρ.mutationSourceCenterIdeal_comap_complement b hOpp c]
  have hTargetExc : (ex(J₁)).comap (T true).ι = ⊤ := by
    rw [← comap_comp, blowupLift_blowupToBase,
      ρ.mutationTargetCenterIdeal_comap_complement b hOpp c]
  rw [← comap_comp (p).ker, (S true).isPullback.w, comap_comp, hF, comap_top,
    comap_mul, hSourceExc, ← comap_comp (ex(J₁)),
    ρ.mutationComplementBlowupι_comp_mutationBlowupIso_hom, comap_comp, hTargetExc, comap_top,
    ← one_eq_top, mul_one]

/-- The total pivot fiber on the global source blowup is the sum of the source
exceptional divisor and the pullback of the target exceptional divisor. -/
theorem Ray.comap_pivotFiber_mutationBlowupIso :
    (p).ker.comap R₀ = ex(J₀) * (ex(J₁)).comap (G).hom := by
  refine ext_of_comap_openCover (𝒰) fun j ↦ ?_
  cases j
  · exact comap_pivotFiber_exceptional_at_torus b ρ hOpp c
  · exact comap_pivotFiber_exceptional_at_complement b ρ hOpp c

end ExceptionalDivisor

/-- The global mutation blowup isomorphism is over the coefficient field. -/
@[reassoc]
theorem Ray.mutationBlowupIso_hom_comp_toBase :
    (ρ.mutationBlowupIso b hOpp c).hom ≫ (J₁).blowupToBase ≫
        (Ψ).finiteFanSchemeToSpec K =
      (J₀).blowupToBase ≫ Φ.finiteFanSchemeToSpec K := by
  have h := congrArg (· ≫ (projectiveLine K ↘ Spec (CommRingCat.of K)))
    (ρ.mutationBlowupIso_hom_comp_ruling b hOpp c)
  simpa only [Category.assoc, CategoryTheory.comp_over r₀, CategoryTheory.comp_over r₁,
    finiteFanScheme_over K] using h

section Boundary

open Scheme.IdealSheafData

local notation "F₀" => Nonempty.intro (Ray.toCone Φ ρ)
local notation "F₁" =>
  Nonempty.intro (Ray.toCone (Ψ) (Φ.mutationFanRayEquiv b hv hp hOpp ρ))
local notation "D₀" => Φ.toricBoundaryIdeal K F₀
local notation "D₁" => toricBoundaryIdeal K (Ψ) F₁
local notation "B₀" => Scheme.Hom.ker (Scheme.IdealSheafData.blowupMap (J₀) (subschemeι (D₀)))
local notation "B₁" => Scheme.Hom.ker (Scheme.IdealSheafData.blowupMap (J₁) (subschemeι (D₁)))

private theorem comap_strictBoundary_mutationComplement :
    (B₁).comap ((T true).ι) = (D₁).comap (U₁).ι ∧
      (B₀).comap ((S true).ι) = (D₀).comap (U₀).ι := by
  have hSource : (S true).ι ≫ (J₀).blowupToBase = (U₀).ι :=
    blowupLift_blowupToBase _ _ _
  have hTarget : (T true).ι ≫ (J₁).blowupToBase = (U₁).ι :=
    blowupLift_blowupToBase _ _ _
  have : IsOpenImmersion (S true).ι := rulingChart_isOpenImmersion (S true)
  have : IsOpenImmersion (T true).ι := rulingChart_isOpenImmersion (T true)
  constructor
  · rw [comap_ker_blowupMap_subschemeι_of_comap_eq_top, hTarget]
    rw [hTarget, ρ.mutationTargetCenterIdeal_comap_complement b hOpp c]
  · rw [comap_ker_blowupMap_subschemeι_of_comap_eq_top, hSource]
    rw [hSource, ρ.mutationSourceCenterIdeal_comap_complement b hOpp c]

/-- The global pivot blowup isomorphism identifies the scheme-theoretic strict
transforms of the two reduced toric boundaries. -/
theorem Ray.comap_strictBoundary_mutationBlowupIso (hΦ : Φ.IsRegular) :
    (B₁).comap (ρ.mutationBlowupIso b hOpp c).hom = B₀ := by
  refine ext_of_comap_openCover (𝒰) fun (j : Bool) ↦ ?_
  have hj : (S j).ι ≫ (ρ.mutationBlowupIso b hOpp c).hom =
      (E j).hom ≫ (T j).ι := mutationChart_ι_mutationBlowupHom b ρ hOpp c j
  -- The glued cover is the pullback of the two ruling opens to the source blowup.
  change ((B₁).comap (ρ.mutationBlowupIso b hOpp c).hom).comap (S j).ι =
    (B₀).comap (S j).ι
  rw [← comap_comp, hj, comap_comp]
  cases j
  · exact ρ.comap_boundaryIdeal_mutationPivotIso b hOpp c hΦ
  · obtain ⟨hTarget, hSource⟩ := comap_strictBoundary_mutationComplement b ρ hOpp c
    rw [hTarget, hSource, ← comap_comp]
    exact comap_boundaryIdeal_mutationComplementIso (Φ := Φ) b hv hp hOpp c F₀ F₁

end Boundary

end TauCeti.Toric.Fan
