/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.InternalBlowup
public import QPainleve.Geometry.Toric.Fan.Mutation.Boundary
public import QPainleve.Geometry.Toric.Fan.Mutation.Evaluation
public import QPainleve.Geometry.Toric.Fan.Picard.Mutation.Basic

import QPainleve.AlgebraicGeometry.Morphisms.Modification.Birational
import QPainleve.Geometry.Toric.Fan.Mutation.OrderedBlowup
import QPainleve.Geometry.Toric.Fan.Picard.Mutation.Geometric

/-!
# The Picard marking of an ordered toric mutation

An elementary transformation at a selected center is an isomorphism of the ordered
internal blowup models. Splitting off the selected center on both sides lets us compute
pullback in the prescribed label order, including for repeated centers away from the
pivot fiber. On the same isomorphism, fixed-center evaluation satisfies the cluster
X mutation equation. The geometric comparison is the one in Gross, Hacking and Keel,
[*Birational geometry of cluster algebras*, §3.1 and Theorem 5.6][GHK].

[GHK]: https://arxiv.org/html/1309.2573v2#S3.SS1
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module Multiplicative PointedCone
open Scheme.IdealSheafData TauCeti.AlgebraicGeometry LineBundleClass
open QPainleve.BlowupTower QPainleve.Cluster TauCeti.LaurentRing
open scoped Int

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {Φ : Fan i} (b : Basis (Fin 2) ℤ N)

section Mutation

variable {n : ℕ} (hΦ : Φ.IsRegular) (s : Fin (n + 1) → Φ.Ray)
  (χ : Multiplicative (Fin (n + 1) → ℤ) →* ℂˣ) (k : Fin (n + 1))
  (hOpp : hull ℝ {i (-(s k).primitiveGenerator)} ∈ Φ.cones)

local notation "d" => fun j : Fin (n + 1) ↦ χ (ofAdd (Pi.single j 1))
local notation "ω" => LinearEquiv.toLinearMap (Basis.detDualEquiv b)
local notation "ε" => chargeExchangeMatrix ω (rayChargeMap s)
local notation "χ′" => MonoidHom.comp χ (AddMonoidHom.toMultiplicative
  (AddEquiv.toAddMonoidHom (LinearEquiv.toAddEquiv (chargeMutationEquiv ε k))))
local notation "ρ" => s k
local notation "c" => (d) k
local notation "v" => Ray.primitiveGenerator (ρ)
local notation "hv" => Ray.primitiveGenerator_ne_zero (ρ)
local notation "hp" => Ray.hull_primitiveGenerator_mem (ρ)
local notation "Ψ" => Φ.mutationFan b hv hp hOpp
local notation "r" => Φ.mutationFanRayEquiv b hv hp hOpp
local notation "hΦ₀" => Nonempty.intro (Ray.toCone Φ (ρ))
local notation "hΨ₀" => Nonempty.intro (Φ.mutationFanConeEquiv b hv hp hOpp (Subtype.mk _ hp))
local notation "hΨ" => Iff.mpr (Φ.isRegular_mutationFan_iff b hv hp hOpp) hΦ
local notation "I₀" => Ray.mutationSourceCenterIdeal b (ρ) (c)
local notation "I₁" => Ray.mutationTargetCenterIdeal b (ρ) hOpp (c)
local notation "j₀" => Ray.mutationSourceBoundaryι b (ρ) (c)
local notation "j₁" => Ray.mutationTargetBoundaryι b (ρ) hOpp (c)
local notation "G" => Ray.mutationBlowupIso b (ρ) hOpp (c)
local notation "t" => Φ.mutationFanCenterRays b s k hOpp
local notation "d′" => fun j : Fin (n + 1) ↦ (χ′) (ofAdd (Pi.single j 1))
local notation "A" => internalBlowupTower (h₀ := hΦ₀) b s (d)
local notation "B" => internalBlowupTower (h₀ := hΨ₀) b (t) (d′)
local notation "A₁" => alongBoundary (j₀)
  (fun l ↦ Ray.internalCenter (h₀ := hΦ₀) b (s (Fin.succAbove k l)) ((d) (Fin.succAbove k l)))
local notation "B₁" => alongBoundary (j₁)
  (fun l ↦ Ray.internalCenter (h₀ := hΨ₀) b (t (Fin.succAbove k l)) (d′ (Fin.succAbove k l)))

private theorem mutated_parameter_of_ne {j : Fin (n + 1)} (hj : j ≠ k) :
    d′ j = d j * c ^ max (b.det ![(s j).primitiveGenerator, v]) 0 := by
  have hω : (ω : LinearMap.BilinForm ℤ N).IsAlt := b.detDualEquiv_self
  simpa only [posPart_def, chargeExchangeMatrix_apply, rayChargeMap_single,
    LinearEquiv.coe_coe, Basis.detDualEquiv_apply] using
    centerMutation_character_apply_of_ne (ω) (rayChargeMap s) k ℂ hω χ hj

include hOpp in
private theorem exists_iso_mutation_tail
    (hsame : ∀ j, j ≠ k → (s j).primitiveGenerator = v → (d) j ≠ c)
    (hopp : ∀ j, j ≠ k → (s j).primitiveGenerator = -v → (d) j * c ≠ 1) :
    ∃ g : (A₁).1 ≅ (B₁).1, IsLift (G) (A₁).2.toTower (B₁).2.toTower g := by
  have htail (l : Fin n) : k.succAbove l ≠ k := Fin.succAbove_ne _ _
  have ht : (fun l : Fin n ↦ (t (k.succAbove l)).internalCenter (h₀ := hΨ₀) b
      (d′ (k.succAbove l))) =
      fun l ↦ (r (s (k.succAbove l))).internalCenter (h₀ := hΨ₀) b
        ((d) (k.succAbove l) *
          (c) ^ max (b.det ![(s (k.succAbove l)).primitiveGenerator, v]) 0) := by
    funext l
    rw [mutationFanCenterRays_of_ne _ _ _ _ _ (htail l), mutated_parameter_of_ne b s χ k (htail l)]
  rw [ht]
  obtain ⟨g, hg, -⟩ := exists_iso_mutation_internal_blowup_tower b (ρ) hOpp (c)
    (s ∘ k.succAbove) ((d) ∘ k.succAbove)
    (fun l ↦ hsame _ (htail l)) (fun l ↦ hopp _ (htail l))
  exact ⟨g, hg⟩

include hOpp in
private theorem mutation_center_ne_pivot
    (hopp : ∀ j, j ≠ k → (s j).primitiveGenerator = -v → (d) j * c ≠ 1)
    {l : Fin (n + 1)} (hl : l ≠ k) : (t l, d′ l) ≠ (t k, d′ k) := by
  intro h
  have hray := (mutationFanCenterRays_eq_pivot_iff _ _ _ _ _ hl).mp (congrArg Prod.fst h)
  have hp' : b.det ![(s l).primitiveGenerator, v] = 0 := by
    rw [hray, ← b.detDualEquiv_apply, map_neg, LinearMap.neg_apply, b.detDualEquiv_self, neg_zero]
  have hd : d′ l = d′ k := congrArg Prod.snd h
  simp only [mutated_parameter_of_ne b s χ k hl, centerMutation_character_apply_self,
    hp', max_self, zpow_zero, mul_one] at hd
  exact hopp l hl hray (by simp only [hd, inv_mul_cancel])

include hOpp in
private theorem mutation_target_center :
    ((t k).internalCenter (h₀ := hΨ₀) b (d′ k)).val.map
      (boundaryIdeal (Ψ) hΨ₀).subschemeι = I₁ := by
  simp only [centerMutation_character_apply_self, Ray.map_internalCenter_subschemeι,
    Ray.mutationTargetCenterIdeal_eq,
    mutationFanCenterRays_self]

include hOpp in
private theorem pullback_picardHom_mutation_tail {g : (A₁).1 ≅ (B₁).1}
    (hg : IsLift (G) (A₁).2.toTower (B₁).2.toTower g)
    (a : Additive (LineBundleClass (Ψ).algebraicRealization) × (Fin (n + 1) → ℤ)) :
    let a₀ := mutationPicardEquiv b s k hOpp hΦ a
    pullback g.hom ((B₁).2.toTower.picardHom
      ((nil.snoc (I₁)).picardHom (a.1, fun _ ↦ a.2 k), a.2 ∘ k.succAbove)).toMul =
      ((A₁).2.toTower.picardHom
        ((nil.snoc (I₀)).picardHom (a₀.1, fun _ ↦ a₀.2 k), a₀.2 ∘ k.succAbove)).toMul := by
  obtain ⟨hpivot, hrest⟩ := mutationPicardEquiv_pivot_split b s k hOpp hΦ a
  dsimp only
  rw [hg.pullback_picardHom,
    Ray.pullback_mutationBlowupIso_picardHom b (ρ) hOpp (c) hΦ, ofMul_toMul, hpivot]
  exact congrArg (fun x ↦ ((A₁).2.toTower.picardHom (_, x)).toMul)
    (funext fun l ↦ (hrest _ (Fin.succAbove_ne _ _)).symm)

local notation "πA" => QPainleve.BlowupTower.toBase (WithBoundary.toTower (Sigma.snd (A)))
local notation "πB" => QPainleve.BlowupTower.toBase (WithBoundary.toTower (Sigma.snd (B)))
local notation "M" => xMutationChartEquiv ℂ k (fun j ↦ ε j k)

/-- The isomorphism over `ℂ` for mutation at a specified center pulls back the full marked
Picard group by `mutationPicardEquiv`. Both markings use the original label order.
The projection to the source pivot blowup and its transport through the elementary
transformation recover the two toric projections. Fixed-center X evaluation satisfies
the X mutation equation on the localized chart. Other centers may repeat away from
the pivot fiber. -/
theorem exists_iso_ordered_mutation_picard_marking
    (hsame : ∀ j, j ≠ k → (s j).primitiveGenerator = v → (d) j ≠ c)
    (hopp : ∀ j, j ≠ k → (s j).primitiveGenerator = -v → (d) j * c ≠ 1) :
    letI : Nonempty Φ.cones := hΦ₀
    letI : Nonempty (Ψ).cones := hΨ₀
    letI := isIntegral_internalBlowupTower b s (d) hΦ
    letI := isModification_internalBlowupTower_toBase b s (d) hΦ
    letI := isModification_internalBlowupTower_toBase b (t) (d′) (hΨ)
    ∃ (e : (A).1 ≅ (B).1) (f : (A).1 ⟶ (I₀).blowup),
      f ≫ (I₀).blowupToBase = (A).2.toTower.toBase ∧
      e.hom ≫ (B).2.toTower.toBase = f ≫ (G).hom ≫ (I₁).blowupToBase ∧
      e.hom ≫ πB ≫ (Ψ).algebraicRealizationStructureMap =
        πA ≫ Φ.algebraicRealizationStructureMap ∧
      (∀ a, pullback e.hom (internalBlowupPicardMarking b (t) (d′) (hΨ) a).toMul =
        (internalBlowupPicardMarking b s (d) hΦ (mutationPicardEquiv b s k hOpp hΦ a)).toMul) ∧
      (e.hom ≫ πB).toRationalMap.comp ((Ψ).xEvaluation b (t) (χ′)) =
        (((πA).toRationalMap.comp (Φ.mutationChartEvaluation b s k χ)).compHom
          (Spec.map (CommRingCat.ofHom (M).toAlgHom.toRingHom))).compHom
            (Spec.algebraMap (LaurentRing ℂ (Fin (n + 1))) (XMutationChart ℂ k)) := by
  let : Nonempty Φ.cones := hΦ₀
  let : Nonempty (Ψ).cones := hΨ₀
  let := isIntegral_internalBlowupTower b s (d) hΦ
  let := isModification_internalBlowupTower_toBase b s (d) hΦ
  let := isModification_internalBlowupTower_toBase b (t) (d′) (hΨ)
  have hsource (l : Fin (n + 1)) (hl : l < k) : (s l, (d) l) ≠ (s k, c) := by
    intro h
    exact hsame l hl.ne (congrArg (Ray.primitiveGenerator ∘ Prod.fst) h) (congrArg Prod.snd h)
  have hI₀ : ((ρ).internalCenter (h₀ := hΦ₀) b (c)).val.map
      (boundaryIdeal Φ hΦ₀).subschemeι = I₀ := by
    rw [Ray.mutationSourceCenterIdeal_eq, Ray.map_internalCenter_subschemeι]
  obtain ⟨e₀, hπ₀, -, hm₀⟩ := exists_iso_internalBlowupTower_split_at b s (d) k hsource hI₀
    ((ρ).mutationSourceBoundaryι_blowupToBase b (c))
  obtain ⟨e₁, hπ₁, -, hm₁⟩ := exists_iso_internalBlowupTower_split_at b (t) (d′) k
    (fun l hl ↦ mutation_center_ne_pivot b s χ k hOpp hopp hl.ne)
    (mutation_target_center b s χ k hOpp) ((ρ).mutationTargetBoundaryι_blowupToBase b hOpp (c))
  obtain ⟨g, hg⟩ := exists_iso_mutation_tail b s χ k hOpp hsame hopp
  let e := e₀ ≪≫ g ≪≫ e₁.symm
  let f := e₀.hom ≫ (A₁).2.toTower.toBase
  have hf : f ≫ (I₀).blowupToBase = πA := by simpa only [f, Category.assoc] using hπ₀
  have he : e.hom ≫ πB = f ≫ (G).hom ≫ (I₁).blowupToBase := by
    simp only [e, f, Iso.trans_hom, Iso.symm_hom, Category.assoc, ← hπ₁,
      Iso.inv_hom_id_assoc, hg.hom_toBase_assoc]
  refine ⟨e, f, hf, he, ?_, ?_, ?_⟩
  · rw [← Category.assoc, he]
    simpa only [Category.assoc, ← hf] using
      congrArg (f ≫ ·) ((ρ).mutationBlowupIso_hom_comp_toBase b hOpp (c))
  · intro a
    simp only [internalBlowupPicardMarking_apply]
    rw [← hm₁ a.1 a.2, pullback_comp]
    simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← pullback_comp, pullback_picardHom_mutation_tail b hΦ s χ k hOpp hg, hm₀]
  · have := (ρ).isModification_mutationSourceBlowupToBase b hOpp (c)
    have : IsDominant (f ≫ (I₀).blowupToBase) := hf ▸ inferInstanceAs (IsDominant (πA))
    have : IsDominant f := IsModification.isDominant_of_comp f (I₀).blowupToBase
    simpa only [hf, ← he] using Φ.mutationBlowupIso_xEvaluation b s k χ hOpp f

/-- A map of the ordered models restricts to the pivot boundary isomorphism
when its projections satisfy the elementary transformation square. This applies
to the same isomorphism used for the full Picard and X-evaluation comparisons. -/
@[reassoc]
theorem boundaryι_comp_of_ordered_mutation
    {g : (A).1 ⟶ (B).1} {f : (A).1 ⟶ (I₀).blowup}
    (hf : f ≫ (I₀).blowupToBase = πA)
    (hg : g ≫ πB = f ≫ (G).hom ≫ (I₁).blowupToBase) :
    (A).2.boundaryι ≫ g =
      (Ray.mutationBoundaryIso b (ρ) hOpp (c) hΦ).hom ≫ (B).2.boundaryι := by
  let : Nonempty Φ.cones := hΦ₀
  let : Nonempty (Ψ).cones := hΨ₀
  let a := (Ray.mutationBoundaryIso b (ρ) hOpp (c) hΦ).hom
  have hA : (A).2.boundaryι ≫ f = (j₀) := by
    apply (I₀).blowup_hom_ext
    · simp only [Category.assoc, hf, WithBoundary.boundaryι_toBase,
        Ray.mutationSourceBoundaryι_blowupToBase]
    · rw [Category.assoc, hf, WithBoundary.boundaryι_toBase, Ray.mutationSourceCenterIdeal_eq,
        ← Ray.map_internalCenter_subschemeι, comap_map_of_isClosedImmersion]
      exact ((ρ).internalCenter (h₀ := hΦ₀) b (c)).property
  let j := (boundaryIdeal (Ψ) hΨ₀).subschemeι
  have hB : ((A).2.boundaryι ≫ g) ≫ πB = a ≫ j := by
    rw [Category.assoc, hg, ← Category.assoc (A).2.boundaryι f, hA,
      ← Ray.mutationBoundaryIso_hom_comp_boundaryι_assoc,
      Ray.mutationTargetBoundaryι_blowupToBase]
  let P (U : Σ Z, WithBoundary j (n + 1) Z) :=
    ∀ p : (boundaryIdeal Φ hΦ₀).subscheme ⟶ U.1,
      p ≫ U.2.toTower.toBase = a ≫ j → p = a ≫ U.2.boundaryι
  suffices P (B) from this _ hB
  rw [internalBlowupTower_eq_alongBoundary]
  intro p hproj
  exact eq_comp_boundaryι_of_comp_toBase_eq j _ a (fun l ↦
    ((t l).internalCenter (h₀ := hΨ₀) b (d′ l)).property.comap a) p hproj

end Mutation

end TauCeti.Toric.Fan
