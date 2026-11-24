/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.InternalBlowup
public import QPainleve.Geometry.Toric.Fan.Mutation.Resolution

import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.IsoLocus
import QPainleve.AlgebraicGeometry.RationalMap.Restriction
import QPainleve.Geometry.Toric.Fan.Separated
import TauCeti.AlgebraicGeometry.Blowup.Restriction

/-!
# The base point of a toric elementary transformation

The source pivot is precisely the indeterminacy locus of the rational map resolved
by the pivot blowup isomorphism. Its exceptional fiber contains points with distinct
images on the target surface, whereas off the pivot the source projection is an
isomorphism. Therefore any resolution of this specified map has the pivot in its
centre.

See Gross, Hacking and Keel, [*Birational geometry of cluster algebras*][GHK],
Lemma 3.2 and Remark 3.3.

[GHK]: https://arxiv.org/html/1309.2573v2#S3.SS1
-/

public section

open AlgebraicGeometry CategoryTheory Module PointedCone TopologicalSpace
open Scheme.IdealSheafData TauCeti.AlgebraicGeometry
open QPainleve.BlowupTower

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (ρ : Φ.Ray)
  (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones) (c : ℂˣ)

local notation "v" => ρ.primitiveGenerator
local notation "hv" => Ray.primitiveGenerator_ne_zero ρ
local notation "hp" => Ray.hull_primitiveGenerator_mem ρ
local notation "Ψ" => Φ.mutationFan b hv hp hOpp
local notation "X" => Φ.algebraicRealization
local notation "Y" => Fan.algebraicRealization Ψ
local notation "J₀" => Ray.mutationSourceCenterIdeal b ρ c
local notation "J₁" => Ray.mutationTargetCenterIdeal b ρ hOpp c
local notation "π" => Scheme.IdealSheafData.blowupToBase J₀
local notation "E" => Ray.mutationBlowupIso b ρ hOpp c
local notation "g" => CategoryTheory.Iso.hom E ≫ Scheme.IdealSheafData.blowupToBase J₁
local notation "hdim" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "s" => ρ.binomialCenter hdim (b.detDualEquiv_self v) (ρ.surjective_detCharacter b) c
local notation "p" => (s) (IsLocalRing.closedPoint ℂ)
local notation "q" =>
  Scheme.PartialMap.toRationalMap (Fan.mutationPartialMap Φ b (c : ℂ) hv hp hOpp)

private theorem sourceCenter_range : Set.range (s) = {p} :=
  Set.range_eq_singleton fun x ↦ congrArg (s) (Subsingleton.elim x _)

private theorem sourceCenter_support :
    ((J₀).support : Set X) = {p} := by
  rw [Ray.mutationSourceCenterIdeal_eq, (s).support_ker,
    (s).isClosedEmbedding.isClosed_range.closure_eq]
  exact sourceCenter_range b ρ c

private theorem exists_lifts_mutationSourceCenter :
    ∃ a a' : Spec (.of ℂ) ⟶ (J₀).blowup,
      a ≫ (π) = s ∧ a ≫ (π) = a' ≫ (π) ∧ a ≫ (g) ≠ a' ≫ (g) := by
  obtain ⟨a, a', ha, hsame, hdiff⟩ := ρ.exists_lifts_mutationPivotSource b hOpp c
  let j := ρ.mutationPivotSourceBlowupι b hOpp c
  refine ⟨a ≫ j, a' ≫ j, ?_, ?_, ?_⟩
  · simpa only [j, Category.assoc, Ray.mutationPivotSourceBlowupι_blowupToBase] using ha
  · simp only [j, Category.assoc, Ray.mutationPivotSourceBlowupι_blowupToBase]
    exact (reassoc_of% hsame) _
  · intro he
    apply hdiff
    rw [← cancel_mono (Limits.pullback.fst
      ((Ψ).characterRuling (LinearMap.toAddMonoidHom (b.detDualEquiv v))
        (mutationDetCharacter_nonneg_or_nonpos Φ b hv hp hOpp)) projectiveLineTorusι)]
    simpa only [j, Category.assoc, Ray.mutationPivotSourceBlowupι_comp_mutationBlowupIso_hom_assoc,
      Ray.mutationPivotTargetBlowupι_blowupToBase] using he

/-- The original pivot center is an actual base point of the toric elementary
transformation. -/
theorem Ray.mutationSourceCenter_notMem_domain : p ∉ (q).domain := by
  intro h
  let : Nonempty Φ.cones := ⟨ρ.toCone⟩
  let : IsIntegral (J₀).blowup := ρ.isIntegral_mutationSourceBlowup b hOpp c
  let : IsModification (π) := ρ.isModification_mutationSourceBlowupToBase b hOpp c
  let : Scheme.IsSeparated Y := (Ψ).isSeparated_algebraicRealization
  obtain ⟨a, a', hsource, hproj, hdiff⟩ := exists_lifts_mutationSourceCenter b ρ hOpp c
  have hrange : Set.range (a ≫ (π)) ⊆ (q).domain := by
    rwa [hsource, sourceCenter_range b ρ c, Set.singleton_subset_iff]
  exact hdiff ((q).resolvingHom_eq_of_comp_eq (π) (g)
    (ρ.mutationPartialMap_resolved b hOpp c).symm hproj hrange)

/-- The entire domain of the toric elementary transformation is the complement of
the source pivot center. -/
theorem Ray.domain_eq_compl_mutationSourceCenter :
    (q).domain = (J₀).support.compl := by
  let : Nonempty Φ.cones := ⟨ρ.toCone⟩
  let : IsIntegral (J₀).blowup := ρ.isIntegral_mutationSourceBlowup b hOpp c
  let : IsModification (π) := ρ.isModification_mutationSourceBlowupToBase b hOpp c
  let : IsIso ((π) ∣_ (J₀).support.compl) :=
    (J₀).isIso_blowupToBase_restrict_compl_support
  have hlower : (J₀).support.compl ≤ (q).domain :=
    (q).le_domain_of_isIso_morphismRestrict (π) (g)
      (ρ.mutationPartialMap_resolved b hOpp c).symm (J₀).support.compl
  refine le_antisymm ?_ hlower
  intro x hx
  rw [← SetLike.mem_coe, Closeds.coe_compl, sourceCenter_support b ρ c,
    Set.mem_compl_iff, Set.mem_singleton_iff]
  rintro rfl
  exact ρ.mutationSourceCenter_notMem_domain b hOpp c hx

/-- The original pivot center belongs to the centre of every dominant morphism
from an integral scheme that resolves the toric elementary transformation. -/
theorem Ray.mutationSourceCenter_mem_centre_of_resolves {W : Scheme} [IsIntegral W]
    (f : W ⟶ X) [IsDominant f] (r : W ⟶ Y)
    (hr : letI : Nonempty Φ.cones := ⟨ρ.toCone⟩
      f.toRationalMap.comp q = r.toRationalMap) :
    p ∈ f.centre := by
  let : Nonempty Φ.cones := ⟨ρ.toCone⟩
  rw [f.centre_def, Set.mem_compl_iff, SetLike.mem_coe]
  exact fun hp' ↦ ρ.mutationSourceCenter_notMem_domain b hOpp c
    ((q).le_domain_of_isIso_morphismRestrict f r hr.symm f.isoLocus hp')

section Ordered

variable [Nonempty Φ.cones] {n : ℕ} (rays : Fin n → Φ.Ray) (parameters : Fin n → ℂˣ)

local notation "D" => Φ.boundaryIdeal inferInstance
local notation "M" => internalBlowupTower b rays parameters
local notation "F" =>
  QPainleve.BlowupTower.toBase (QPainleve.BlowupTower.WithBoundary.toTower (Sigma.snd M))

/-- If the specified elementary transformation becomes regular after the ordered
internal blowups, there is a first occurrence of the pivot ray and its parameter
among the prescribed centers. Repeated centers are allowed. -/
theorem Ray.exists_first_internalBlowupTower_center_of_resolves
    [IsIntegral (M).1] [IsDominant (F)] (r : (M).1 ⟶ Y)
    (hr : (F).toRationalMap.comp q = r.toRationalMap) :
    ∃ k, rays k = ρ ∧ parameters k = c ∧ ∀ j < k, (rays j, parameters j) ≠ (ρ, c) := by
  let J (j : Fin n) := (rays j).internalCenter b (parameters j)
  have hp' := ρ.mutationSourceCenter_mem_centre_of_resolves b hOpp c (F) r hr
  rw [internalBlowupTower_eq_alongBoundary] at hp'
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp
    (centre_subset_iUnion_alongBoundary (D).subschemeι J hp')
  have hcenter : p ∈ (((ρ.internalCenter b c).val.map (D).subschemeι).support : Set X) := by
    rw [Ray.map_internalCenter_subschemeι, ← Ray.mutationSourceCenterIdeal_eq,
      sourceCenter_support b ρ c]
    exact Set.mem_singleton _
  have hnd : ¬ Disjoint (((J j).val.map (D).subschemeι).support : Set X)
      (((ρ.internalCenter b c).val.map (D).subschemeι).support : Set X) :=
    fun h ↦ Set.disjoint_left.mp h hj hcenter
  have hdisjoint := disjoint_support_map_internalCenter_iff b (D).subschemeι
    (rays j) ρ (parameters j) c
  have he := not_ne_iff.mp (hdisjoint.not.mp hnd)
  let pivots : Set (Fin n) := {k | (rays k, parameters k) = (ρ, c)}
  obtain ⟨k, hk, hmin⟩ := Set.exists_min_image pivots id (Set.toFinite pivots) ⟨j, he⟩
  exact ⟨k, congrArg Prod.fst hk, congrArg Prod.snd hk,
    fun l hl hlp ↦ (not_le_of_gt hl) (hmin l hlp)⟩

end Ordered

end TauCeti.Toric.Fan
