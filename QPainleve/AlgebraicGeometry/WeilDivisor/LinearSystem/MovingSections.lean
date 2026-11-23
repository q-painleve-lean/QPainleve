/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.CartierDivisor.SectionDivision
public import QPainleve.AlgebraicGeometry.WeilDivisor.IdealSheaf
public import QPainleve.AlgebraicGeometry.WeilDivisor.LinearSystem.FixedPart

/-!
# Sections of the moving part of a linear system

Removing the fixed divisor from the zero divisors of a nonempty family of sections
gives the zero divisors of the divided sections in the Cartier twist. This supplies
actual sections for the moving linear system used in base-point resolution.

## References

* P. Hacking, *583C Lecture notes*, §7.2 and Proposition 7.3.
-/

public section

open AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.SchemeWeilDivisor

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]

attribute [local instance] IsNormalScheme.of_uniqueFactorizationMonoid_stalk

/-- Dividing a section by a contained effective Weil divisor subtracts that divisor
from its zero divisor. The divided section belongs to the canonical Cartier twist. -/
theorem exists_idealTwist_section_toWeilDivisor_eq_sub
    (L : InvertibleSheaf X) {s : Γ(L.obj, ⊤)} (hs : s ≠ 0)
    (F : SchemeWeilDivisor X) (hF : 0 ≤ F) (hFD : F ≤ (L.zeroDivisor hs).toWeilDivisor) :
    let hI := F.isEffectiveCartier_idealSheaf hF
    let M := hI.toInvertibleSheaf.tensorProduct L
    ∃ (t : Γ(M.obj, ⊤)) (ht : t ≠ 0),
      (L.idealTwistInclusion hI).app ⊤ t = s ∧
        (M.zeroDivisor ht).toWeilDivisor = (L.zeroDivisor hs).toWeilDivisor - F := by
  intro hI M
  let D := (L.zeroDivisor hs).toWeilDivisor
  let B := D - F
  have hB : 0 ≤ B := sub_nonneg.mpr hFD
  have hBF : B + F = D := sub_add_cancel D F
  have hOld : (B + F).idealSheaf (add_nonneg hB hF) = L.zeroIdeal s := by
    have hD := (Scheme.CartierDivisor.isEffective_iff_toWeilDivisor_nonneg _).mp
      (L.isEffective_zeroDivisor hs)
    have h : D.idealSheaf hD = L.zeroIdeal s :=
      (idealSheaf_toWeilDivisor (L.isEffective_zeroDivisor hs)).trans
        (L.idealSheaf_zeroDivisor hs)
    exact (show ∀ D' (hD' : 0 ≤ D'), D' = D → D'.idealSheaf hD' = L.zeroIdeal s from
      fun D' hD' he ↦ by subst D'; exact h) _ _ hBF
  rw [idealSheaf_add B F hB hF] at hOld
  obtain ⟨t, ht, -⟩ := (L.existsUnique_idealTwist_section_iff hI s).mpr
    (hOld ▸ fun _ ↦ Ideal.mul_le_right)
  have htn : t ≠ 0 := fun h ↦ hs (by rw [← ht, h, map_zero])
  refine ⟨t, htn, ht, ?_⟩
  have he := L.zeroIdeal_idealTwistInclusion hI t
  rw [ht, ← hOld] at he
  have hzero : M.zeroIdeal t = B.idealSheaf hB :=
    hI.mul_left_cancel (by simpa only [mul_comm] using he.symm)
  let hT := (Scheme.CartierDivisor.isEffective_iff_toWeilDivisor_nonneg _).mp
    (M.isEffective_zeroDivisor htn)
  have hIdeal : (M.zeroDivisor htn).toWeilDivisor.idealSheaf hT = B.idealSheaf hB :=
    (idealSheaf_toWeilDivisor (M.isEffective_zeroDivisor htn)).trans
      ((M.idealSheaf_zeroDivisor htn).trans hzero)
  apply equivCartierDivisorOfUniqueFactorizationMonoid.injective
  rw [← toCartierDivisor_idealSheaf _ hT, ← toCartierDivisor_idealSheaf B hB]
  exact ((isEffectiveCartier_idealSheaf _ hT).toCartierDivisor_eq_iff
    (isEffectiveCartier_idealSheaf B hB)).mpr hIdeal

/-- The moving part of a nonempty family of nonzero sections is the family cut out by
the corresponding divided sections, with the original indexing preserved. -/
theorem exists_sections_movingPart
    (L : InvertibleSheaf X) {ι : Type*} [Nonempty ι]
    (s : ι → Γ(L.obj, ⊤)) (hs : ∀ i, s i ≠ 0) :
    let D i := (L.zeroDivisor (hs i)).toWeilDivisor
    let S := Set.range D
    let hS : ∀ E ∈ S, 0 ≤ E := fun _ ⟨i, hi⟩ ↦ hi ▸
      (Scheme.CartierDivisor.isEffective_iff_toWeilDivisor_nonneg _).mp
        (L.isEffective_zeroDivisor (hs i))
    let hn := Set.range_nonempty (f := D)
    let F : SchemeWeilDivisor X := WeilDivisor.fixedPart S hn hS
    let hI := F.isEffectiveCartier_idealSheaf (WeilDivisor.fixedPart_nonneg hn hS)
    let M := hI.toInvertibleSheaf.tensorProduct L
    ∃ (t : ι → Γ(M.obj, ⊤)) (ht : ∀ i, t i ≠ 0),
      (∀ i, (L.idealTwistInclusion hI).app ⊤ (t i) = s i) ∧
        Set.range (fun i ↦ (M.zeroDivisor (ht i)).toWeilDivisor) =
          WeilDivisor.movingPart S hn hS := by
  intro D S hS hn F hI M
  have hFD (i : ι) : F ≤ D i := (WeilDivisor.isGLB_fixedPart hn hS).1 (Set.mem_range_self i)
  choose t ht hs' hD using fun i ↦
    exists_idealTwist_section_toWeilDivisor_eq_sub L (hs i) F
      (WeilDivisor.fixedPart_nonneg hn hS) (hFD i)
  refine ⟨t, ht, hs', ?_⟩
  have h (i : ι) : (M.zeroDivisor (ht i)).toWeilDivisor = D i - F := hD i
  ext E
  rw [WeilDivisor.mem_movingPart_iff]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, (sub_add_cancel (D i) F).symm.trans (congrArg (· + F) (h i).symm)⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, (h i).trans (sub_eq_iff_eq_add.mpr hi)⟩

end TauCeti.AlgebraicGeometry.SchemeWeilDivisor
