/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Modules.Differentials.Canonical
public import QPainleve.Geometry.Toric.Fan.Boundary.SelfIntersection
public import QPainleve.Geometry.Toric.Fan.Smooth

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
import QPainleve.Geometry.Toric.Fan.Boundary.ProjectiveLine
import QPainleve.Geometry.Toric.Fan.Rationality
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveLine.Basic

/-!
# Picard coordinates of a Hirzebruch fan

For the four rays of a Hirzebruch fan, the fiber ray and the section of
self-intersection `-e` give an integral basis of the Picard group of the toric
surface. These are the coordinates used for the Sarkisov degree in Lutz's
appendix to Hacking and Keating, [*Homological mirror symmetry for log
Calabi–Yau surfaces*, Definition 8.5](https://arxiv.org/abs/2005.05010v3).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module
open TauCeti.AlgebraicGeometry (LineBundleClass InvertibleSheaf projectiveLine)
open TauCeti.AlgebraicGeometry.Chow

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (e : ℕ)

open Classical in
/-- The four primitive generators in Hirzebruch normal form give an indexing
of the rays by `Fin 4`. -/
theorem exists_rayEquiv_of_hirzebruch_ray_generators
    (h : Set.range (Ray.primitiveGenerator (Phi := Φ)) =
      {b 0, b 1, -b 0, (e : ℤ) • b 0 - b 1}) :
    ∃ r : Fin 4 ≃ Φ.Ray,
      (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (e : ℤ) • b 0 - b 1] := by
  let v : Fin 4 → N := ![b 0, b 1, -b 0, (e : ℤ) • b 0 - b 1]
  have hv : Set.range v = Set.range (Ray.primitiveGenerator (Phi := Φ)) := by
    rw [h]
    ext x
    simp [v, or_comm, or_left_comm, or_assoc]
  have hinj : Function.Injective v := by
    intro j k hjk
    have h₀ := congrArg (b.coord 0) hjk
    have h₁ := congrArg (b.coord 1) hjk
    fin_cases j <;> fin_cases k <;> norm_num [v, Basis.coord_apply] at *
  let rays := Equiv.ofInjective _ (Ray.primitiveGenerator_injective (Φ := Φ))
  let vectors := (Equiv.ofInjective v hinj).trans (Set.equivOfEq hv)
  refine ⟨vectors.trans rays.symm, funext fun j ↦ ?_⟩
  exact congrArg Subtype.val (rays.apply_symm_apply (vectors j))

variable [Nonempty Φ.cones] (hΦ : Φ.IsRegular) (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (e : ℤ) • b 0 - b 1])

local notation "X" => Φ.algebraicRealization
local notation "Pic" => Additive (LineBundleClass X)
local notation "R" => Φ.rayDivisorToPicard hΦ
local notation "D" j:arg => R (Pi.single (r j) 1)

include hr in
open Classical in
private theorem hirzebruch_character_relation (m : N →+ ℤ) :
    m (b 0) • D 0 + m (b 1) • D 1 + (-m (b 0)) • D 2 +
      ((e : ℤ) * m (b 0) - m (b 1)) • D 3 = 0 := by
  let := Fintype.ofFinite Φ.Ray
  have h := (Φ.exact_characterToRayDivisor_rayDivisorToPicard hΦ _).mpr ⟨m, rfl⟩
  have hsum (a : Φ.Ray → ℤ) : R a = ∑ j : Fin 4, a (r j) • D j := by
    rw [Φ.rayDivisorToPicard_apply hΦ a, ← r.sum_comp]
    simp only [rayDivisorToPicard_single, one_zsmul]
  rw [hsum, Fin.sum_univ_four] at h
  simpa [congrFun hr, ← rayDivisorToPicard_single] using h

include hr in
open Classical in
private theorem hirzebruch_ray_classes :
    D 2 = D 0 + (e : ℤ) • D 1 ∧ D 3 = D 1 := by
  have h₀ := hirzebruch_character_relation b e hΦ r hr (b.coord 0).toAddMonoidHom
  have h₁ := hirzebruch_character_relation b e hΦ r hr (b.coord 1).toAddMonoidHom
  have h₃ : D 3 = D 1 := by
    apply (sub_eq_zero.mp _).symm
    simpa [Basis.coord_apply, sub_eq_add_neg, ← rayDivisorToPicard_single] using h₁
  rw [h₃] at h₀
  have h : D 0 + (-1 : ℤ) • D 2 + (e : ℤ) • D 1 = 0 := by
    simpa [Basis.coord_apply, ← rayDivisorToPicard_single] using h₀
  refine ⟨(sub_eq_zero.mp ?_).symm, h₃⟩
  rw [← h]
  simp only [neg_one_zsmul]
  abel

open Classical in
/-- In a regular Hirzebruch fan the ray classes for `b 1` and `b 0`, in that order,
are an integral Picard basis. -/
def hirzebruchPicardBasis : Basis (Fin 2) ℤ Pic := by
  let v : Fin 2 → Pic := ![D 1, D 0]
  refine Basis.mk (v := v) ?_ ?_
  · rw [Fintype.linearIndependent_iff]
    intro a ha j
    let q : Φ.Ray → ℤ := Pi.single (r 1) (a 0) + Pi.single (r 0) (a 1)
    have hq : R q = 0 := by
      simpa [q, v, Fin.sum_univ_two, rayDivisorToPicard_single] using ha
    obtain ⟨m, hm⟩ := (Φ.exact_characterToRayDivisor_rayDivisorToPicard hΦ _).mp hq
    have he (k : Fin 4) : m ((r k).primitiveGenerator) = q (r k) := by
      simpa only [characterToRayDivisor_apply] using congrFun hm (r k)
    have h₂ : m (b 0) = 0 := by
      simpa [q, congrFun hr, Equiv.apply_eq_iff_eq] using he 2
    have h₃ : m (b 1) = 0 := by
      simpa [q, congrFun hr, Equiv.apply_eq_iff_eq, h₂] using he 3
    fin_cases j
    · simpa [q, congrFun hr, Equiv.apply_eq_iff_eq, h₃] using (he 1).symm
    · simpa [q, congrFun hr, Equiv.apply_eq_iff_eq, h₂] using (he 0).symm
  · obtain ⟨h₂, h₃⟩ := hirzebruch_ray_classes b e hΦ r hr
    let W := Submodule.span ℤ (Set.range v)
    have hF : D 1 ∈ W := Submodule.subset_span ⟨0, rfl⟩
    have hB : D 0 ∈ W := Submodule.subset_span ⟨1, rfl⟩
    have hall (j : Fin 4) : D j ∈ W := by
      fin_cases j
      · exact hB
      · exact hF
      · exact h₂ ▸ W.add_mem hB (W.smul_mem _ hF)
      · exact h₃ ▸ hF
    intro x _
    obtain ⟨a, rfl⟩ := Φ.rayDivisorToPicard_surjective hΦ x
    let := Fintype.ofFinite Φ.Ray
    rw [Φ.rayDivisorToPicard_apply hΦ]
    refine W.sum_mem fun ρ _ ↦ W.smul_mem _ ?_
    simpa only [rayDivisorToPicard_single, one_smul, Equiv.apply_symm_apply] using hall (r.symm ρ)

open Classical in
/-- The first Hirzebruch Picard basis vector is the fiber ray class. -/
@[simp]
theorem hirzebruchPicardBasis_apply_zero :
    hirzebruchPicardBasis b e hΦ r hr 0 = D 1 := by
  rw [hirzebruchPicardBasis, Basis.mk_apply]
  rfl

open Classical in
/-- The second Hirzebruch Picard basis vector is the section ray class. -/
@[simp]
theorem hirzebruchPicardBasis_apply_one :
    hirzebruchPicardBasis b e hΦ r hr 1 = D 0 := by
  rw [hirzebruchPicardBasis, Basis.mk_apply]
  rfl

section Intersection

variable [Φ.algebraicRealization.IsProjectiveOver ℂ]
variable (hc : Φ.IsComplete)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "B" => intersectionBilinForm ℂ X
local notation "K" => Additive.ofMul (LineBundleClass.mk (QPainleve.canonicalBundle ℂ X 2))
local notation "C" => hirzebruchPicardBasis b e hΦ r hr
local notation "Adj[" j "," k "]" =>
  ∃ σ : Φ.cones, Ray.toCone Φ (r j) ≤ σ ∧ Ray.toCone Φ (r k) ≤ σ

omit [Nonempty Φ.cones] [Φ.algebraicRealization.IsProjectiveOver ℂ] in
include hΦ hc hr in
private theorem hirzebruch_adjacent :
    Adj[0, 1] ∧ Adj[0, 3] ∧ Adj[2, 1] := by
  obtain ⟨p, q, hp, hq, h₀⟩ := exists_ray_neighbors b hΦ hc (r 0)
  obtain ⟨p', _, hp', _, h₂⟩ := exists_ray_neighbors b hΦ hc (r 2)
  have hcoord (j : Fin 4) := congrFun hr j
  have hd : b.detDualEquiv (b 0) = b.coord 1 := by
    apply b.ext
    intro j
    fin_cases j <;> norm_num [Basis.coord_apply, -Basis.detDualEquiv_apply,
      Basis.detDualEquiv_self, Basis.detDualEquiv_apply_basis_zero_one]
  have hp₃ : p = r 3 := by
    obtain ⟨j, rfl⟩ := r.surjective p
    fin_cases j <;> first | rfl | norm_num [hcoord, hd, Basis.coord_apply] at hp
  have hq₁ : q = r 1 := by
    obtain ⟨j, rfl⟩ := r.surjective q
    fin_cases j <;> first | rfl | norm_num [hcoord, hd, Basis.coord_apply] at hq
  have hp'₁ : p' = r 1 := by
    obtain ⟨j, rfl⟩ := r.surjective p'
    fin_cases j <;> first | rfl | norm_num [hcoord, -Basis.detDualEquiv_apply, hd,
      Basis.coord_apply] at hp'
  exact ⟨((h₀ _).2 (Or.inr hq₁.symm)).2, ((h₀ _).2 (Or.inl hp₃.symm)).2,
    ((h₂ _).2 (Or.inl hp'₁.symm)).2⟩

omit [Nonempty Φ.cones] in
include hc hr in
private theorem hirzebruch_selfIntersection :
    Φ.rayBoundarySelfIntersection hΦ (r 0) = -(e : ℤ) ∧
      Φ.rayBoundarySelfIntersection hΦ (r 1) = 0 := by
  obtain ⟨h₀₁, h₀₃, h₂₁⟩ := hirzebruch_adjacent b e hΦ r hr hc
  have hcoord (j : Fin 4) := congrFun hr j
  have hd₃₀ : b.detDualEquiv (r 3).primitiveGenerator (r 0).primitiveGenerator = 1 := by
    simp [hcoord, -Module.Basis.detDualEquiv_apply, Module.Basis.detDualEquiv_self,
      Module.Basis.detDualEquiv_apply_basis_zero_one,
      Module.Basis.detDualEquiv_swap (b := b) (b 1) (b 0)]
  have hd₀₁ : b.detDualEquiv (r 0).primitiveGenerator (r 1).primitiveGenerator = 1 := by
    simp [hcoord, -Module.Basis.detDualEquiv_apply, Module.Basis.detDualEquiv_apply_basis_zero_one]
  have hd₁₂ : b.detDualEquiv (r 1).primitiveGenerator (r 2).primitiveGenerator = 1 := by
    simp [hcoord, -Module.Basis.detDualEquiv_apply, Module.Basis.detDualEquiv_apply_basis_zero_one,
      Module.Basis.detDualEquiv_swap (b := b) (b 1) (b 0)]
  have h₀ := primitiveGenerator_add_selfIntersection_smul_add_eq_zero b hΦ hc
    ⟨hd₃₀, h₀₃.imp (fun _ h ↦ h.symm)⟩ ⟨hd₀₁, h₀₁⟩
  have h₁ := primitiveGenerator_add_selfIntersection_smul_add_eq_zero b hΦ hc
    ⟨hd₀₁, h₀₁⟩ ⟨hd₁₂, h₂₁.imp (fun _ h ↦ h.symm)⟩
  have hsec := congrArg (b.coord 0) h₀
  have hfib := congrArg (b.coord 1) h₁
  have hsec' : (e : ℤ) + Φ.rayBoundarySelfIntersection hΦ (r 0) = 0 := by
    simpa [hcoord, Basis.coord_apply] using hsec
  refine ⟨by omega, ?_⟩
  simpa [hcoord, Basis.coord_apply] using hfib

include hc in
open Classical in
/-- The Hirzebruch Picard intersection matrix in the ordered fiber and section basis.
The fiber has square zero, the section has square `-e`, and they intersect once. -/
theorem hirzebruchPicardBasis_intersection (j k : Fin 2) :
    letI : SmoothOfRelativeDimension 2 (X ↘ Spec (CommRingCat.of ℂ)) :=
      (by simpa using Module.finrank_eq_card_basis b : Module.finrank ℤ N = 2) ▸
        Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    B (C j) (C k) = (!![0, 1; 1, -(e : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ) j k := by
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  let : SmoothOfRelativeDimension 2 (X ↘ Spec (CommRingCat.of ℂ)) :=
    hN ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  obtain ⟨hB, hF⟩ := hirzebruch_selfIntersection b e hΦ r hr hc
  have h₀₁ := (hirzebruch_adjacent b e hΦ r hr hc).1
  have h₁₀ : Adj[1, 0] := h₀₁.imp (fun _ h ↦ h.symm)
  fin_cases j <;> fin_cases k <;>
    simp only [Fin.zero_eta, Fin.mk_one, hirzebruchPicardBasis_apply_zero,
      hirzebruchPicardBasis_apply_one, Equiv.apply_eq_iff_eq,
      Φ.intersectionBilinForm_rayDivisorToPicard_single_single hΦ hN] <;> simp [hF, hB, h₀₁, h₁₀]

omit [Nonempty Φ.cones] [Φ.algebraicRealization.IsProjectiveOver ℂ] in
include hΦ hc hr in
private theorem isRationalOver_of_hirzebruch :
    Scheme.IsRationalOver (X ↘ S) := by
  obtain ⟨σ, h₀, h₁⟩ := (hirzebruch_adjacent b e hΦ r hr hc).1
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  have hcone := Φ.cone_eq_sup_of_ray_ne_of_le hΦ hN
    (r.injective.ne (by decide : (0 : Fin 4) ≠ 1)) h₀ h₁
  have h₀' : (r 0).primitiveGenerator = b 0 := congrFun hr 0
  have h₁' : (r 1).primitiveGenerator = b 1 := congrFun hr 1
  rw [Ray.toCone_eq_hull_primitiveGenerator, Ray.toCone_eq_hull_primitiveGenerator,
    h₀', h₁', ← Submodule.span_union] at hcone
  apply Φ.isRationalOver_of_hull_basis_mem b
  have hpair : Set.range (fun j : Fin 2 ↦ i (b j)) = {i (b 0)} ∪ {i (b 1)} := by
    ext x
    simp [Fin.exists_fin_succ, eq_comm, or_comm]
  have hcone' : σ.val = PointedCone.hull ℝ ({i (b 0)} ∪ {i (b 1)}) := hcone
  rw [hpair, ← hcone']
  exact σ.property

include hc in
open Classical in
/-- The canonical class pairs to `-2` with the fiber and to `e - 2` with the section. -/
theorem hirzebruchPicardBasis_intersection_canonical (j : Fin 2) :
    letI : SmoothOfRelativeDimension 2 (X ↘ S) :=
      (by simpa using Module.finrank_eq_card_basis b : Module.finrank ℤ N = 2) ▸
        Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    B (C j) K = ![-2, (e : ℤ) - 2] j := by
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  let : SmoothOfRelativeDimension 2 (X ↘ S) :=
    hN ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let := isRationalOver_of_hirzebruch b e hΦ r hr hc
  have hadj (ρ : Φ.Ray) :
      B (R (Pi.single ρ 1)) K = -2 - Φ.rayBoundarySelfIntersection hΦ ρ := by
    let Dρ := Φ.rayBoundaryIdeal hΦ ρ
    let m := b.detDualEquiv ρ.primitiveGenerator
    have hm : m ρ.primitiveGenerator = 0 := b.detDualEquiv_self _
    have hprim : Function.Surjective m :=
      b.surjective_detDualEquiv_of_isPrimitive ρ.isPrimitiveGenerator.isPrimitive
    let a := ρ.boundaryIsoProjectiveLine hΦ hN (m := m.toAddMonoidHom) hm hprim
    have : a.hom.IsOver S := ρ.isOver_boundaryIsoProjectiveLine_hom hΦ hN hm hprim
    have : Dρ.subscheme.IsProjectiveOver ℂ :=
      Scheme.IsProjectiveOver.of_isClosedImmersion ℂ Dρ.subschemeι
    have := Scheme.Modules.moduleFinite_cohomology_of_isProjectiveOver ℂ
      (InvertibleSheaf.trivial Dρ.subscheme).obj 1
    have hg : Dρ.subscheme.genus ℂ = (projectiveLine ℂ).genus ℂ := by
      simpa only [Scheme.genus_def] using a.hom.finrank_cohomology_trivial_of_isIso ℂ 1
    have h := two_mul_genus_sub_two_eq_intersection_primeDivisorClass ℂ (Φ.rayBoundaryPoint hΦ ρ)
    dsimp only at h
    rw [← Φ.rayBoundaryIdeal_def hΦ ρ] at h
    rw [hg, TauCeti.AlgebraicGeometry.projectiveLine.genus_eq_zero] at h
    rw [intersectionBilinForm_apply, rayDivisorToPicard_single, one_smul, toMul_ofMul,
      rayBoundarySelfIntersection_def, toMul_ofMul]
    omega
  obtain ⟨hsec, hfib⟩ := hirzebruch_selfIntersection b e hΦ r hr hc
  fin_cases j
  · simpa only [Fin.zero_eta, hirzebruchPicardBasis_apply_zero, hfib, sub_zero,
      Matrix.cons_val_zero] using hadj (r 1)
  · simpa [hirzebruchPicardBasis_apply_one, hsec, sub_neg_eq_add, add_comm, sub_eq_add_neg]
      using hadj (r 0)

end Intersection

end TauCeti.Toric.Fan
