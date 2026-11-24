/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Modules.Differentials.Canonical
public import QPainleve.Geometry.Toric.Fan.Boundary.SelfIntersection
public import QPainleve.Geometry.Toric.Fan.Hirzebruch.Corner
public import QPainleve.Geometry.Toric.Fan.Smooth

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Transvection.Basic
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
import QPainleve.Geometry.Toric.Fan.Boundary.ProjectiveLine
import QPainleve.Geometry.Toric.Fan.Rationality
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveLine.Basic

/-!
# Picard coordinates of a Hirzebruch fan

For the four rays of a Hirzebruch fan, the fiber ray and the section of
self-intersection `-e` give an integral basis of the Picard group of the toric
surface. The signed parameter `e` lets either section be used. These are the
coordinates used for the Sarkisov degree in Lutz's appendix to Hacking and
Keating, [*Homological mirror symmetry for log Calabi–Yau surfaces*][HKL],
Definition 8.5.

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module
open TauCeti.AlgebraicGeometry (LineBundleClass InvertibleSheaf projectiveLine)
open TauCeti.AlgebraicGeometry.Chow

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (e : ℤ)

variable [Nonempty Φ.cones] (hΦ : Φ.IsRegular) (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])

local notation "X" => Φ.algebraicRealization
local notation "Pic" => Additive (LineBundleClass X)
local notation "R" => Φ.rayDivisorToPicard hΦ
local notation "D" j:arg => R (Pi.single (r j) 1)

include hr in
open Classical in
private theorem hirzebruch_character_relation (m : N →+ ℤ) :
    m (b 0) • D 0 + m (b 1) • D 1 + (-m (b 0)) • D 2 +
      (e * m (b 0) - m (b 1)) • D 3 = 0 := by
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
    D 2 = D 0 + e • D 1 ∧ D 3 = D 1 := by
  have h₀ := hirzebruch_character_relation b e hΦ r hr (b.coord 0).toAddMonoidHom
  have h₁ := hirzebruch_character_relation b e hΦ r hr (b.coord 1).toAddMonoidHom
  have h₃ : D 3 = D 1 := by
    apply (sub_eq_zero.mp _).symm
    simpa [Basis.coord_apply, sub_eq_add_neg, ← rayDivisorToPicard_single] using h₁
  rw [h₃] at h₀
  have h : D 0 + (-1 : ℤ) • D 2 + e • D 1 = 0 := by
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

open Classical in
/-- The other invariant fiber of a Hirzebruch surface also represents its first
Picard basis vector. -/
theorem hirzebruchPicardBasis_apply_zero_eq_ray_three :
    hirzebruchPicardBasis b e hΦ r hr 0 = D 3 := by
  rw [hirzebruchPicardBasis_apply_zero, (hirzebruch_ray_classes b e hΦ r hr).2]

omit [Nonempty Φ.cones] in
include hr in
private theorem exists_hirzebruch_marking_swap_fibers :
    ∃ (d : Basis (Fin 2) ℤ N),
      (fun j ↦ (r (Equiv.swap 1 3 j)).primitiveGenerator) =
        ![d 0, d 1, -d 0, e • d 0 - d 1] := by
  let d := (b.map (LinearEquiv.transvection (f := (-e) • b.coord 1) (v := b 0)
    (by simp [Basis.coord_apply]))).unitsSMul (fun j ↦ if j = 1 then (-1 : ℤˣ) else 1)
  have h₀ : d 0 = b 0 := by
    simp [d, Basis.unitsSMul_apply, LinearMap.transvection.apply, Basis.coord_apply]
  have h₁ : d 1 = e • b 0 - b 1 := by
    simp [d, Basis.unitsSMul_apply, LinearMap.transvection.apply, Basis.coord_apply,
      sub_eq_add_neg, add_comm]
  refine ⟨d, funext fun j ↦ ?_⟩
  fin_cases j <;> simp [Equiv.swap_apply_def, h₀, h₁, congrFun hr]

include hr in
/-- Either invariant fiber can be placed first among the fiber rays in a
Hirzebruch marking. The section at index zero and the entire Picard basis are
unchanged, so every fiber degree and section coefficient is preserved. -/
theorem exists_hirzebruch_picardBasis_of_fiber (hΦ : Φ.IsRegular) (t : Fin 2) :
    ∃ (d : Basis (Fin 2) ℤ N) (s : Fin 4 ≃ Φ.Ray)
      (hs : (fun j ↦ (s j).primitiveGenerator) = ![d 0, d 1, -d 0, e • d 0 - d 1]),
      s 0 = r 0 ∧ s 1 = r ((![1, 3] : Fin 2 → Fin 4) t) ∧
      hirzebruchPicardBasis d e hΦ s hs = hirzebruchPicardBasis b e hΦ r hr := by
  classical
  fin_cases t
  · exact ⟨b, r, hr, rfl, rfl, rfl⟩
  obtain ⟨d, hd⟩ := exists_hirzebruch_marking_swap_fibers b e r hr
  let s := (Equiv.swap 1 3).trans r
  have hs : (fun j ↦ (s j).primitiveGenerator) = ![d 0, d 1, -d 0, e • d 0 - d 1] := hd
  have h₀ : s 0 = r 0 := by simp [s, Equiv.swap_apply_def]
  have h₁ : s 1 = r 3 := by simp [s]
  refine ⟨d, s, hs, h₀, h₁, DFunLike.ext _ _ (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)⟩
  · simp only [hirzebruchPicardBasis_apply_zero d, h₁,
      hirzebruchPicardBasis_apply_zero_eq_ray_three b]
  · simp only [hirzebruchPicardBasis_apply_one, h₀]

local notation "C" => hirzebruchPicardBasis b e hΦ r hr

include hr in
open Classical in
/-- In a Hirzebruch marking based at a selected toric corner, the section coefficient
of every Picard class is preserved. If the chosen section changes, the fiber coefficient
changes by subtracting the original signed Hirzebruch parameter times the section coefficient. -/
theorem exists_hirzebruch_corner_picardBasis (hc : Φ.IsComplete)
    (σ : Φ.cones) (hσ : Nat.card (ToricRay σ.val) = 2) :
    ∃ (d : Basis (Fin 2) ℤ N) (a : ℤ) (t : Fin 4 ≃ Φ.Ray)
      (ht : (fun j ↦ (t j).primitiveGenerator) = ![d 0, d 1, -d 0, a • d 0 - d 1])
      (shift : ℤ),
      σ.val = PointedCone.hull ℝ (Set.range (i ∘ d)) ∧
      (shift = 0 ∨ shift = e) ∧ a = e - 2 * shift ∧
      ∀ L : Pic, (hirzebruchPicardBasis d a hΦ t ht).repr L 0 =
        (C).repr L 0 - shift * (C).repr L 1 ∧
        (hirzebruchPicardBasis d a hΦ t ht).repr L 1 = (C).repr L 1 := by
  obtain ⟨d, a, t, hcone, ht, hf, hs⟩ := exists_hirzebruch_corner_basis b e r hr hΦ hc σ hσ
  let C' := hirzebruchPicardBasis d a hΦ t ht
  have hfiber : C' 0 = (C) 0 := by
    rw [hirzebruchPicardBasis_apply_zero]
    rcases hf with h | h
    · rw [h, hirzebruchPicardBasis_apply_zero]
    · rw [h, hirzebruchPicardBasis_apply_zero_eq_ray_three]
  have hsection : ∃ shift : ℤ, (shift = 0 ∨ shift = e) ∧ a = e - 2 * shift ∧
      C' 1 = (C) 1 + shift • (C) 0 := by
    rw [hirzebruchPicardBasis_apply_one, hirzebruchPicardBasis_apply_one,
      hirzebruchPicardBasis_apply_zero]
    rcases hs with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · exact ⟨0, Or.inl rfl, by simp, by simp [h]⟩
    · exact ⟨e, Or.inr rfl, by omega, by
        rw [h, (hirzebruch_ray_classes b e hΦ r hr).1]⟩
  obtain ⟨shift, hshift, ha, hsection⟩ := hsection
  refine ⟨d, a, t, ht, shift, hcone, hshift, ha, fun L ↦ ?_⟩
  have hL : L = ((C).repr L 0 - shift * (C).repr L 1) • C' 0 + (C).repr L 1 • C' 1 := by
    have hsum := (C).sum_repr L
    rw [Fin.sum_univ_two] at hsum
    calc
      L = (C).repr L 0 • (C) 0 + (C).repr L 1 • (C) 1 := hsum.symm
      _ = _ := by
        rw [hfiber, hsection, smul_add, sub_smul, smul_smul, mul_comm ((C).repr L 1) shift]
        abel
  exact ⟨by simpa [Basis.repr_self] using congrArg (fun x ↦ C'.repr x 0) hL,
    by simpa [Basis.repr_self] using congrArg (fun x ↦ C'.repr x 1) hL⟩

section Intersection

variable [Φ.algebraicRealization.IsProjectiveOver ℂ]
variable (hc : Φ.IsComplete)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "B" => intersectionBilinForm ℂ X
local notation "K" => Additive.ofMul (LineBundleClass.mk (QPainleve.canonicalBundle ℂ X 2))

omit [Nonempty Φ.cones] in
include hc hr in
private theorem hirzebruch_selfIntersection :
    Φ.rayBoundarySelfIntersection hΦ (r 0) = -e ∧
      Φ.rayBoundarySelfIntersection hΦ (r 1) = 0 := by
  have h₀₁ := exists_cone_of_hirzebruch_section_fiber b e r hr hΦ hc 0 0
  have h₀₃ := exists_cone_of_hirzebruch_section_fiber b e r hr hΦ hc 0 1
  have h₂₁ := exists_cone_of_hirzebruch_section_fiber b e r hr hΦ hc 1 0
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
    B (C j) (C k) = (!![0, 1; 1, -e] : Matrix (Fin 2) (Fin 2) ℤ) j k := by
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  let : SmoothOfRelativeDimension 2 (X ↘ Spec (CommRingCat.of ℂ)) :=
    hN ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  obtain ⟨hB, hF⟩ := hirzebruch_selfIntersection b e hΦ r hr hc
  have h₀₁ : ∃ σ : Φ.cones, (r 0).toCone ≤ σ ∧ (r 1).toCone ≤ σ :=
    exists_cone_of_hirzebruch_section_fiber b e r hr hΦ hc 0 0
  have h₁₀ : ∃ σ : Φ.cones, (r 1).toCone ≤ σ ∧ (r 0).toCone ≤ σ := h₀₁.imp (fun _ h ↦ h.symm)
  fin_cases j <;> fin_cases k <;>
    simp only [Fin.zero_eta, Fin.mk_one, hirzebruchPicardBasis_apply_zero,
      hirzebruchPicardBasis_apply_one, Equiv.apply_eq_iff_eq,
      Φ.intersectionBilinForm_rayDivisorToPicard_single_single hΦ hN] <;> simp [hF, hB, h₀₁, h₁₀]

include hc in
/-- A class with Hirzebruch Picard coordinates `(a, d)` intersects the fiber
in degree `d` and the section of square `-e` in degree `a - e * d`. -/
theorem hirzebruchPicardBasis_intersection_repr [SmoothOfRelativeDimension 2 (X ↘ S)]
    (x : Pic) :
    B x (C 0) = (C).repr x 1 ∧ B x (C 1) = (C).repr x 0 - e * (C).repr x 1 := by
  let a := (C).repr x 0
  let d := (C).repr x 1
  have hx : x = a • C 0 + d • C 1 := by
    simpa only [a, d, Fin.sum_univ_two] using ((C).sum_repr x).symm
  have h (j : Fin 2) : B x (C j) =
      a * (!![0, 1; 1, -e] : Matrix (Fin 2) (Fin 2) ℤ) 0 j +
        d * (!![0, 1; 1, -e] : Matrix (Fin 2) (Fin 2) ℤ) 1 j := by
    conv_lhs => rw [hx]
    simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, Int.zsmul_eq_mul,
      hirzebruchPicardBasis_intersection b e hΦ r hr hc]
  exact ⟨by simpa using h 0, by simpa [sub_eq_add_neg, mul_comm d] using h 1⟩

omit [Nonempty Φ.cones] [Φ.algebraicRealization.IsProjectiveOver ℂ] in
include hΦ hc hr in
private theorem isRationalOver_of_hirzebruch :
    Scheme.IsRationalOver (X ↘ S) := by
  obtain ⟨σ, h₀, h₁⟩ := exists_cone_of_hirzebruch_section_fiber b e r hr hΦ hc 0 0
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
    B (C j) K = ![-2, e - 2] j := by
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
