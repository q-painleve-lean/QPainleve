/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.PresentedGroup
public import QPainleve.Algebra.Cluster.Word.ModularGroup
public import QPainleve.SignedClusterModularGroup.Examples.FourVertex.Words

import QPainleve.SignedClusterModularGroup.Examples.FourVertex.NormalForm
import QPainleve.SignedClusterModularGroup.Examples.FourVertex.Relations
import TauCeti.Algebra.Group.Subgroup.Pointwise
import TauCeti.Algebra.Group.Subgroup.ZPowers

/-!
# Presentations of the four-vertex cluster modular groups

The rotation `p` and translation `t` in the four-vertex seed of Bershtein, Gavrylenko
and Marshakov, *Cluster integrable systems, q-Painlevé equations and their
quantization*, equation (3.1), satisfy `p⁴ = (pt)² = (p³t)² = 1`. Adjoining
the reflection `s` adds the three relations `s² = (sp)² = (spt)² = 1`.
Together with `p⁴ = 1`, the two mixed relators make the half-turn `p²` commute with `t`.

The integer relation criterion verifies the relators on independent X maps.
The relators collect every element of the presented groups into the power forms
`pⁱtᵐ` and `pⁱtᵐsᵉ`. Uniqueness of those forms on X maps proves completeness.
-/

public noncomputable section

open CategoryTheory Quiver
open QPainleve.Cluster

namespace QPainleve.FourVertex

local notation "B" => exchangeMatrix
local notation "Γ" => ClusterModularGroup ℂ B
local notation "Γs" => SignedClusterModularGroup ℂ B
local notation "unsigned[" w "," h "]" =>
  clusterModularGroupMap ℂ B
    (Subtype.mk (End.of w) (Iff.mpr (mem_inversionFreeLoops_iff B (End.of w)) h))

/-- The unsigned relators `p⁴`, `(pt)²`, `(p³t)²`, in point-map multiplication order.
Generator zero is the rotation, and generator one is the translation. -/
def unsignedRelators : Set (FreeGroup (Fin 2)) :=
  let p := FreeGroup.of (0 : Fin 2)
  let t := FreeGroup.of (1 : Fin 2)
  {p ^ 4, (p * t) ^ 2, (p ^ 3 * t) ^ 2}

/-- The signed presentation adds `s²`, `(sp)²`, and `(spt)²` to the unsigned relators.
Generator two is the reflection. -/
def signedRelators : Set (FreeGroup (Fin 3)) :=
  let p := FreeGroup.of (0 : Fin 3)
  let t := FreeGroup.of (1 : Fin 3)
  let s := FreeGroup.of (2 : Fin 3)
  {p ^ 4, (p * t) ^ 2, (p ^ 3 * t) ^ 2, s ^ 2, (s * p) ^ 2, (s * p * t) ^ 2}

private def point (w : Word B B) : Γs :=
  signedClusterModularGroupMap ℂ B (End.of w)

private theorem point_comp (u v : Word B B) : point (u.comp v) = point v * point u :=
  (signedClusterModularGroupMap ℂ B).map_mul (End.of v) (End.of u)

local notation "tropical" => Paths.lift (tropicalPrefunctor (A := ℤ) (Fin 4))

private theorem tropical_comp_apply (w v : Word B B) (x : Fin 4 → ℤ) :
    Equiv.toFun ((tropical).map (w.comp v)) x =
      Equiv.toFun ((tropical).map v) (Equiv.toFun ((tropical).map w) x) := by
  exact (congrArg (fun e : Equiv.Perm (Fin 4 → ℤ) ↦ e x)
    ((tropical).map_comp w v)).trans (Equiv.Perm.mul_apply _ _ _)

local notation "exponents[" w "," x "]" =>
  Path.exchangeKernelEquiv w (exchangeKernelEquiv x)

private theorem point_eq_one_of_actions (w : Word B B)
    (hSign : Even w.inversionCount)
    (hKernel : ∀ x, exponents[w,x] = exchangeKernelEquiv x)
    (hBoundary : Equiv.toFun ((tropical).map w) (boundaryOrders 0) = boundaryOrders 0) :
    point w = 1 := by
  unfold point
  rw [← map_one (signedClusterModularGroupMap ℂ B)]
  apply (signedClusterModularGroupMap_eq_iff ℂ B (End.of w) 1).mpr
  apply (xPullback_eq_iff_signedLoopInvariants_eq ℂ w Path.nil).mpr
  have hK : w.exchangeKernelEquiv = (Path.nil : Word B B).exchangeKernelEquiv :=
    LinearEquiv.ext fun x ↦ by
      obtain ⟨y, rfl⟩ := exchangeKernelEquiv.surjective x
      simpa only [Path.exchangeKernelEquiv_nil, LinearEquiv.refl_apply] using hKernel y
  simp only [Path.signedLoopInvariants_def, Prod.mk.injEq, Path.inversionCount_nil,
    hSign.neg_one_pow, pow_zero, ← Path.coe_exchangeKernelEquiv_apply, hK, true_and,
    ← Equiv.toFun_as_coe, hBoundary, Paths.lift_nil, SingleObj.id_as_one, Equiv.Perm.one_apply]
  rfl

private theorem point_satisfies_relators :
    let p := point rotationWord
    let t := point translationWord
    let s := point reflectionWord
    p ^ 4 = 1 ∧ (p * t) ^ 2 = 1 ∧ (p ^ 3 * t) ^ 2 = 1 ∧
      s ^ 2 = 1 ∧ (s * p) ^ 2 = 1 ∧ (s * p * t) ^ 2 = 1 := by
  dsimp only
  have hp4 : point rotationWord ^ 4 = (point rotationWord ^ 2) ^ 2 := pow_mul _ 2 2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [hp4, pow_succ (point rotationWord) 2, pow_two, ← point_comp]
    apply point_eq_one_of_actions
    · simp [Path.inversionCount_comp]
    · intro x
      simp only [Path.exchangeKernelEquiv_comp, LinearEquiv.trans_apply,
        rotationWord_exchangeKernelEquiv, translationWord_exchangeKernelEquiv,
        reflectionWord_exchangeKernelEquiv, Matrix.cons_val_zero, Matrix.cons_val_one,
        Pi.neg_apply]
      apply congrArg (fun v : Fin 2 → ℤ ↦ exchangeKernelEquiv v)
      funext j
      fin_cases j <;> simp
    · simp only [tropical_comp_apply, rotationWord_tropical_boundaryOrders,
        translationWord_tropical_boundaryOrders, reflectionWord_tropical_boundaryOrders]
      exact congrArg boundaryOrders (by decide)

section Collection

open Subgroup

variable {G : Type*} [Group G] {p t s : G}

private theorem commute_halfTurn_translation
    (hp : p ^ 4 = 1) (hpt : (p * t) ^ 2 = 1) (hppt : (p ^ 3 * t) ^ 2 = 1) :
    Commute (p ^ 2) t := by
  have hpp : (p ^ 2)⁻¹ = p ^ 2 := inv_eq_of_mul_eq_one_right (by simpa [← pow_add] using hp)
  have hq : (p * t)⁻¹ = p * t := inv_eq_of_mul_eq_one_right (by rwa [← pow_two])
  have hprod : (p ^ 2 * (p * t))⁻¹ = p ^ 2 * (p * t) := by
    apply inv_eq_of_mul_eq_one_right
    rwa [← pow_two, ← mul_assoc, ← pow_succ]
  have hc : Commute (p ^ 2) (p * t) := by
    rw [commute_iff_eq, ← hprod, mul_inv_rev, hpp, hq]
  have he := hc.eq
  rw [← mul_assoc, ((Commute.refl p).pow_left 2).eq, mul_assoc] at he
  exact mul_left_cancel (by simpa only [mul_assoc] using he)

private theorem rotation_mem_normalizer
    (hp : p ^ 4 = 1) (hpt : (p * t) ^ 2 = 1) :
    p ∈ normalizer (zpowers (p ^ 2) ⊔ zpowers t : Subgroup G) := by
  let H := zpowers (p ^ 2) ⊔ zpowers t
  have hp2 : p ^ 2 ∈ H := mem_sup_left (mem_zpowers _)
  have ht : t ∈ H := mem_sup_right (mem_zpowers _)
  have hp2inv : (p ^ 2)⁻¹ = p ^ 2 :=
    inv_eq_of_mul_eq_one_right (by simpa only [← pow_add] using hp)
  have hconj : p * t * p⁻¹ = t⁻¹ * p ^ 2 := by
    have hq : (p * t)⁻¹ = p * t := inv_eq_of_mul_eq_one_right (by rwa [← pow_two])
    rw [← hq, mul_inv_rev, mul_assoc, ← pow_two, inv_pow, hp2inv]
  have hmap : H.map (MulAut.conj p) ≤ H := by
    simp only [H, Subgroup.map_sup, MonoidHom.map_zpowers, ← MulEquiv.toMonoidHom_eq_coe,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hconj, sup_le_iff, zpowers_le]
    constructor
    · rw [((Commute.refl p).pow_right 2).eq, mul_assoc, mul_inv_cancel, mul_one]
      exact hp2
    · exact H.mul_mem (H.inv_mem ht) hp2
  have hin (x : G) (hx : x ∈ H) : p * x * p⁻¹ ∈ H :=
    hmap ⟨x, hx, rfl⟩
  apply mem_normalizer_iff.mpr
  intro x
  refine ⟨hin x, fun hx ↦ ?_⟩
  have he : (p ^ 2)⁻¹ * (p * (p * x * p⁻¹) * p⁻¹) * p ^ 2 = x := by group
  have h := (H.le_normalizer (H.inv_mem hp2) _).mp (hin _ hx)
  rwa [inv_inv, he] at h

private theorem rotationTranslation_normal_form
    (hp : p ^ 4 = 1) (hpt : (p * t) ^ 2 = 1) (hppt : (p ^ 3 * t) ^ 2 = 1)
    {g : G} (hg : g ∈ zpowers p ⊔ zpowers t) :
    ∃ a : Fin 4 × ℤ, p ^ (a.1 : ℕ) * t ^ a.2 = g := by
  let H := zpowers (p ^ 2) ⊔ zpowers t
  have hpH : p ∈ normalizer H := rotation_mem_normalizer hp hpt
  have hle : zpowers p ⊔ zpowers t ≤ H ⊔ zpowers p :=
    sup_le le_sup_right (le_sup_right.trans le_sup_left)
  have h := hle hg
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_sup_of_right_le_normalizer_left (zpowers_le.mpr hpH)).mp h
  -- Move the rotation to the left by conjugating the element of the normalized subgroup.
  have hxy : y⁻¹ * x * y ∈ H := (mem_normalizer_iff''.mp ((zpowers_le.mpr hpH) hy) _).mp hx
  have hcomm := commute_halfTurn_translation hp hpt hppt
  have htN : t ∈ normalizer (zpowers (p ^ 2)) := by
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    simp only [← MulEquiv.toMonoidHom_eq_coe, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      hcomm.symm.eq, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨z, hz, u, ⟨m, rfl⟩, hzu⟩ :=
    (mem_sup_of_right_le_normalizer_left (zpowers_le.mpr htN)).mp hxy
  have hz' : z ∈ Submonoid.powers (p ^ 2) :=
    (IsOfFinOrder.mem_powers_iff_mem_zpowers (x := p ^ 2)
      (isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, (pow_mul p 2 2).symm.trans hp⟩)).mpr hz
  have hy' : y ∈ Submonoid.powers p :=
    (IsOfFinOrder.mem_powers_iff_mem_zpowers
      (isOfFinOrder_iff_pow_eq_one.mpr ⟨4, by decide, hp⟩)).mpr hy
  obtain ⟨i, rfl⟩ := hy'
  obtain ⟨j, rfl⟩ := hz'
  refine ⟨⟨⟨(i + 2 * j) % 4, Nat.mod_lt _ (by decide)⟩, m⟩, ?_⟩
  -- Reduce the combined rotation exponent modulo its order bound.
  rw [← pow_eq_pow_mod _ hp, pow_add, pow_mul, mul_assoc, hzu]
  group

private theorem reflection_mem_normalizer
    (hs : s ^ 2 = 1) (hsp : (s * p) ^ 2 = 1)
    (hpt : (p * t) ^ 2 = 1) (hspt : (s * p * t) ^ 2 = 1) :
    s ∈ normalizer (zpowers p ⊔ zpowers t : Subgroup G) := by
  let R := zpowers p ⊔ zpowers t
  let a := MulAut.conj s
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by rwa [← pow_two])
  have hap : a p = p⁻¹ := by
    rw [MulAut.conj_apply, hsinv, ← mul_eq_one_iff_eq_inv]
    simpa only [pow_two, mul_assoc] using hsp
  have haq : a (p * t) = p * t := by
    have hq : (p * t)⁻¹ = p * t := inv_eq_of_mul_eq_one_right (by rwa [← pow_two])
    have hprod : (s * (p * t))⁻¹ = s * (p * t) :=
      inv_eq_of_mul_eq_one_right (by simpa only [pow_two, mul_assoc] using hspt)
    have hc : Commute s (p * t) := by rw [commute_iff_eq, ← hprod, mul_inv_rev, hsinv, hq]
    rw [MulAut.conj_apply, hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hat : a t = p * (p * t) := by
    have h := map_mul a p t
    rw [haq, hap] at h
    rw [h, mul_inv_cancel_left]
  have hmap : R.map a ≤ R := by
    simp only [R, Subgroup.map_sup, MonoidHom.map_zpowers, ← MulEquiv.toMonoidHom_eq_coe,
      MulEquiv.coe_toMonoidHom, hap, hat, sup_le_iff, zpowers_le]
    have hp : p ∈ R := mem_sup_left (mem_zpowers _)
    exact ⟨R.inv_mem hp, R.mul_mem hp (R.mul_mem hp (mem_sup_right (mem_zpowers _)))⟩
  have hin (x : G) (hx : x ∈ R) : s * x * s⁻¹ ∈ R := hmap ⟨x, hx, rfl⟩
  apply mem_normalizer_iff.mpr
  intro x
  refine ⟨hin x, fun hx ↦ ?_⟩
  have he : s * (s * x * s⁻¹) * s⁻¹ = x := calc
    _ = (s * s) * x * (s * s)⁻¹ := by group
    _ = x := by simp only [← pow_two, hs, one_mul, inv_one, mul_one]
  exact he ▸ hin _ hx

private theorem rotationTranslationReflection_normal_form
    (hp : p ^ 4 = 1) (hpt : (p * t) ^ 2 = 1) (hppt : (p ^ 3 * t) ^ 2 = 1)
    (hs : s ^ 2 = 1) (hsp : (s * p) ^ 2 = 1) (hspt : (s * p * t) ^ 2 = 1)
    {g : G} (hg : g ∈ (zpowers p ⊔ zpowers t) ⊔ zpowers s) :
    ∃ a : Fin 2 × Fin 4 × ℤ, p ^ (a.2.1 : ℕ) * t ^ a.2.2 * s ^ (a.1 : ℕ) = g := by
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_sup_of_right_le_normalizer_left
    (zpowers_le.mpr (reflection_mem_normalizer hs hsp hpt hspt))).mp hg
  obtain ⟨a, ha⟩ := rotationTranslation_normal_form hp hpt hppt hx
  rcases (mem_zpowers_iff_of_sq_eq_one hs).mp hy with rfl | rfl
  · exact ⟨⟨0, a⟩, by simpa using ha⟩
  · exact ⟨⟨1, a⟩, by simpa using congrArg (· * y) ha⟩

end Collection

open scoped Matrix

private def signedGenerators : Fin 3 → Γs :=
  ![point rotationWord, point translationWord, point reflectionWord]

private def unsignedGenerators : Fin 2 → Γ :=
  ![unsigned[rotationWord,inversionCount_rotationWord],
    unsigned[translationWord,inversionCount_translationWord]]

private theorem lift_signedGenerators (r : FreeGroup (Fin 3)) (h : r ∈ signedRelators) :
    FreeGroup.lift signedGenerators r = 1 := by
  obtain ⟨hp, hpt, hppt, hs, hsp, hspt⟩ := point_satisfies_relators
  simp only [signedRelators, Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [signedGenerators] using hp
  · simpa [signedGenerators] using hpt
  · simpa [signedGenerators] using hppt
  · simpa [signedGenerators] using hs
  · simpa [signedGenerators] using hsp
  · simpa [signedGenerators] using hspt

private theorem lift_unsignedGenerators (r : FreeGroup (Fin 2)) (h : r ∈ unsignedRelators) :
    FreeGroup.lift unsignedGenerators r = 1 := by
  obtain ⟨hp, hpt, hppt, -⟩ := point_satisfies_relators
  apply clusterModularGroupInclusion_injective ℂ B
  simp only [unsignedRelators, Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with rfl | rfl | rfl
  · simpa [unsignedGenerators, point] using hp
  · simpa [unsignedGenerators, point] using hpt
  · simpa [unsignedGenerators, point] using hppt

local notation "pu" => PresentedGroup.of (rels := unsignedRelators) (0 : Fin 2)
local notation "tu" => PresentedGroup.of (rels := unsignedRelators) (1 : Fin 2)
local notation "ps" => PresentedGroup.of (rels := signedRelators) (0 : Fin 3)
local notation "ts" => PresentedGroup.of (rels := signedRelators) (1 : Fin 3)
local notation "ss" => PresentedGroup.of (rels := signedRelators) (2 : Fin 3)

private theorem unsignedPresentedGroup_relations :
    pu ^ 4 = 1 ∧ (pu * tu) ^ 2 = 1 ∧ (pu ^ 3 * tu) ^ 2 = 1 := by
  let p := FreeGroup.of (0 : Fin 2)
  let t := FreeGroup.of (1 : Fin 2)
  refine ⟨?_, ?_, ?_⟩
  · have h : p ^ 4 ∈ unsignedRelators := by simp [unsignedRelators, p]
    simpa only [map_pow, PresentedGroup.of, p] using PresentedGroup.one_of_mem h
  · have h : (p * t) ^ 2 ∈ unsignedRelators := by simp [unsignedRelators, p, t]
    simpa only [map_mul, map_pow, PresentedGroup.of, p, t] using PresentedGroup.one_of_mem h
  · have h : (p ^ 3 * t) ^ 2 ∈ unsignedRelators := by simp [unsignedRelators, p, t]
    simpa only [map_mul, map_pow, PresentedGroup.of, p, t] using PresentedGroup.one_of_mem h

private theorem signedPresentedGroup_relations :
    ps ^ 4 = 1 ∧ (ps * ts) ^ 2 = 1 ∧ (ps ^ 3 * ts) ^ 2 = 1 ∧
      ss ^ 2 = 1 ∧ (ss * ps) ^ 2 = 1 ∧ (ss * ps * ts) ^ 2 = 1 := by
  let p := FreeGroup.of (0 : Fin 3)
  let t := FreeGroup.of (1 : Fin 3)
  let s := FreeGroup.of (2 : Fin 3)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h : p ^ 4 ∈ signedRelators := by simp [signedRelators, p]
    simpa only [map_pow, PresentedGroup.of, p] using PresentedGroup.one_of_mem h
  · have h : (p * t) ^ 2 ∈ signedRelators := by simp [signedRelators, p, t]
    simpa only [map_mul, map_pow, PresentedGroup.of, p, t] using PresentedGroup.one_of_mem h
  · have h : (p ^ 3 * t) ^ 2 ∈ signedRelators := by simp [signedRelators, p, t]
    simpa only [map_mul, map_pow, PresentedGroup.of, p, t] using PresentedGroup.one_of_mem h
  · have h : s ^ 2 ∈ signedRelators := by simp [signedRelators, s]
    simpa only [map_pow, PresentedGroup.of, s] using PresentedGroup.one_of_mem h
  · have h : (s * p) ^ 2 ∈ signedRelators := by simp [signedRelators, s, p]
    simpa only [map_mul, map_pow, PresentedGroup.of, p, s] using PresentedGroup.one_of_mem h
  · have h : (s * p * t) ^ 2 ∈ signedRelators := by simp [signedRelators, s, p, t]
    simpa only [map_mul, map_pow, PresentedGroup.of, p, t, s] using PresentedGroup.one_of_mem h

/-- The unsigned group of independent X maps is presented by the rotation, translation,
and `unsignedRelators`. The equivalence sends the abstract generators to the two point maps. -/
def unsignedPresentationMulEquiv : PresentedGroup unsignedRelators ≃* Γ := by
  let f := PresentedGroup.toGroup lift_unsignedGenerators
  let collect (a : Fin 4 × ℤ) := pu ^ (a.1 : ℕ) * tu ^ a.2
  have hcollect : Function.Surjective collect := by
    intro g
    have hg := PresentedGroup.generated_by unsignedRelators
      (Subgroup.zpowers pu ⊔ Subgroup.zpowers tu) (fun i ↦ by
        fin_cases i
        · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers pu)
        · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers tu)) g
    obtain ⟨hp, hpt, hppt⟩ := unsignedPresentedGroup_relations
    exact rotationTranslation_normal_form hp hpt hppt hg
  have hf : Function.Bijective (f ∘ collect) := by
    rw [Function.bijective_iff_existsUnique]
    intro g
    simpa [f, collect, unsignedGenerators] using existsUnique_unsigned_normal_form g
  exact MulEquiv.ofBijective f ⟨hf.injective.of_comp_right hcollect, hf.surjective.of_comp⟩

/-- The signed group of independent X maps is presented by the rotation, translation,
reflection, and `signedRelators`. The equivalence preserves the point-map product order. -/
def signedPresentationMulEquiv : PresentedGroup signedRelators ≃* Γs := by
  let f := PresentedGroup.toGroup lift_signedGenerators
  let collect (a : Fin 2 × Fin 4 × ℤ) := ps ^ (a.2.1 : ℕ) * ts ^ a.2.2 * ss ^ (a.1 : ℕ)
  have hcollect : Function.Surjective collect := by
    intro g
    have hg := PresentedGroup.generated_by signedRelators
      ((Subgroup.zpowers ps ⊔ Subgroup.zpowers ts) ⊔ Subgroup.zpowers ss) (fun i ↦ by
        fin_cases i
        · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers ps))
        · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers ts))
        · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers ss)) g
    obtain ⟨hp, hpt, hppt, hs, hsp, hspt⟩ := signedPresentedGroup_relations
    exact rotationTranslationReflection_normal_form hp hpt hppt hs hsp hspt hg
  have hf : Function.Bijective (f ∘ collect) := by
    rw [Function.bijective_iff_existsUnique]
    intro g
    simpa [f, collect, signedGenerators, point] using existsUnique_signed_normal_form g
  exact MulEquiv.ofBijective f ⟨hf.injective.of_comp_right hcollect, hf.surjective.of_comp⟩

/-- The unsigned presentation evaluates its generators as the rotation and translation. -/
@[simp]
theorem unsignedPresentationMulEquiv_apply_of (i : Fin 2) :
    unsignedPresentationMulEquiv (PresentedGroup.of i) =
      ![unsigned[rotationWord,inversionCount_rotationWord],
        unsigned[translationWord,inversionCount_translationWord]] i :=
  PresentedGroup.toGroup.of lift_unsignedGenerators

/-- The signed presentation evaluates its generators as the rotation, translation and reflection. -/
@[simp]
theorem signedPresentationMulEquiv_apply_of (i : Fin 3) :
    signedPresentationMulEquiv (PresentedGroup.of i) =
      ![signedClusterModularGroupMap ℂ B (End.of rotationWord),
        signedClusterModularGroupMap ℂ B (End.of translationWord),
        signedClusterModularGroupMap ℂ B (End.of reflectionWord)] i :=
  PresentedGroup.toGroup.of lift_signedGenerators

private theorem unsignedRelators_mapsTo_signedRelators :
    Set.MapsTo (FreeGroup.map Fin.castSucc) unsignedRelators signedRelators := by
  intro r hr
  simp only [unsignedRelators, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl | rfl <;> simp [signedRelators]

/-- The unsigned presentation includes into the signed one by keeping its two generators. -/
def unsignedPresentationInclusion :
    PresentedGroup unsignedRelators →* PresentedGroup signedRelators :=
  PresentedGroup.map _ unsignedRelators_mapsTo_signedRelators

/-- The inclusion preserves the rotation and translation in the presented groups. -/
@[simp]
theorem unsignedPresentationInclusion_apply_of (i : Fin 2) :
    unsignedPresentationInclusion (PresentedGroup.of i) = PresentedGroup.of i.castSucc := by
  calc
    _ = PresentedGroup.mk signedRelators ((FreeGroup.map Fin.castSucc) (FreeGroup.of i)) := rfl
    _ = _ := congrArg (PresentedGroup.mk signedRelators) FreeGroup.map.of

/-- The two presentations identify the inclusion of the unsigned point maps. -/
theorem signedPresentationMulEquiv_comp_unsignedPresentationInclusion :
    signedPresentationMulEquiv.toMonoidHom.comp unsignedPresentationInclusion =
      (clusterModularGroupInclusion ℂ B).comp unsignedPresentationMulEquiv.toMonoidHom := by
  apply PresentedGroup.ext
  intro i
  fin_cases i <;> simp

end QPainleve.FourVertex
