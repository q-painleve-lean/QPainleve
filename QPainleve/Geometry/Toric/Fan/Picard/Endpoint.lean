/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.ChargeKernel.Basic
public import QPainleve.Geometry.Toric.Fan.InternalBlowup
public import QPainleve.Geometry.Toric.Fan.Picard.CycleNumerics
public import QPainleve.LinearAlgebra.Determinant.Dual
public import QPainleve.SignedClusterModularGroup.Boundary.Intersection

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.SignedClusterModularGroup.Endpoint
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced

/-!
# Endpoint charges of toric presentations

The component classes of a primitive nef square-zero anticanonical cycle give
the numerical bounds on the center count and charge index of its toric presentation.
With these bounds the exchange matrix determines a unique identification of the
ambient integral lattices preserving the labelled rays and their determinant pairing.
The identification also applies directly to an ordered presentation with the
corresponding Picard data.
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower TopologicalSpace
open QPainleve.Cluster
open TauCeti.AlgebraicGeometry LineBundleClass
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

private theorem existsUnique_rayChargeEquiv_of_index
    {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N']
    [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
    {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}
    {n k : ℕ} [NeZero k] (s : Fin n → Φ.Ray) (t : Fin n → Ψ.Ray)
    (b : Module.Basis (Fin 2) ℤ N) (b' : Module.Basis (Fin 2) ℤ N')
    (hmat : chargeExchangeMatrix b.detDualEquiv.toLinearMap (rayChargeMap s) =
      chargeExchangeMatrix b'.detDualEquiv.toLinearMap (rayChargeMap t))
    (hcount : n + k = 12) (hk : k ≤ 9) (hindex : (rayChargeMap s).range.toAddSubgroup.index ^ 2 ∣ k)
    (hrel : ∃ x : (rayChargeMap s).ker, IsPrimitive x ∧
      ((rayChargeMap s).range.toAddSubgroup.index : ℤ) ∣ ∑ j, x.val j ^ 2) :
    ∃! E : N ≃ₗ[ℤ] N', (∀ j, E (s j).primitiveGenerator = (t j).primitiveGenerator) ∧
      ∀ x y, b'.detDualEquiv (E x) (E y) = b.detDualEquiv x y := by
  obtain ⟨x, hx, hsqx⟩ := hrel
  have hkpos := Nat.pos_of_ne_zero (NeZero.ne k)
  obtain ⟨E, hE, hpair⟩ := exists_charge_lattice_equiv
    (v₁ := rayChargeMap s) (v₂ := rayChargeMap t) b b'
    b.detDualEquiv_self b'.detDualEquiv_self
    b.detDualEquiv_apply_basis_zero_one b'.detDualEquiv_apply_basis_zero_one
    (fun j ↦ isPrimitive_def.mp (rayChargeMap_primitive s j))
    (fun j ↦ isPrimitive_def.mp (rayChargeMap_primitive t j)) hmat hkpos hk
    (by simpa only [Fintype.card_fin] using hcount) hindex fun h ↦
      ⟨x, isPrimitive_def.mp hx, by simpa only [h, Nat.cast_ofNat] using hsqx⟩
  have hE' (j : Fin n) : E (s j).primitiveGenerator = (t j).primitiveGenerator := by
    simpa only [rayChargeMap_single] using hE (Pi.single j 1)
  let : Module.Free ℤ N' := Module.Free.of_basis b'
  have hnz : (rayChargeMap s).range.toAddSubgroup.index ≠ 0 := by
    intro hz
    simp [hz, NeZero.ne k] at hindex
  exact ⟨E, ⟨hE', hpair⟩, fun F hF ↦ rayChargeEquiv_ext s hnz (fun j ↦ (hF.1 j).trans (hE' j).symm)⟩

section NodalCycle

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] {n : ℕ}
  [Φ.algebraicRealization.IsProjectiveOver ℂ]
  (hΦ : Φ.IsRegular) (hdim : Module.finrank ℤ N = 2)
  (s : Fin n → Φ.Ray) (m : Fin n → N →+ ℤ)
  (hm : ∀ j, m j (s j).primitiveGenerator = 0) (hprim : ∀ j, Function.Surjective (m j))
  (c : Fin n → ℂˣ)
  (J : Fin n →
    {I : (Φ.boundaryIdeal inferInstance).subscheme.IdealSheafData // I.IsEffectiveCartier})
  (hJ : ∀ j, (J j).val = ((s j).binomialCenterOnBoundary hdim (hm j) (hprim j) (c j)).ker)
  {X Y : Scheme} [X.Over (Spec (.of ℂ))] [X.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of ℂ))]
  [rational : Scheme.IsRationalOver (X ↘ Spec (.of ℂ))]
  {D : X.IdealSheafData} {d : ℕ} {T : QPainleve.BlowupTower X d Y}
  (hT : IsNodalBoundaryTower D (X ↘ Spec (.of ℂ)) (𝟙 X) T)
  (e : Y ≅ (alongBoundary (Φ.boundaryIdeal inferInstance).subschemeι J).1)
  (he : e.inv ≫ T.toBase ≫ (X ↘ Spec (.of ℂ)) =
    (alongBoundary (Φ.boundaryIdeal inferInstance).subschemeι J).2.toTower.toBase ≫
      (Φ.algebraicRealization ↘ Spec (.of ℂ)))
  (hD : ((D.comap T.toBase).comap e.inv).support =
    (alongBoundary (Φ.boundaryIdeal inferInstance).subschemeι J).2.boundaryι.ker.support)
  (hc : Φ.IsComplete)

local notation "fX" => (X ↘ Spec (CommRingCat.of ℂ))

local instance : IsIntegral X :=
  let : Smooth fX := SmoothOfRelativeDimension.smooth 2 fX
  rational.isIntegral_of_smooth
local instance : IsNoetherian X := isNoetherian_of_finiteType fX
local instance : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
  (fX).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two

variable {k : ℕ} [NeZero k]

local notation "divClass(" hCart ")" => (LineBundleClass.mk
  (IsEffectiveCartier.toInvertibleSheaf hCart))⁻¹
local notation "v" => rayChargeMap s

include hΦ hc hJ hT he hD in
/-- The center count, charge rank, and charge index bounds for an ordered toric
presentation of a primitive nef square-zero anticanonical boundary cycle. The
component labelling is in cyclic order, with the two nodes of a two-component
cycle counted separately. -/
theorem chargeIndex_bounds_of_nodal_anticanonical_cycle
    (hCart : D.IsEffectiveCartier)
    (hnodal : AtWorstNodalOfRelativeDimensionOne (D.subscheme ↘ Spec (.of ℂ)))
    (hnef : (divClass(hCart)).IsNef ℂ fX)
    (hsq : Chow.classIntersectionNumber ℂ X divClass(hCart) divClass(hCart) = 0)
    (hcan : divClass(hCart) = (LineBundleClass.mk (QPainleve.canonicalBundle ℂ X 2))⁻¹)
    (hδ : TauCeti.IsPrimitive (Additive.ofMul divClass(hCart)))
    (p : ZMod k ↪ CodimensionOnePoint X) (node : ZMod k ↪ X)
    (hp : ∀ q : CodimensionOnePoint X, (q : X) ∈ D.support ↔ q ∈ Set.range p)
    (hinc : ∀ i j, i ≠ j →
      closure {(p i : X)} ∩ closure {(p j : X)} =
        node '' {a | (a = i ∧ j = i + 1) ∨ (a = j ∧ i = j + 1)}) :
    n + k = 12 ∧ Module.finrank ℤ (v).ker = 10 - k ∧ Module.finrank ℤ (v).range = 2 ∧
      k ≤ 9 ∧ (v).range.toAddSubgroup.index ^ 2 ∣ k ∧
      (v).range.toAddSubgroup.index ∈ ({1, 2, 3} : Finset ℕ) ∧
      ∃ x : (v).ker, TauCeti.IsPrimitive x ∧
        ((v).range.toAddSubgroup.index : ℤ) ∣ ∑ j, x.val j ^ 2 := by
  let C (j : ZMod k) := Additive.ofMul (primeDivisorClass (p j))
  let U : X.Opens := Closeds.compl D.support
  have hspan : U.primeDivisorSpanCompl = Submodule.span ℤ (Set.range C) := by
    apply U.primeDivisorSpanCompl_eq_span_of_mem_iff p
    intro q
    simpa only [U, ← SetLike.mem_coe, Closeds.coe_compl, Set.mem_compl_iff, not_not] using hp q
  have hGram := QPainleve.BoundaryCycle.intersectionBilinForm_eq_of_nodal_cycle
    hCart hnodal hnef hsq p node hp hinc
  let : IsReduced D.subscheme := hnodal.isReduced
  have hsum : Additive.ofMul divClass(hCart) = ∑ j, C j :=
    hCart.ofMul_inv_toInvertibleSheaf_eq_sum_primeDivisorClass p hp
  have hsumCan : (∑ j, C j) = -Additive.ofMul (LineBundleClass.mk
      (QPainleve.canonicalBundle ℂ X 2)) := by
    rw [← hsum, hcan, ofMul_inv]
  exact chargeIndex_bounds_of_anticanonical_cycle hΦ hdim s m hm hprim c J hJ hT e he hD
    hc C hGram hspan hsumCan (hsum ▸ hδ)

include hΦ hc hJ hT he hD in
/-- The exchange matrix of a toric presentation of a primitive nef square-zero
anticanonical cycle determines the ambient charge lattice. For another labelled
family of rays with the same exchange matrix, the integral equivalence transports
the labelled generators and preserves the determinant pairing. -/
theorem exists_charge_lattice_equiv_of_anticanonical_cycle
    (hCart : D.IsEffectiveCartier)
    (hnodal : AtWorstNodalOfRelativeDimensionOne (D.subscheme ↘ Spec (.of ℂ)))
    (hnef : (divClass(hCart)).IsNef ℂ fX)
    (hsq : Chow.classIntersectionNumber ℂ X divClass(hCart) divClass(hCart) = 0)
    (hcan : divClass(hCart) = (LineBundleClass.mk (QPainleve.canonicalBundle ℂ X 2))⁻¹)
    (hδ : TauCeti.IsPrimitive (Additive.ofMul divClass(hCart)))
    (p : ZMod k ↪ CodimensionOnePoint X) (node : ZMod k ↪ X)
    (hp : ∀ q : CodimensionOnePoint X, (q : X) ∈ D.support ↔ q ∈ Set.range p)
    (hinc : ∀ i j, i ≠ j →
      closure {(p i : X)} ∩ closure {(p j : X)} =
        node '' {a | (a = i ∧ j = i + 1) ∨ (a = j ∧ i = j + 1)})
    {N' V' : Type*} [AddCommGroup N'] [AddCommGroup V'] [Module ℝ V']
    {i' : N' →+ V'} {Ψ : Fan i'} (t : Fin n → Ψ.Ray)
    (b : Module.Basis (Fin 2) ℤ N) (b' : Module.Basis (Fin 2) ℤ N')
    (hmat : chargeExchangeMatrix b.detDualEquiv.toLinearMap (rayChargeMap s) =
      chargeExchangeMatrix b'.detDualEquiv.toLinearMap (rayChargeMap t)) :
    ∃ E : N ≃ₗ[ℤ] N',
      (∀ j, E (s j).primitiveGenerator = (t j).primitiveGenerator) ∧
      ∀ x y, b'.detDualEquiv (E x) (E y) = b.detDualEquiv x y := by
  obtain ⟨hcount, _, _, hk, hdiv, _, hrel⟩ :=
    chargeIndex_bounds_of_nodal_anticanonical_cycle hΦ hdim s m hm hprim c J hJ hT e he hD hc
      hCart hnodal hnef hsq hcan hδ p node hp hinc
  obtain ⟨E, hE, _⟩ := existsUnique_rayChargeEquiv_of_index s t b b' hmat hcount hk hdiv hrel
  exact ⟨E, hE⟩

end NodalCycle

section PicardCycle

variable {N N' V V' : Type} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}
  {n : ℕ} (s : Fin n → Φ.Ray) (t : Fin n → Ψ.Ray)
  [Nonempty Φ.cones] [Φ.algebraicRealization.IsProjectiveOver ℂ]
  (b : Module.Basis (Fin 2) ℤ N) (b' : Module.Basis (Fin 2) ℤ N') (c : Fin n → ℂˣ)
  {X Y : Scheme} [X.Over (Spec (.of ℂ))] [X.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of ℂ))]
  [rational : Scheme.IsRationalOver (X ↘ Spec (.of ℂ))]
  {D : X.IdealSheafData} {d : ℕ} {T : QPainleve.BlowupTower X d Y}

local notation "Pic(" S ")" => Additive (LineBundleClass S)
local notation "P" => internalBlowupTower b s c
local notation "fX" => (X ↘ Spec (CommRingCat.of ℂ))

local instance : IsIntegral X :=
  let : Smooth fX := SmoothOfRelativeDimension.smooth 2 fX
  rational.isIntegral_of_smooth
local instance : IsNoetherian X := isNoetherian_of_finiteType fX
local instance : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
  (fX).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two

/-- Equal exchange matrices in a common label order identify the labeled rays of a
toric presentation of a primitive square-zero anticanonical cycle with their counterparts
by a unique integral equivalence preserving the determinant pairings. -/
theorem existsUnique_rayChargeEquiv_of_anticanonical_cycle
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (hT : IsNodalBoundaryTower D (X ↘ Spec (.of ℂ)) (𝟙 X) T)
    (e : Y ≅ (P).1)
    (he : e.inv ≫ T.toBase ≫ (X ↘ Spec (.of ℂ)) =
      (P).2.toTower.toBase ≫ (Φ.algebraicRealization ↘ Spec (.of ℂ)))
    (hD : ((D.comap T.toBase).comap e.inv).support = (P).2.boundaryι.ker.support)
    {k : ℕ} [NeZero k] (C : ZMod k → Pic(X))
    (hGram : ∀ j l : ZMod k, Chow.intersectionBilinForm ℂ X (C j) (C l) =
      (-2 : ℤ) * (if j = l then 1 else 0) +
        (if l = j + 1 then 1 else 0) + (if l = j - 1 then 1 else 0))
    (hspan : Scheme.Opens.primeDivisorSpanCompl (Closeds.compl D.support) =
      Submodule.span ℤ (Set.range C))
    (hcan : ∑ j, C j = -Additive.ofMul (LineBundleClass.mk (QPainleve.canonicalBundle ℂ X 2)))
    (hδ : IsPrimitive (∑ j, C j))
    (hmat : chargeExchangeMatrix b.detDualEquiv.toLinearMap (rayChargeMap s) =
      chargeExchangeMatrix b'.detDualEquiv.toLinearMap (rayChargeMap t)) :
    ∃! E : N ≃ₗ[ℤ] N', (∀ j, E (s j).primitiveGenerator = (t j).primitiveGenerator) ∧
      ∀ x y, b'.detDualEquiv (E x) (E y) = b.detDualEquiv x y := by
  have hrank := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  let m (j : Fin n) := (b.detDualEquiv (s j).primitiveGenerator).toAddMonoidHom
  revert e he hD
  rw [internalBlowupTower_eq_alongBoundary]
  intro e he hD
  obtain ⟨hcount, _, _, hk, hindex, _, hrel⟩ :=
    chargeIndex_bounds_of_anticanonical_cycle hΦ hrank s m
      (fun _ ↦ b.detDualEquiv_self _) (fun j ↦ (s j).surjective_detCharacter b) c
      (fun j ↦ (s j).internalCenter b (c j)) (fun j ↦ (s j).internalCenter_val b (c j))
      hT e he hD hc C hGram hspan hcan hδ
  exact existsUnique_rayChargeEquiv_of_index s t b b' hmat hcount hk hindex hrel

end PicardCycle

end TauCeti.Toric.Fan
