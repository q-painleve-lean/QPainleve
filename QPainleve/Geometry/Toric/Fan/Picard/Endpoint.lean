/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.ChargeKernel.Basic
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
With these bounds the exchange matrix determines the ambient integral lattice and
the labelled primitive ray generators, together with their determinant pairing.
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower TopologicalSpace
open TauCeti.AlgebraicGeometry LineBundleClass
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

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

open QPainleve.Cluster in
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
  obtain ⟨hcount, _, _, hk, hdiv, _, x, hx, hsqx⟩ :=
    chargeIndex_bounds_of_nodal_anticanonical_cycle hΦ hdim s m hm hprim c J hJ hT e he hD hc
      hCart hnodal hnef hsq hcan hδ p node hp hinc
  obtain ⟨E, hE, hpair⟩ := exists_charge_lattice_equiv
    (v₁ := rayChargeMap s) (v₂ := rayChargeMap t) b b'
    b.detDualEquiv_self b'.detDualEquiv_self
    b.detDualEquiv_apply_basis_zero_one b'.detDualEquiv_apply_basis_zero_one
    (fun j ↦ by simpa only [rayChargeMap_single] using
      TauCeti.isPrimitive_def.mp (s j).isPrimitiveGenerator.isPrimitive)
    (fun j ↦ by simpa only [rayChargeMap_single] using
      TauCeti.isPrimitive_def.mp (t j).isPrimitiveGenerator.isPrimitive)
    hmat (Nat.pos_of_ne_zero (NeZero.ne k)) hk
    (by simpa only [Fintype.card_fin] using hcount) hdiv fun h ↦
      ⟨x, TauCeti.isPrimitive_def.mp hx, by simpa only [h, Nat.cast_ofNat] using hsqx⟩
  exact ⟨E, fun j ↦ by simpa only [rayChargeMap_single] using hE (Pi.single j 1), hpair⟩

end TauCeti.Toric.Fan
