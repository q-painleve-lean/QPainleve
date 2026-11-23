/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.ChargeKernel.Basic
public import QPainleve.Geometry.Toric.Fan.Picard.CycleNumerics

import Mathlib.GroupTheory.IndexNSmul
import QPainleve.SignedClusterModularGroup.Endpoint

/-!
# Integral identification of the ray lattices of toric presentations

For a toric presentation of a primitive square-zero anticanonical cycle, its Picard
numerics supply precisely the index and norm conditions needed by
`QPainleve.Cluster.exists_charge_lattice_equiv`. Thus the exchange matrix determines
the ambient oriented ray lattice with its labeled primitive vectors. The other set
of vectors need only come from rays in an oriented rank-two fan.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open QPainleve QPainleve.BlowupTower QPainleve.Cluster
open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {N N' V V' : Type} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}

variable {n : ℕ} (s : Fin n → Φ.Ray) (t : Fin n → Ψ.Ray)

private theorem rayChargeMap_primitive (j : Fin n) :
    IsPrimitive (rayChargeMap s (Pi.single j 1)) := by
  rw [rayChargeMap_single]
  exact (s j).isPrimitiveGenerator.isPrimitive

private theorem rayChargeEquiv_ext [Module.IsTorsionFree ℤ N']
    (hindex : (rayChargeMap s).range.toAddSubgroup.index ≠ 0)
    {E F : N ≃ₗ[ℤ] N'}
    (hE : ∀ j, E (s j).primitiveGenerator = (t j).primitiveGenerator)
    (hF : ∀ j, F (s j).primitiveGenerator = (t j).primitiveGenerator) : E = F := by
  have hcomp : E.toLinearMap.comp (rayChargeMap s) = F.toLinearMap.comp (rayChargeMap s) := by
    apply (Pi.basisFun ℤ (Fin n)).ext
    simp [hE, hF]
  ext x
  apply AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree hindex
  obtain ⟨a, ha⟩ := (rayChargeMap s).range.toAddSubgroup.nsmul_index_mem x
  have h := LinearMap.congr_fun hcomp a
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, ha, map_nsmul,
    nsmulAddMonoidHom_apply] using h

variable [Nonempty Φ.cones] [Φ.algebraicRealization.IsProjectiveOver ℂ]
  (b : Module.Basis (Fin 2) ℤ N) (b' : Module.Basis (Fin 2) ℤ N') (c : Fin n → ℂˣ)
  {X Y : Scheme} [X.Over (Spec (.of ℂ))] [X.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of ℂ))]
  [rational : Scheme.IsRationalOver (X ↘ Spec (.of ℂ))]
  {D : X.IdealSheafData} {d : ℕ} {T : BlowupTower X d Y}

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
    (hcan : ∑ j, C j = -Additive.ofMul (LineBundleClass.mk (canonicalBundle ℂ X 2)))
    (hδ : IsPrimitive (∑ j, C j))
    (hmat : chargeExchangeMatrix b.detDualEquiv.toLinearMap (rayChargeMap s) =
      chargeExchangeMatrix b'.detDualEquiv.toLinearMap (rayChargeMap t)) :
    ∃! E : N ≃ₗ[ℤ] N', (∀ j, E (s j).primitiveGenerator = (t j).primitiveGenerator) ∧
      ∀ x y, b'.detDualEquiv (E x) (E y) = b.detDualEquiv x y := by
  have hrank := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  let m (j : Fin n) := (b.detDualEquiv (s j).primitiveGenerator).toAddMonoidHom
  -- Rewrite the ordered model together with the comparisons that depend on it.
  revert e he hD
  rw [internalBlowupTower_eq_alongBoundary]
  intro e he hD
  obtain ⟨hcount, -, -, hk, hindex, -, hrel⟩ :=
    chargeIndex_bounds_of_anticanonical_cycle hΦ hrank s m
      (fun _ ↦ b.detDualEquiv_self _) (fun j ↦ (s j).surjective_detCharacter b) c
      (fun j ↦ (s j).internalCenter b (c j)) (fun j ↦ (s j).internalCenter_val b (c j))
      hT e he hD hc C hGram hspan hcan hδ
  have hdet (M : Type) [AddCommGroup M] (a : Module.Basis (Fin 2) ℤ M) :
      a.detDualEquiv (a 0) (a 1) = 1 := by
    simp [Module.Basis.det_apply, Module.Basis.toMatrix_apply, Matrix.det_fin_two]
  obtain ⟨E, hE, hpair⟩ := exists_charge_lattice_equiv b b'
    (fun x ↦ b.detDualEquiv_self x) (fun x ↦ b'.detDualEquiv_self x) (hdet N b) (hdet N' b')
    (fun j ↦ isPrimitive_def.mp (rayChargeMap_primitive s j))
    (fun j ↦ isPrimitive_def.mp (rayChargeMap_primitive t j)) hmat
    (Nat.pos_of_ne_zero (NeZero.ne k)) hk (by simpa only [Fintype.card_fin] using hcount) hindex
    (fun h ↦ by
      rw [h] at hrel
      obtain ⟨x, hx, hsq⟩ := hrel
      exact ⟨x, isPrimitive_def.mp hx, hsq⟩)
  have hE' (j : Fin n) : E (s j).primitiveGenerator = (t j).primitiveGenerator := by
    simpa only [rayChargeMap_single] using hE (Pi.single j 1)
  let : Module.Free ℤ N' := Module.Free.of_basis b'
  have hnz : (rayChargeMap s).range.toAddSubgroup.index ≠ 0 := by
    intro hz
    simp [hz, NeZero.ne k] at hindex
  exact ⟨E, ⟨hE', hpair⟩, fun F hF ↦ rayChargeEquiv_ext s t hnz hF.1 hE'⟩

end TauCeti.Toric.Fan
