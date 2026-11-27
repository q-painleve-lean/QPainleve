/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Noncollision
public import QPainleve.Geometry.Toric.Fan.Picard.Period.Surjectivity

import Mathlib.Analysis.Real.Cardinality
import Mathlib.Data.Finsupp.Encodable
import Mathlib.LinearAlgebra.FreeModule.PID
import QPainleve.Geometry.Toric.CharacterTorus.Avoidance
import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Weight

/-!
# Compatible toric periods in all word domains

For a fixed ordered toric model, choose two injective periods related by a charge
isomorphism and an orientation sign. The period formula of Gross, Hacking and Keel
([Proposition 2.9](https://arxiv.org/html/1211.6367v5#S2)) has a fixed base character.
Avoiding its range on every nonzero charge relation also makes the two center
characters injective on the charge kernel. Their center points then belong to the
noncollision opens of all finite words from the given charge seed.
-/

public section

open AlgebraicGeometry Multiplicative QPainleve.CharacterTorus QPainleve.Cluster
open Scheme (IdealSheafData NodalCycleNumbering)
open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable (F : Type) [Field F] [IsAlgClosed F]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] {n : ℕ}
  (hΦ : Φ.IsRegular) (b : Module.Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray)

local notation "K" => LinearMap.ker (rayChargeMap s)

variable [PrestableFamily ((Φ.toricBoundaryIdeal F inferInstance).subscheme ↘ Spec (.of F))]
  [(Φ.finiteFanScheme F).IsProjectiveOver F]
  [SmoothOfRelativeDimension 2 ((Φ.finiteFanScheme F) ↘ Spec (.of F))]
  [LinearMap.IsPerfPair
    ((Chow.intersectionBilinForm F (Φ.finiteFanScheme F)).prod
      (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin n → ℤ))))]
  {α : Type*}
  {p : α → ((Φ.toricBoundaryIdeal F inferInstance).subscheme ↘ Spec (.of F)).smoothLocus}
  {a : ℕ} [NeZero a]
  (A : NodalCycleNumbering p a)
  (r : ZMod a ≃ Φ.Ray)
  (hr : ∀ j,
    (Φ.toricBoundaryIdeal F inferInstance).subscheme.dualGraphVertexEquiv p (A.vertex j) =
      Φ.boundaryNormalizationComponentEquiv F hΦ (r j))
  (hdet : ∀ j, b.detDualEquiv (r j).primitiveGenerator (r (j + 1)).primitiveGenerator = 1)
  (hnodes : ∀ j, ∃ σ : Φ.cones, (r j).toCone ≤ σ ∧ (r (j + 1)).toCone ≤ σ ∧
    (Φ.toricBoundaryIdeal F inferInstance).subschemeι
      ((Φ.toricBoundaryIdeal F inferInstance).subscheme.dualGraphEdgeEquiv p (A.edge j)).val =
      (Φ.distinguishedSection (R := F) σ) (IsLocalRing.closedPoint F))

local notation "period" => orderedBoundaryPeriod F hΦ b s A

include hr hdet hnodes in
private theorem injective_of_period_avoids_base_range (c : Fin n → Fˣ)
    (h : ∀ x : Multiplicative K, x ≠ 1 → period c x ∉ (period 1).range) :
    Function.Injective (period c) ∧
      Function.Injective (fun x : K ↦ centerCharacter c (ofAdd (x : Fin n → ℤ))) := by
  have hp : Function.Injective (period c) := (injective_iff_map_eq_one _).mpr fun x hx ↦
    by_contra fun hn ↦ h x hn (hx ▸ (period 1).range.one_mem)
  let f := (centerCharacter c).comp (Submodule.subtype K).toAddMonoidHom.toMultiplicative
  suffices Function.Injective f from ⟨hp, this.comp ofAdd.injective⟩
  apply (injective_iff_map_eq_one f).mpr
  intro x hx
  by_contra hne
  have hval : torusCharacter c (x.toAdd : Fin n → ℤ) = 1 := by
    rw [← freeAbelianCharEquiv.apply_symm_apply c,
      ← SplitTorus.apply_weightCharacter, SplitTorus.weightCharacter_def]
    exact hx
  have hbase :=
    orderedBoundaryPeriod_mul_torusCharacter F hΦ b s A r hr hdet hnodes c 1 x.toAdd
  rw [ofAdd_toAdd, hval, torusCharacter_one, mul_one, mul_one] at hbase
  exact h x hne ⟨x, hbase.symm⟩

include hr hdet hnodes in
/-- Two periods in the same ordered toric model can be chosen injective and related
by any specified linear equivalence of charge relations and orientation sign. Both
center points lie in the noncollision open of every finite word of a seed whose
charge relations are relations of the model. The words can therefore be chosen
after fixing the periods. -/
theorem exists_ordered_boundary_periods_mem_all_center_opens [Uncountable F]
    {B : SkewExchangeMatrix (Fin n)} (P : ChargeSeed B N) (hP : P.charge.ker ≤ K)
    (g : K ≃ₗ[ℤ] K) (η : ℤˣ) :
    ∃ c₀ c₁ : Fin n → Fˣ,
      Function.Injective (period c₀) ∧ Function.Injective (period c₁) ∧
      (∀ x : K, period c₁ (ofAdd x) = period c₀ (ofAdd (g x)) ^ (η : ℤ)) ∧
      ∀ ⦃C : SkewExchangeMatrix (Fin n)⦄ (w : Word B C),
        ((pointsEquiv F (Fin n → ℤ)).symm (centerCharacter c₀)).val default ∈ w.centerOpen F P ∧
        ((pointsEquiv F (Fin n → ℤ)).symm (centerCharacter c₁)).val default ∈ w.centerOpen F P := by
  let : Countable (Multiplicative K) := (Finsupp.equivFunOnFinite.symm.injective.comp
    (Subtype.val_injective.comp Multiplicative.toAdd.injective)).countable
  obtain ⟨u, hu⟩ := exists_character_avoiding
    (fun j : {x : Multiplicative K // x ≠ 1} × Multiplicative K ↦ j.1.val)
    (fun j ↦ j.1.property) (fun j ↦ period 1 j.2)
  have havoid (x : Multiplicative K) (hx : x ≠ 1) : u x ∉ (period 1).range := by
    rintro ⟨y, hy⟩
    exact hu (⟨x, hx⟩, y) hy.symm
  let q := g.toAddEquiv.toMultiplicative
  let v := (zpowGroupHom (η : ℤ)).comp (u.comp q.toMonoidHom)
  have havoid' (x : Multiplicative K) (hx : x ≠ 1) : v x ∉ (period 1).range := by
    intro hmem
    apply havoid (q x) (fun h ↦ hx (q.injective (h.trans q.map_one.symm)))
    have hpow : (v x) ^ ((η⁻¹ : ℤˣ) : ℤ) = u (q x) := by
      simp [v, ← zpow_mul, ← Units.val_mul]
    exact hpow ▸ (period 1).range.zpow_mem hmem _
  obtain ⟨c₀, hc₀⟩ := orderedBoundaryPeriod_surjective F hΦ b s A r hr hdet hnodes u
  obtain ⟨c₁, hc₁⟩ := orderedBoundaryPeriod_surjective F hΦ b s A r hr hdet hnodes v
  have ⟨hu₀, hc₀'⟩ := injective_of_period_avoids_base_range F hΦ b s A r hr hdet hnodes c₀
    (hc₀.symm ▸ havoid)
  have ⟨hu₁, hc₁'⟩ := injective_of_period_avoids_base_range F hΦ b s A r hr hdet hnodes c₁
    (hc₁.symm ▸ havoid')
  refine ⟨c₀, c₁, hu₀, hu₁, fun x ↦ ?_, fun _ w ↦ ?_⟩
  · rw [hc₀, hc₁]
    rfl
  · have hinj := Submodule.inclusion_injective hP
    exact ⟨w.point_mem_centerOpen_of_injective_on_chargeKernel P _ (hc₀'.comp hinj) _,
      w.point_mem_centerOpen_of_injective_on_chargeKernel P _ (hc₁'.comp hinj) _⟩

end TauCeti.Toric.Fan
