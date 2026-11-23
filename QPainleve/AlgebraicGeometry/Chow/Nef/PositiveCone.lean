/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.Nef.Cone
import TauCeti.Topology.Algebra.Module.ModuleTopology

/-!
# The nef cone from the positive component and negative curves

A prime divisor of nonnegative square lies in the closure of the ample component.
When this closure lies in the closed curve cone, nefness inside the closure is cut
out by the negative prime curves. The nef cone is the closure of these inequalities
inside the open positive component.

This is the cone argument of Gross, Hacking and Keel,
[*Moduli of surfaces with an anti-canonical cycle*, Lemmas 2.14–2.15][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S2
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory QuadraticMap Set TopologicalSpace
open scoped TensorProduct

namespace TauCeti.AlgebraicGeometry.Chow

universe u

variable (k : Type u) [Field k] [Infinite k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "V(" X ")" => (ℝ ⊗[ℤ] Additive (LineBundleClass X))
local notation "B" => realIntersectionBilinForm k X
local notation "Q" => LinearMap.BilinMap.toQuadraticMap B
local notation "ι" => (fun a : LineBundleClass X ↦ (1 : ℝ) ⊗ₜ[ℤ] Additive.ofMul a)
local notation "c" => realPrimeDivisorClass k (X := X)
local notation "C(" h ")" => connectedComponentIn (Set.ofPred (fun x : V(X) ↦ 0 < Q x)) (ι h)

variable [FiniteDimensional ℝ V(X)] [TopologicalSpace V(X)] [IsModuleTopology ℝ V(X)]
  {h : LineBundleClass X}

local instance : IsTopologicalAddGroup V(X) := IsModuleTopology.isTopologicalAddGroup ℝ _

local instance : T2Space V(X) := TauCeti.ModuleTopology.t2Space (Module.Free.chooseBasis ℝ _)

/-- If the closed cone of curves contains the closed positive component, then a nef
class lies in that component. Within the component, the inequalities for negative
prime curves suffice for nefness. -/
theorem mem_nefCone_iff_mem_closure_and_nonneg_negative
    (hQ : (Q).Nondegenerate) (hsig : sigPos Q ≤ 1) (hh : h.IsAmple)
    (hpos : closure C(h) ⊆ (closedCurveCone k (X := X) : Set V(X))) {x : V(X)} :
    x ∈ nefCone k ↔ x ∈ closure C(h) ∧
      ∀ p : CodimensionOnePoint X, B (c p) (c p) < 0 → 0 ≤ B x (c p) := by
  rw [mem_nefCone]
  constructor
  · intro hx
    have hhh : 0 < Q (ι h) := realIntersectionBilinForm_pos_of_isAmple k hh hh
    have hx' := (nonneg_on_closedCurveCone_iff k
      (LinearMap.toContinuousLinearMap (B x))).mpr hx
    rw [closure_connectedComponentIn_pos_eq_of_isAmple k hQ hsig hh]
    have hside (y : V(X)) : 0 ≤ polar Q (ι h) y ↔ 0 ≤ B (ι h) y := by
      rw [polar_realIntersectionBilinForm k, mul_nonneg_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)]
    have hdual := QuadraticForm.nonneg_and_polar_nonneg_iff_forall hQ hsig hhh (x := x)
    have ⟨hsq, hpair⟩ := hdual.mpr fun y hy hhy ↦ by
      rw [polar_realIntersectionBilinForm k]
      apply mul_nonneg (by norm_num)
      exact hx' y (hpos (by
        rw [closure_connectedComponentIn_pos_eq_of_isAmple k hQ hsig hh]
        exact ⟨hy, (hside y).mp hhy⟩))
    exact ⟨⟨hsq, (hside x).mp hpair⟩, fun p _ ↦ hx p⟩
  · rintro ⟨hx, hneg⟩ p
    by_cases hp : B (c p) (c p) < 0
    · exact hneg p hp
    · exact realIntersectionBilinForm_nonneg_of_mem_closure_connectedComponentIn_pos
        k hQ hsig hh hx (realPrimeDivisorClass_mem_closure_connectedComponentIn_pos
          k hQ hsig hh p (le_of_not_gt hp))

/-- The real nef cone is the closure of the positive-component classes that
pair nonnegatively with every negative prime curve, provided the positive
component is contained in the closed cone of curves. -/
theorem coe_nefCone_eq_closure_inter_negative
    (hQ : (Q).Nondegenerate) (hsig : sigPos Q ≤ 1) (hh : h.IsAmple)
    (hpos : closure C(h) ⊆ (closedCurveCone k (X := X) : Set V(X))) :
    (nefCone k (X := X) : Set V(X)) = closure (C(h) ∩
      {x | ∀ p : CodimensionOnePoint X, B (c p) (c p) < 0 → 0 ≤ B x (c p)}) := by
  have hmem (x : V(X)) := mem_nefCone_iff_mem_closure_and_nonneg_negative k hQ hsig hh hpos (x := x)
  refine Set.Subset.antisymm ?_ ((nefCone k (X := X)).isClosed.closure_subset_iff.mpr fun x hx ↦
    (hmem x).mpr ⟨subset_closure hx.1, hx.2⟩)
  intro x hx
  obtain ⟨hxc, hxn⟩ := (hmem x).mp hx
  rw [closure_connectedComponentIn_pos_eq_of_isAmple k hQ hsig hh] at hxc
  have hhh : 0 < Q (ι h) := realIntersectionBilinForm_pos_of_isAmple k hh hh
  have hc : Continuous (fun t : ℝ ↦ x + t • ι h) := by fun_prop
  have h0 : (0 : ℝ) ∈ closure (Ioi 0) := by simp [closure_Ioi]
  have happrox : x ∈ closure ((fun t : ℝ ↦ x + t • ι h) '' Ioi 0) := by
    simpa only [zero_smul, add_zero] using mem_closure_image hc.continuousAt h0
  apply closure_mono (image_subset_iff.mpr ?_) happrox
  intro t ht
  have ht' : 0 < t := ht
  refine ⟨QuadraticForm.add_smul_mem_connectedComponentIn_pos hQ hsig hhh hxc.1 ?_ ht', ?_⟩
  · rw [polar_realIntersectionBilinForm k]
    exact mul_nonneg (by norm_num) hxc.2
  · intro p hp
    rw [(B).add_left, (B).smul_left]
    exact add_nonneg (hxn p hp)
      (mul_nonneg ht'.le (realIntersectionBilinForm_realPrimeDivisorClass_pos k hh p).le)

end TauCeti.AlgebraicGeometry.Chow
