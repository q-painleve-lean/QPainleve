/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Center

/-!
# Center domains from charge characters

A center character that is injective on the charge kernel lies in the center domain
of every word. At any prefix, the difference of two distinct basis vectors of equal
charge is a nonzero charge relation. The prefix transports this difference into the
initial kernel, where the center character separates it from zero.
-/

public section

open AlgebraicGeometry Multiplicative QPainleve.CharacterTorus QPainleve.Cluster

namespace Quiver.Path

universe u

variable {ι k : Type u} [Fintype ι] [DecidableEq ι] [Field k]
  {N : Type*} [AddCommGroup N] {B C : SkewExchangeMatrix ι}

/-- A center character injective on the initial charge kernel meets the
distinct-center conditions at every prefix of a word. -/
theorem point_mem_centerOpen_of_injective_on_chargeKernel (w : Word B C) (P : ChargeSeed B N)
    (c : Multiplicative (ι → ℤ) →* kˣ)
    (hc : Function.Injective fun v : P.charge.ker ↦ c (ofAdd (v : ι → ℤ)))
    (x : Spec (.of k)) :
    ((pointsEquiv k (ι → ℤ)).symm c).val x ∈ w.centerOpen k P := by
  apply (w.point_mem_centerOpen_iff P c x).mpr
  intro _ p _ _ j l hjl hcharge hcenter
  let v : (p.chargeTarget P).charge.ker := ⟨Pi.single j 1 - Pi.single l 1, by
    rw [LinearMap.mem_ker, map_sub, hcharge, sub_self]⟩
  have hval : c (ofAdd (p.chargeKernelEquiv P v : ι → ℤ)) = 1 := by
    simp only [coe_chargeKernelEquiv_apply, v, map_sub, ofAdd_sub, map_div, hcenter, div_self']
  have hv : p.chargeKernelEquiv P v = 0 := hc (hval.trans (c.map_one).symm)
  have hzero : v = 0 := (p.chargeKernelEquiv P).injective (hv.trans (map_zero _).symm)
  have hj := congrArg (fun y : (p.chargeTarget P).charge.ker ↦ (y : ι → ℤ) j) hzero
  simp [v, Pi.single_eq_of_ne hjl] at hj

end Quiver.Path
