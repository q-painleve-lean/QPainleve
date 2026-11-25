/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.RayPoint
public import QPainleve.Geometry.Toric.Fan.Hirzebruch.CoordinateBoundary

import QPainleve.Geometry.Toric.Fan.Boundary.Component
import QPainleve.Geometry.Toric.Fan.Hirzebruch.Corner

/-!
# Closed centers on invariant Hirzebruch fibers

The ruling value identifies the fiber of a projected center. On an invariant
fiber, a closed center away from one section is either a binomial point or
the corner on the other section. The comparison retains the choice of
section at Hirzebruch index zero, where both sections have square zero.
-/

public section

open AlgebraicGeometry CategoryTheory Module PointedCone
open Scheme.IdealSheafData
open TauCeti.AlgebraicGeometry (projectiveLine)

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (e : ℤ)
  (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])

local notation "X" => Φ.algebraicRealization
local notation "z" => (IsLocalRing.closedPoint ℂ : Spec (CommRingCat.of ℂ))
local notation "p[" k "]" => projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) k 0
local notation "q" =>
  Φ.characterRuling (LinearMap.toAddMonoidHom (b.coord 1))
    (nonneg_or_nonpos_hirzebruch_ruling_character b e r hr)
local notation "sec[" j "]" => r ((![0, 2] : Fin 2 → Fin 4) j)
local notation "fib[" j "]" => r ((![1, 3] : Fin 2 → Fin 4) j)
local notation "I[" ρ "]" => Φ.rayBoundaryIdeal hΦ ρ
local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "center[" ρ "," c "]" =>
  Fan.Ray.binomialCenter ρ rankTwo (b.detDualEquiv_self (Fan.Ray.primitiveGenerator ρ))
    (Fan.Ray.surjective_detCharacter ρ b) c z

/-- A point lies on the invariant fiber ray divisor exactly when its ruling
value is the corresponding coordinate point of the projective line. -/
theorem mem_support_hirzebruch_fiber_iff (j : Fin 2) (x : X) :
    x ∈ I[fib[j]].support ↔ q x = p[j] z := by
  let : Nonempty Φ.cones := ⟨(r 0).toCone⟩
  have hp := (projectiveLine.polynomialPoint_over ℂ (RingHom.id ℂ) j (0 : ℂ)).trans
    (Spec.map_id (CommRingCat.of ℂ))
  have : IsClosedImmersion p[j] := (p[j]).isClosedImmersion_of_comp_eq_id hp
  rw [Φ.rayBoundaryIdeal_hirzebruch_eq_coordinateFiber b e hΦ r hr j, ← SetLike.mem_coe,
    support_comap, TopologicalSpace.Closeds.coe_preimage, Set.mem_preimage,
    (p[j]).support_ker, (p[j]).isClosedEmbedding.isClosed_range.closure_eq]
  exact ⟨fun ⟨y, hy⟩ ↦ hy.symm.trans (congrArg p[j] (Subsingleton.elim y z)),
    fun hx ↦ ⟨z, hx.symm⟩⟩

include hc in
/-- On a complete regular Hirzebruch surface, a closed point over a ruling
coordinate point and off one of the two invariant sections is either in
the open orbit of the fiber or at its corner on the other section. -/
theorem hirzebruch_ruling_eq_coordinatePoint_and_notMem_section_iff
    (j s : Fin 2) {x : X} (hx : IsClosed ({x} : Set X)) :
    q x = p[j] z ∧ x ∉ I[sec[s.rev]].support ↔
      (∃ c : ℂˣ, x = center[fib[j],c]) ∨
      ∃ σ : Φ.cones, Nat.card (ToricRay σ.val) = 2 ∧
        (fib[j]).toCone ≤ σ ∧ (sec[s]).toCone ≤ σ ∧ x = Φ.distinguishedPointHom σ z := by
  let : Nonempty Φ.cones := hc.nonempty_cones
  have hfib : x ∈ I[fib[j]].support ↔ q x = p[j] z :=
    mem_support_hirzebruch_fiber_iff b e hΦ r hr j x
  have hclass := Φ.mem_support_rayBoundaryIdeal_iff b hΦ hc (fib[j]) hx
  constructor
  · rintro ⟨hvalue, hoff⟩
    rcases hclass.mp (hfib.mpr hvalue) with hb | ⟨σ, hσ, hf, hp⟩
    · exact Or.inl hb
    obtain ⟨a, k, ha, _⟩ := Φ.exists_hirzebruch_section_fiber_le b e r hr hΦ hc σ hσ
    have has : a = s := by
      have hne : a ≠ s.rev := by
        intro he
        apply hoff
        rw [hp, ← he]
        exact (Φ.distinguishedPoint_mem_support_rayBoundaryIdeal_iff hΦ σ (sec[a])).mpr ha
      fin_cases a <;> fin_cases s <;> simp_all
    exact Or.inr ⟨σ, hσ, hf, has ▸ ha, hp⟩
  · intro h
    refine ⟨hfib.mp (hclass.mpr (h.imp id (fun ⟨σ, hσ, hf, _, hp⟩ ↦ ⟨σ, hσ, hf, hp⟩))), ?_⟩
    rcases h with ⟨c, rfl⟩ | ⟨σ, _, _, hs, rfl⟩
    · intro hmem
      have he := ((fib[j]).binomialCenter_mem_support_rayBoundaryIdeal_iff hΦ rankTwo
        (b.detDualEquiv_self _) ((fib[j]).surjective_detCharacter b) c (sec[s.rev])).mp hmem
      have he' := r.injective he
      fin_cases j <;> fin_cases s <;> contradiction
    · obtain ⟨f, _, hf, hdisj, _⟩ :=
        Φ.exists_hirzebruch_toric_boundary_sections_and_fibers b e hΦ r hr hc
      rw [hf 0, hf 1] at hdisj
      have hd : Disjoint (I[sec[s]].support) (I[sec[s.rev]].support) := by
        fin_cases s
        · simpa using hdisj
        · simpa using hdisj.symm
      have hd' : Disjoint (I[sec[s]].support : Set X) I[sec[s.rev]].support := by
        rw [Set.disjoint_iff_inter_eq_empty, ← TopologicalSpace.Closeds.coe_inf,
          disjoint_iff.mp hd, TopologicalSpace.Closeds.coe_bot]
      exact (Set.disjoint_left.mp hd') ((Φ.distinguishedPoint_mem_support_rayBoundaryIdeal_iff
        hΦ σ (sec[s])).mpr hs)

end TauCeti.Toric.Fan
