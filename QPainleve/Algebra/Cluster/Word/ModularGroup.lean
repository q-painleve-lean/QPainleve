/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Inversion
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.PathCategory.Basic
public import Mathlib.GroupTheory.Congruence.Basic

/-!
# Signed and unsigned cluster modular groups

At a fixed exchange matrix, the pullbacks of signed loops form a subgroup of the
automorphisms of the field of independent cluster X coordinates. The unsigned subgroup is
the image of loops using only mutations and relabelings. The point-map groups are the
opposites of the pullback subgroups. Quotienting loops by equality of X pullbacks
recovers these groups.

The signed generators are those of Bershtein, Gavrylenko and Marshakov,
*Cluster integrable systems, q-Painlevé equations and their quantization*, §3.1.
-/

public noncomputable section

namespace QPainleve.Cluster

open CategoryTheory MulOpposite Quiver

variable (k : Type*) [Field k] {ι : Type*} [DecidableEq ι] (B : SkewExchangeMatrix ι)

local notation "Aut" => (FractionRing (AddMonoidAlgebra k (ι →₀ ℤ)) ≃ₐ[k]
  FractionRing (AddMonoidAlgebra k (ι →₀ ℤ)))
local notation "Loops" => End (Prefunctor.obj (Paths.of (SkewExchangeMatrix ι)) B)

/-- The subgroup of X pullbacks represented by signed loops at `B`. -/
def signedLoopPullbacks : Subgroup Aut where
  carrier := Set.range (fun w : Word B B ↦ w.xPullback k)
  one_mem' := ⟨Path.nil, Path.xPullback_nil k⟩
  mul_mem' := by
    rintro _ _ ⟨w, rfl⟩ ⟨v, rfl⟩
    exact ⟨w.comp v, by simp⟩
  inv_mem' := by
    rintro _ ⟨w, rfl⟩
    exact ⟨w.reverse, by simp⟩

/-- The subgroup of X pullbacks represented by inversion-free loops at `B`. -/
def unsignedLoopPullbacks : Subgroup Aut where
  carrier := {f | ∃ w : Word B B, w.inversionCount = 0 ∧ w.xPullback k = f}
  one_mem' := ⟨Path.nil, Path.inversionCount_nil, Path.xPullback_nil k⟩
  mul_mem' := by
    rintro _ _ ⟨w, hw, rfl⟩ ⟨v, hv, rfl⟩
    exact ⟨w.comp v, by simp [hw, hv], by simp⟩
  inv_mem' := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨w.reverse, by simpa using hw, by simp⟩

@[simp]
theorem mem_signedLoopPullbacks_iff (f : Aut) :
    f ∈ signedLoopPullbacks k B ↔ ∃ w : Word B B, w.xPullback k = f :=
  (Iff.rfl)

@[simp]
theorem mem_unsignedLoopPullbacks_iff (f : Aut) :
    f ∈ unsignedLoopPullbacks k B ↔ ∃ w : Word B B, w.inversionCount = 0 ∧ w.xPullback k = f :=
  (Iff.rfl)

/-- An even loop represents an unsigned pullback, and each unsigned pullback has an even
representative. -/
theorem mem_unsignedLoopPullbacks_iff_exists_even (f : Aut) :
    f ∈ unsignedLoopPullbacks k B ↔ ∃ w : Word B B, Even w.inversionCount ∧ w.xPullback k = f := by
  rw [mem_unsignedLoopPullbacks_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, by simp [hw], rfl⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨v, hv, h⟩ := w.exists_xPullback_eq_of_even_inversionCount k hw
    exact ⟨v, hv, h.symm⟩

theorem unsignedLoopPullbacks_le_signedLoopPullbacks :
    unsignedLoopPullbacks k B ≤ signedLoopPullbacks k B := by
  intro f hf
  obtain ⟨w, _, hw⟩ := (mem_unsignedLoopPullbacks_iff k B f).1 hf
  exact (mem_signedLoopPullbacks_iff k B f).2 ⟨w, hw⟩

/-- The signed cluster modular group with multiplication given by composition of point maps. -/
abbrev SignedClusterModularGroup := (signedLoopPullbacks k B)ᵐᵒᵖ

/-- The unsigned cluster modular group with multiplication given by composition of point maps. -/
abbrev ClusterModularGroup := (unsignedLoopPullbacks k B)ᵐᵒᵖ

/-- The submonoid of loops built solely from mutations and relabelings. -/
def inversionFreeLoops : Submonoid Loops where
  carrier := {w | w.asHom.inversionCount = 0}
  one_mem' := Path.inversionCount_nil
  mul_mem' := by
    intro w v hw hv
    -- Endomorphism multiplication concatenates the right-hand loop first.
    exact (Path.inversionCount_comp v.asHom w.asHom).trans (by rw [hv, hw, add_zero])

@[simp]
theorem mem_inversionFreeLoops_iff (w : Loops) :
    w ∈ inversionFreeLoops B ↔ w.asHom.inversionCount = 0 :=
  (Iff.rfl)

/-- Evaluate a signed loop as an element of the point-map group. -/
def signedClusterModularGroupMap : Loops →* SignedClusterModularGroup k B where
  toFun w := op ⟨w.asHom.xPullback k, (mem_signedLoopPullbacks_iff k B _).2 ⟨w.asHom, rfl⟩⟩
  map_one' := unop_injective (Subtype.ext (Path.xPullback_nil k))
  map_mul' w v := unop_injective (Subtype.ext (Path.xPullback_comp k v.asHom w.asHom))

@[simp]
theorem signedClusterModularGroupMap_unop_coe (w : Loops) :
    ((signedClusterModularGroupMap k B w).unop : Aut) = w.asHom.xPullback k :=
  (rfl)

theorem signedClusterModularGroupMap_surjective :
    Function.Surjective (signedClusterModularGroupMap k B) := by
  intro f
  obtain ⟨w, hw⟩ := (mem_signedLoopPullbacks_iff k B _).1 f.unop.property
  exact ⟨End.of w, unop_injective (Subtype.ext hw)⟩

/-- Evaluate an inversion-free loop as an element of the unsigned point-map group. -/
def clusterModularGroupMap : inversionFreeLoops B →* ClusterModularGroup k B where
  toFun w := op ⟨w.val.asHom.xPullback k,
    (mem_unsignedLoopPullbacks_iff k B _).2
      ⟨w.val.asHom, (mem_inversionFreeLoops_iff B _).1 w.property, rfl⟩⟩
  map_one' := unop_injective (Subtype.ext (Path.xPullback_nil k))
  map_mul' w v := unop_injective (Subtype.ext (Path.xPullback_comp k v.val.asHom w.val.asHom))

@[simp]
theorem clusterModularGroupMap_unop_coe (w : inversionFreeLoops B) :
    ((clusterModularGroupMap k B w).unop : Aut) = w.val.asHom.xPullback k :=
  (rfl)

theorem clusterModularGroupMap_surjective :
    Function.Surjective (clusterModularGroupMap k B) := by
  intro f
  obtain ⟨w, hw, he⟩ := (mem_unsignedLoopPullbacks_iff k B _).1 f.unop.property
  exact ⟨⟨End.of w, (mem_inversionFreeLoops_iff B _).2 hw⟩, unop_injective (Subtype.ext he)⟩

/-- Two signed loops give the same group element exactly when their X pullbacks agree. -/
theorem signedClusterModularGroupMap_eq_iff (w v : Loops) :
    signedClusterModularGroupMap k B w = signedClusterModularGroupMap k B v ↔
      w.asHom.xPullback k = v.asHom.xPullback k := by
  rw [← unop_injective.eq_iff, ← Subtype.coe_injective.eq_iff]
  simp

/-- Two inversion-free loops give the same group element exactly when their X pullbacks agree. -/
theorem clusterModularGroupMap_eq_iff (w v : inversionFreeLoops B) :
    clusterModularGroupMap k B w = clusterModularGroupMap k B v ↔
      w.val.asHom.xPullback k = v.val.asHom.xPullback k := by
  rw [← unop_injective.eq_iff, ← Subtype.coe_injective.eq_iff]
  simp

/-- The quotient of signed loops by equality of X pullbacks is the signed point-map group. -/
def signedLoopQuotientMulEquiv :
    (Con.ker (signedClusterModularGroupMap k B)).Quotient ≃* SignedClusterModularGroup k B :=
  Con.quotientKerEquivOfSurjective _ (signedClusterModularGroupMap_surjective k B)

@[simp]
theorem signedLoopQuotientMulEquiv_mk (w : Loops) :
    signedLoopQuotientMulEquiv k B ↑w = signedClusterModularGroupMap k B w :=
  (rfl)

/-- The quotient of inversion-free loops by equality of X pullbacks is the unsigned
point-map group. -/
def unsignedLoopQuotientMulEquiv :
    (Con.ker (clusterModularGroupMap k B)).Quotient ≃* ClusterModularGroup k B :=
  Con.quotientKerEquivOfSurjective _ (clusterModularGroupMap_surjective k B)

@[simp]
theorem unsignedLoopQuotientMulEquiv_mk (w : inversionFreeLoops B) :
    unsignedLoopQuotientMulEquiv k B ↑w = clusterModularGroupMap k B w :=
  (rfl)

end QPainleve.Cluster
