/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
public import QPainleve.SignedClusterModularGroup.Realization.Boundary

import QPainleve.AlgebraicGeometry.Curves.Node.NumberedPrime
import QPainleve.SignedClusterModularGroup.Boundary.Intersection

/-!
# Reversing involutions of marked anticanonical cycles

The actual numbered components and nodes of a nef square-zero boundary give the
negative cycle Laplacian in the Picard marking. For a primitive anticanonical
boundary on a rational surface, the marked lattice then contains an involution
with negative sign. Its action on the boundary and its orthogonal complement
are supplied by the integral construction `exists_cycle_reversing_involution`.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti TauCeti.AlgebraicGeometry LineBundleClass
open Scheme Scheme.IdealSheafData LinearMap

universe u

namespace QPainleve.SignedClusterModularGroup.MarkedSurface

variable {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ} [NeZero n] {L : Type u}
  [AddCommGroup L] {B : LinearMap.BilinForm ℤ L} {X : Scheme.{u}}
  (M : MarkedSurface k n B X)

local notation "S" => Spec (CommRingCat.of k)
local notation "f" => (M.surface ↘ S)
local notation "D" => M.pair.hom.left.ker
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "K" => LineBundleClass.mk (QPainleve.canonicalBundle k M.surface 2)

/-- The Gram matrix of a marked nef square-zero cycle is the negative cycle Laplacian.
The two nodes of a two-component boundary contribute separately. -/
theorem intersectionForm_boundaryClass (hD : (D).IsEffectiveCartier)
    (hnef : (classOf(hD)).IsNef k f)
    (hsq : Chow.classIntersectionNumber k M.surface classOf(hD) classOf(hD) = 0)
    (i j : ZMod n) :
    B (M.boundaryClass hD i) (M.boundaryClass hD j) =
      (-2 : ℤ) * (if i = j then 1 else 0) +
        (if j = i + 1 then 1 else 0) + (if j = i - 1 then 1 else 0) := by
  let : M.surface.IsProjectiveOver k := M.projective
  let : SmoothOfRelativeDimension 2 f := M.smooth
  let : PrestableFamily ((D).subscheme ↘ S) := M.prestable_boundaryImage
  let A := M.imageCycle
  let p := (A.boundaryPrimeEquiv hD).toEmbedding.trans (D).boundaryPrimeEmbedding
  have hp (a : ZMod n) : p a = M.boundaryPrime hD a := by
    let : PrestableFamily (M.boundary ↘ S) := M.prestable
    apply Subtype.ext
    simp only [p, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
      coe_boundaryPrimeEmbedding, NodalCycleNumbering.boundaryPrimeEquiv_apply_val,
      M.coe_boundaryPrime]
    exact M.imageCycle_genericPoint a
  have hprimes : (p : ZMod n → CodimensionOnePoint M.surface) = M.boundaryPrime hD := funext hp
  have hsupport (q : CodimensionOnePoint M.surface) : (q : M.surface) ∈ (D).support ↔
      q ∈ Set.range p := by
    rw [hprimes]
    exact (M.mem_range_boundaryPrime_iff hD q).symm
  have hinc (a b : ZMod n) (hab : a ≠ b) :
      closure {(p a : M.surface)} ∩ closure {(p b : M.surface)} =
        A.ambientNode '' {e | (e = a ∧ b = a + 1) ∨ (e = b ∧ a = b + 1)} := by
    simpa only [p, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
      coe_boundaryPrimeEmbedding] using A.closure_boundaryPrime_inter_of_ne hD hab
  rw [← M.intersectionBilinForm_picardMarking, M.picardMarking_boundaryClass,
    M.picardMarking_boundaryClass, ← hp i, ← hp j]
  exact BoundaryCycle.intersectionBilinForm_eq_of_nodal_cycle hD
    PrestableFamily.atWorstNodalOfRelativeDimensionOne hnef hsq p
    ⟨A.ambientNode, A.ambientNode_injective⟩ hsupport hinc i j

variable [Scheme.IsRationalOver (M.surface ↘ Spec (CommRingCat.of k))]

local notation "d[" h "]" => M.boundaryClass h
local notation "δ[" h "]" => ∑ j, d[h] j

/-- The sum of the marked anticanonical cycle classes is characteristic. -/
theorem isCharacteristic_sum_boundaryClass (hD : (D).IsEffectiveCartier)
    (hcan : letI : SmoothOfRelativeDimension 2 f := M.smooth
      classOf(hD) = K⁻¹) :
    B.IsCharacteristic (δ[hD]) := by
  let : M.surface.IsProjectiveOver k := M.projective
  let : SmoothOfRelativeDimension 2 f := M.smooth
  let : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  let := (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hform : Chow.intersectionBilinForm k M.surface = Chow.classIntersectionBilinForm k
      (topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)) := by
    ext x y
    simp only [Chow.intersectionBilinForm_apply, Chow.classIntersectionBilinForm_apply]
  have hchar := Chow.isCharacteristic_canonicalBundle_of_isRationalOver k M.surface
  have hneg := BilinForm.isCharacteristic_neg_iff.mpr hchar
  apply M.marking.isCharacteristic_apply_iff.mp
  have hsum : M.marking (δ[hD]) = -Additive.ofMul K := by
    rw [← M.picardMarking_apply, M.picardMarking_sum_boundaryClass, hcan, ofMul_inv]
  exact hsum.symm ▸ hform.symm ▸ hneg

open SignedBoundaryIsometryGroup

local notation "cartier" => M.isEffectiveCartier_boundaryIdeal

/-- A primitive nef square-zero anticanonical cycle on a marked rational surface admits a
signed Picard involution that reflects the numbered components about a component. It fixes the
total cycle and a square `-1` class meeting that component once. On the orthogonal complement
the involution is negation corrected in the direction of the total cycle. -/
theorem exists_marked_boundary_reversing_involution
    (hcan : letI : SmoothOfRelativeDimension 2 f := M.smooth
      classOf(cartier) = K⁻¹) (hnef : (classOf(cartier)).IsNef k f)
    (hsq : Chow.classIntersectionNumber k M.surface classOf(cartier) classOf(cartier) = 0)
    (hprim : IsPrimitive (Additive.ofMul classOf(cartier))) :
    ∃ (j₀ : ZMod n) (a : L) (s : signedBoundaryIsometryGroup B d[cartier]),
      B a a = -1 ∧ (∀ j, B a (d[cartier] j) = if j = j₀ then 1 else 0) ∧
      sign B d[cartier] s = -1 ∧ s * s = 1 ∧
      (toIsometry B d[cartier] s).val a = a ∧
      (toIsometry B d[cartier] s).val (δ[cartier]) = δ[cartier] ∧
      (∀ j, (toIsometry B d[cartier] s).val (d[cartier] j) = d[cartier] (2 * j₀ - j)) ∧
      (∀ x, x ∈ B.orthogonal (Submodule.span ℤ (Set.range d[cartier])) →
        (toIsometry B d[cartier] s).val x = -x + (2 * B x a) • (δ[cartier])) := by
  let hD := cartier
  let : M.surface.IsProjectiveOver k := M.projective
  let : SmoothOfRelativeDimension 2 f := M.smooth
  let : B.IsPerfPair := M.isPerfPair_of_isRationalOver
  let : Module.Free ℤ (Additive (LineBundleClass M.surface)) :=
    M.surface.free_picard_of_isRationalOver k
  let : Module.Finite ℤ (Additive (LineBundleClass M.surface)) :=
    M.surface.finite_picard_of_isRationalOver k
  let : Module.Free ℤ L := Module.Free.of_equiv M.picardMarking.symm
  let : Module.Finite ℤ L := Module.Finite.of_surjective _ M.picardMarking.symm.surjective
  have hpair (x y : L) : B x y =
      Chow.classIntersectionNumber k M.surface (M.picardMarking x).toMul
        (M.picardMarking y).toMul :=
    (M.intersectionBilinForm_picardMarking x y).symm.trans (Chow.intersectionBilinForm_apply ..)
  have hSymm : B.IsSymm := ⟨fun x y ↦
    (hpair x y).trans ((Chow.classIntersectionNumber_comm _ _).trans (hpair y x).symm)⟩
  have hprimitive : IsPrimitive (δ[hD]) :=
    M.picardMarking.isPrimitive_iff.mp (by rwa [M.picardMarking_sum_boundaryClass])
  have hchar (x : L) : Even (B x x - B x (δ[hD])) := by
    rw [even_iff_two_dvd, dvd_sub_comm, hSymm.eq x (δ[hD])]
    exact (BilinForm.isCharacteristic_iff.mp (M.isCharacteristic_sum_boundaryClass hD hcan)) x
  obtain ⟨j₀, a, g, haa, ha, hg, hga, hgδ, hgd, hgK⟩ :=
    exists_cycle_reversing_involution L B hSymm (IsPerfPair.bijective_left B) n d[hD]
      (M.intersectionForm_boundaryClass hD hnef hsq) (isPrimitive_def.mp hprimitive) hchar
  have hrev : ∃ t : ZMod n, ∀ j, g (d[hD] j) = d[hD] (-j + t) :=
    ⟨2 * j₀, fun j ↦ by simpa only [sub_eq_neg_add] using hgd j⟩
  let s := reversal g hrev
  have hs : ⇑(toIsometry B d[hD] s).val = ⇑g := by
    simp only [s, toIsometry_apply, coe_reversal,
      BilinForm.coe_isometryGroupEquivIsometryEquiv_symm]
  refine ⟨j₀, a, s, haa, ha, by simp [s], reversal_mul_self g hrev hg, ?_⟩
  simp only [hs]
  refine ⟨hga, hgδ, hgd, fun x hx ↦ hgK x fun j ↦ ?_⟩
  exact (hSymm.eq _ _).trans
    (B.mem_orthogonal_iff.mp hx _ (Submodule.subset_span (Set.mem_range_self j)))

end QPainleve.SignedClusterModularGroup.MarkedSurface
