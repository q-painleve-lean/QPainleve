/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
public import QPainleve.AlgebraicGeometry.LineBundle.EffectiveClass

import QPainleve.AlgebraicGeometry.Blowup.Tower.Pluricanonical
import QPainleve.AlgebraicGeometry.CartierDivisor.ZeroDivisor
import QPainleve.AlgebraicGeometry.Modules.Differentials.Restriction
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.TwistingSheaf

/-!
# Pluricanonical vanishing on rational surfaces

The spaces of global sections of positive tensor powers of the canonical bundle
vanish on smooth projective rational surfaces. The comparison uses
`IsClosedPointTower.nonempty_cohomologyZero_pluricanonicalLinearEquiv`
on the two projections of a common resolution with the plane. For the bicanonical
case, see [Vakil, *Complex Algebraic Surfaces*, Class 16, §1.2][Vakil].

[Vakil]: https://math.stanford.edu/~vakil/02-245/sclass16A.pdf
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.LineBundleClass TauCeti.SymmetricAlgebra
open AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] [IsAlgClosed k]
  (X : Scheme.{u}) [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [Scheme.IsRationalOver (X ↘ Spec (.of k))]

local notation "S" => Spec (CommRingCat.of k)
local notation "P" => Proj (homogeneousSubmodule k (Fin 3 → k))
local notation "ω[" Y "]" => canonicalBundle k Y 2

/-- The space of global sections of any positive tensor power of the canonical bundle
of a smooth projective rational surface over an algebraically closed field vanishes. -/
theorem subsingleton_cohomology_zero_pluricanonical_of_isRationalOver {m : ℕ} (hm : 0 < m) :
    Subsingleton (Cohomology ((ω[X]).tensorPow m).obj 0) := by
  obtain ⟨_, _, V, W, T, U, e, hT, hU, he⟩ :=
    X.exists_common_pointBlowup_resolution_projectivePlane k
  let : V.Over S := ⟨T.toBase ≫ X ↘ S⟩
  let : W.Over S := ⟨U.toBase ≫ P ↘ S⟩
  have : T.toBase.IsOver S := ⟨rfl⟩
  have : U.toBase.IsOver S := ⟨rfl⟩
  have : e.hom.IsOver S := ⟨he⟩
  have : SmoothOfRelativeDimension 2 (V ↘ S) := hT.smoothOfRelativeDimension (X ↘ S)
  have : SmoothOfRelativeDimension 2 (W ↘ S) := hU.smoothOfRelativeDimension (P ↘ S)
  obtain ⟨eT⟩ := hT.nonempty_cohomologyZero_pluricanonicalLinearEquiv k m
  obtain ⟨eU⟩ := hU.nonempty_cohomologyZero_pluricanonicalLinearEquiv k m
  let L := (ω[V]).tensorPow m
  have hL : LineBundleClass.mk ((InvertibleSheaf.pullback e.hom).obj L) =
      LineBundleClass.mk ((ω[W]).tensorPow m) := by
    dsimp only [L]
    rw [← pullback_mk, mk_tensorPow, pullback_pow, mk_tensorPow, pullback_mk,
      mk_pullback_canonicalBundle]
  obtain ⟨eL⟩ := mk_eq_mk_iff.mp hL
  let eVW := (e.hom.cohomologyPullbackBaseLinearEquivOfIsIso k L.obj 0).symm.trans
    (cohomologyBaseLinearEquivOfIso k eL 0)
  let b := Pi.basisFun k (Fin 3)
  let d : ℤ := (-3) * (m : ℤ)
  let H := Proj.symmetricAlgebraTwistingBundle k (Fin 3 → k) d
  have hH : LineBundleClass.mk ((ω[P]).tensorPow m) = LineBundleClass.mk H := by
    apply Additive.ofMul.injective
    apply b.picardTwistEquiv.injective
    rw [mk_tensorPow, ofMul_pow, map_nsmul, mk_canonicalBundle_projectivePlane]
    simp [H, d, mul_comm]
  obtain ⟨eH⟩ := mk_eq_mk_iff.mp hH
  have hd : d < 0 := by dsimp [d]; omega
  have : Subsingleton (Cohomology H.obj 0) := by
    dsimp only [H]
    rw [Proj.symmetricAlgebraTwistingBundle_obj]
    exact subsingleton_cohomology_zero_twistingSheaf_of_neg hd b
  exact (eT.trans (eVW.trans (eU.symm.trans
    (cohomologyBaseLinearEquivOfIso k eH 0)))).injective.subsingleton

/-- Positive multiples of the canonical class of a smooth projective rational surface
over an algebraically closed field are ineffective. -/
theorem not_mem_effectiveClasses_nsmul_canonical [IsIntegral X] {m : ℕ}
    (hm : 0 < m) : m • Additive.ofMul (LineBundleClass.mk ω[X]) ∉ X.effectiveClasses := by
  intro h
  obtain ⟨D, hD, hclass⟩ := mem_effectiveClasses.mp h
  let L := (ω[X]).tensorPow m
  have hL : LineBundleClass.mk L = D.toLineBundleClass := by
    simpa only [L, mk_tensorPow, toMul_nsmul, toMul_ofMul] using congrArg Additive.toMul hclass.symm
  have hvan := X.subsingleton_cohomology_zero_pluricanonical_of_isRationalOver k hm
  have : Subsingleton Γ(L.obj, ⊤) :=
    (cohomologyZeroBaseLinearEquiv k X L.obj).surjective.subsingleton
  obtain ⟨s, hs, _⟩ := L.exists_zeroDivisor_eq hD hL.symm
  exact hs (Subsingleton.elim s 0)

end AlgebraicGeometry.Scheme
