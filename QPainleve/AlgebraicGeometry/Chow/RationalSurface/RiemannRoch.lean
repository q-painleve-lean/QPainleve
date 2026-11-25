/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
public import QPainleve.AlgebraicGeometry.LineBundle.EffectiveClass

import QPainleve.AlgebraicGeometry.Blowup.Tower.Cohomology
import QPainleve.AlgebraicGeometry.Blowup.Tower.SecondCohomology
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Effectivity
import QPainleve.AlgebraicGeometry.Modules.Differentials.Restriction

/-!
# Riemann–Roch effectivity on rational surfaces

If a line bundle has positive Euler characteristic, it or its canonical complement has
a nonzero section. On a common resolution with the projective plane, the two plane
degrees sum to `-3`. At least one degree is greater than `-3`, so that bundle has
vanishing second cohomology on the resolution. For the canonical complement, the
comparison back to the surface uses the exceptional coefficient one.

See [Hacking, *Compact Complex Surfaces*, Theorem 5.2][Hacking] for the surface
Riemann–Roch formula.

[Hacking]: https://paulhacking.github.io/surfaces.pdf#page=30
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry TauCeti.SymmetricAlgebra
open AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry.LineBundleClass TauCeti.AlgebraicGeometry.Scheme.CartierDivisor

universe u

variable (k : Type u) [Field k] [algClosed : IsAlgClosed k]

local notation "S" => Spec (CommRingCat.of k)
local notation "P" => Proj (homogeneousSubmodule k (Fin 3 → k))
local notation "ω[" Y "]" => canonicalBundle k Y 2
local notation "K[" Y "]" => LineBundleClass.mk (ω[Y])
local notation "degree" => Module.Basis.picardTwistEquiv (Pi.basisFun k (Fin 3))
local notation "L†" L:arg => InvertibleSheaf.tensorProduct (ω[_]) (InvertibleSheaf.dual L)

namespace AlgebraicGeometry.Scheme

include algClosed in
private theorem subsingleton_cohomology_two_or_of_plane_marking
    {W : Scheme.{u}} {n : ℕ} {U : BlowupTower P n W} (hU : IsClosedPointTower P U) :
    let : W.Over S := ⟨U.toBase ≫ (P ↘ S)⟩
    let : SmoothOfRelativeDimension 2 (W ↘ S) := hU.smoothOfRelativeDimension (P ↘ S)
    ∀ M N : InvertibleSheaf W, LineBundleClass.mk N = K[W] * (LineBundleClass.mk M)⁻¹ →
      Subsingleton (Cohomology M.obj 2) ∨ Subsingleton (Cohomology N.obj 2) := by
  intro _ _ M N hN
  have : IsNoetherian P := isNoetherian_of_finiteType (P ↘ S)
  let mark := U.picardMarking hU (P ↘ S)
  let a := mark.symm (Additive.ofMul (LineBundleClass.mk M))
  let b := mark.symm (Additive.ofMul (LineBundleClass.mk N))
  have hk : mark.symm (Additive.ofMul K[W]) = (Additive.ofMul K[P], fun _ ↦ 1) :=
    (LinearEquiv.symm_apply_eq mark).mpr (picardMarking_canonicalClass k hU).symm
  have hab : b = (Additive.ofMul K[P], fun _ ↦ 1) - a := by
    dsimp only [b, a]
    rw [hN, ← div_eq_mul_inv, ofMul_div, map_sub, hk]
  have hdegree : degree b.1 = -3 - degree a.1 := by
    rw [hab, Prod.fst_sub, map_sub, mk_canonicalBundle_projectivePlane,
      (Pi.basisFun k (Fin 3)).picardTwistEquiv_apply_twist]
  have hmark (L : InvertibleSheaf W) :
      U.picardHom (mark.symm (Additive.ofMul (LineBundleClass.mk L))) =
        Additive.ofMul (LineBundleClass.mk L) :=
    (U.picardMarking_apply hU (P ↘ S) _).symm.trans (mark.apply_symm_apply _)
  by_cases ha : -3 < degree a.1
  · exact Or.inl (hU.subsingleton_cohomology_two_of_plane_degree_gt_neg_three k
      a M (hmark M) ha)
  · exact Or.inr (hU.subsingleton_cohomology_two_of_plane_degree_gt_neg_three k
      b N (hmark N) (by omega))

variable {X V : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

variable [X.IsProjectiveOver k] [rational : Scheme.IsRationalOver (X ↘ Spec (.of k))]

include algClosed rational in
/-- On a smooth projective rational surface, at least one of a line bundle and its
canonical complement has vanishing second cohomology. -/
theorem subsingleton_cohomology_two_or_canonical_complement_of_isRationalOver
    (L : InvertibleSheaf X) :
    Subsingleton (Cohomology L.obj 2) ∨ Subsingleton (Cohomology (L† L).obj 2) := by
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral X := rational.isIntegral_of_smooth
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  obtain ⟨_, _, V, W, T, U, e, hT, hU, he⟩ :=
    X.exists_common_pointBlowup_resolution_projectivePlane k
  let : V.Over S := ⟨T.toBase ≫ X ↘ S⟩
  let : W.Over S := ⟨U.toBase ≫ P ↘ S⟩
  have : T.toBase.IsOver S := ⟨rfl⟩
  have : e.hom.IsOver S := ⟨he⟩
  have : SmoothOfRelativeDimension 2 (V ↘ S) := hT.smoothOfRelativeDimension (X ↘ S)
  have : SmoothOfRelativeDimension 2 (W ↘ S) := hU.smoothOfRelativeDimension (P ↘ S)
  let M := (InvertibleSheaf.pullback T.toBase).obj L
  let N := L† M
  let g := InvertibleSheaf.pullback e.hom
  have hN : LineBundleClass.mk (g.obj N) = K[W] * (LineBundleClass.mk (g.obj M))⁻¹ := by
    simp only [g, N, mk_tensorProduct, ← inv_mk, ← pullback_mk, pullback_mul, pullback_inv]
    rw [pullback_mk, mk_pullback_canonicalBundle]
  rcases subsingleton_cohomology_two_or_of_plane_marking k hU (g.obj M) (g.obj N) hN with h | h
  · exact Or.inl (hT.subsingleton_cohomology_two_of_pullback_tower_iso k e L h)
  · have hM : LineBundleClass.mk M =
        (T.picardHom (Additive.ofMul (LineBundleClass.mk L), 0)).toMul := by
      rw [picardHom_apply_zero, toMul_ofMul, pullback_mk]
    have hNmark := canonical_complement_picardHom k hT L 0 M hM
    obtain ⟨eL⟩ := hT.nonempty_cohomologyTwoLinearEquiv_picardHom k (L† L) (fun _ ↦ 1)
      (fun _ ↦ le_rfl) N (by simpa only [Pi.zero_apply, sub_zero] using hNmark)
    have : Subsingleton (Cohomology N.obj 2) := by
      change Subsingleton (Cohomology ((InvertibleSheaf.pullback e.hom).obj N).obj 2) at h
      rw [InvertibleSheaf.pullback_obj_obj] at h
      exact (e.hom.cohomologyPullbackBaseLinearEquivOfIsIso k N.obj 2).surjective.subsingleton
    exact Or.inr (eL.injective.subsingleton)

end AlgebraicGeometry.Scheme

namespace TauCeti.AlgebraicGeometry.LineBundleClass

open Chow

variable {X : Scheme.{u}} [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [rational : Scheme.IsRationalOver (X ↘ Spec (.of k))]

include algClosed rational

/-- On a smooth projective rational surface, a class and its canonical complement
have the same Euler characteristic. -/
theorem eulerCharBelow_canonical_mul_inv_of_isRationalOver (a : LineBundleClass X) :
    eulerCharBelow k (K[X] * a⁻¹) 3 = eulerCharBelow k a 3 := by
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral X := rational.isIntegral_of_smooth
  have (x : X) : UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two x
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  let B := classIntersectionBilinForm k hX
  let K := Additive.ofMul K[X]
  let A := Additive.ofMul a
  have hsym : B K A = B A K := (classIntersectionBilinForm_isSymm k hX).eq _ _
  have heq : B (K - A) (K - A) - B (K - A) K = B A A - B A K := by
    simp only [map_sub, LinearMap.sub_apply]
    omega
  simp only [B, classIntersectionBilinForm_apply, K, A, toMul_sub, toMul_ofMul,
    div_eq_mul_inv] at heq
  have h₁ := eulerCharBelow_eq_riemannRoch_of_isRationalOver k a
  have h₂ := eulerCharBelow_eq_riemannRoch_of_isRationalOver k (K[X] * a⁻¹)
  omega

/-- On a smooth projective rational surface, a class of positive Euler characteristic
or its canonical complement is represented by an effective Cartier divisor. -/
theorem exists_effectiveCartier_or_canonical_mul_inv_of_eulerCharBelow_pos
    (a : LineBundleClass X) (ha : 0 < eulerCharBelow k a 3) :
    ∃ (I : X.IdealSheafData) (hI : I.IsEffectiveCartier),
      (mk hI.toInvertibleSheaf)⁻¹ = a ∨ (mk hI.toInvertibleSheaf)⁻¹ = K[X] * a⁻¹ := by
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral X := rational.isIntegral_of_smooth
  obtain ⟨L, rfl⟩ := mk_surjective a
  let N := L† L
  have hN : mk N = K[X] * (mk L)⁻¹ := by simp only [N, mk_tensorProduct, ← inv_mk]
  have χN : 0 < eulerCharBelow k (mk N) 3 := by
    rw [hN, eulerCharBelow_canonical_mul_inv_of_isRationalOver]
    exact ha
  rcases X.subsingleton_cohomology_two_or_canonical_complement_of_isRationalOver k L with h | h
  · obtain ⟨I, hI, hclass⟩ := L.exists_effectiveCartier_of_eulerCharBelow_pos k ha h
    exact ⟨I, hI, Or.inl (by rw [hclass, inv_inv])⟩
  · obtain ⟨I, hI, hclass⟩ := N.exists_effectiveCartier_of_eulerCharBelow_pos k χN h
    exact ⟨I, hI, Or.inr (by rw [hclass, inv_inv, hN])⟩

variable [IsIntegral X]

/-- A Picard class of positive Euler characteristic or its canonical complement is effective. -/
theorem mem_effectiveClasses_or_canonical_sub_of_eulerChar_pos (a : Additive (LineBundleClass X))
    (ha : 0 < eulerCharBelow k a.toMul 3) :
    a ∈ X.effectiveClasses ∨ Additive.ofMul K[X] - a ∈ X.effectiveClasses := by
  obtain ⟨I, hI, hclass | hclass⟩ :=
    exists_effectiveCartier_or_canonical_mul_inv_of_eulerCharBelow_pos k a.toMul ha
  · exact Or.inl (Scheme.mem_effectiveClasses.mpr
      ⟨hI.toCartierDivisor, hI.isEffective_toCartierDivisor, by
        rw [hI.toLineBundleClass_toCartierDivisor, hclass, ofMul_toMul]⟩)
  · exact Or.inr (Scheme.mem_effectiveClasses.mpr
      ⟨hI.toCartierDivisor, hI.isEffective_toCartierDivisor, by
        rw [hI.toLineBundleClass_toCartierDivisor, hclass, ofMul_mul, ofMul_inv, ofMul_toMul,
          sub_eq_add_neg]⟩)

end TauCeti.AlgebraicGeometry.LineBundleClass

namespace AlgebraicGeometry.Scheme

open Chow

variable (X : Scheme.{u}) [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [rational : Scheme.IsRationalOver (X ↘ Spec (.of k))]

local notation "B" => classIntersectionBilinForm k
  (topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2))
local notation "K" => Additive.ofMul K[X]

include algClosed rational in
/-- On a smooth projective rational surface, if a class intersects its difference with the
canonical class nonnegatively, either the class or its canonical complement is effective. -/
theorem mem_effectiveClasses_or_canonical_sub
    [IsIntegral X] [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]
    (a : Additive (LineBundleClass X))
    (h : 0 ≤ B a a - B a K) : a ∈ X.effectiveClasses ∨ K - a ∈ X.effectiveClasses := by
  have hRR : 2 * (eulerCharBelow k a.toMul 3 - 1) = B a a - B a K := by
    simpa only [classIntersectionBilinForm_apply, toMul_ofMul] using
      eulerCharBelow_eq_riemannRoch_of_isRationalOver k a.toMul
  exact mem_effectiveClasses_or_canonical_sub_of_eulerChar_pos k a (by omega)

end AlgebraicGeometry.Scheme
