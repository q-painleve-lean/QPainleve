/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Surjectivity.Periods

import QPainleve.SignedClusterModularGroup.Realization.NodalFiber
import QPainleve.SignedClusterModularGroup.Realization.PairIso.Torelli

/-!
# Realizing signed Picard actions at generic centers

For a fixed marked toric presentation, choose two root-free fibers with compatible
periods and use signed Torelli to realize a prescribed Picard action by a pair
isomorphism. The centers work for every finite word, so the source center already
lies in the domain of a word subsequently read from the change of projections.
The boundary marking transports the numerical conditions from a single fiber.

The construction uses the toric center formula and the root-free form of Torelli
from Gross, Hacking and Keel.
[Proposition 2.9](https://arxiv.org/html/1211.6367v5#S2),
[Theorem 1.8](https://arxiv.org/html/1211.6367v5#S1.Thmtheorem8).
-/

public section

open AlgebraicGeometry CategoryTheory MulOpposite Quiver
open QPainleve.CharacterTorus QPainleve.Cluster
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData

namespace QPainleve.SignedClusterModularGroup.CompleteToricPresentation

open GeometricRealization (Point)
open MarkedSurface (boundaryIso surfaceIso)
open SignedBoundaryIsometryGroup

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {M : Point Centers[r] → MarkedSurface ℂ n B XTor[r]}

/-- Every signed boundary isometry of a marked toric presentation with primitive nef
square-zero boundary is the Picard pullback of a pair isomorphism between two root-free
fibers. Both centers lie in every word's noncollision open. The isomorphism induces the
forward boundary action on ordered branches, including for one and two components. -/
theorem exists_root_free_pair_iso_of_signed_boundary_isometry
    (Q : CompleteToricPresentation i b r L γ) {E : SkewExchangeMatrix (Fin r)}
    (P : ChargeSeed E N) (hcharge : P.charge.ker ≤ (Fan.rayChargeMap Q.rays).ker)
    (hD : ∀ c, D[M c].IsEffectiveCartier)
    {d : ZMod n → L} (hmark : ∀ c, (M c).boundaryClass (hD c) = d)
    {c : Point Centers[r]} (href : Q.HasNodalModel c (M c))
    (hprim : IsPrimitive (Additive.ofMul classOf(hD c)))
    (hnef : (classOf(hD c)).IsNef ℂ ((M c).surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ (M c).surface classOf(hD c) classOf(hD c) = 0)
    (hmodels : ∀ c' : Point Centers[r],
      c'.left (default : S) ∈ (Path.nil : Word E E).centerOpen ℂ P → Q.HasNodalModel c' (M c'))
    (g : signedBoundaryIsometryGroup B d) :
    let hd := hmark c ▸ (M c).boundaryClass_injective_of_nef_square_zero (hD c) hnef hsq
    ∃ c₀ c₁ : Point Centers[r], Q.HasNodalModel c₀ (M c₀) ∧ Q.HasNodalModel c₁ (M c₁) ∧
      (∀ ⦃C : SkewExchangeMatrix (Fin r)⦄ (w : Word E C),
        c₀.left (default : S) ∈ w.centerOpen ℂ P ∧ c₁.left (default : S) ∈ w.centerOpen ℂ P) ∧
      IsPrimitive (Additive.ofMul classOf(hD c₀)) ∧
      (classOf(hD c₀)).IsNef ℂ ((M c₀).surface ↘ S) ∧
      Chow.classIntersectionNumber ℂ (M c₀).surface classOf(hD c₀) classOf(hD c₀) = 0 ∧
      (∀ z : CodimensionOnePoint (M c₀).surface,
        ¬Disjoint (closure {(z : (M c₀).surface)}) (D[M c₀].support : Set (M c₀).surface)) ∧
      (∀ z : CodimensionOnePoint (M c₁).surface,
        ¬Disjoint (closure {(z : (M c₁).surface)}) (D[M c₁].support : Set (M c₁).surface)) ∧
      ∃ e : (M c₀).pair ≅ (M c₁).pair,
        (letI : PrestableFamily ((M c₀).boundary ↘ S) := (M c₀).prestable
         letI : PrestableFamily ((M c₁).boundary ↘ S) := (M c₁).prestable
         (boundaryIso e).boundaryCycleAction (M c₀).cycle (M c₁).cycle =
           boundaryAction B d hd (op g)) ∧
        ∀ z, (M c₀).picardMarking ((toIsometry B d g).val z) =
          Additive.ofMul
            (LineBundleClass.pullback (surfaceIso e).hom ((M c₁).picardMarking z).toMul) := by
  let : IsRationalOver ((M c).surface ↘ S) := href.isRationalOver
  let : B.IsPerfPair := (M c).isPerfPair_of_isRationalOver
  obtain ⟨c₀, c₁, hm₀, hm₁, hword, hroot₀, hroot₁, hg₀, hg₁, hperiod⟩ :=
    Q.exists_root_free_fibers_with_compatible_periods P hcharge hD hmark g hmodels
  have hnum (c' : Point Centers[r]) :=
    ((M c).primitive_nef_square_zero_iff_of_boundaryClass_eq (M c') (hD c) (hD c')
      (fun j ↦ congrFun ((hmark c).trans (hmark c').symm) j)).mp ⟨hprim, hnef, hsq⟩
  obtain ⟨hprim₀, hnef₀, hsq₀⟩ := hnum c₀
  obtain ⟨_, hnef₁, hsq₁⟩ := hnum c₁
  exact ⟨c₀, c₁, hm₀, hm₁, fun _ w ↦ hword w, hprim₀, hnef₀, hsq₀, hroot₀, hroot₁,
    Q.exists_marked_pair_iso_of_signed_boundary_isometry hm₀ hm₁ (hD c₀) (hD c₁)
      (hmark c₀) (hmark c₁) hnef₀ hnef₁ hsq₁ g hg₀ hg₁
      (fun z hz ↦ (hroot₀ z hz).elim) (fun z hz ↦ (hroot₁ z hz).elim) hperiod⟩

end QPainleve.SignedClusterModularGroup.CompleteToricPresentation
