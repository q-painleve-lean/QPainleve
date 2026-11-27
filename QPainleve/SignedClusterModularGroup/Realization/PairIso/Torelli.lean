/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Period.Restriction
public import QPainleve.SignedClusterModularGroup.Realization.Boundary
public import QPainleve.SignedClusterModularGroup.Realization.Presentation

import QPainleve.AlgebraicGeometry.Chow.NegativeCurve
import QPainleve.Geometry.Toric.Fan.Picard.Period.Torelli
import QPainleve.SignedClusterModularGroup.Realization.Anticanonical
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber

/-!
# Signed Torelli in a fixed toric marking

Compatible signed geometric periods on two root-free fibers of a fixed
presentation give a pair isomorphism with prescribed marked Picard pullback
and ordered branch action. This applies [Gross, Hacking and Keel's root-free
Torelli theorem][GHK] in the same marking used by the cluster-word comparison.

[GHK]: https://arxiv.org/html/1211.6367v5#S2
-/

public section

open AlgebraicGeometry CategoryTheory DihedralGroup MulOpposite Multiplicative
open QPainleve.CharacterTorus
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData LineBundleClass

namespace QPainleve.SignedClusterModularGroup

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀] [NeZero (2 : k₀)]

open GeometricRealization (Point)
open MarkedSurface (surfaceIso boundaryIso)
open SignedBoundaryIsometryGroup

local notation "S" => Spec (CommRingCat.of k₀)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {H : LinearMap.BilinForm ℤ L}
  (Q : CompleteToricPresentation k₀ i b r L γ)

local notation "Centers" => Over.mk (structureMap k₀ (Fin r → ℤ))
local notation "XTor" => scheme k₀ (Fin r →₀ ℤ)

local instance : Nonempty Q.fan.cones := Q.complete.nonempty_cones
local instance : NeZero Q.length := Q.neZero
local instance : PrestableFamily ((Q.fan.toricBoundaryIdeal k₀
  Q.complete.nonempty_cones).subscheme ↘ S) :=
  Q.prestable

variable {d : ZMod n → L}

local instance (M : MarkedSurface k₀ n H XTor) : IsIntegral M.surface := M.integral
local instance instProjectiveTorelliSurface (M : MarkedSurface k₀ n H XTor) :
    M.surface.IsProjectiveOver k₀ := M.projective
local instance instSmoothTorelliSurface (M : MarkedSurface k₀ n H XTor) :
    SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
local instance (M : MarkedSurface k₀ n H XTor) : IsNoetherian M.surface :=
  isNoetherian_of_finiteType (M.surface ↘ S)
local instance (M : MarkedSurface k₀ n H XTor) (p : M.surface) :
    UniqueFactorizationMonoid (M.surface.presheaf.stalk p) :=
  (M.surface ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two p
local instance instPrestableTorelliBoundaryImage (M : MarkedSurface k₀ n H XTor) :
    PrestableFamily (D[M].subscheme ↘ S) := M.prestable_boundaryImage
local instance (M : MarkedSurface k₀ n H XTor) : PrestableFamily (M.boundary ↘ S) := M.prestable

namespace CompleteToricPresentation

omit [NeZero (2 : k₀)] in
private theorem exists_marked_pair_iso_of_torelli
    {P₀ P₁ : MarkedSurface k₀ n H XTor}
    {G : LineBundleClass P₁.surface → LineBundleClass P₀.surface} {act : DihedralGroup n}
    (e : SignedTorelliPairIso (D := D[P₀]) (E := D[P₁]) P₀.imageCycle P₁.imageCycle G act) :
    ∃ f : P₀.pair ≅ P₁.pair,
      (surfaceIso f).hom = e.surfaceIso.hom ∧ MarkedSurface.imagePairIso f = e.boundaryIso := by
  obtain ⟨f, hf⟩ := P₀.exists_pairIso_of_boundaryIdeal P₁ e.surfaceIso
    (comp_over e.surfaceIso.hom S) e.comap_surfaceIso_hom
  refine ⟨f, hf, Iso.ext ((cancel_mono D[P₁].subschemeι).mp ?_)⟩
  rw [MarkedSurface.imagePairIso_hom_comp, e.boundaryIso_hom_comp, hf]

/-- For two marked fibers of the same ordered toric presentation, a specified
signed boundary isometry is induced by a pair isomorphism when the boundaries
are nef, the target boundary has square zero, there are no internal curves of
square `-2`, and the geometric periods intertwine the signed marked pullback.
The isomorphism acts on the ordered branches by the isometry's forward boundary
action, including for one and two boundary components. -/
theorem exists_marked_pair_iso_of_signed_boundary_isometry
    {c₀ c₁ : Point Centers} {P₀ P₁ : MarkedSurface k₀ n H XTor}
    (hm₀ : Q.HasNodalModel c₀ P₀) (hm₁ : Q.HasNodalModel c₁ P₁)
    (hD : D[P₀].IsEffectiveCartier) (hE : D[P₁].IsEffectiveCartier)
    (hP : P₀.boundaryClass hD = d) (hQ : P₁.boundaryClass hE = d)
    (hn₀ : (classOf(hD)).IsNef k₀ (P₀.surface ↘ S))
    (hn₁ : (classOf(hE)).IsNef k₀ (P₁.surface ↘ S))
    (hsq : Chow.classIntersectionNumber k₀ P₁.surface (classOf(hE)) (classOf(hE)) = 0)
    (g : signedBoundaryIsometryGroup H d)
    (g₀ : ∀ v : irreducibleComponents (D[P₀].subscheme.singularLocus k₀).blowup,
      (D[P₀].subscheme.blowupComponent (K := k₀) v).toScheme.genus k₀ = 0)
    (g₁ : ∀ v : irreducibleComponents (D[P₁].subscheme.singularLocus k₀).blowup,
      (D[P₁].subscheme.blowupComponent (K := k₀) v).toScheme.genus k₀ = 0)
    (hroot₀ : ∀ z : CodimensionOnePoint P₀.surface,
      Disjoint (closure {(z : P₀.surface)}) D[P₀].support →
      Chow.classIntersectionNumber k₀ P₀.surface (primeDivisorClass z) (primeDivisorClass z) ≠ -2)
    (hroot₁ : ∀ z : CodimensionOnePoint P₁.surface,
      Disjoint (closure {(z : P₁.surface)}) D[P₁].support →
      Chow.classIntersectionNumber k₀ P₁.surface (primeDivisorClass z) (primeDivisorClass z) ≠ -2)
    (hper : ∀ x : D[P₁].boundaryOrthogonal k₀,
      let y := P₀.picardMarking ((toIsometry H d g).val (P₁.picardMarking.symm x.val))
      ∃ hy : y ∈ D[P₀].boundaryOrthogonal k₀,
        hE.boundaryPeriod g₁ P₁.imageCycle.endpoint_eq (ofAdd x) =
          hD.boundaryPeriod g₀ P₀.imageCycle.endpoint_eq (ofAdd ⟨y, hy⟩) ^ (sign H d g : ℤ)) :
    let hd := hQ ▸ P₁.boundaryClass_injective_of_nef_square_zero hE hn₁ hsq
    ∃ a : P₀.pair ≅ P₁.pair,
      (letI : PrestableFamily (P₀.boundary ↘ S) := P₀.prestable
       letI : PrestableFamily (P₁.boundary ↘ S) := P₁.prestable
       (boundaryIso a).boundaryCycleAction P₀.cycle P₁.cycle = boundaryAction H d hd (op g)) ∧
      ∀ z, P₀.picardMarking ((toIsometry H d g).val z) =
        Additive.ofMul (pullback (surfaceIso a).hom (P₁.picardMarking z).toMul) := by
  intro hd
  let := hm₀.isRationalOver
  let := hm₁.isRationalOver
  have hk₀ := hm₀.canonicalClass hD
  have hk₁ := hm₁.canonicalClass hE
  let act := boundaryAction H d hd (op g)
  have hact : cycleOrientationSign act = sign H d g :=
    cycleOrientationSign_boundaryAction H d hd g
  let G := (P₁.marking.symm.trans
    (H.isometryGroupEquivIsometryEquiv (toIsometry H d g))).trans P₀.marking
  have hG (z : L) : G (P₁.picardMarking z) = P₀.picardMarking ((toIsometry H d g).val z) := by
    simp only [G, MarkedSurface.picardMarking_apply, LinearMap.BilinForm.IsometryEquiv.trans_apply,
      LinearMap.BilinForm.IsometryEquiv.symm_apply_apply,
      LinearMap.BilinForm.coe_isometryGroupEquivIsometryEquiv]
  have hclass j : G (Additive.ofMul (primeDivisorClass
      (D[P₁].boundaryPrimeEmbedding
        (P₁.imageCycle.boundaryPrimeEquiv hE (cycleVertexPerm act j))))) =
      Additive.ofMul (primeDivisorClass
        (D[P₀].boundaryPrimeEmbedding (P₀.imageCycle.boundaryPrimeEquiv hD j))) := by
    rw [P₀.boundaryPrimeEmbedding_imageCycle, P₁.boundaryPrimeEmbedding_imageCycle,
      ← P₀.picardMarking_boundaryClass, ← P₁.picardMarking_boundaryClass, hG, hP, hQ,
      toIsometry_apply_boundaryAction H d hd g]
  have hperiod (x : D[P₁].boundaryOrthogonal k₀) (y : D[P₀].boundaryOrthogonal k₀)
      (hxy : G x.val = y.val) : hE.boundaryPeriod g₁ P₁.imageCycle.endpoint_eq (ofAdd x) =
      hD.boundaryPeriod g₀ P₀.imageCycle.endpoint_eq (ofAdd y) ^
        (cycleOrientationSign act : ℤ) := by
    obtain ⟨hy, hy'⟩ := hper x
    have hval : G x.val =
        P₀.picardMarking ((toIsometry H d g).val (P₁.picardMarking.symm x.val)) := by
      rw [← hG, LinearEquiv.apply_symm_apply]
    have heq : (⟨_, hy⟩ : D[P₀].boundaryOrthogonal k₀) = y :=
      Subtype.ext (hval.symm.trans hxy)
    simpa only [heq, hact] using hy'
  obtain ⟨e⟩ :=
    D[P₀].exists_pair_iso_of_root_free_signed_boundary_period_of_toric_presentation_of_nef
      k₀ P₀.imageCycle P₁.imageCycle hD hE act G hclass hk₀ hk₁
      (Chow.prime_self_intersection_ne_neg_two_off_boundary k₀ hD hk₀ hroot₀)
      (Chow.prime_self_intersection_ne_neg_two_off_boundary k₀ hE hk₁ hroot₁)
      g₀ g₁ hperiod hm₀.hasToricPresentation
      (by simpa only [← hk₀] using hn₀) (by simpa only [← hk₁] using hn₁)
      (by simpa only [← hk₁] using hsq)
  obtain ⟨f, hf, hfB⟩ := exists_marked_pair_iso_of_torelli e
  refine ⟨f, ?_, fun z ↦ ?_⟩
  · rw [← MarkedSurface.imagePairIso_boundaryAction]
    exact ((MarkedSurface.imagePairIso f).boundaryCycleAction_congr
      P₀.imageCycle P₁.imageCycle e.boundaryIso hfB).trans e.boundaryCycleAction_eq
  · rw [hf, e.pullback_eq]
    simp only [ofMul_toMul, hG]

end CompleteToricPresentation

end QPainleve.SignedClusterModularGroup
