/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.Nef.Cone
public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.NakaiMoishezon

import QPainleve.AlgebraicGeometry.Chow.RationalSurface.AmpleCone.Interior
import TauCeti.Topology.Algebra.Module.ModuleTopology

/-!
# Ample classes and negative curves on rational surfaces

In the positive component containing an ample class, an integral class is ample
exactly when it pairs positively with all negative prime curves. Nonnegative-square
prime curves lie in the closure of this component and have positive degree against
every point of the component.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory QuadraticMap TopologicalSpace
open scoped TensorProduct

namespace TauCeti.AlgebraicGeometry.LineBundleClass

universe u

variable (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [rational : Scheme.IsRationalOver (X ↘ Spec (.of k))]

local notation "V(" X ")" => (ℝ ⊗[ℤ] Additive (LineBundleClass X))
local notation "B" => Chow.realIntersectionBilinForm k X
local notation "Q" => LinearMap.BilinMap.toQuadraticMap B
local notation "ι" => (fun a : LineBundleClass X ↦ (1 : ℝ) ⊗ₜ[ℤ] Additive.ofMul a)
local notation "c" => Chow.realPrimeDivisorClass k (X := X)

variable [TopologicalSpace V(X)] [IsModuleTopology ℝ V(X)]

include rational in
/-- On a smooth projective rational surface, an integral class is ample if and only
if it belongs to the ample component and has positive intersection with every
negative prime divisor class. -/
theorem isAmple_iff_mem_positiveComponent_and_pos_negative {h : LineBundleClass X}
    (hh : h.IsAmple) (a : LineBundleClass X) :
    letI : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
    letI : IsIntegral X := rational.isIntegral_of_smooth
    a.IsAmple ↔
      ι a ∈ connectedComponentIn {x : V(X) | 0 < Q x} (ι h) ∧
      ∀ p : CodimensionOnePoint X, B (c p) (c p) < 0 → 0 < B (ι a) (c p) := by
  let : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
  let : IsIntegral X := rational.isIntegral_of_smooth
  let : Module.Finite ℤ (Additive (LineBundleClass X)) := X.finite_picard_of_isRationalOver k
  obtain ⟨hQ, hsig, _⟩ := Chow.signature_realIntersectionBilinForm_of_isRationalOver k X
  have hpos (p : CodimensionOnePoint X) := Chow.realIntersectionBilinForm_realPrimeDivisorClass_pos
    k hh p
  constructor
  · intro ha
    rw [Chow.connectedComponentIn_pos_eq_of_isAmple k hQ hsig.le hh]
    exact ⟨⟨Chow.realIntersectionBilinForm_pos_of_isAmple k ha ha,
      Chow.realIntersectionBilinForm_pos_of_isAmple k hh ha⟩,
      fun p _ ↦ Chow.realIntersectionBilinForm_realPrimeDivisorClass_pos k ha p⟩
  · rintro ⟨ha, hneg⟩
    rw [isAmple_iff_self_pos_and_intersectionNumber_pos (k := k)]
    have hself := connectedComponentIn_subset _ _ ha
    refine ⟨?_, ?_⟩
    · simp only [Set.mem_ofPred_eq, LinearMap.BilinMap.toQuadraticMap_apply,
        Chow.realIntersectionBilinForm_tmul, one_mul, toMul_ofMul, Int.cast_pos] at hself
      exact hself
    · intro C _ _ i _ hi
      have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of k)) (n := 2)
      have hC := Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := C) k
      let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
      let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
        (X ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
      let : i.IsOver (Spec (.of k)) := ⟨hi.symm⟩
      let p : CodimensionOnePoint X :=
        ⟨i (genericPoint C), i.coheight_apply_genericPoint_eq_one_of_dim_eq_two k hX hC⟩
      have hp : 0 < B (ι a) (c p) := by
        by_cases hp' : B (c p) (c p) < 0
        · exact hneg p hp'
        · have hp₀ : c p ≠ 0 := fun he ↦
            lt_irrefl (0 : ℝ) (by simpa only [he, map_zero] using hpos p)
          exact Chow.realIntersectionBilinForm_pos_of_mem_connectedComponentIn_pos
            k hQ hsig.le hh ha
            (Chow.realPrimeDivisorClass_mem_closure_connectedComponentIn_pos
              k hQ hsig.le hh p (le_of_not_gt hp')) hp₀
      rw [Chow.realIntersectionBilinForm_one_tmul_realPrimeDivisorClass,
        Chow.classIntersectionNumber_primeDivisorClass_eq_intersectionNumber_of_isClosedImmersion
          k hX i hC a, Int.cast_pos] at hp
      exact hp

section Transport

variable {Y : Scheme.{u}} [Y.Over (Spec (.of k))] [Y.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]
  [rationalY : Scheme.IsRationalOver (Y ↘ Spec (.of k))]
  [TopologicalSpace V(Y)] [IsModuleTopology ℝ V(Y)]

local instance : IsTopologicalAddGroup V(X) := IsModuleTopology.isTopologicalAddGroup ℝ _
local instance : IsTopologicalAddGroup V(Y) := IsModuleTopology.isTopologicalAddGroup ℝ _

local instance : T2Space V(X) := TauCeti.ModuleTopology.t2Space (Module.Free.chooseBasis ℝ _)
local instance : T2Space V(Y) := TauCeti.ModuleTopology.t2Space (Module.Free.chooseBasis ℝ _)

include rational rationalY in
/-- An integral Picard isometry identifying the real nef cones identifies the
ample classes. -/
theorem isAmple_iff_of_image_nefCone_eq :
    let : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
    let : Smooth (Y ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
    let : IsIntegral X := rational.isIntegral_of_smooth
    let : IsIntegral Y := rationalY.isIntegral_of_smooth
    let : Module.Finite ℤ (Additive (LineBundleClass X)) :=
      X.finite_picard_of_isRationalOver k
    let : Module.Finite ℤ (Additive (LineBundleClass Y)) :=
      Y.finite_picard_of_isRationalOver k
    ∀ (e : (Chow.intersectionBilinForm k X).IsometryEquiv (Chow.intersectionBilinForm k Y)),
      (e.baseChange ℝ) '' (Chow.nefCone k (X := X) : Set V(X)) = Chow.nefCone k (X := Y) →
      ∀ a : LineBundleClass X, a.IsAmple ↔ (e (Additive.ofMul a)).toMul.IsAmple := by
  intro _ _ _ _ _ _ e hnef a
  let g := (e.baseChange ℝ).toLinearEquiv.toContinuousLinearEquivOfIsModuleTopology.toHomeomorph
  have hg : (g : V(X) → V(Y)) = e.baseChange ℝ := by
    simp only [g, ContinuousLinearEquiv.coe_toHomeomorph,
      LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology,
      LinearMap.BilinForm.IsometryEquiv.coe_toLinearEquiv]
  have hmap : g '' interior (Chow.nefCone k (X := X) : Set V(X)) =
      interior (Chow.nefCone k (X := Y) : Set V(Y)) := by
    rw [g.image_interior, hg, hnef]
  have htmul : g (ι a) = (1 : ℝ) ⊗ₜ[ℤ] e (Additive.ofMul a) :=
    congrFun hg (ι a) |>.trans (e.baseChange_tmul (1 : ℝ) (Additive.ofMul a))
  rw [← Chow.one_tmul_mem_interior_nefCone_iff k a,
    ← Chow.one_tmul_mem_interior_nefCone_iff k ((e (Additive.ofMul a)).toMul),
    ofMul_toMul, ← hmap, ← htmul]
  exact g.injective.mem_set_image.symm

end Transport

end TauCeti.AlgebraicGeometry.LineBundleClass
