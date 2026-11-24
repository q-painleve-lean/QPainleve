/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.Nef.Cone
public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic

import QPainleve.AlgebraicGeometry.Chow.NegativeCurve
import QPainleve.AlgebraicGeometry.Chow.Nef.NumericalExceptional
import QPainleve.AlgebraicGeometry.Chow.Nef.PositiveCone
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.PositiveCone
import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Numerical
import QPainleve.AlgebraicGeometry.Scheme.LocalDimension
import TauCeti.Topology.Algebra.Module.ModuleTopology

/-!
# The nef cone of a rational surface with an anticanonical divisor

Within the ample component of the positive cone, the nef inequalities come from
the boundary components, the numerical exceptional classes of positive ample
degree, and the internal `(-2)`-curves. This is the description of Gross, Hacking
and Keel, [*Moduli of surfaces with an anti-canonical cycle*, Lemma 2.15][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S2
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory QuadraticMap TopologicalSpace
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData
open scoped TensorProduct

namespace TauCeti.AlgebraicGeometry.Chow

universe u

variable (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "Pic(" S ")" => Additive (LineBundleClass S)
local notation "V(" S ")" => (ℝ ⊗[ℤ] Pic(S))
local notation "B(" S ")" => realIntersectionBilinForm k S
local notation "b(" S ")" => classIntersectionNumber k S
local notation "K(" S ")" => LineBundleClass.mk (QPainleve.canonicalBundle k S 2)
local notation "ι" => (fun a : LineBundleClass _ ↦ (1 : ℝ) ⊗ₜ[ℤ] Additive.ofMul a)
local notation "c" => realPrimeDivisorClass k

variable [rational : Scheme.IsRationalOver (X ↘ Spec (.of k))] {D : X.IdealSheafData}
  (hD : D.IsEffectiveCartier)
  (hcan : LineBundleClass.mk hD.toInvertibleSheaf =
    LineBundleClass.mk (QPainleve.canonicalBundle k X 2))

include rational hD hcan in
private theorem negativePrimeDivisorClass_cases [IsIntegral X] (p : CodimensionOnePoint X)
    (hp : B(X) (c p) (c p) < 0) (hdis : (p : X) ∉ D.support) :
    (B(X) (c p) (c p) = -1 ∧ B(X) (c p) (ι K(X)) = -1) ∨
      B(X) (c p) (c p) = -2 := by
  let I := vanishingIdeal (Closeds.mk (closure {(p : X)}) isClosed_closure)
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of k)) (n := 2)
  have : IsProper (I.subscheme ↘ Spec (.of k)) := by
    rw [← comp_over I.subschemeι]
    infer_instance
  have : I.subscheme.IsCurveOver k := Scheme.isCurveOver_iff.mpr
    ⟨inferInstance, inferInstance, QPainleve.topologicalKrullDim_vanishingIdeal_subscheme k hX p⟩
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (X ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hI : I.IsEffectiveCartier := isEffectiveCartier_vanishingIdeal_closure_singleton p.property
  let a := (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹
  have hp' : c p = ι a := by
    rw [realPrimeDivisorClass_def, primeDivisorClass_def]
  have hneg : b(X) a a < 0 := by
    rw [hp', realIntersectionBilinForm_tmul, one_mul, one_mul, toMul_ofMul, Int.cast_lt_zero] at hp
    exact hp
  have hoff : I.subschemeι (genericPoint I.subscheme) ∉ D.support := by
    simpa only [I, subschemeι_genericPoint_vanishingIdeal_closure_singleton] using hdis
  rcases (hI.classIntersectionNumber_self_neg_iff_of_anticanonical hD hcan hoff).mp hneg with
    ⟨he, hd⟩ | ⟨_, hsq, _⟩
  · have hsq := ((hI.isExceptionalCurveOfFirstKind_iff_genus_eq_zero_and_classIntersectionNumber
      (k := k) hX.le).mp he).2
    have hc := (intersectionBilinForm k X (Additive.ofMul a)).map_neg (Additive.ofMul K(X))
    have hd' : b(X) a K(X) = -1 := by
      simp only [intersectionBilinForm_apply, toMul_neg, toMul_ofMul] at hc
      rw [hcan, classIntersectionNumber_comm] at hd
      have hdeg : b(X) a K(X)⁻¹ = 1 := hd
      exact neg_eq_iff_eq_neg.mp (hdeg.symm.trans hc).symm
    have hsq' : b(X) a a = -1 := hsq
    left
    simp [hp', hsq', hd']
  · have hsq' : b(X) a a = -2 := hsq
    right
    simp [hp', hsq']

variable [TopologicalSpace V(X)] [IsModuleTopology ℝ V(X)]

local instance : IsTopologicalAddGroup V(X) := IsModuleTopology.isTopologicalAddGroup ℝ _

local instance : T2Space V(X) := TauCeti.ModuleTopology.t2Space (Module.Free.chooseBasis ℝ _)

include rational hD hcan in
/-- The nef cone is the closure of the classes in the ample component pairing
nonnegatively with each boundary component, each numerical exceptional class of
positive ample degree, and each prime of square `-2` off the boundary. A negative
prime off the anticanonical divisor of square `-2` is disjoint from it by adjunction. -/
theorem coe_nefCone_eq_closure_inter_anticanonical {h : LineBundleClass X} (hh : h.IsAmple) :
    let : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
    let : IsIntegral X := rational.isIntegral_of_smooth
    let : Module.Finite ℤ Pic(X) := X.finite_picard_of_isRationalOver k
    (nefCone k (X := X) : Set V(X)) =
      closure (connectedComponentIn {x : V(X) | 0 < (B(X)).toQuadraticMap x} (ι h) ∩
        {x | (∀ p : CodimensionOnePoint X, (p : X) ∈ D.support → 0 ≤ B(X) x (c p)) ∧
          (∀ a : LineBundleClass X, b(X) a a = -1 → b(X) a K(X) = -1 →
            0 < b(X) h a → 0 ≤ B(X) x (ι a)) ∧
          (∀ p : CodimensionOnePoint X, (p : X) ∉ D.support →
            B(X) (c p) (c p) = -2 → 0 ≤ B(X) x (c p))}) := by
  intro _ _ _
  obtain ⟨hQ, hsig, _⟩ := signature_realIntersectionBilinForm_of_isRationalOver k X
  have hpos : closure (connectedComponentIn {x : V(X) | 0 < (B(X)).toQuadraticMap x} (ι h))
      ⊆ (closedCurveCone k (X := X) : Set V(X)) := by
    rw [connectedComponentIn_pos_eq_of_isAmple k hQ hsig.le hh]
    simpa only [LinearMap.BilinMap.toQuadraticMap_apply] using
      closure_positive_component_subset_closedCurveCone k h hh
  have hcone := coe_nefCone_eq_closure_inter_negative k hQ hsig.le hh hpos
  refine Set.Subset.antisymm ?_ ?_
  · rw [hcone]
    apply closure_mono
    rintro x ⟨hx, hneg⟩
    have hn := (mem_nefCone_iff_mem_closure_and_nonneg_negative k hQ hsig.le hh hpos).mpr
      ⟨subset_closure hx, hneg⟩
    have hpair := (mem_nefCone k).mp hn
    refine ⟨hx, fun p _ ↦ hpair p, ?_, fun p _ _ ↦ hpair p⟩
    intro a ha hK hha
    obtain ⟨E, hE, hclass⟩ :=
      (exists_effectiveWeilDivisor_iff_classIntersectionNumber_pos_of_isAmple k
        hh ha hK hD hcan).mpr hha
    have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
    let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
      (X ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    have hmem := one_tmul_weilToLineBundleClassHom_mem_closedCurveCone k hE
    rw [← ofMul_toMul (Scheme.CartierDivisor.weilToLineBundleClassHom X E), hclass] at hmem
    exact (nonneg_on_closedCurveCone_iff k (LinearMap.toContinuousLinearMap (B(X) x))).mpr
      hpair _ hmem
  · rw [hcone]
    apply closure_mono
    rintro x ⟨hx, hboundary, hexc, hint⟩
    refine ⟨hx, fun p hp ↦ ?_⟩
    by_cases hmem : (p : X) ∈ D.support
    · exact hboundary p hmem
    rcases negativePrimeDivisorClass_cases k hD hcan p hp hmem with ⟨hs, hc⟩ | hs
    · rw [realPrimeDivisorClass_def] at hs hc ⊢
      have hdeg := realIntersectionBilinForm_realPrimeDivisorClass_pos k hh p
      rw [realIntersectionBilinForm_one_tmul_realPrimeDivisorClass, Int.cast_pos] at hdeg
      simp only [realIntersectionBilinForm_tmul, one_mul, toMul_ofMul] at hs hc
      exact hexc _ (by exact_mod_cast hs) (by exact_mod_cast hc) hdeg
    · exact hint p hmem hs

section Transport

variable {Y : Scheme.{u}} [Y.Over (Spec (.of k))] [Y.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]
  [rationalY : Scheme.IsRationalOver (Y ↘ Spec (.of k))]
  [TopologicalSpace V(Y)] [IsModuleTopology ℝ V(Y)]
  {E : Y.IdealSheafData} (hE : E.IsEffectiveCartier)
  (hcanY : LineBundleClass.mk hE.toInvertibleSheaf =
    LineBundleClass.mk (QPainleve.canonicalBundle k Y 2))

local instance : IsTopologicalAddGroup V(Y) := IsModuleTopology.isTopologicalAddGroup ℝ _

local instance : T2Space V(Y) := TauCeti.ModuleTopology.t2Space (Module.Free.chooseBasis ℝ _)

local notation "Eℝ[" e "]" => LinearMap.BilinForm.IsometryEquiv.baseChange ℝ e
local notation "G[" e "]" =>
  (Additive.toMul ∘ e ∘ Additive.ofMul : LineBundleClass X → LineBundleClass Y)

include rational rationalY hD hcan hE hcanY in
/-- An intersection isometry carrying the canonical class, the boundary component
classes, and one ample class to their counterparts identifies the real nef cones
when both anticanonical pairs have no internal `(-2)`-curves. -/
theorem image_nefCone_eq_of_anticanonical {h : LineBundleClass X} (hh : h.IsAmple) :
    let : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
    let : Smooth (Y ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
    let : IsIntegral X := rational.isIntegral_of_smooth
    let : IsIntegral Y := rationalY.isIntegral_of_smooth
    let : Module.Finite ℤ Pic(X) := X.finite_picard_of_isRationalOver k
    let : Module.Finite ℤ Pic(Y) := Y.finite_picard_of_isRationalOver k
    ∀ (e : (intersectionBilinForm k X).IsometryEquiv (intersectionBilinForm k Y)),
      (G[e] h).IsAmple → G[e] K(X) = K(Y) →
      Eℝ[e] '' ((c) '' {p : CodimensionOnePoint X | (p : X) ∈ D.support}) =
        (c) '' {q : CodimensionOnePoint Y | (q : Y) ∈ E.support} →
      (∀ p : CodimensionOnePoint X, (p : X) ∉ D.support → B(X) (c p) (c p) ≠ -2) →
      (∀ q : CodimensionOnePoint Y, (q : Y) ∉ E.support → B(Y) (c q) (c q) ≠ -2) →
      Eℝ[e] '' (nefCone k (X := X) : Set V(X)) = nefCone k (X := Y) := by
  intro _ _ _ _ _ _ e hhY hK hboundary hrootX hrootY
  let t := (Eℝ[e]).toLinearEquiv.toContinuousLinearEquiv.toHomeomorph
  have hmap (v w : V(X)) : B(Y) (Eℝ[e] v) (Eℝ[e] w) = B(X) v w := by
    simpa only [realIntersectionBilinForm_def] using (Eℝ[e]).map_app w v
  have hmapℤ (a d : LineBundleClass X) : b(Y) (G[e] a) (G[e] d) = b(X) a d := by
    simpa only [intersectionBilinForm_apply, Function.comp_apply, toMul_ofMul] using
      e.map_app (Additive.ofMul d) (Additive.ofMul a)
  have htmul (a : LineBundleClass X) : Eℝ[e] (ι a) = ι (G[e] a) :=
    e.baseChange_tmul (1 : ℝ) (Additive.ofMul a)
  obtain ⟨hQX, hsigX, _⟩ := signature_realIntersectionBilinForm_of_isRationalOver k X
  obtain ⟨hQY, hsigY, _⟩ := signature_realIntersectionBilinForm_of_isRationalOver k Y
  rw [coe_nefCone_eq_closure_inter_anticanonical k hD hcan hh,
    coe_nefCone_eq_closure_inter_anticanonical k hE hcanY hhY]
  have ht : ∀ S : Set V(X), Eℝ[e] '' closure S = closure (Eℝ[e] '' S) := fun S ↦
    by simpa only [t, ContinuousLinearEquiv.coe_toHomeomorph,
      LinearEquiv.coe_toContinuousLinearEquiv', LinearMap.BilinForm.IsometryEquiv.coe_toLinearEquiv]
      using t.image_closure S
  rw [ht]
  congr 1
  ext y
  obtain ⟨x, rfl⟩ := (Eℝ[e]).surjective y
  have hinj : Function.Injective (Eℝ[e] : V(X) → V(Y)) := (Eℝ[e]).injective
  simp only [LinearMap.BilinForm.IsometryEquiv.coe_toLinearEquiv, hinj.mem_set_image,
    Set.mem_inter_iff, Set.mem_ofPred_eq]
  have hpos :
      x ∈ connectedComponentIn {v : V(X) | 0 < (B(X)).toQuadraticMap v} (ι h) ↔
      Eℝ[e] x ∈ connectedComponentIn {v : V(Y) | 0 < (B(Y)).toQuadraticMap v} (ι (G[e] h)) := by
    rw [connectedComponentIn_pos_eq_of_isAmple k hQX hsigX.le hh,
      connectedComponentIn_pos_eq_of_isAmple k hQY hsigY.le hhY, ← htmul h]
    simp only [Set.mem_ofPred_eq, LinearMap.BilinMap.toQuadraticMap_apply, hmap]
  have hb :
      (∀ p : CodimensionOnePoint X, (p : X) ∈ D.support → 0 ≤ B(X) x (c p)) ↔
      (∀ q : CodimensionOnePoint Y, (q : Y) ∈ E.support → 0 ≤ B(Y) (Eℝ[e] x) (c q)) := by
    have h := congrArg (fun S : Set V(Y) ↦ ∀ v ∈ S, 0 ≤ B(Y) (Eℝ[e] x) v) hboundary
    simpa only [Set.forall_mem_image, Set.mem_ofPred_eq, hmap] using Iff.of_eq h
  have hex :
      (∀ a : LineBundleClass X, b(X) a a = -1 → b(X) a K(X) = -1 → 0 < b(X) h a →
        0 ≤ B(X) x (ι a)) ↔
      (∀ d : LineBundleClass Y, b(Y) d d = -1 → b(Y) d K(Y) = -1 → 0 < b(Y) (G[e] h) d →
        0 ≤ B(Y) (Eℝ[e] x) (ι d)) := by
    have hg : Function.Surjective G[e] := Additive.toMul.surjective.comp
      (e.surjective.comp Additive.ofMul.surjective)
    rw [hg.forall (p := fun d ↦ b(Y) d d = -1 → b(Y) d K(Y) = -1 →
      0 < b(Y) (G[e] h) d → 0 ≤ B(Y) (Eℝ[e] x) (ι d))]
    simp only [← hK, hmapℤ, ← htmul, hmap]
  have hrX : ∀ p : CodimensionOnePoint X, (p : X) ∉ D.support →
      B(X) (c p) (c p) = -2 → 0 ≤ B(X) x (c p) := fun p hp hs ↦ (hrootX p hp hs).elim
  have hrY : ∀ q : CodimensionOnePoint Y, (q : Y) ∉ E.support →
      B(Y) (c q) (c q) = -2 → 0 ≤ B(Y) (Eℝ[e] x) (c q) :=
    fun q hq hs ↦ (hrootY q hq hs).elim
  exact and_congr hpos (and_congr hb (and_congr hex ⟨fun _ ↦ hrY, fun _ ↦ hrX⟩))

end Transport

end TauCeti.AlgebraicGeometry.Chow
