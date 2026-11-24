/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
public import QPainleve.Geometry.Toric.Fan.Logarithmic.Quadric.Preparation
public import QPainleve.Geometry.Toric.Fan.Picard.FiberDegree
public import QPainleve.Geometry.Toric.Fan.Picard.ProjectedPoint

import QPainleve.AlgebraicGeometry.Blowup.Tower.Factorization
import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.AlgebraicGeometry.Modules.Differentials.PoleIdeal
import QPainleve.AlgebraicGeometry.Morphisms.Modification.Birational
import QPainleve.Geometry.Toric.Fan.Ruling.Quadric
import TauCeti.Topology.KrullDimension.Irreducible

/-!
# Retaining a high-order base center in the preparation to the quadric

A Hirzebruch resolution can be prepared by toric links on one invariant fiber
while retaining the fiber degree and a specified first base order on the other
fiber. The same nodal refinement resolves every intermediate projection and
carries the logarithmic poles. This is the preparation in
[Lutz, Proposition 8.11, Case C][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=73
-/

public section

open AlgebraicGeometry CategoryTheory Module
open TauCeti.AlgebraicGeometry TauCeti.Toric LineBundleClass Scheme.IdealSheafData

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}
  (b : Basis (Fin 2) ℤ N) (a : ℕ) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (a : ℤ) • b 0 - b 1])

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" Δ "]" => Fan.algebraicRealization Δ
local notation "s[" Δ "]" => (X[Δ] ↘ S)
local notation "s(" X ")" => (X ↘ S)
local notation "π[" H "]" => FanHom.algebraicMap (Fan.IsSubdivision.toFanHom H)
local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "B[" Δ "," h "]" => Fan.boundaryIdeal Δ (Fan.IsComplete.nonempty_cones h)
local notation "p[" ρ "," c "]" => Fan.Ray.binomialCenter ρ rankTwo
  (Basis.detDualEquiv_self b (Fan.Ray.primitiveGenerator ρ))
  (Fan.Ray.surjective_detCharacter ρ b) c (IsLocalRing.closedPoint ℂ)

variable [X[Φ].IsProjectiveOver ℂ]
  {Y : Scheme} {n : ℕ} {T : BlowupTower X[Φ] n Y} (hT : IsClosedPointTower X[Φ] T)

private theorem exists_quadric_tower_of_resolved_preparation
    (P : Fan.HirzebruchQuadricPreparation b a Φ) {m : ℕ} {W : Scheme}
    {R : BlowupTower Y m W} (hR : IsClosedPointTower Y R)
    (q : W ⟶ X[P.common])
    (hq : (q ≫ π[P.common_model 0]) ≫ s[P.model 0] = R.toBase ≫ T.toBase ≫ s[Φ])
    (hmap : letI : Nonempty Φ.cones := hc.nonempty_cones
      letI : Nonempty (P.model 0).cones := (P.model_complete 0).nonempty_cones
      letI : SmoothOfRelativeDimension 2 s[Φ] :=
        rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
      letI : IsIntegral W := (hT.append hR).isIntegral s[Φ]
      letI : IsModification (R.toBase ≫ T.toBase) := by
        rw [← toBase_append]
        exact (hT.append hR).isModification_of_smoothOfRelativeDimension_two s[Φ]
      (R.toBase ≫ T.toBase).toRationalMap.comp (Φ.denseTorusPartialIso (P.model 0)).toRationalMap =
        (q ≫ π[P.common_model 0]).toRationalMap) :
    ∃ (l : ℕ) (Z : Scheme) (U : BlowupTower X[P.model 0] l Z) (e : W ≅ Z),
      IsClosedPointTower X[P.model 0] U ∧ e.hom ≫ U.toBase = q ≫ π[P.common_model 0] := by
  let Δ := P.model 0
  let f : W ⟶ X[Δ] := q ≫ π[P.common_model 0]
  let : Nonempty Φ.cones := hc.nonempty_cones
  let : Nonempty Δ.cones := (P.model_complete 0).nonempty_cones
  let : SmoothOfRelativeDimension 2 s[Φ] :=
    rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let : SmoothOfRelativeDimension 2 s[Δ] :=
    rankTwo ▸ Δ.smoothOfRelativeDimension_algebraicRealizationStructureMap (P.model_regular 0)
  let : IsLocallyNoetherian X[Φ] := LocallyOfFiniteType.isLocallyNoetherian s[Φ]
  let : Nontrivial X[Φ] := by
    rw [← not_subsingleton_iff_nontrivial, ← TauCeti.topologicalKrullDim_eq_zero_iff_subsingleton,
      topologicalKrullDim_eq_of_smoothOfRelativeDimension s[Φ] (n := 2)]
    decide
  let : W.Over S := ⟨(T.append R).toBase ≫ s[Φ]⟩
  let : W.IsProjectiveOver ℂ := (T.append R).isProjectiveOver ℂ
  let : IsIntegral W := (hT.append hR).isIntegral s[Φ]
  let : SmoothOfRelativeDimension 2 s(W) := (hT.append hR).smoothOfRelativeDimension s[Φ]
  have hq' : f ≫ s[Δ] = (T.append R).toBase ≫ s[Φ] := by
    simpa only [f, Δ, toBase_append, Category.assoc] using hq
  let : f.IsOver S := ⟨hq'⟩
  have hqMod := (hT.append hR).isModification_of_resolved_partialIso s[Φ] s[Δ]
    (Φ.denseTorusPartialIso Δ) f hq' (by simpa only [toBase_append] using hmap)
  exact f.exists_isClosedPointTower_factorization (k := ℂ) (IsModification.birationalOver f)

/-- The specified toric preparation carries a first base center of order greater
than half the Hirzebruch fiber degree to the same binomial point of the quadric,
with equal order and equal fiber degree. The prepared point tower resolves the
prescribed rational change of target on the same nodal refinement as the
intermediate toric links. Its pole ideal is the pulled-back reduced total
boundary. The line bundle can in particular be the pullback of the plane
hyperplane bundle along a specified resolving morphism. -/
theorem exists_prepared_quadric_resolution_of_high_fiber_center
    (j : Fin n) (c : ℂˣ) (hj : hT.baseCenter j = p[r 1,c])
    (hfirst : ∀ l < j, hT.baseCenter l ≠ p[r 1,c]) (L : LineBundleClass Y)
    (D : Y.IdealSheafData) (hD : D.IsEffectiveCartier) :
    letI : Nonempty Φ.cones := hc.nonempty_cones
    letI : SmoothOfRelativeDimension 2 s[Φ] :=
      rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    letI : IsNoetherian X[Φ] := isNoetherian_of_finiteType s[Φ]
    letI : IsIntegral Y := hT.isIntegral s[Φ]
    letI : Y.Over S := ⟨T.toBase ≫ s[Φ]⟩
    letI : SmoothOfRelativeDimension 2 s(Y) := hT.smoothOfRelativeDimension s[Φ]
    letI : Smooth s(Y) := SmoothOfRelativeDimension.smooth 2 _
    letI : T.toBase.IsOver S := ⟨rfl⟩
    letI : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two s[Φ]
    let hB := Φ.isEffectiveCartier_boundaryIdeal hΦ hc rankTwo
    let v := (T.picardMarking hT s[Φ]).symm (Additive.ofMul L)
    let β := (Φ.hirzebruchPicardBasis b a hΦ r hr).repr v.1 1
    (hB.toInvertibleSheaf ≅ canonicalBundle ℂ X[Φ] 2) →
      B[Φ,hc].comap T.toBase = D * ramificationIdealSheaf ℂ T.toBase →
      β < 2 * (-v.2 j) →
      ∃ (P : Fan.HirzebruchQuadricPreparation b a Φ)
        (m : ℕ) (W : Scheme) (R : BlowupTower Y m W)
        (hR : IsNodalBoundaryTower D s(Y) (𝟙 Y) R)
        (q : W ⟶ X[P.common]) (hW : IsIntegral W) (_ : IsDominant q)
        (hdom : IsDominant (R.toBase ≫ T.toBase)),
        letI := hW
        letI := hdom
        let Δ := P.model 0
        letI : Nonempty Δ.cones := (P.model_complete 0).nonempty_cones
        letI : SmoothOfRelativeDimension 2 s[Δ] :=
          rankTwo ▸ Δ.smoothOfRelativeDimension_algebraicRealizationStructureMap (P.model_regular 0)
        letI : Smooth s[Δ] := SmoothOfRelativeDimension.smooth 2 _
        letI : IsNoetherian X[Δ] := isNoetherian_of_finiteType s[Δ]
        ∃ (u : Fin 4 ≃ Δ.Ray)
          (hu : (fun l ↦ (u l).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])
          (_ : X[Δ].IsProjectiveOver ℂ) (l : ℕ) (Z : Scheme) (U : BlowupTower X[Δ] l Z)
          (hU : IsClosedPointTower X[Δ] U) (e : W ≅ Z) (j' : Fin l),
        q ≫ π[P.common_source] = R.toBase ≫ T.toBase ∧
        q ≫ π[P.common_model 0] = e.hom ≫ U.toBase ∧
        e.hom ≫ U.toBase ≫ s[Δ] = R.toBase ≫ s(Y) ∧
        (∀ (Γ : Fan i) [Nonempty Γ.cones] (A : P.common.IsSubdivision Γ),
          (R.toBase ≫ T.toBase).toRationalMap.comp (Φ.denseTorusPartialIso Γ).toRationalMap =
            (q ≫ π[A]).toRationalMap ∧
          ∃ hOver : q ≫ π[A] ≫ Γ.algebraicRealizationStructureMap = R.toBase ≫ s(Y),
            letI : W.Over S := ⟨R.toBase ≫ s(Y)⟩
            letI : (q ≫ π[A]).IsOver S := ⟨hOver⟩
            letI : Smooth s(W) := (hR.isClosedPointTower.smoothOfRelativeDimension s(Y)).smooth
            Γ.IsRegular →
            (Γ.boundaryIdeal inferInstance).comap (q ≫ π[A]) =
              (D.comap R.toBase).radical * ramificationIdealSheaf ℂ (q ≫ π[A])) ∧
        letI : Z.Over S := ⟨U.toBase ≫ s[Δ]⟩
        letI : U.toBase.IsOver S := ⟨rfl⟩
        letI : Smooth s(Z) := (hU.smoothOfRelativeDimension s[Δ]).smooth
        B[Δ,P.model_complete 0].comap U.toBase =
          ((D.comap R.toBase).radical.comap e.inv) * ramificationIdealSheaf ℂ U.toBase ∧
        hU.baseCenter j' = p[u 1,c] ∧ (∀ k < j', hU.baseCenter k ≠ p[u 1,c]) ∧
        pullback R.toBase (T.exceptionalClass j) = pullback e.hom (U.exceptionalClass j') ∧
        let w := (U.picardMarking hU s[Δ]).symm (Additive.ofMul (pullback (e.inv ≫ R.toBase) L))
        let β' := (Δ.hirzebruchPicardBasis b 0 (P.model_regular 0) u hu).repr w.1 1
        β' = β ∧ -w.2 j' = -v.2 j ∧ β' < 2 * (-w.2 j') := by
  intro hB v β ω hPole hhigh
  let : Nonempty Φ.cones := hc.nonempty_cones
  let : SmoothOfRelativeDimension 2 s[Φ] :=
    rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let : IsNoetherian X[Φ] := isNoetherian_of_finiteType s[Φ]
  let : IsIntegral Y := hT.isIntegral s[Φ]
  let : Y.Over S := ⟨T.toBase ≫ s[Φ]⟩
  let : SmoothOfRelativeDimension 2 s(Y) := hT.smoothOfRelativeDimension s[Φ]
  let : Smooth s(Y) := SmoothOfRelativeDimension.smooth 2 _
  let : T.toBase.IsOver S := ⟨rfl⟩
  let : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two s[Φ]
  let : Y.IsProjectiveOver ℂ := T.isProjectiveOver ℂ
  have hTotal := hB.comap_of_isDominant T.toBase
  have hRam : (ramificationIdealSheaf ℂ T.toBase).IsEffectiveCartier := by
    rw [← hT.ramificationIdealSheafToBase_def ℂ]
    exact hT.isEffectiveCartier_ramificationIdealSheafToBase ℂ
  have hdiv :=
    (QPainleve.pullbackTopFormDivisor_eq_neg_iff ℂ T.toBase 2 hB ω hTotal hD hRam).mpr hPole
  have hrays : Set.range (Fan.Ray.primitiveGenerator (Phi := Φ)) =
      {b 0, b 1, -b 0, (a : ℤ) • b 0 - b 1} := by
    rw [← r.surjective.range_comp, Function.comp_def, hr]
    simp [Fin.range_fin_succ]
  -- Keep the single nodal refinement that resolves all the toric stages.
  obtain ⟨P, m, W, R, q, hW, hq, hdom, hR, hproj, hreg⟩ :=
    Φ.exists_nodal_resolution_of_hirzebruch_quadric_preparation b a hΦ hc hrays
      (IsModification.birationalOver T.toBase) hD ω hTotal hRam hdiv
  let Δ := P.model 0
  let : Nonempty Δ.cones := (P.model_complete 0).nonempty_cones
  have hrays' : Set.range (Fan.Ray.primitiveGenerator (Phi := Δ)) =
      {b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1} := P.model_rays 0
  obtain ⟨u, hu⟩ := Fan.exists_rayEquiv_of_hirzebruch_ray_generators b 0 hrays'
  let : X[Δ].IsProjectiveOver ℂ := Δ.isProjectiveOver_quadric b
    (P.model_regular 0) (P.model_complete 0) u hu
  let : SmoothOfRelativeDimension 2 s[Δ] :=
    rankTwo ▸ Δ.smoothOfRelativeDimension_algebraicRealizationStructureMap (P.model_regular 0)
  let : Smooth s[Δ] := SmoothOfRelativeDimension.smooth 2 _
  let : IsNoetherian X[Δ] := isNoetherian_of_finiteType s[Δ]
  let f : W ⟶ X[Δ] := q ≫ π[P.common_model 0]
  obtain ⟨hmap, hf, hpole⟩ := hreg Δ (P.common_model 0)
  have hfOver : f ≫ s[Δ] = R.toBase ≫ s(Y) := by
    dsimp only [f]
    rw [Category.assoc, Fan.algebraicRealization_over]
    exact hf
  obtain ⟨l, Z, U, e, hU, he⟩ :=
    exists_quadric_tower_of_resolved_preparation b a hΦ hc hT P hR.isClosedPointTower q hfOver hmap
  -- The common subdivision preserves both the selected point ideal and the ruling.
  have hρ : (r 1).primitiveGenerator = (u 1).primitiveGenerator :=
    (congrFun hr (1 : Fin 4)).trans (congrFun hu (1 : Fin 4)).symm
  obtain ⟨j', hj', hfirst', hclass, horder⟩ := hT.base_order_eq_of_common_subdivision
    hR.isClosedPointTower hU hΦ (P.model_regular 0) e P.common_source (P.common_model 0) q
    hproj he.symm b (r 1) (u 1) hρ c j hj hfirst L
  have hdegree := hT.hirzebruch_fiber_degree_eq_of_common_subdivision b a hΦ hc r hr
    0 (P.model_regular 0) (P.model_complete 0) u hu hR.isClosedPointTower hU e
    P.common_source (P.common_model 0) q hproj he.symm L
  have heOver : e.hom ≫ U.toBase ≫ s[Δ] = R.toBase ≫ s(Y) := by
    rw [← Category.assoc, he]
    exact hfOver
  refine ⟨P, m, W, R, hR, q, hW, hq, hdom, u, hu, inferInstance, l, Z, U, hU, e, j',
    hproj, he.symm, heOver, hreg, ?_, hj', hfirst', hclass, hdegree.symm, horder.symm,
    hdegree.symm ▸ horder.symm ▸ hhigh⟩
  -- Transport the pole factorization to the endpoint of the closed-point tower.
  let : W.Over S := ⟨R.toBase ≫ s(Y)⟩
  let : Z.Over S := ⟨U.toBase ≫ s[Δ]⟩
  let : e.hom.IsOver S := ⟨heOver⟩
  let : U.toBase.IsOver S := ⟨rfl⟩
  let : SmoothOfRelativeDimension 2 s(W) := hR.isClosedPointTower.smoothOfRelativeDimension s(Y)
  let : SmoothOfRelativeDimension 2 s(Z) := hU.smoothOfRelativeDimension s[Δ]
  have h := comap_eq_mul_ramificationIdealSheaf_comp_iff_of_isIso ℂ e.hom U.toBase 2
    (D := B[Δ,P.model_complete 0]) (Q := (D.comap R.toBase).radical)
  rw [IsIso.inv_eq_of_hom_inv_id e.hom_inv_id] at h
  exact h.mp (by simpa only [he, f] using hpole (P.model_regular 0))

end QPainleve.BlowupTower.IsClosedPointTower
