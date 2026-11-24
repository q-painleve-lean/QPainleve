/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Isometry.Descent
public import QPainleve.Geometry.Toric.Fan.Boundary.Reconstruction
public import QPainleve.Geometry.Toric.Fan.Picard.StrictTransform
public import QPainleve.Geometry.Toric.Fan.Smooth

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.Geometry.Toric.Fan.Boundary.Equiv

/-!
# Reconstructing toric bases from a Picard isometry

A Picard isometry matching the total exceptional classes and the cyclically ordered
strict boundary classes determines a toric isomorphism of the bases. The pullback
of this isomorphism on the base summand, together with the matched exceptional
summand, recovers the full given Picard isometry.

The reconstruction from the toric boundary and the matched exceptional classes
is used in [Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical
cycle*, Remark 2.4 and Theorem 4.7][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S4.Thmtheorem7
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve QPainleve.BlowupTower TauCeti.AlgebraicGeometry
open LineBundleClass Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N N' V V' : Type} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Pic(" X ")" => Additive (LineBundleClass X)
local notation "B(" X ")" => Chow.intersectionBilinForm ℂ X
local notation "rankTwo(" b ")" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "rayClass(" A ", " h ", " r ")" =>
  Additive.ofMul (LineBundleClass.primeDivisorClass (Fan.rayBoundaryPoint A h r))
local notation "cartierClass(" h ")" => Additive.ofMul (LineBundleClass.mk
  (Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheaf h))⁻¹

private theorem rayClass_eq_cartierClass (hΦ : Φ.IsRegular) (r : Φ.Ray) :
    let := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
    rayClass(Φ, hΦ, r) = cartierClass(Φ.isEffectiveCartier_rayBoundaryIdeal hΦ r) := by
  intro _
  rw [primeDivisorClass_def, mk_toInvertibleSheaf_congr _ _ (Φ.rayBoundaryIdeal_def hΦ r).symm]

private theorem pullback_eq_of_rayClasses [Nonempty Ψ.cones] (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)
    (f : FanEquiv Φ Ψ)
    (e₀ : Pic(Ψ.algebraicRealization) →ₗ[ℤ] Pic(Φ.algebraicRealization))
    (he₀ : let := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
           let := Ψ.uniqueFactorizationMonoid_stalk_algebraicRealization hΨ
           ∀ r : Φ.Ray, e₀ rayClass(Ψ, hΨ, f.rayEquiv r) = rayClass(Φ, hΦ, r))
    (a : Pic(Ψ.algebraicRealization)) :
    e₀ a = Additive.ofMul (pullback f.toFanHom.algebraicMap a.toMul) := by
  let := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  let := Ψ.uniqueFactorizationMonoid_stalk_algebraicRealization hΨ
  let := Fintype.ofFinite Ψ.Ray
  obtain ⟨x, rfl⟩ := Ψ.rayDivisorToPicard_surjective hΨ a
  let p := (pullbackHom f.toFanHom.algebraicMap).toAdditive
  have hp (r : Ψ.Ray) : e₀ rayClass(Ψ, hΨ, r) = p rayClass(Ψ, hΨ, r) := by
    obtain ⟨s, rfl⟩ := f.rayEquiv.surjective r
    rw [he₀ s]
    simpa only [p, MonoidHom.toAdditive_apply_apply, pullbackHom_apply, toMul_ofMul] using
      congrArg Additive.ofMul (f.pullback_primeDivisorClass_rayBoundaryPoint hΦ hΨ s).symm
  calc
    e₀ (Ψ.rayDivisorToPicard hΨ x) = p (Ψ.rayDivisorToPicard hΨ x) := by
      simp only [Ψ.rayDivisorToPicard_apply hΨ, map_sum, map_zsmul, hp]
    _ = _ := by simp only [p, MonoidHom.toAdditive_apply_apply, pullbackHom_apply]

variable [Φ.algebraicRealization.IsProjectiveOver ℂ] [Ψ.algebraicRealization.IsProjectiveOver ℂ]
  {m n : ℕ} [NeZero m] {Y W : Scheme}
  {T : BlowupTower Φ.algebraicRealization n Y} {U : BlowupTower Ψ.algebraicRealization n W}

local notation "s(" A ")" => (Fan.algebraicRealization A ↘ S)

/-- If a Picard isometry of two point-blowup models matches the ordered total
exceptional classes and the cyclically ordered strict ray classes, a unique fan
equivalence matches the ray numberings. In the full blowup coordinates the
isometry acts by pullback along that toric map on the base classes and fixes
each exceptional coefficient. The statement allows infinitely near centers. -/
theorem existsUnique_fanEquiv_of_strictRayBoundaryClasses
    (b : Module.Basis (Fin 2) ℤ N) (b' : Module.Basis (Fin 2) ℤ N')
    (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (hc : Φ.IsComplete) (hc' : Ψ.IsComplete)
    (u : ZMod m ≃ Φ.Ray) (v : ZMod m ≃ Ψ.Ray)
    (hu : ∀ j, b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ)
    (hv : ∀ j, b'.detDualEquiv (v j).primitiveGenerator (v (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : Ψ.cones, (v j).toCone ≤ σ ∧ (v (j + 1)).toCone ≤ σ)
    (hT : IsClosedPointTower Φ.algebraicRealization T)
    (hU : IsClosedPointTower Ψ.algebraicRealization U)
    (e :
      let : Nonempty Φ.cones := hc.nonempty_cones
      let : Nonempty Ψ.cones := hc'.nonempty_cones
      let : SmoothOfRelativeDimension 2 s(Φ) :=
        rankTwo(b) ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
      let : SmoothOfRelativeDimension 2 s(Ψ) :=
        rankTwo(b') ▸ Ψ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΨ
      let : IsNoetherian Φ.algebraicRealization := isNoetherian_of_finiteType s(Φ)
      let : IsNoetherian Ψ.algebraicRealization := isNoetherian_of_finiteType s(Ψ)
      let : Y.Over S := ⟨T.toBase ≫ s(Φ)⟩
      let : W.Over S := ⟨U.toBase ≫ s(Ψ)⟩
      let : Y.IsProjectiveOver ℂ := T.isProjectiveOver ℂ
      let : W.IsProjectiveOver ℂ := U.isProjectiveOver ℂ
      let : IsIntegral Y := hT.isIntegral s(Φ)
      let : IsIntegral W := hU.isIntegral s(Ψ)
      let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension s(Φ)
      let : SmoothOfRelativeDimension 2 (W ↘ S) := hU.smoothOfRelativeDimension s(Ψ)
      B(W).IsometryEquiv B(Y))
    (he : ∀ j, e (Additive.ofMul (U.exceptionalClass j)) = Additive.ofMul (T.exceptionalClass j))
    (hD :
      let : Nonempty Φ.cones := hc.nonempty_cones
      let : Nonempty Ψ.cones := hc'.nonempty_cones
      ∀ j, e (strictRayBoundaryClass hΨ rankTwo(b') U hU (v j)) =
        strictRayBoundaryClass hΦ rankTwo(b) T hT (u j)) :
    ∃! f : FanEquiv Φ Ψ, (∀ j, f.rayEquiv (u j) = v j) ∧
      ∀ (a : Pic(Ψ.algebraicRealization)) (t : Fin n → ℤ),
        e (U.picardHom (a, t)) =
          T.picardHom (Additive.ofMul (pullback f.toFanHom.algebraicMap a.toMul), t) := by
  let : Nonempty Φ.cones := hc.nonempty_cones
  let : Nonempty Ψ.cones := hc'.nonempty_cones
  let : SmoothOfRelativeDimension 2 s(Φ) :=
    rankTwo(b) ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let : SmoothOfRelativeDimension 2 s(Ψ) :=
    rankTwo(b') ▸ Ψ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΨ
  let := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  let := Ψ.uniqueFactorizationMonoid_stalk_algebraicRealization hΨ
  obtain ⟨e₀, hdesc, -⟩ := (existsUnique_picardIsometryCongr_eq hU hT e).mpr he
  have hbase (j : ZMod m) : e₀ rayClass(Ψ, hΨ, v j) = rayClass(Φ, hΦ, u j) := by
    have h := hD j
    rw [← hdesc,
      strictRayBoundaryClass_eq hΨ rankTwo(b') U hU (v j)
        (hU.isEffectiveCartier_strictTransform s(Ψ)
          (Ψ.isEffectiveCartier_rayBoundaryIdeal hΨ (v j))),
      strictRayBoundaryClass_eq hΦ rankTwo(b) T hT (u j)
        (hT.isEffectiveCartier_strictTransform s(Φ)
          (Φ.isEffectiveCartier_rayBoundaryIdeal hΦ (u j)))] at h
    obtain ⟨hr, -⟩ :=
      (picardIsometryCongr_strictTransform_eq_iff ℂ hU hT e₀
        (Ψ.isEffectiveCartier_rayBoundaryIdeal hΨ (v j))
        (Φ.isEffectiveCartier_rayBoundaryIdeal hΦ (u j))).mp h
    simpa only [rayClass_eq_cartierClass] using hr
  have hs (j : ZMod m) : Φ.rayBoundarySelfIntersection hΦ (u j) =
      Ψ.rayBoundarySelfIntersection hΨ (v j) := by
    have h := e₀.map_app rayClass(Ψ, hΨ, v j) rayClass(Ψ, hΨ, v j)
    simpa only [hbase, Chow.intersectionBilinForm_apply, toMul_ofMul,
      rayBoundarySelfIntersection_def] using h
  obtain ⟨f, hf, huniq⟩ :=
    existsUnique_fanEquiv_of_boundarySelfIntersections b b' hΦ hΨ hc hc' u v hu hv hs
  refine ⟨f, ⟨hf, ?_⟩, fun f' hf' ↦ huniq f' hf'.1⟩
  intro a t
  rw [← hdesc, picardIsometryCongr_picardHom]
  have hp := pullback_eq_of_rayClasses hΦ hΨ f e₀.toLinearEquiv.toLinearMap (fun r ↦ by
    obtain ⟨j, rfl⟩ := u.surjective r
    rw [hf j]
    exact hbase j) a
  simpa only [LinearEquiv.coe_coe, LinearMap.BilinForm.IsometryEquiv.coe_toLinearEquiv] using
    congrArg (fun x ↦ T.picardHom (x, t)) hp

end TauCeti.Toric.Fan
