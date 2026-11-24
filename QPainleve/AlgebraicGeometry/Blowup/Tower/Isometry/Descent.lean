/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Isometry.Basic

/-!
# Descending Picard isometries through point blowups

An isometry that matches the total exceptional classes of two ordered point-blowup
towers descends uniquely to their base surfaces. The descent preserves the class
and the center multiplicities of a divisor when the strict-transform classes match.

This is the lattice comparison after contracting the matched exceptional curves
in the proof of [Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical
cycle*, Theorem 4.7][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S4.Thmtheorem7
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry
open LineBundleClass

universe u

namespace QPainleve.BlowupTower

local notation "Pic(" S ")" => Additive (LineBundleClass S)
local notation "B(" k ", " S ")" => Chow.intersectionBilinForm k S
local notation "g(" k ", " S ")" => (S ↘ Spec (CommRingCat.of k))

variable {k : Type u} [Field k] [IsAlgClosed k]
  {X Y Z W : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y} {U : BlowupTower Z n W}
  [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 2 (g(k, X))] [SmoothOfRelativeDimension 2 (g(k, Z))]
  [IsIntegral X] [IsIntegral Z] [X.IsProjectiveOver k] [Z.IsProjectiveOver k]
  (hT : IsClosedPointTower X T) (hU : IsClosedPointTower Z U)

include hT in
/-- Intersecting a marked class with the total exceptional class of one blowup
reads the negative of that blowup's coefficient. -/
@[simp]
theorem classIntersectionNumber_picardHom_exceptionalClass
    (a : Pic(X) × (Fin n → ℤ)) (j : Fin n) :
    let : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ g(k, X)⟩
    Chow.classIntersectionNumber k Y (T.picardHom a).toMul (T.exceptionalClass j) =
      -a.2 j := by
  let : IsNoetherian X := isNoetherian_of_finiteType (g(k, X))
  have h := classIntersectionNumber_picardMarking k hT a (0, Pi.single j 1)
  simpa [picardMarking_apply, picardHom_apply_single, Pi.single_apply,
    mul_ite, Finset.sum_ite_eq', Chow.classIntersectionNumber_one_right] using h

variable (e :
   let : IsNoetherian X := isNoetherian_of_finiteType (g(k, X))
   let : IsNoetherian Z := isNoetherian_of_finiteType (g(k, Z))
   let : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ g(k, X)⟩
   let : W.Over (Spec (.of k)) := ⟨U.toBase ≫ g(k, Z)⟩
   let : Y.IsProjectiveOver k := T.isProjectiveOver k
   let : W.IsProjectiveOver k := U.isProjectiveOver k
   let : IsIntegral Y := hT.isIntegral (g(k, X))
   let : IsIntegral W := hU.isIntegral (g(k, Z))
   let : SmoothOfRelativeDimension 2 (g(k, Y)) := hT.smoothOfRelativeDimension (g(k, X))
   let : SmoothOfRelativeDimension 2 (g(k, W)) := hU.smoothOfRelativeDimension (g(k, Z))
   B(k, Y).IsometryEquiv B(k, W))

private theorem classIntersectionNumber_map (a b : Pic(Y)) :
    let : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ g(k, X)⟩
    let : W.Over (Spec (.of k)) := ⟨U.toBase ≫ g(k, Z)⟩
    Chow.classIntersectionNumber k W (e a).toMul (e b).toMul =
      Chow.classIntersectionNumber k Y a.toMul b.toMul := by
  intro _ _
  let : IsNoetherian X := isNoetherian_of_finiteType (g(k, X))
  let : IsNoetherian Z := isNoetherian_of_finiteType (g(k, Z))
  let : Y.IsProjectiveOver k := T.isProjectiveOver k
  let : W.IsProjectiveOver k := U.isProjectiveOver k
  let : IsIntegral Y := hT.isIntegral (g(k, X))
  let : IsIntegral W := hU.isIntegral (g(k, Z))
  let : SmoothOfRelativeDimension 2 (g(k, Y)) := hT.smoothOfRelativeDimension (g(k, X))
  let : SmoothOfRelativeDimension 2 (g(k, W)) := hU.smoothOfRelativeDimension (g(k, Z))
  exact (Chow.intersectionBilinForm_apply k W (e a) (e b)).symm.trans
    ((e.map_app b a).trans (Chow.intersectionBilinForm_apply k Y a b))

variable (he : ∀ j, e (Additive.ofMul (T.exceptionalClass j)) =
    Additive.ofMul (U.exceptionalClass j))

include he in
private theorem snd_eq_of_picardHom_eq
    {a : Pic(X) × (Fin n → ℤ)} {b : Pic(Z) × (Fin n → ℤ)}
    (h : e (T.picardHom a) = U.picardHom b) :
    b.2 = a.2 := by
  funext j
  have hj := classIntersectionNumber_map hT hU e
    (T.picardHom a) (Additive.ofMul (T.exceptionalClass j))
  rw [h, he j] at hj
  simpa only [toMul_ofMul, classIntersectionNumber_picardHom_exceptionalClass hT,
    classIntersectionNumber_picardHom_exceptionalClass hU, neg_inj] using hj

include he in
private theorem exists_linearEquiv_picardHom :
    ∃ e₀ : Pic(X) ≃ₗ[ℤ] Pic(Z), ∀ a, e (T.picardHom a) = U.picardHom (e₀ a.1, a.2) := by
  let : IsNoetherian X := isNoetherian_of_finiteType (g(k, X))
  let : IsNoetherian Z := isNoetherian_of_finiteType (g(k, Z))
  let m := U.picardMarking hU (g(k, Z))
  let E := m.symm.toLinearMap ∘ₗ e.toLinearEquiv.toLinearMap ∘ₗ T.picardHom
  have hE (a : Pic(X) × (Fin n → ℤ)) : U.picardHom (E a) = e (T.picardHom a) := by
    rw [← picardMarking_apply U hU (g(k, Z))]
    exact m.apply_symm_apply _
  have hs (a : Pic(X) × (Fin n → ℤ)) : (E a).2 = a.2 :=
    snd_eq_of_picardHom_eq hT hU e he (hE a).symm
  let f := LinearMap.fst ℤ (Pic(Z)) (Fin n → ℤ) ∘ₗ
    E ∘ₗ LinearMap.inl ℤ (Pic(X)) (Fin n → ℤ)
  have hcoords : E = f.prodMap LinearMap.id := by
    apply LinearMap.prod_ext
    · apply LinearMap.ext
      intro a
      exact Prod.ext rfl (hs (a, 0))
    · apply (Pi.basisFun ℤ (Fin n)).ext
      intro j
      have hj : E (0, Pi.single j 1) = (0, Pi.single j 1) := by
        apply (hU.bijective_picardHom (g(k, Z))).injective
        have hsT : T.picardHom (0, Pi.single j 1) = Additive.ofMul (T.exceptionalClass j) :=
          Additive.toMul.injective (by rw [picardHom_apply_single, zpow_one, toMul_ofMul])
        have hsU : U.picardHom (0, Pi.single j 1) = Additive.ofMul (U.exceptionalClass j) :=
          Additive.toMul.injective (by rw [picardHom_apply_single, zpow_one, toMul_ofMul])
        rw [hE, hsT, hsU, he]
      simp only [LinearMap.comp_apply, LinearMap.inr_apply, Pi.basisFun_apply, hj,
        LinearMap.prodMap_apply, map_zero, LinearMap.id_apply]
  have hbij : Function.Bijective E :=
    m.symm.bijective.comp (e.toLinearEquiv.bijective.comp (hT.bijective_picardHom (g(k, X))))
  rw [hcoords, LinearMap.coe_prodMap, LinearMap.id_coe] at hbij
  refine ⟨LinearEquiv.ofBijective f (Prod.map_bijective.mp hbij).1, fun a ↦ ?_⟩
  rw [← hE a, hcoords, LinearMap.prodMap_apply, LinearMap.id_apply, LinearEquiv.ofBijective_apply]

/-- An isometry of the blown-up Picard groups is the extension of a unique base
isometry if and only if it pairs the ordered total exceptional classes. -/
theorem existsUnique_picardIsometryCongr_eq :
    (∃! e₀ : B(k, X).IsometryEquiv B(k, Z), picardIsometryCongr k hT hU e₀ = e) ↔
      ∀ j, e (Additive.ofMul (T.exceptionalClass j)) = Additive.ofMul (U.exceptionalClass j) := by
  constructor
  · rintro ⟨e₀, rfl, -⟩
    exact picardIsometryCongr_exceptionalClass k hT hU e₀
  · intro he
    have : IsNoetherian X := isNoetherian_of_finiteType (g(k, X))
    have : IsNoetherian Z := isNoetherian_of_finiteType (g(k, Z))
    obtain ⟨f, hf⟩ := exists_linearEquiv_picardHom hT hU e he
    let e₀ : B(k, X).IsometryEquiv B(k, Z) := {
      f with
      map_app' := by
        intro x y
        have h := classIntersectionNumber_map hT hU e (T.picardHom (x, 0)) (T.picardHom (y, 0))
        simp only [hf, picardHom_apply_zero,
          IsClosedPointTower.classIntersectionNumber_pullback k hT,
          IsClosedPointTower.classIntersectionNumber_pullback k hU] at h
        simpa only [Chow.intersectionBilinForm_apply, LinearEquiv.toFun_eq_coe] using h }
    refine ⟨e₀, DFunLike.ext _ _ ?_, ?_⟩
    · intro a
      obtain ⟨⟨x, y⟩, rfl⟩ := (hT.bijective_picardHom (g(k, X))).surjective a
      rw [picardIsometryCongr_picardHom, hf]
      rfl
    · intro e₁ he₁
      apply DFunLike.ext _ _
      intro a
      have h := DFunLike.congr_fun he₁ (T.picardHom (a, 0))
      rw [picardIsometryCongr_picardHom, hf] at h
      exact congrArg Prod.fst ((hU.bijective_picardHom (g(k, Z))).injective h)

end QPainleve.BlowupTower
