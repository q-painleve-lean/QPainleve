/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Blowdown
public import QPainleve.Geometry.Toric.Fan.Boundary.Prime

import QPainleve.AlgebraicGeometry.Blowup.Tower.Isometry.Basic
import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.ExceptionalCurve
import QPainleve.Geometry.Toric.Fan.Boundary.Canonical
import QPainleve.Geometry.Toric.Fan.Boundary.InternalBlowup
import QPainleve.Geometry.Toric.Fan.Logarithmic.InternalBlowup
import QPainleve.Geometry.Toric.Fan.Picard.StrictTransform
import QPainleve.Geometry.Toric.Fan.Rationality
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective


/-!
# Nodal contractions after moving internal centers

The fixed Picard coordinates of a strict boundary ray and the canonical class
determine whether that component can be contracted. If it is exceptional for
one ordered choice of internal centers, it contracts to a node for every choice.
The resulting contractions remove the same ray from the boundary.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module QPainleve QPainleve.BlowupTower TopologicalSpace
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData LineBundleClass

namespace TauCeti.Toric.Fan

universe u

variable (k : Type u) [Field k] [IsAlgClosed k] {N V : Type u}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]
  (b : Basis (Fin 2) ℤ N) {r : ℕ} (s : Fin r → Φ.Ray) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)

local notation "S" => Spec (CommRingCat.of k)
local notation "Z" => Φ.finiteFanScheme k
local notation "model[" c "]" => internalBlowupTower k b s c
local notation "Y[" c "]" => (model[c]).1
local notation "T[" c "]" => WithBoundary.toTower (Sigma.snd (model[c]))
local notation "B[" c "]" => Scheme.Hom.ker (WithBoundary.boundaryι (Sigma.snd (model[c])))
local notation "hT[" c "]" => isClosedPointTower_internalBlowupTower k b s c
local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "K[" X "]" => LineBundleClass.mk (canonicalBundle k X 2)
local notation "I[" p "]" =>
  vanishingIdeal (Closeds.mk (closure (Singleton.singleton p)) isClosed_closure)
local notation "bp[" c "," ρ "]" => internalBlowupBoundaryPrimeEquiv k hΦ b s c ρ
local notation "C[" c "," ρ "]" =>
  I[(Subtype.val (bp[c,ρ]))]
local notation "pointTower[" p "]" => BlowupTower.nil.snoc (I[p])

include hc in
/-- The strict transform of a specified ray is exceptional of the first kind
for one tuple of internal centers if and only if it is exceptional for the other.
The comparison fixes the ordered exceptional coordinates in the Picard marking. -/
theorem isExceptionalCurveOfFirstKind_internalBlowupRay_iff
    (c d : Fin r → kˣ) (ρ : Φ.Ray) :
    (C[c,ρ]).IsExceptionalCurveOfFirstKind ↔ (C[d,ρ]).IsExceptionalCurveOfFirstKind := by
  classical
  let : SmoothOfRelativeDimension 2 (Z ↘ S) := by
    rw [Φ.finiteFanScheme_over k]
    exact rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k hΦ
  let : (Z).IsProjectiveOver k := Φ.isProjectiveOver_finiteFanScheme_of_isComplete k hΦ hc b
  let : IsIntegral Z := inferInstance
  let : Y[c].Over S := ⟨(T[c]).toBase ≫ Z ↘ S⟩
  let : Y[d].Over S := ⟨(T[d]).toBase ≫ Z ↘ S⟩
  let : IsNoetherian Y[c] := (T[c]).isNoetherian
  let : IsNoetherian Y[d] := (T[d]).isNoetherian
  let : SmoothOfRelativeDimension 2 (Y[c] ↘ S) := (hT[c]).smoothOfRelativeDimension (Z ↘ S)
  let : SmoothOfRelativeDimension 2 (Y[d] ↘ S) := (hT[d]).smoothOfRelativeDimension (Z ↘ S)
  let : IsIntegral Y[c] := isIntegral_internalBlowupTower k b s c hΦ
  let : IsIntegral Y[d] := isIntegral_internalBlowupTower k b s d hΦ
  let : Y[c].IsProjectiveOver k := (T[c]).isProjectiveOver k
  let : Y[d].IsProjectiveOver k := (T[d]).isProjectiveOver k
  let : Scheme.IsRationalOver (Z ↘ S) := by
    rw [Φ.finiteFanScheme_over k]
    exact Φ.isRationalOver_of_isComplete k hΦ hc b
  let : Scheme.IsRationalOver (Y[c] ↘ S) := (hT[c]).isRationalOver (Z ↘ S)
  let : Scheme.IsRationalOver (Y[d] ↘ S) := (hT[d]).isRationalOver (Z ↘ S)
  let e := picardIsometryCongr k (hT[c]) (hT[d])
    (.refl (Chow.intersectionBilinForm k Z))
  let p : CodimensionOnePoint Y[c] := ⟨_, (mem_boundaryPrimes.mp (bp[c,ρ]).property).2⟩
  let q : CodimensionOnePoint Y[d] := ⟨_, (mem_boundaryPrimes.mp (bp[d,ρ]).property).2⟩
  let := (Y[c] ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let := (Y[d] ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let a := Additive.ofMul (primeDivisorClass p)
  let a' := Additive.ofMul (primeDivisorClass q)
  have ha : e a = a' := by
    dsimp only [a, a', p, q, e]
    rw [← picardHom_markedBoundaryMap_single_eq_primeDivisorClass k hΦ b s c ρ,
      ← picardHom_markedBoundaryMap_single_eq_primeDivisorClass k hΦ b s d ρ,
      picardIsometryCongr_picardHom]
    rfl
  have hk : e (Additive.ofMul K[Y[c]]) = Additive.ofMul K[Y[d]] :=
    picardIsometryCongr_canonicalClass k (hT[c]) (hT[d]) _ rfl
  have hmap (x y : Additive (LineBundleClass Y[c])) :
      Chow.classIntersectionNumber k Y[d] (e x).toMul (e y).toMul =
        Chow.classIntersectionNumber k Y[c] x.toMul y.toMul :=
    (Chow.intersectionBilinForm_apply k Y[d] (e x) (e y)).symm.trans
      ((e.map_app y x).trans (Chow.intersectionBilinForm_apply k Y[c] x y))
  have hsq := hmap a a
  have hpair := hmap a (Additive.ofMul K[Y[c]])
  rw [ha] at hsq
  rw [ha, hk] at hpair
  simp only [a, a', toMul_ofMul] at hsq hpair
  have hc' := Chow.isExceptionalCurveOfFirstKind_iff_primeDivisorClass k p
  have hd' := Chow.isExceptionalCurveOfFirstKind_iff_primeDivisorClass k q
  dsimp only at hc' hd'
  have h := hc'.trans (Iff.trans (by rw [hsq, hpair]) hd'.symm)
  exact h

private theorem bijOn_surviving_rays (d : Fin r → kˣ) (ρ : Φ.Ray) :
    Set.BijOn (fun τ ↦ (bp[d,τ]).val) {τ | τ ≠ ρ}
      ((B[d]).boundaryPrimes \ (C[d,ρ]).support) := by
  let j := internalBlowupBoundaryPrimeEquiv k hΦ b s d
  have hmem (τ : Φ.Ray) : (j τ).val ∈ (C[d,ρ]).support ↔ τ = ρ := by
    rw [← SetLike.mem_coe, coe_support_vanishingIdeal, Closeds.coe_mk]
    constructor
    · intro h
      let point (ν : Φ.Ray) := (B[d]).boundaryPrimeEmbedding (j ν)
      have hh : (point ρ : Y[d]) ⤳ (point τ : Y[d]) := by
        simpa only [point, coe_boundaryPrimeEmbedding] using specializes_iff_mem_closure.mpr h
      have he := congrArg Subtype.val (CodimensionOnePoint.eq_of_specializes hh)
      apply j.injective
      apply Subtype.ext
      simpa only [point, coe_boundaryPrimeEmbedding] using he.symm
    · rintro rfl
      exact subset_closure (Set.mem_singleton _)
  refine ⟨fun τ hτ ↦ ⟨(j τ).property, fun h ↦ hτ ((hmem τ).mp h)⟩,
    (Subtype.val_injective.comp j.injective).injOn, ?_⟩
  intro x hx
  obtain ⟨τ, hτ⟩ := j.surjective ⟨x, hx.1⟩
  have he : (j τ).val = x := congrArg Subtype.val hτ
  exact ⟨τ, fun h ↦ hx.2 (he ▸ (hmem τ).mpr h), he⟩

include hc in
variable [NeZero (2 : k)] in
/-- A ray that is exceptional for one ordered center tuple defines a nodal
blowdown for every other tuple in the same presentation. The exceptional fiber is
the strict transform of that ray. The reduced total transform is the entire
strict boundary of the ordered model. Projection identifies the remaining rays
with the boundary primes downstairs. -/
theorem exists_matching_nodal_boundary_blowdown
    (c d : Fin r → kˣ) (ρ : Φ.Ray) (hE : (C[c,ρ]).IsExceptionalCurveOfFirstKind) :
    let : Y[d].Over S := ⟨(T[d]).toBase ≫ Z ↘ S⟩
    ∃ (X : Scheme) (t : X ⟶ S) (f : Y[d] ⟶ X) (p : X),
      let : X.Over S := ⟨t⟩
      ∃ (_ : IsIntegral X) (_ : X.IsProjectiveOver k) (hSm : SmoothOfRelativeDimension 2 t),
        let : SmoothOfRelativeDimension 2 (X ↘ S) := hSm
        f.IsOver S ∧ IsModification f ∧ IsClosed ({p} : Set X) ∧ f.centre = {p} ∧
        (I[p]).comap f = C[d,ρ] ∧
        ∃ e : Y[d] ≅ (I[p]).blowup, e.hom ≫ (pointTower[p]).toBase = f ∧
          let F := (B[d]).map f
          ∃ hF : F.IsEffectiveCartier,
            LineBundleClass.mk hF.toInvertibleSheaf = K[X] ∧
            AtWorstNodalOfRelativeDimensionOne (F.subschemeι ≫ t) ∧
            IsNodalBoundaryTower F t (𝟙 X) (pointTower[p]) ∧ (F.comap f).radical = B[d] ∧
            Set.BijOn (fun τ ↦ f (bp[d,τ]).val) {τ | τ ≠ ρ} F.boundaryPrimes := by
  intro _
  let : SmoothOfRelativeDimension 2 (Z ↘ S) := by
    rw [Φ.finiteFanScheme_over k]
    exact rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k hΦ
  let : (Z).IsProjectiveOver k := Φ.isProjectiveOver_finiteFanScheme_of_isComplete k hΦ hc b
  let : IsIntegral Y[d] := isIntegral_internalBlowupTower k b s d hΦ
  let : Y[d].IsProjectiveOver k := (T[d]).isProjectiveOver k
  let : SmoothOfRelativeDimension 2 (Y[d] ↘ S) := (hT[d]).smoothOfRelativeDimension (Z ↘ S)
  let hBase := Φ.isEffectiveCartier_boundaryIdeal k hΦ hc rankTwo
  let hB := isEffectiveCartier_internalBlowupBoundary k b s hΦ d hBase
  have hcan : LineBundleClass.mk hB.toInvertibleSheaf = K[Y[d]] :=
    canonicalClass_internalBlowupTower k b s d hΦ hBase hB
      (Φ.canonicalClass_boundaryIdeal k hΦ hc b hBase)
  have hsub : (C[d,ρ]).support ≤ (B[d]).support := by
    rw [← SetLike.coe_subset_coe, coe_support_vanishingIdeal, Closeds.coe_mk]
    exact (B[d]).support.isClosed.closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr (mem_boundaryPrimes.mp (bp[d,ρ]).property).1)
  obtain ⟨X, t, f, p, hX, hP, hSm, hover, hmod, hp, hcentre, hexc, e, he, hF, hK, hN, hT,
    hred, hbij⟩ := hB.exists_nodal_boundary_blowdown
      (atWorstNodalOfRelativeDimensionOne_internalBlowupBoundary k b s hΦ hc d) hcan
      ((isExceptionalCurveOfFirstKind_internalBlowupRay_iff k b s hΦ hc c d ρ).mp hE) hsub
  exact ⟨X, t, f, p, hX, hP, hSm, hover, hmod, hp, hcentre, hexc, e, he, hF, hK, hN, hT, hred,
    hbij.comp (bijOn_surviving_rays k b s hΦ d ρ)⟩

end TauCeti.Toric.Fan
