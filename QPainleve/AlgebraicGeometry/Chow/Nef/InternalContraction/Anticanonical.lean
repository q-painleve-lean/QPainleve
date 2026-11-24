/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Contraction
public import QPainleve.AlgebraicGeometry.Chow.Nef.InternalContraction.Basic

import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.BoundaryPrimes
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced

/-!
# Transporting internal contractions of anticanonical pairs

A Picard isometry preserving nef cones and matching the boundary classes transports
an internal exceptional configuration. The reduced boundary descends through the
transported contraction and its complexity drops by the length of the tower. The
uncontracted pairs have equal complexity, so a configuration whose size is the source
pair's complexity gives a contracted pair of complexity zero.

This is the contraction step in the proof of
[Gross, Hacking and Keel, Theorem 1.8](https://arxiv.org/html/1211.6367v5#S2).
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve
open Scheme.IdealSheafData Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind
open TauCeti.AlgebraicGeometry.LineBundleClass
open scoped TensorProduct

namespace TauCeti.AlgebraicGeometry.Chow

universe u

variable (k : Type u) [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X.IsProjectiveOver k] [Y.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]
  [hRatX : Scheme.IsRationalOver (X ↘ Spec (.of k))]
  [hRatY : Scheme.IsRationalOver (Y ↘ Spec (.of k))]

local notation "S" => Spec (CommRingCat.of k)
local notation "Pic(" X ")" => Additive (LineBundleClass X)
local notation "V(" X ")" => (ℝ ⊗[ℤ] Pic(X))
local notation "K(" X ")" => mk (canonicalBundle k X 2)
local notation "B(" X ")" => intersectionBilinForm k X
local notation "classOf(" h ")" => Additive.ofMul ((mk
  (IsEffectiveCartier.toInvertibleSheaf (IsExceptionalCurveOfFirstKind.isEffectiveCartier h)))⁻¹)
local notation "primeClass(" D "," p ")" =>
  Additive.ofMul (primeDivisorClass (boundaryPrimeEmbedding D p))

variable [TopologicalSpace V(X)] [IsTopologicalAddGroup V(X)] [ContinuousSMul ℝ V(X)] [T2Space V(X)]
  [TopologicalSpace V(Y)] [IsTopologicalAddGroup V(Y)] [ContinuousSMul ℝ V(Y)] [T2Space V(Y)]

/-- A nef-cone preserving Picard isometry that matches the reduced anticanonical
boundary classes transports a disjoint internal exceptional configuration to a
contraction of the target. The schematic image of the target boundary is nodal
anticanonical and the contraction identifies the two boundary schemes. The image
contains all the projected centers in its smooth locus. Its complexity is the
source pair's complexity minus the number of contracted curves, and the
ordered total exceptional classes are the specified images under the isometry. -/
theorem exists_ordered_anticanonical_contraction_of_nefCone_isometry {n : ℕ}
    {D : X.IdealSheafData} {F : Y.IdealSheafData} [IsReduced D.subscheme]
    (hD : D.IsEffectiveCartier) (hF : F.IsEffectiveCartier)
    (hcanD : mk hD.toInvertibleSheaf = K(X)) (hcanF : mk hF.toInvertibleSheaf = K(Y))
    (hN : AtWorstNodalOfRelativeDimensionOne (F.subschemeι ≫ (Y ↘ S)))
    (E : Fin n → X.IdealSheafData) (hE : ∀ j, (E j).IsExceptionalCurveOfFirstKind)
    (hdis : Pairwise fun i j ↦ Disjoint ((E i).support : Set X) (E j).support)
    (hinternal : ∀ j, ¬ (E j).support ≤ D.support)
    (σ : D.boundaryPrimes ≃ F.boundaryPrimes) :
    let : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    let : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    let : IsIntegral X := hRatX.isIntegral_of_smooth
    let : IsIntegral Y := hRatY.isIntegral_of_smooth
    let : Module.Finite ℤ Pic(X) := X.finite_picard_of_isRationalOver k
    let : Module.Finite ℤ Pic(Y) := Y.finite_picard_of_isRationalOver k
    let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
    let : IsNoetherian Y := isNoetherian_of_finiteType (Y ↘ S)
    let := (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let := (Y ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    ∀ (e : B(X).IsometryEquiv B(Y)),
      (e.baseChange ℝ) '' (nefCone k (X := X) : Set V(X)) = nefCone k (X := Y) →
      (∀ p, e primeClass(D,p) = primeClass(F,σ p)) →
      ∃ (Z : Scheme.{u}) (t : Z ⟶ S) (W : Scheme.{u}) (T : BlowupTower Z n W)
        (a : Y ≅ W) (hT : T.IsClosedPointTower Z),
        let : Z.Over S := ⟨t⟩
        let f := a.hom ≫ T.toBase
        let C := F.map f
        ∃ (_ : IsIntegral Z) (_ : Z.IsProjectiveOver k) (hsm : SmoothOfRelativeDimension 2 t),
          ∃ (_ : Scheme.IsRationalOver t) (hC : C.IsEffectiveCartier)
            (hNC : AtWorstNodalOfRelativeDimensionOne (C.subschemeι ≫ t)),
          let : SmoothOfRelativeDimension 2 (Z ↘ S) := hsm
          let : LocallyOfFinitePresentation (C.subschemeι ≫ t) :=
            hNC.syntomic.locallyOfFinitePresentation
          f.IsOver S ∧ IsModification f ∧ Function.Injective hT.baseCenter ∧
          mk hC.toInvertibleSheaf = K(Z) ∧ C.boundaryComplexity + n = D.boundaryComplexity ∧
          C.comap f = F * (hT.ramificationIdealSheafToBase k).comap a.hom ∧
          (∀ j, ∃ q : C.subscheme, C.subschemeι q = hT.baseCenter j ∧
            q ∈ (C.subschemeι ≫ t).smoothLocus) ∧
          (∃ d : F.subscheme ≅ C.subscheme, d.hom ≫ C.subschemeι = F.subschemeι ≫ f) ∧
          ∀ j, Additive.ofMul (pullback a.hom (T.exceptionalClass j)) = e classOf(hE j) := by
  intro _ _ _ _ _ _ _ _ _ _ e hnef hσ
  have : IsReduced F.subscheme := hN.isReduced
  have hK := hD.map_ofMul_inv_toInvertibleSheaf_of_boundaryPrimes hF
    e.toLinearEquiv.toAddMonoidHom σ hσ
  have hK' : e (Additive.ofMul K(X)) = Additive.ofMul K(Y) := by
    simpa only [LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe,
      LinearMap.BilinForm.IsometryEquiv.coe_toLinearEquiv, hcanD, hcanF, ofMul_inv,
      map_neg, neg_inj] using hK
  have hq := D.boundaryComplexity_eq_of_picardEquiv e.toLinearEquiv σ
  obtain ⟨Z, t, W, T, a, hT, hZ, hproj, hsm, hrat, hover, hmod, hinj, -, homit, he⟩ :=
    exists_ordered_internal_contraction_of_nefCone_isometry k E hE hdis hinternal e hK' hnef
      (fun p ↦ ⟨σ.symm p, by rw [hσ, σ.apply_symm_apply]⟩)
  let : Z.Over S := ⟨t⟩
  let : SmoothOfRelativeDimension 2 (Z ↘ S) := hsm
  let : Z.IsProjectiveOver k := hproj
  have : IsNoetherian Z := isNoetherian_of_finiteType (Z ↘ S)
  have : Module.Finite ℤ Pic(Z) := Z.finite_picard_of_isRationalOver k (rational := hrat)
  obtain ⟨hC, hKC, hNC, ht, hp, hq', d, hd⟩ :=
    hT.internalBlowdown_tower_of_anticanonical_of_iso k hinj a hover hF homit hN hcanF
  exact ⟨Z, t, W, T, a, hT, hZ, hproj, hsm, hrat, hC, hNC, hover, hmod, hinj, hKC,
    hq'.symm.trans hq.symm, ht, hp, ⟨d, hd⟩, he⟩

end TauCeti.AlgebraicGeometry.Chow
