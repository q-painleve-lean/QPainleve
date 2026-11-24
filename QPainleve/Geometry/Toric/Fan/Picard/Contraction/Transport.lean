/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import QPainleve.AlgebraicGeometry.Chow.Nef.InternalContraction.Anticanonical
public import QPainleve.Geometry.Toric.Fan.Picard.Complexity

import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.ExceptionalConfiguration
import QPainleve.Geometry.Toric.Fan.Smooth

/-!
# Transporting the internal contraction of a toric presentation

An ordered toric presentation of a root-free anticanonical pair gives a disjoint
internal exceptional configuration. A Picard isometry preserving the nef cone
and matching the boundary classes transports the contraction to the other pair.
The contracted boundary has complexity zero, and the exceptional classes of
the transported tower match the original toric marking in their given order.

This is the contraction of the toric exceptional configuration in
[Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*,
proof of Theorem 1.8](https://arxiv.org/html/1211.6367v5#S2).
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower
open QPainleve (canonicalBundle BlowupTower)
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData
open scoped TensorProduct

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] [Φ.algebraicRealization.IsProjectiveOver ℂ]
  (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (b : Module.Basis (Fin 2) ℤ N)
  {n : ℕ} (s : Fin n → Φ.Ray) (c : Fin n → ℂˣ)
  {X Y : Scheme}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Pic(" X ")" => Additive (LineBundleClass X)
local notation "V(" X ")" => (ℝ ⊗[ℤ] Pic(X))
local notation "K(" X ")" => LineBundleClass.mk (canonicalBundle ℂ X 2)
local notation "B(" X ")" => Chow.intersectionBilinForm ℂ X
local notation "primeClass(" D "," p ")" =>
  Additive.ofMul (primeDivisorClass (boundaryPrimeEmbedding D p))
local notation "M" => internalBlowupTower b s c
local notation "T" => WithBoundary.toTower (Sigma.snd M)
local notation "ι" => WithBoundary.boundaryι (Sigma.snd M)
local notation "rankTwo" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)

variable [X.Over S] [Y.Over S] [X.IsProjectiveOver ℂ] [Y.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (X ↘ S)] [SmoothOfRelativeDimension 2 (Y ↘ S)]
  [hRatX : Scheme.IsRationalOver (X ↘ S)] [hRatY : Scheme.IsRationalOver (Y ↘ S)]
  [TopologicalSpace V(X)] [IsTopologicalAddGroup V(X)] [ContinuousSMul ℝ V(X)] [T2Space V(X)]
  [TopologicalSpace V(Y)] [IsTopologicalAddGroup V(Y)] [ContinuousSMul ℝ V(Y)] [T2Space V(Y)]

include hΦ hc in
/-- Transport the internal contraction of a specified ordered toric model of a
root-free anticanonical pair across a Picard isometry matching the boundary
classes and the nef cone. The resulting tower has the same ordered exceptional
classes under the isometry, and its base has anticanonical boundary of
complexity zero. Its projected centers are distinct smooth boundary points. -/
theorem exists_transported_toric_contraction_of_nefCone_isometry
    {D : X.IdealSheafData} {F : Y.IdealSheafData} [IsReduced D.subscheme]
    (hD : D.IsEffectiveCartier) (hF : F.IsEffectiveCartier)
    (hcanD : LineBundleClass.mk hD.toInvertibleSheaf = K(X))
    (hcanF : LineBundleClass.mk hF.toInvertibleSheaf = K(Y))
    (hN : AtWorstNodalOfRelativeDimensionOne (F.subschemeι ≫ (Y ↘ S)))
    (a : X ≅ (M).1)
    (ha : a.hom ≫ (T).toBase ≫ Φ.algebraicRealizationStructureMap = X ↘ S)
    (hbound : (D.comap a.inv).support = (ι).ker.support)
    (hroot : ¬ ∃ (C : Scheme) (g : C ⟶ X) (_ : IsClosedImmersion g) (_ : IsIntegral C)
      (hg : g.ker.IsEffectiveCartier),
      topologicalKrullDim C = 1 ∧ Disjoint (Set.range g) D.support ∧
      Chow.classIntersectionNumber ℂ X (LineBundleClass.mk hg.toInvertibleSheaf)⁻¹
        (LineBundleClass.mk hg.toInvertibleSheaf)⁻¹ = -2)
    (σ : D.boundaryPrimes ≃ F.boundaryPrimes) :
    let : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    let : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    let : IsIntegral X := hRatX.isIntegral_of_smooth
    let : IsIntegral Y := hRatY.isIntegral_of_smooth
    let : Module.Finite ℤ Pic(X) := X.finite_picard_of_isRationalOver ℂ
    let : Module.Finite ℤ Pic(Y) := Y.finite_picard_of_isRationalOver ℂ
    let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
    let : IsNoetherian Y := isNoetherian_of_finiteType (Y ↘ S)
    let := (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let := (Y ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    ∀ (e : B(X).IsometryEquiv B(Y)),
      (e.baseChange ℝ) '' (Chow.nefCone ℂ (X := X) : Set V(X)) = Chow.nefCone ℂ (X := Y) →
      (∀ p, e primeClass(D,p) = primeClass(F,σ p)) →
      ∃ (Z : Scheme) (t : Z ⟶ S) (W : Scheme) (U : BlowupTower Z n W)
        (d : Y ≅ W) (hU : U.IsClosedPointTower Z),
        let : Z.Over S := ⟨t⟩
        let f := d.hom ≫ U.toBase
        let C := F.map f
        ∃ (_ : IsIntegral Z) (_ : Z.IsProjectiveOver ℂ) (hsm : SmoothOfRelativeDimension 2 t),
          ∃ (_ : Scheme.IsRationalOver t) (hC : C.IsEffectiveCartier)
            (hNC : AtWorstNodalOfRelativeDimensionOne (C.subschemeι ≫ t)),
          let : SmoothOfRelativeDimension 2 (Z ↘ S) := hsm
          let : LocallyOfFinitePresentation (C.subschemeι ≫ t) :=
            hNC.syntomic.locallyOfFinitePresentation
          f.IsOver S ∧ IsModification f ∧ Function.Injective hU.baseCenter ∧
          LineBundleClass.mk hC.toInvertibleSheaf = K(Z) ∧ C.boundaryComplexity = 0 ∧
          C.comap f = F * (hU.ramificationIdealSheafToBase ℂ).comap d.hom ∧
          (∀ j, ∃ q : C.subscheme, C.subschemeι q = hU.baseCenter j ∧
            q ∈ (C.subschemeι ≫ t).smoothLocus) ∧
          (∃ v : F.subscheme ≅ C.subscheme, v.hom ≫ C.subschemeι = F.subschemeι ≫ f) ∧
          ∀ j, Additive.ofMul (pullback d.hom (U.exceptionalClass j)) =
            e (Additive.ofMul (pullback a.hom ((T).exceptionalClass j))) := by
  intro _ _ _ _ _ _ _ _ _ _ e hnef hσ
  let : IsNoetherian Φ.algebraicRealization :=
    isNoetherian_of_finiteType (Φ.algebraicRealization ↘ S)
  let : SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ S) := by
    rw [algebraicRealization_over]
    exact rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  have hcomplex : D.boundaryComplexity = n := calc
    _ = (D.comap a.inv).boundaryComplexity := (boundaryComplexity_comap_iso a.symm D).symm
    _ = (ι).ker.boundaryComplexity := boundaryComplexity_eq_of_support_eq hbound
    _ = _ := boundaryComplexity_internalBlowupTower hΦ b s c hc
  -- The model identification and its boundary comparison depend on the tower.
  revert a ha hbound
  rw [internalBlowupTower_eq_alongBoundary]
  intro a ha hbound
  let Btor := Φ.boundaryIdeal ‹Nonempty Φ.cones›
  let J (j : Fin n) := (s j).internalCenter b (c j)
  have hJ (j : Fin n) : ∃ p : Btor.subscheme, IsClosed ({p} : Set Btor.subscheme) ∧
      (J j).val = (Btor.subscheme.fromSpecResidueField p).ker := by
    dsimp only [J]
    rw [Ray.internalCenter_val]
    exact (s j).exists_closedPoint_ker_binomialCenterOnBoundary rankTwo
      (b.detDualEquiv_self _) ((s j).surjective_detCharacter b) (c j)
  obtain ⟨hdis, hinternal, hex⟩ :=
    exceptional_configuration_alongBoundary_of_iso Btor.subschemeι J ℂ D a
      (by simpa only [algebraicRealization_over] using ha) hbound hJ hroot
  choose hE hclass using hex
  obtain ⟨Z, t, W, U, d, hU, hZ, hproj, hsm, hrat, hC, hNC, hover, hmod, hinj, hK, hq,
    hpole, hcenters, hboundary, he⟩ :=
    Chow.exists_ordered_anticanonical_contraction_of_nefCone_isometry ℂ hD hF
      hcanD hcanF hN _ hE hdis hinternal σ e hnef hσ
  refine ⟨Z, t, W, U, d, hU, hZ, hproj, hsm, hrat, hC, hNC, hover, hmod, hinj, hK, ?_,
    hpole, hcenters, hboundary, fun j ↦ ?_⟩
  · rw [hcomplex] at hq
    omega
  · simpa only [hclass j] using he j

end TauCeti.Toric.Fan
