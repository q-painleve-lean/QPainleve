/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.Nef.InternalContraction.Anticanonical
public import QPainleve.Geometry.Toric.Fan.Picard.Complexity

import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.ExceptionalConfiguration
import QPainleve.Geometry.Toric.BaseChange.Fan

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

universe u

variable (k : Type u) [Field k] [IsAlgClosed k] {N : Type u} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] [(Φ.finiteFanScheme k).IsProjectiveOver k]
  (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (b : Module.Basis (Fin 2) ℤ N)
  {n : ℕ} (s : Fin n → Φ.Ray) (c : Fin n → kˣ)
  {X Y : Scheme}

local notation "S" => Spec (CommRingCat.of k)
local notation "Pic(" X ")" => Additive (LineBundleClass X)
local notation "V(" X ")" => (ℝ ⊗[ℤ] Pic(X))
local notation "K(" X ")" => LineBundleClass.mk (canonicalBundle k X 2)
local notation "B(" X ")" => Chow.intersectionBilinForm k X
local notation "primeClass(" D "," p ")" =>
  Additive.ofMul (primeDivisorClass (boundaryPrimeEmbedding D p))
local notation "M" => internalBlowupTower k b s c
local notation "T" => WithBoundary.toTower (Sigma.snd M)
local notation "ι" => WithBoundary.boundaryι (Sigma.snd M)
local notation "rankTwo" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)

variable [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X.IsProjectiveOver k] [Y.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))] [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]
  [hRatX : Scheme.IsRationalOver (X ↘ Spec (.of k))]
  [hRatY : Scheme.IsRationalOver (Y ↘ Spec (.of k))]
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
    (ha : a.hom ≫ (T).toBase ≫ (Φ.finiteFanSchemeToSpec k) = X ↘ S)
    (hbound : (D.comap a.inv).support = (ι).ker.support)
    (hroot : ¬ ∃ (C : Scheme) (g : C ⟶ X) (_ : IsClosedImmersion g) (_ : IsIntegral C)
      (hg : g.ker.IsEffectiveCartier),
      topologicalKrullDim C = 1 ∧ Disjoint (Set.range g) D.support ∧
      Chow.classIntersectionNumber k X (LineBundleClass.mk hg.toInvertibleSheaf)⁻¹
        (LineBundleClass.mk hg.toInvertibleSheaf)⁻¹ = -2)
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
      (e.baseChange ℝ) '' (Chow.nefCone k (X := X) : Set V(X)) = Chow.nefCone k (X := Y) →
      (∀ p, e primeClass(D,p) = primeClass(F,σ p)) →
      ∃ (Z : Scheme) (t : Z ⟶ S) (W : Scheme) (U : BlowupTower Z n W)
        (d : Y ≅ W) (hU : U.IsClosedPointTower Z),
        let : Z.Over S := ⟨t⟩
        let f := d.hom ≫ U.toBase
        let C := F.map f
        ∃ (_ : IsIntegral Z) (_ : Z.IsProjectiveOver k) (hsm : SmoothOfRelativeDimension 2 t),
          ∃ (_ : Scheme.IsRationalOver t) (hC : C.IsEffectiveCartier)
            (hNC : AtWorstNodalOfRelativeDimensionOne (C.subschemeι ≫ t)),
          let : SmoothOfRelativeDimension 2 (Z ↘ S) := hsm
          let : LocallyOfFinitePresentation (C.subschemeι ≫ t) :=
            hNC.syntomic.locallyOfFinitePresentation
          f.IsOver S ∧ IsModification f ∧ Function.Injective hU.baseCenter ∧
          LineBundleClass.mk hC.toInvertibleSheaf = K(Z) ∧ C.boundaryComplexity = 0 ∧
          C.comap f = F * (hU.ramificationIdealSheafToBase k).comap d.hom ∧
          (∀ j, ∃ q : C.subscheme, C.subschemeι q = hU.baseCenter j ∧
            q ∈ (C.subschemeι ≫ t).smoothLocus) ∧
          (∃ v : F.subscheme ≅ C.subscheme, v.hom ≫ C.subschemeι = F.subschemeι ≫ f) ∧
          ∀ j, Additive.ofMul (pullback d.hom (U.exceptionalClass j)) =
            e (Additive.ofMul (pullback a.hom ((T).exceptionalClass j))) := by
  intro _ _ _ _ _ _ _ _ _ _ e hnef hσ
  let : IsNoetherian (Φ.finiteFanScheme k) :=
    isNoetherian_of_finiteType ((Φ.finiteFanScheme k) ↘ S)
  let : SmoothOfRelativeDimension 2 ((Φ.finiteFanScheme k) ↘ S) := by
    rw [finiteFanScheme_over k]
    exact rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k hΦ
  have hcomplex : D.boundaryComplexity = n := calc
    _ = (D.comap a.inv).boundaryComplexity := (boundaryComplexity_comap_iso a.symm D).symm
    _ = (ι).ker.boundaryComplexity := boundaryComplexity_eq_of_support_eq hbound
    _ = _ := boundaryComplexity_internalBlowupTower k hΦ b s c hc
  -- The model identification and its boundary comparison depend on the tower.
  revert a ha hbound
  rw [internalBlowupTower_eq_alongBoundary]
  intro a ha hbound
  let Btor := Φ.toricBoundaryIdeal k ‹Nonempty Φ.cones›
  let J (j : Fin n) := (s j).internalCenter k b (c j)
  have hJ (j : Fin n) : ∃ p : Btor.subscheme, IsClosed ({p} : Set Btor.subscheme) ∧
      (J j).val = (Btor.subscheme.fromSpecResidueField p).ker := by
    dsimp only [J]
    rw [Ray.internalCenter_val]
    exact (s j).exists_closedPoint_ker_binomialCenterOnBoundary k rankTwo
      (b.detDualEquiv_self _) ((s j).surjective_detCharacter b) (c j)
  obtain ⟨hdis, hinternal, hex⟩ :=
    exceptional_configuration_alongBoundary_of_iso Btor.subschemeι J k D a
      (by simpa only [finiteFanScheme_over k] using ha) hbound hJ hroot
  choose hE hclass using hex
  obtain ⟨Z, t, W, U, d, hU, hZ, hproj, hsm, hrat, hC, hNC, hover, hmod, hinj, hK, hq,
    hpole, hcenters, hboundary, he⟩ :=
    Chow.exists_ordered_anticanonical_contraction_of_nefCone_isometry k hD hF
      hcanD hcanF hN _ hE hdis hinternal σ e hnef hσ
  refine ⟨Z, t, W, U, d, hU, hZ, hproj, hsm, hrat, hC, hNC, hover, hmod, hinj, hK, ?_,
    hpole, hcenters, hboundary, fun j ↦ ?_⟩
  · rw [hcomplex] at hq
    omega
  · simpa only [hclass j] using he j

end TauCeti.Toric.Fan
