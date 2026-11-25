/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Contraction.Nodal

import QPainleve.AlgebraicGeometry.Curves.Node.Reindex

/-!
# Transporting an ordered toric contraction with a signed boundary action

A rotation or reflection of the boundary labels determines how to match the nodes
of two nodal towers. After reindexing the target,
`exists_transported_toric_contraction_of_numbered_nodal_tower` transports the
ordered internal exceptional configuration. The target projection
preserves branch order relative to the original orientation for a rotation and
relative to the reversed orientation for a reflection.
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower
open QPainleve (BlowupTower canonicalBundle)
open DihedralGroup
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData

universe v w

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Φ.algebraicRealization.IsProjectiveOver ℂ]
  (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (b : Module.Basis (Fin 2) ℤ N)
  {r : ℕ} (s : Fin r → Φ.Ray) (c : Fin r → ℂˣ)

local notation "SpecC" => Spec (CommRingCat.of ℂ)
local notation "g(" X ")" => (X ↘ SpecC)
local notation "K(" X ")" => LineBundleClass.mk (canonicalBundle ℂ X 2)
local notation "B(" X ")" => Chow.intersectionBilinForm ℂ X
local notation "P(" D ", " p ")" => Additive.ofMul (primeDivisorClass (boundaryPrimeEmbedding D p))
local notation "R(" D ", " T ")" => radical (comap D (BlowupTower.toBase T))
local notation "β(" E ", " D ", " T ")" =>
  subschemeMap E D (BlowupTower.toBase T) (le_map_iff_comap_le.mpr (le_radical _))
local notation "M" => internalBlowupTower b s c
local notation "J" => WithBoundary.toTower (Sigma.snd M)
local notation "ιM" => WithBoundary.boundaryι (Sigma.snd M)

variable {X Z Y : Scheme} [X.Over SpecC] [Z.Over SpecC]
  [X.IsProjectiveOver ℂ] [Z.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 g(X)] [SmoothOfRelativeDimension 2 g(Z)]
  [hRatX : Scheme.IsRationalOver g(X)] [hRatZ : Scheme.IsRationalOver g(Z)]
  {D : X.IdealSheafData} {F : Z.IdealSheafData}
  [PrestableFamily g(D.subscheme)] [PrestableFamily g(F.subscheme)]
  {n : ℕ} [NeZero n] {ι : Type v} {κ : Type w}
  {p : ι → g(D.subscheme).smoothLocus} {q : κ → g(F.subscheme).smoothLocus}
  (A : Scheme.NodalCycleNumbering p n) (C : Scheme.NodalCycleNumbering q n)
  {m : ℕ} {T : BlowupTower X m Y}

include hΦ hc in
/-- A Picard isometry with a prescribed dihedral action on the boundary primes
transports a given nodal tower followed by its ordered internal contraction.
The new contraction has complexity zero and matches the ordered exceptional
classes. The sign determines the orientation of the target subdivision, even
when the boundary has only one or two components. The input isometry sends
source classes to target classes, so it is the inverse of the prescribed
Picard pullback in a reconstruction. -/
theorem exists_transported_toric_contraction_of_signed_boundary_isometry
    (act : DihedralGroup n)
    (hT : IsNodalBoundaryTower D g(X) (𝟙 X) T)
    (hD : D.IsEffectiveCartier) (hF : F.IsEffectiveCartier)
    (hcanD : LineBundleClass.mk hD.toInvertibleSheaf = K(X))
    (hcanF : LineBundleClass.mk hF.toInvertibleSheaf = K(Z)) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    ∀ (a : Y ≅ (M).1),
    a.hom ≫ (J).toBase ≫ Φ.algebraicRealizationStructureMap = T.toBase ≫ g(X) →
    (R(D, T).comap a.inv).support = (ιM).ker.support →
    let : Smooth g(X) := SmoothOfRelativeDimension.smooth 2 _
    let : Smooth g(Z) := SmoothOfRelativeDimension.smooth 2 _
    let : IsIntegral X := hRatX.isIntegral_of_smooth
    let : IsIntegral Z := hRatZ.isIntegral_of_smooth
    ∀ (e : B(X).IsometryEquiv B(Z)) {H : LineBundleClass X},
      H.IsAmple → (e (Additive.ofMul H)).toMul.IsAmple →
    (∀ p : CodimensionOnePoint X, (p : X) ∉ D.support →
      Chow.realIntersectionBilinForm ℂ X (Chow.realPrimeDivisorClass ℂ p)
        (Chow.realPrimeDivisorClass ℂ p) ≠ -2) →
    (∀ p : CodimensionOnePoint Z, (p : Z) ∉ F.support →
      Chow.realIntersectionBilinForm ℂ Z (Chow.realPrimeDivisorClass ℂ p)
        (Chow.realPrimeDivisorClass ℂ p) ≠ -2) →
    (let := LocallyOfFiniteType.isLocallyNoetherian g(X)
     let := LocallyOfFiniteType.isLocallyNoetherian g(Z)
     let := g(X).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
     let := g(Z).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
     ∀ j, e P(D, A.boundaryPrimeEquiv hD j) =
       P(F, C.boundaryPrimeEquiv hF (cycleVertexPerm act j))) →
    ∃ (W : Scheme) (U : BlowupTower Z m W)
      (hU : IsNodalBoundaryTower F g(Z) (𝟙 Z) U),
      let E := R(D, T)
      let G := R(F, U)
      let : Y.Over SpecC := ⟨T.toBase ≫ g(X)⟩
      let : W.Over SpecC := ⟨U.toBase ≫ g(Z)⟩
      let : PrestableFamily g(E.subscheme) := hT.prestableFamily_radical_comap_toBase hD
      let : PrestableFamily g(G.subscheme) := hU.prestableFamily_radical_comap_toBase hF
      let : NeZero (n + m) := ⟨by have := NeZero.ne n; omega⟩
      let : IsNoetherian X := isNoetherian_of_finiteType g(X)
      let : IsNoetherian Z := isNoetherian_of_finiteType g(Z)
      let nd := D.over_eq_subschemeι_comp (S := SpecC) ▸
        PrestableFamily.atWorstNodalOfRelativeDimensionOne
      let nf := F.over_eq_subschemeι_comp (S := SpecC) ▸
        PrestableFamily.atWorstNodalOfRelativeDimensionOne
      let hE := (hT.radical_comap_toBase hD nd).1
      let hG := (hU.radical_comap_toBase hF nf).1
      let : Y.IsProjectiveOver ℂ := T.isProjectiveOver ℂ
      let : W.IsProjectiveOver ℂ := U.isProjectiveOver ℂ
      let : IsIntegral Y := hT.isClosedPointTower.isIntegral g(X)
      let : IsIntegral W := hU.isClosedPointTower.isIntegral g(Z)
      let : SmoothOfRelativeDimension 2 g(Y) := hT.isClosedPointTower.smoothOfRelativeDimension _
      let : SmoothOfRelativeDimension 2 g(W) := hU.isClosedPointTower.smoothOfRelativeDimension _
      let : Smooth g(Y) := SmoothOfRelativeDimension.smooth 2 _
      let : Smooth g(W) := SmoothOfRelativeDimension.smooth 2 _
      let := LocallyOfFiniteType.isLocallyNoetherian g(Y)
      let := LocallyOfFiniteType.isLocallyNoetherian g(W)
      let := g(Y).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
      let := g(W).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
      let e' := picardIsometryCongr ℂ hT.isClosedPointTower hU.isClosedPointTower e
      ∃ (ι' : Type v) (κ' : Type w)
        (p' : ι' → g(E.subscheme).smoothLocus) (q' : κ' → g(G.subscheme).smoothLocus)
        (A' : Scheme.NodalCycleNumbering p' (n + m)) (C' : Scheme.NodalCycleNumbering q' (n + m)),
        β(E, D, T).IsOrientedCycleSubdivision A' A ∧
        β(G, F, U).IsOrientedCycleSubdivision C'
          (if cycleOrientationSign act = -1 then C.reverse else C) ∧
        (∀ j, e' P(E, A'.boundaryPrimeEquiv hE j) = P(G, C'.boundaryPrimeEquiv hG j)) ∧
        ∃ (Z₀ : Scheme) (t : Z₀ ⟶ SpecC) (W₀ : Scheme) (L : BlowupTower Z₀ r W₀)
          (d : W ≅ W₀) (hL : L.IsClosedPointTower Z₀),
          let : Z₀.Over SpecC := ⟨t⟩
          let f := d.hom ≫ L.toBase
          let G₀ := G.map f
          ∃ (_ : IsIntegral Z₀) (_ : Z₀.IsProjectiveOver ℂ) (hsm : SmoothOfRelativeDimension 2 t),
            ∃ (_ : Scheme.IsRationalOver t) (hG₀ : G₀.IsEffectiveCartier)
              (hN : AtWorstNodalOfRelativeDimensionOne (G₀.subschemeι ≫ t)),
            let : SmoothOfRelativeDimension 2 g(Z₀) := hsm
            let : LocallyOfFinitePresentation (G₀.subschemeι ≫ t) :=
              hN.syntomic.locallyOfFinitePresentation
            f.IsOver SpecC ∧ IsModification f ∧ Function.Injective hL.baseCenter ∧
            LineBundleClass.mk hG₀.toInvertibleSheaf = K(Z₀) ∧ G₀.boundaryComplexity = 0 ∧
            G₀.comap f = G * (hL.ramificationIdealSheafToBase ℂ).comap d.hom ∧
            (∀ j, ∃ x : G₀.subscheme, G₀.subschemeι x = hL.baseCenter j ∧
              x ∈ (G₀.subschemeι ≫ t).smoothLocus) ∧
            (∃ v : G.subscheme ≅ G₀.subscheme, v.hom ≫ G₀.subschemeι = G.subschemeι ≫ f) ∧
            ∀ j, Additive.ofMul (pullback d.hom (L.exceptionalClass j)) =
              e' (Additive.ofMul (pullback a.hom ((J).exceptionalClass j))) := by
  intro _ a ha hbound _ _ _ _ e H hH hHe hrootD hrootF he
  obtain ⟨W, U, hU, h⟩ := exists_transported_toric_contraction_of_numbered_nodal_tower
    hΦ hc b s c A (C.reindex act) hT hD hF hcanD hcanF a ha hbound e hH hHe hrootD hrootF
    (by simpa only [Scheme.NodalCycleNumbering.reindex_boundaryPrimeEquiv] using he)
  refine ⟨W, U, hU, ?_⟩
  intro E G _ _ _ _ _ _ _ nd nf hE hG _ _ _ _ _ _ _ _ _ _ _ _ e'
  obtain ⟨ι', κ', p', q', A', C', hA', hC', hclasses, hcontraction⟩ := h
  exact ⟨ι', κ', p', q', A', C', hA',
    (Scheme.Hom.isOrientedCycleSubdivision_reindex_target_iff act).mp hC', hclasses, hcontraction⟩

end TauCeti.Toric.Fan
