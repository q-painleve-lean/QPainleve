/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Ample
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Matching
public import QPainleve.Geometry.Toric.Fan.Picard.Contraction.Transport

import QPainleve.AlgebraicGeometry.Chow.NegativeCurve
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.Topology.Algebra.Module.ModuleTopology

/-!
# Transporting an ordered toric contraction through nodal blowups

A numbered Picard isometry that matches a pair of ample classes transports a
specified nodal tower and then the ordered internal contraction of its source
auxiliary surface. The oriented subdivisions and the Picard comparison are
retained for reconstructing an isomorphism from the boundary periods.

This is the transport of the auxiliary model and its exceptional configuration
in [Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*,
proof of Theorem 1.8][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S2
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower
open QPainleve (BlowupTower canonicalBundle)
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData
open scoped TensorProduct

universe v w

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Φ.algebraicRealization.IsProjectiveOver ℂ]
  (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (b : Module.Basis (Fin 2) ℤ N)
  {r : ℕ} (s : Fin r → Φ.Ray) (c : Fin r → ℂˣ)

local notation "SpecC" => Spec (CommRingCat.of ℂ)
local notation "g(" X ")" => (X ↘ SpecC)
local notation "Pic(" X ")" => Additive (LineBundleClass X)
local notation "V(" X ")" => (ℝ ⊗[ℤ] Pic(X))
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
/-- Match a specified numbered nodal tower on root-free anticanonical surfaces
and transport its ordered toric exceptional configuration. The target
auxiliary surface contracts to a smooth projective rational surface with
anticanonical boundary of complexity zero. The contracted tower retains the
ordered exceptional classes, and the reduced total boundaries of the paired
nodal towers retain their oriented subdivisions. -/
theorem exists_transported_toric_contraction_of_numbered_nodal_tower
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
     ∀ j, e P(D, A.boundaryPrimeEquiv hD j) = P(F, C.boundaryPrimeEquiv hF j)) →
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
        β(G, F, U).IsOrientedCycleSubdivision C' C ∧
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
  obtain ⟨W, U, hU, hmatch⟩ := exists_matching_numbered_nodal_boundary_tower A C hD hF e hT he
  refine ⟨W, U, hU, ?_⟩
  intro E G _ _ _ _ _ _ _ nd nf hE hG _ _ _ _ _ _ _ _ _ _ _ _ e'
  obtain ⟨_, _, _, _, A', C', hA', hC', hclasses⟩ := hmatch
  refine ⟨_, _, _, _, A', C', hA', hC', hclasses, ?_⟩
  let : TopologicalSpace V(Y) := moduleTopology ℝ V(Y)
  let : TopologicalSpace V(W) := moduleTopology ℝ V(W)
  let : IsModuleTopology ℝ V(Y) := ⟨rfl⟩
  let : IsModuleTopology ℝ V(W) := ⟨rfl⟩
  let : IsTopologicalAddGroup V(Y) := IsModuleTopology.isTopologicalAddGroup ℝ V(Y)
  let : IsTopologicalAddGroup V(W) := IsModuleTopology.isTopologicalAddGroup ℝ V(W)
  let : T2Space V(Y) := TauCeti.ModuleTopology.t2Space (Module.Free.chooseBasis ℝ V(Y))
  let : T2Space V(W) := TauCeti.ModuleTopology.t2Space (Module.Free.chooseBasis ℝ V(W))
  -- The cone comparison is indexed by boundary primes instead of their cycle numbers.
  let σ := (A'.boundaryPrimeEquiv hE).symm.trans (C'.boundaryPrimeEquiv hG)
  have hσ (p : E.boundaryPrimes) : e' P(E, p) = P(G, σ p) := by
    simpa only [σ, Equiv.trans_apply, Equiv.apply_symm_apply] using
      hclasses ((A'.boundaryPrimeEquiv hE).symm p)
  have hnef := (image_nefCone_eq_and_isAmple_iff_picardIsometryCongr_of_nodal hT hU
    hD hF nd nf hcanD hcanF σ e hH hHe hrootD hrootF hσ).2.1
  have hcanE := (hT.canonicalClass_radical_comap_toBase_iff hD nd).mpr hcanD
  have hcanG := (hU.canonicalClass_radical_comap_toBase_iff hF nf).mpr hcanF
  have hNG : AtWorstNodalOfRelativeDimensionOne (G.subschemeι ≫ g(W)) :=
    (hU.radical_comap_toBase hF nf).2
  let : IsReduced E.subscheme := (hT.radical_comap_toBase hD nd).2.isReduced
  let : Scheme.IsRationalOver g(Y) := hT.isClosedPointTower.isRationalOver g(X)
  let : Scheme.IsRationalOver g(W) := hU.isClosedPointTower.isRationalOver g(Z)
  have hrootE := (hT.forall_realPrimeDivisorClass_self_ne_neg_two_iff ℂ hD nd hcanD).mpr hrootD
  have hnoRoot : ¬ ∃ (Q : Scheme) (j : Q ⟶ Y) (_ : IsClosedImmersion j) (_ : IsIntegral Q)
      (hj : j.ker.IsEffectiveCartier),
      topologicalKrullDim Q = 1 ∧ Disjoint (Set.range j) E.support ∧
      Chow.classIntersectionNumber ℂ Y (LineBundleClass.mk hj.toInvertibleSheaf)⁻¹
        (LineBundleClass.mk hj.toInvertibleSheaf)⁻¹ = -2 := by
    rw [← Chow.exists_realPrimeDivisorClass_self_eq_neg_two_iff ℂ hE hcanE]
    rintro ⟨p, hp, hp'⟩
    exact hrootE p (by simpa only [E, support_radical] using hp) hp'
  exact exists_transported_toric_contraction_of_nefCone_isometry hΦ hc b s c
    hE hG hcanE hcanG hNG a ha hbound hnoRoot σ e' hnef hσ

end TauCeti.Toric.Fan
