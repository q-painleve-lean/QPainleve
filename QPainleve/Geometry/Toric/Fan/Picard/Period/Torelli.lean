/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import QPainleve.AlgebraicGeometry.Chow.CurveCone
public import QPainleve.AlgebraicGeometry.Chow.Nef.Basic
public import QPainleve.AlgebraicGeometry.Curves.Node.CycleAction
public import QPainleve.AlgebraicGeometry.Curves.Node.NumberedPrime
public import QPainleve.AlgebraicGeometry.Curves.Node.Period.Restriction
public import QPainleve.Geometry.Toric.Fan.Presentation.Basic

import QPainleve.AlgebraicGeometry.Chow.Nef.EffectiveTransport
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Ample
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
import QPainleve.AlgebraicGeometry.Curves.Node.Period.Isometry
import QPainleve.AlgebraicGeometry.LineBundle.Ample
import QPainleve.Geometry.Toric.Fan.Picard.Contraction.Signed
import QPainleve.Geometry.Toric.Fan.Picard.Contraction.Source
import QPainleve.Geometry.Toric.Fan.Picard.Period.Contraction
import QPainleve.Geometry.Toric.Fan.Presentation.Recognition
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.LinearAlgebra.BilinearForm.Isometry.Basic

/-!
# Signed Torelli for root-free anticanonical pairs

Starting with a toric presentation of the source, a Picard isometry matching
the boundary classes and signed periods and taking an ample class to an ample
class lifts to a pair isomorphism. The proof transports an ordered exceptional
configuration to the second surface, recognizes its contracted pair as toric,
and preserves the specified action on ordered branches through the nodal towers.
This uses the root-free case of [Gross, Hacking and Keel, Theorem 1.8][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S2
-/

public section

open AlgebraicGeometry CategoryTheory DihedralGroup Multiplicative QPainleve
open QPainleve.BlowupTower TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme.IdealSheafData LineBundleClass

namespace AlgebraicGeometry.Scheme.IdealSheafData

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "g(" X ")" => (X ↘ S)
local notation "B(" X ")" => Chow.intersectionBilinForm ℂ X
local notation "K(" X ")" => LineBundleClass.mk (canonicalBundle ℂ X 2)
local notation "P(" D "," p ")" => Additive.ofMul (primeDivisorClass (boundaryPrimeEmbedding D p))
local notation "R(" D "," T ")" => radical (comap D (BlowupTower.toBase T))
variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N}

private theorem exists_toric_iso_of_contracted_boundary
    (b : Module.Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)
    {W Q : Scheme} [W.Over S] [Q.Over S] [Q.IsProjectiveOver ℂ]
    [SmoothOfRelativeDimension 2 g(Q)] [Scheme.IsRationalOver g(Q)]
    {E : W.IdealSheafData} {F : Q.IdealSheafData}
    [PrestableFamily g(E.subscheme)] {m : ℕ} [NeZero m] {ι : Type}
    {p : ι → g(E.subscheme).smoothLocus} (A : Scheme.NodalCycleNumbering p m)
    (f : W ⟶ Q) [f.IsOver S] (v : E.subscheme ≅ F.subscheme)
    (hv : v.hom ≫ F.subschemeι = E.subschemeι ≫ f)
    (hF : F.IsEffectiveCartier) (hcan : LineBundleClass.mk hF.toInvertibleSheaf = K(Q))
    (hzero : F.boundaryComplexity = 0) :
    ∃ (Ψ : Fan i) (_ : Ψ.IsRegular)
      (hc : Ψ.IsComplete) (e : Ψ.algebraicRealization ≅ Q),
      e.hom ≫ g(Q) = Ψ.algebraicRealizationStructureMap ∧
        F.comap e.hom = Ψ.boundaryIdeal hc.nonempty_cones := by
  have hover : v.hom ≫ g(F.subscheme) = g(E.subscheme) := by
    rw [F.over_eq_subschemeι_comp, ← Category.assoc, hv, Category.assoc, comp_over,
      E.over_eq_subschemeι_comp]
  let : v.hom.IsOver S := ⟨hover⟩
  let : PrestableFamily g(F.subscheme) :=
    (MorphismProperty.cancel_left_of_respectsIso (P := @PrestableFamily) v.hom _).mp
      (hover ▸ inferInstanceAs (PrestableFamily g(E.subscheme)))
  let q : PEmpty.{1} → g(F.subscheme).smoothLocus := PEmpty.elim
  exact F.exists_toric_iso_of_boundaryComplexity_zero (v.mapNodalCycleNumbering A (q := q))
    b hi hF hcan hzero

section RationalSurfaces

local instance smoothRationalSurface (X : Scheme) [X.Over S]
    [SmoothOfRelativeDimension 2 g(X)] : Smooth g(X) :=
  SmoothOfRelativeDimension.smooth 2 _

local instance integralRationalSurface (X : Scheme) [X.Over S]
    [SmoothOfRelativeDimension 2 g(X)] [h : Scheme.IsRationalOver g(X)] :
    IsIntegral X := h.isIntegral_of_smooth

local instance noetherianRationalSurface (X : Scheme) [X.Over S]
    [X.IsProjectiveOver ℂ] : IsNoetherian X :=
  isNoetherian_of_finiteType g(X)

local instance factorialRationalSurface (X : Scheme) [X.Over S]
    [SmoothOfRelativeDimension 2 g(X)] (x : X) :
    UniqueFactorizationMonoid (X.presheaf.stalk x) :=
  g(X).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two x

variable {X Y : Scheme} [X.Over S] [Y.Over S] [X.IsProjectiveOver ℂ] [Y.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 g(X)] [SmoothOfRelativeDimension 2 g(Y)]
  [Scheme.IsRationalOver g(X)] [Scheme.IsRationalOver g(Y)]
  (D : X.IdealSheafData) {E : Y.IdealSheafData}
  [PrestableFamily g(D.subscheme)] [PrestableFamily g(E.subscheme)]
  {n : ℕ} [NeZero n] {ι κ : Type}
  {p : ι → g(D.subscheme).smoothLocus} {q : κ → g(E.subscheme).smoothLocus}
  (A : Scheme.NodalCycleNumbering p n) (C : Scheme.NodalCycleNumbering q n)
  (hD : D.IsEffectiveCartier) (hE : E.IsEffectiveCartier)
  (act : DihedralGroup n) (G : B(Y).IsometryEquiv B(X))
  (hclass : ∀ j, G P(E,C.boundaryPrimeEquiv hE (cycleVertexPerm act j)) =
    P(D,A.boundaryPrimeEquiv hD j))

variable
  (hcanD : LineBundleClass.mk hD.toInvertibleSheaf = K(X))
  (hcanE : LineBundleClass.mk hE.toInvertibleSheaf = K(Y))
  (hrootD : ∀ r : CodimensionOnePoint X, (r : X) ∉ D.support →
    Chow.realIntersectionBilinForm ℂ X (Chow.realPrimeDivisorClass ℂ r)
      (Chow.realPrimeDivisorClass ℂ r) ≠ -2)
  (hrootE : ∀ r : CodimensionOnePoint Y, (r : Y) ∉ E.support →
    Chow.realIntersectionBilinForm ℂ Y (Chow.realPrimeDivisorClass ℂ r)
      (Chow.realPrimeDivisorClass ℂ r) ≠ -2)
  (gD : ∀ w : irreducibleComponents (D.subscheme.singularLocus ℂ).blowup,
    (D.subscheme.blowupComponent (K := ℂ) w).toScheme.genus ℂ = 0)
  (gE : ∀ w : irreducibleComponents (E.subscheme.singularLocus ℂ).blowup,
    (E.subscheme.blowupComponent (K := ℂ) w).toScheme.genus ℂ = 0)
  (hperiod : ∀ (x : E.boundaryOrthogonal ℂ) (y : D.boundaryOrthogonal ℂ), G x.val = y.val →
    hE.boundaryPeriod gE C.endpoint_eq (ofAdd x) =
      hD.boundaryPeriod gD A.endpoint_eq (ofAdd y) ^ (cycleOrientationSign act : ℤ))

include A C G act hD hE hcanD hcanE hrootD hrootE hclass gD gE hperiod in
/-- Signed Torelli for root-free anticanonical pairs with a toric presentation
of the source. A Picard isometry sending one ample class to an ample class,
matching the specified boundary components and intertwining the signed periods
is induced by a pair isomorphism with the given action on the ordered branches. -/
theorem exists_pair_iso_of_root_free_signed_boundary_period_of_toric_presentation
    (hpres : D.HasToricPresentation g(X) b i)
    {H : LineBundleClass Y} (hH : H.IsAmple) (hGH : (G (Additive.ofMul H)).toMul.IsAmple) :
    ∃ (a : X ≅ Y) (aB : D.subscheme ≅ E.subscheme) (haB : aB.hom.IsOver S),
      a.hom ≫ g(Y) = g(X) ∧ E.comap a.hom = D ∧
      aB.hom ≫ E.subschemeι = D.subschemeι ≫ a.hom ∧
      (∀ L : LineBundleClass Y, pullback a.hom L = (G (Additive.ofMul L)).toMul) ∧
      (letI := haB; aB.boundaryCycleAction (k := ℂ) A C = act) := by
  -- The inverse of the prescribed pullback transports the source contraction.
  obtain ⟨Φ, hΦ, hc, r, s, c, m, W, T, hT, a, ha, hB, hdistinct, hcenters, v, hv⟩ :=
    D.exists_toric_contraction_of_root_free_presentation hpres hD hcanD hrootD
  let : Nonempty Φ.cones := hc.nonempty_cones
  let : Φ.algebraicRealization.IsProjectiveOver ℂ :=
    Φ.isProjectiveOver_algebraicRealization_of_isComplete hΦ hc b
  have hfwd (j : ZMod n) : G.symm P(D,A.boundaryPrimeEquiv hD j) =
      P(E,C.boundaryPrimeEquiv hE (cycleVertexPerm act j)) :=
    (congrArg G.symm (hclass j).symm).trans (LinearMap.BilinForm.IsometryEquiv.symm_apply_apply G _)
  have hH' : (G.symm (Additive.ofMul (G (Additive.ofMul H)).toMul)).toMul.IsAmple := by
    simpa only [ofMul_toMul, LinearMap.BilinForm.IsometryEquiv.symm_apply_apply, toMul_ofMul]
      using hH
  obtain ⟨Z, U, hU, htransport⟩ :=
    Fan.exists_transported_toric_contraction_of_signed_boundary_isometry
      hΦ hc b s c A C act hT hD hE hcanD hcanE a ha (congrArg support hB)
      G.symm hGH hH' hrootD hrootE hfwd
  -- Keep the supplied structure maps on the two auxiliary surfaces and on the contraction.
  let : W.Over S := ⟨T.toBase ≫ g(X)⟩
  let : Z.Over S := ⟨U.toBase ≫ g(Y)⟩
  let : W.IsProjectiveOver ℂ := T.isProjectiveOver ℂ
  let : Z.IsProjectiveOver ℂ := U.isProjectiveOver ℂ
  let : IsIntegral W := hT.isClosedPointTower.isIntegral g(X)
  let : IsIntegral Z := hU.isClosedPointTower.isIntegral g(Y)
  let : SmoothOfRelativeDimension 2 g(W) := hT.isClosedPointTower.smoothOfRelativeDimension _
  let : SmoothOfRelativeDimension 2 g(Z) := hU.isClosedPointTower.smoothOfRelativeDimension _
  let : PrestableFamily g((R(D,T)).subscheme) := hT.prestableFamily_radical_comap_toBase hD
  let : PrestableFamily g((R(E,U)).subscheme) := hU.prestableFamily_radical_comap_toBase hE
  let : NeZero (n + m) := ⟨by have := NeZero.ne n; omega⟩
  obtain ⟨_, _, _, _, A', C', hsub, hsub', hclasses, hlift, Q, t, V, L, d, hL, -,
    hProj, hSmooth, hRat, hF, hN, hf, -, hdistinct', hcanF, hzero, -, hcenters', ⟨v', hv'⟩, hex⟩ :=
    htransport
  let : Q.Over S := ⟨t⟩
  let : Q.IsProjectiveOver ℂ := hProj
  let : SmoothOfRelativeDimension 2 g(Q) := hSmooth
  let : Scheme.IsRationalOver g(Q) := hRat
  let : LocallyOfFinitePresentation (((R(E,U)).map (d.hom ≫ L.toBase)).subschemeι ≫ t) :=
    hN.syntomic.locallyOfFinitePresentation
  obtain ⟨Ψ, hΨ, hcΨ, e, he, hE'⟩ :=
    exists_toric_iso_of_contracted_boundary b Φ.lattice C' (d.hom ≫ L.toBase) v' hv'
      hF hcanF hzero
  -- Reconstruct in the pullback direction and use the surviving component above zero.
  let : LinearMap.IsPerfPair B(X) := Chow.isPerfPair_intersectionBilinForm_of_isRationalOver ℂ X
  let F := picardIsometryCongr ℂ hT.isClosedPointTower hU.isClosedPointTower G.symm
  have horth (x : E.boundaryOrthogonal ℂ) : G x.val ∈ D.boundaryOrthogonal ℂ :=
    (C.isometry_mem_boundaryOrthogonal_iff A hE hD (cycleVertexPerm act).symm G
      (fun j ↦ by simpa only [Equiv.apply_symm_apply] using hclass ((cycleVertexPerm act).symm j))
      x.val).mpr x.property
  obtain ⟨j, hj, hj'⟩ := hlift 0
  refine Fan.exists_iso_of_signed_boundary_period_of_toric_contractions
    hΦ hc hΨ hcΨ b b A C A' C' hT hU rfl rfl hD hE ?_ ?_
    (Fan.isClosedPointTower_internalBlowupTower b s c) hL a d (Iso.refl _) e.symm
    ?_ ?_ (by simp) ?_ ⟨?_⟩ hf v v' hv hv' hdistinct hdistinct' hcenters hcenters'
    G F.symm ?_ ?_ ?_ act hsub hsub' gD gE horth (fun x ↦ hperiod x ⟨_, horth x⟩ rfl) j hj hj'
  · exact (hT.radical_comap_toBase hD ((D.over_eq_subschemeι_comp :
      g(D.subscheme) = D.subschemeι ≫ g(X)) ▸
      PrestableFamily.atWorstNodalOfRelativeDimensionOne)).1
  · exact (hU.radical_comap_toBase hE ((E.over_eq_subschemeι_comp :
      g(E.subscheme) = E.subschemeι ≫ g(Y)) ▸
      PrestableFamily.atWorstNodalOfRelativeDimensionOne)).1
  · simp [Fan.algebraicRealization_over]
  · rw [← he, Iso.symm_hom, Iso.inv_hom_id_assoc]
  · rw [← hE', Iso.symm_hom, ← comap_comp, Iso.inv_hom_id, comap_id]
  · rw [Category.assoc, Fan.algebraicRealization_over, ha]
    rfl
  · intro x
    have hx := picardIsometryCongr_pullback ℂ hT.isClosedPointTower hU.isClosedPointTower
      G.symm (G (Additive.ofMul x)).toMul
    rw [ofMul_toMul, LinearMap.BilinForm.IsometryEquiv.symm_apply_apply, toMul_ofMul] at hx
    exact (congrArg F.symm hx.symm).trans (LinearMap.BilinForm.IsometryEquiv.symm_apply_apply F _)
  · exact fun j ↦ (congrArg F.symm (hex j)).trans
      (LinearMap.BilinForm.IsometryEquiv.symm_apply_apply F _)
  · exact fun j ↦ (congrArg F.symm (hclasses j).symm).trans
      (LinearMap.BilinForm.IsometryEquiv.symm_apply_apply F _)

private theorem prime_self_intersection_ne_neg_two_of_disjoint
    {F : X.IdealSheafData}
    (hroot : ∀ r : CodimensionOnePoint X, (r : X) ∉ F.support →
      Chow.realIntersectionBilinForm ℂ X (Chow.realPrimeDivisorClass ℂ r)
        (Chow.realPrimeDivisorClass ℂ r) ≠ -2)
    (r : CodimensionOnePoint X) (hr : Disjoint (closure {(r : X)}) F.support) :
    Chow.classIntersectionNumber ℂ X (primeDivisorClass r) (primeDivisorClass r) ≠ -2 := by
  have hout : (r : X) ∉ F.support :=
    fun hs ↦ Set.disjoint_left.mp hr (subset_closure (Set.mem_singleton _)) hs
  intro h
  apply hroot r hout
  rw [Chow.realPrimeDivisorClass_def, Chow.realIntersectionBilinForm_tmul,
    one_mul, toMul_ofMul, h]
  norm_num

include A C G act hD hE hcanD hcanE hrootD hrootE hclass gD gE hperiod in
/-- For root-free pairs with nef anticanonical boundary of square zero, a toric
presentation of the source and compatibility of the boundary classes and signed
periods suffice to realize the prescribed Picard pullback and branch action. -/
theorem exists_pair_iso_of_root_free_signed_boundary_period_of_toric_presentation_of_nef
    (hpres : D.HasToricPresentation g(X) b i)
    (hnefD : (K(X))⁻¹.IsNef ℂ g(X)) (hnefE : (K(Y))⁻¹.IsNef ℂ g(Y))
    (hsq : Chow.classIntersectionNumber ℂ Y (K(Y))⁻¹ (K(Y))⁻¹ = 0) :
    ∃ (a : X ≅ Y) (aB : D.subscheme ≅ E.subscheme) (haB : aB.hom.IsOver S),
      a.hom ≫ g(Y) = g(X) ∧ E.comap a.hom = D ∧
      aB.hom ≫ E.subschemeι = D.subschemeι ≫ a.hom ∧
      (∀ L : LineBundleClass Y, pullback a.hom L = (G (Additive.ofMul L)).toMul) ∧
      (letI := haB; aB.boundaryCycleAction (k := ℂ) A C = act) := by
  let : IsReduced D.subscheme :=
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := g(D.subscheme))).isReduced
  let : IsReduced E.subscheme :=
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := g(E.subscheme))).isReduced
  let p := ((cycleVertexPerm act).trans (C.boundaryPrimeEquiv hE)).toEmbedding.trans
    E.boundaryPrimeEmbedding
  let q := (A.boundaryPrimeEquiv hD).toEmbedding.trans D.boundaryPrimeEmbedding
  have hp (r : CodimensionOnePoint Y) : (r : Y) ∈ E.support ↔ r ∈ Set.range p := by
    simp only [p, Function.Embedding.coe_trans, Equiv.coe_toEmbedding, EquivLike.range_comp,
      range_boundaryPrimeEmbedding, Set.mem_ofPred_eq]
  have hq (r : CodimensionOnePoint X) : (r : X) ∈ D.support ↔ r ∈ Set.range q := by
    simp only [q, Function.Embedding.coe_trans, Equiv.coe_toEmbedding, EquivLike.range_comp,
      range_boundaryPrimeEmbedding, Set.mem_ofPred_eq]
  have hEff := Chow.map_effectiveClasses_of_nef_anticanonical_isometry ℂ hE hD p q hp hq
    hcanE hcanD hnefE hnefD hsq G hclass
    (prime_self_intersection_ne_neg_two_of_disjoint hrootE)
    (prime_self_intersection_ne_neg_two_of_disjoint hrootD)
  obtain ⟨H, hH⟩ := Y.exists_isAmple_of_isProjectiveOver ℂ
  exact D.exists_pair_iso_of_root_free_signed_boundary_period_of_toric_presentation
    A C hD hE act G hclass hcanD hcanE hrootD hrootE gD gE hperiod hpres hH
    ((Chow.isAmple_iff_of_map_effectiveClasses ℂ H G hEff).mpr hH)

end RationalSurfaces

end AlgebraicGeometry.Scheme.IdealSheafData
