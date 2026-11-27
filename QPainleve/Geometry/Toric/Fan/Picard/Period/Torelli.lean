/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import QPainleve.AlgebraicGeometry.AffineSpace.Dimension
public import QPainleve.AlgebraicGeometry.Chow.CurveCone
public import QPainleve.AlgebraicGeometry.Chow.Nef.Basic
public import QPainleve.AlgebraicGeometry.Curves.Node.CycleAction
public import QPainleve.AlgebraicGeometry.Curves.Node.NumberedPrime
public import QPainleve.AlgebraicGeometry.Curves.Node.Period.PairIso
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

variable (k₀ : Type) [Field k₀] [IsAlgClosed k₀] [NeZero (2 : k₀)]

local notation "S" => Spec (CommRingCat.of k₀)
local notation "overBase[" coeff "," X "]" => (X ↘ Spec (CommRingCat.of coeff))
local notation "canonical[" coeff "," X "]" => LineBundleClass.mk (canonicalBundle coeff X 2)
local notation "P(" D "," p ")" => Additive.ofMul (primeDivisorClass (boundaryPrimeEmbedding D p))
local notation "R(" D "," T ")" => radical (comap D (BlowupTower.toBase T))
variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N}

private theorem exists_toric_iso_of_contracted_boundary
    (b : Module.Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)
    {W Q : Scheme} [W.Over S] [Q.Over S] [Q.IsProjectiveOver k₀]
    [SmoothOfRelativeDimension 2 overBase[k₀,Q]] [Scheme.IsRationalOver overBase[k₀,Q]]
    {E : W.IdealSheafData} {F : Q.IdealSheafData}
    [PrestableFamily overBase[k₀,E.subscheme]] {m : ℕ} [NeZero m] {ι : Type}
    {p : ι → overBase[k₀,E.subscheme].smoothLocus} (A : Scheme.NodalCycleNumbering p m)
    (f : W ⟶ Q) [f.IsOver S] (v : E.subscheme ≅ F.subscheme)
    (hv : v.hom ≫ F.subschemeι = E.subschemeι ≫ f)
    (hF : F.IsEffectiveCartier) (hcan : LineBundleClass.mk hF.toInvertibleSheaf = canonical[k₀,Q])
    (hzero : F.boundaryComplexity = 0) :
    ∃ (Ψ : Fan i) (_ : Ψ.IsRegular)
      (hc : Ψ.IsComplete) (e : (Ψ.finiteFanScheme k₀) ≅ Q),
      e.hom ≫ overBase[k₀,Q] = (Ψ.finiteFanSchemeToSpec k₀) ∧
        F.comap e.hom = Ψ.toricBoundaryIdeal k₀ hc.nonempty_cones := by
  have hover : v.hom ≫ overBase[k₀,F.subscheme] = overBase[k₀,E.subscheme] := by
    rw [F.over_eq_subschemeι_comp, ← Category.assoc, hv, Category.assoc, comp_over,
      E.over_eq_subschemeι_comp]
  let : v.hom.IsOver S := ⟨hover⟩
  let : PrestableFamily overBase[k₀,F.subscheme] :=
    (MorphismProperty.cancel_left_of_respectsIso (P := @PrestableFamily) v.hom _).mp
      (hover ▸ inferInstanceAs (PrestableFamily overBase[k₀,E.subscheme]))
  let q : PEmpty.{1} → overBase[k₀,F.subscheme].smoothLocus := PEmpty.elim
  exact F.exists_toric_iso_of_boundaryComplexity_zero k₀ (v.mapNodalCycleNumbering A (q := q))
    b hi hF hcan hzero

section RationalSurfaces

local instance smoothRationalSurface (X : Scheme) [X.Over S]
    [SmoothOfRelativeDimension 2 overBase[k₀,X]] : Smooth overBase[k₀,X] :=
  SmoothOfRelativeDimension.smooth 2 _

local macro "withRationalSurface[" k:term "," X:term "," body:term "]" : term =>
  `(let f := $X ↘ Spec (CommRingCat.of $k)
    letI : Smooth f := SmoothOfRelativeDimension.smooth 2 f
    letI : IsIntegral $X := (inferInstance : Scheme.IsRationalOver f).isIntegral_of_smooth
    letI : IsNoetherian $X := isNoetherian_of_finiteType f
    letI : ∀ x : $X, UniqueFactorizationMonoid (($X).presheaf.stalk x) :=
      f.uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    $body)

variable {X Y : Scheme} [X.Over (Spec (.of k₀))] [Y.Over (Spec (.of k₀))] [X.IsProjectiveOver k₀]
  [Y.IsProjectiveOver k₀]
  [SmoothOfRelativeDimension 2 overBase[k₀,X]] [SmoothOfRelativeDimension 2 overBase[k₀,Y]]
  [Scheme.IsRationalOver overBase[k₀,X]] [Scheme.IsRationalOver overBase[k₀,Y]]
  (D : X.IdealSheafData) {E : Y.IdealSheafData}
  [PrestableFamily overBase[k₀,D.subscheme]] [PrestableFamily overBase[k₀,E.subscheme]]
  {n : ℕ} [NeZero n] {ι κ : Type}
  {p : ι → overBase[k₀,D.subscheme].smoothLocus} {q : κ → overBase[k₀,E.subscheme].smoothLocus}
  (A : Scheme.NodalCycleNumbering p n) (C : Scheme.NodalCycleNumbering q n)
  (hD : D.IsEffectiveCartier) (hE : E.IsEffectiveCartier)
  (act : DihedralGroup n)

include A C act hD hE in
/-- Signed Torelli for root-free anticanonical pairs with a toric presentation
of the source. A Picard isometry sending one ample class to an ample class,
matching the specified boundary components and intertwining the signed periods
is induced by a pair isomorphism with the given action on the ordered branches. -/
theorem exists_pair_iso_of_root_free_signed_boundary_period_of_toric_presentation
  (G : withRationalSurface[k₀,X,withRationalSurface[k₀,Y,LinearMap.BilinForm.IsometryEquiv
      (Chow.intersectionBilinForm k₀ Y) (Chow.intersectionBilinForm k₀ X)]])
  (hclass : withRationalSurface[k₀,X,withRationalSurface[k₀,Y,∀ j,
    G P(E,C.boundaryPrimeEquiv hE (cycleVertexPerm act j)) = P(D,A.boundaryPrimeEquiv hD j)]])
  (hcanD : LineBundleClass.mk hD.toInvertibleSheaf = canonical[k₀,X])
  (hcanE : LineBundleClass.mk hE.toInvertibleSheaf = canonical[k₀,Y])
  (hrootD : withRationalSurface[k₀,X,∀ r : CodimensionOnePoint X, (r : X) ∉ D.support →
    Chow.realIntersectionBilinForm k₀ X (Chow.realPrimeDivisorClass k₀ r)
      (Chow.realPrimeDivisorClass k₀ r) ≠ -2])
  (hrootE : withRationalSurface[k₀,Y,∀ r : CodimensionOnePoint Y, (r : Y) ∉ E.support →
    Chow.realIntersectionBilinForm k₀ Y (Chow.realPrimeDivisorClass k₀ r)
      (Chow.realPrimeDivisorClass k₀ r) ≠ -2])
  (gD : ∀ w : irreducibleComponents (D.subscheme.singularLocus k₀).blowup,
    (D.subscheme.blowupComponent (K := k₀) w).toScheme.genus k₀ = 0)
  (gE : ∀ w : irreducibleComponents (E.subscheme.singularLocus k₀).blowup,
    (E.subscheme.blowupComponent (K := k₀) w).toScheme.genus k₀ = 0)
  (hperiod : withRationalSurface[k₀,X,withRationalSurface[k₀,Y,∀ (x : E.boundaryOrthogonal k₀)
    (y : D.boundaryOrthogonal k₀), G x.val = y.val →
    hE.boundaryPeriod gE C.endpoint_eq (ofAdd x) =
      hD.boundaryPeriod gD A.endpoint_eq (ofAdd y) ^ (cycleOrientationSign act : ℤ)]])
    (hpres : D.HasToricPresentation overBase[k₀,X] b i)
    {H : LineBundleClass Y} (hH : H.IsAmple) (hGH : (G (Additive.ofMul H)).toMul.IsAmple) :
    Nonempty (SignedTorelliPairIso (D := D) (E := E) A C
      (fun L ↦ (G (Additive.ofMul L)).toMul) act) :=
  withRationalSurface[k₀,X,withRationalSurface[k₀,Y,by
  -- The inverse of the prescribed pullback transports the source contraction.
  obtain ⟨Φ, hΦ, hc, r, s, c, m, W, T, hT, a, ha, hB, hdistinct, hcenters, v, hv⟩ :=
    D.exists_toric_contraction_of_root_free_presentation hpres hD hcanD hrootD
  let : Nonempty Φ.cones := hc.nonempty_cones
  let : (Φ.finiteFanScheme k₀).IsProjectiveOver k₀ :=
    Φ.isProjectiveOver_finiteFanScheme_of_isComplete k₀ hΦ hc b
  have hfwd (j : ZMod n) : G.symm P(D,A.boundaryPrimeEquiv hD j) =
      P(E,C.boundaryPrimeEquiv hE (cycleVertexPerm act j)) :=
    (congrArg G.symm (hclass j).symm).trans (LinearMap.BilinForm.IsometryEquiv.symm_apply_apply G _)
  have hH' : (G.symm (Additive.ofMul (G (Additive.ofMul H)).toMul)).toMul.IsAmple := by
    simpa only [ofMul_toMul, LinearMap.BilinForm.IsometryEquiv.symm_apply_apply, toMul_ofMul]
      using hH
  obtain ⟨Z, U, hU, htransport⟩ :=
    Fan.exists_transported_toric_contraction_of_signed_boundary_isometry
      k₀ hΦ hc b s c A C act hT hD hE hcanD hcanE a ha (congrArg support hB)
      G.symm hGH hH' hrootD hrootE hfwd
  -- Keep the supplied structure maps on the two auxiliary surfaces and on the contraction.
  let : W.Over S := ⟨T.toBase ≫ overBase[k₀,X]⟩
  let : Z.Over S := ⟨U.toBase ≫ overBase[k₀,Y]⟩
  let : W.IsProjectiveOver k₀ := T.isProjectiveOver k₀
  let : Z.IsProjectiveOver k₀ := U.isProjectiveOver k₀
  let : IsIntegral W := hT.isClosedPointTower.isIntegral overBase[k₀,X]
  let : IsIntegral Z := hU.isClosedPointTower.isIntegral overBase[k₀,Y]
  let : SmoothOfRelativeDimension 2 overBase[k₀,W] :=
    hT.isClosedPointTower.smoothOfRelativeDimension _
  let : SmoothOfRelativeDimension 2 overBase[k₀,Z] :=
    hU.isClosedPointTower.smoothOfRelativeDimension _
  let : PrestableFamily overBase[k₀,(R(D,T)).subscheme] := hT.prestableFamily_radical_comap_toBase
    hD
  let : PrestableFamily overBase[k₀,(R(E,U)).subscheme] := hU.prestableFamily_radical_comap_toBase
    hE
  let : NeZero (n + m) := ⟨Nat.ne_of_gt (Nat.add_pos_left (Nat.pos_of_ne_zero (NeZero.ne n)) m)⟩
  obtain ⟨_, _, _, _, A', C', hsub, hsub', hclasses, hlift, Q, t, V, L, d, hL, -,
    hProj, hSmooth, hRat, hF, hN, hf, -, hdistinct', hcanF, hzero, -, hcenters', ⟨v', hv'⟩, hex⟩ :=
    htransport
  let : Q.Over S := ⟨t⟩
  let : Q.IsProjectiveOver k₀ := hProj
  let : SmoothOfRelativeDimension 2 overBase[k₀,Q] := hSmooth
  let : Scheme.IsRationalOver overBase[k₀,Q] := hRat
  let : LocallyOfFinitePresentation (((R(E,U)).map (d.hom ≫ L.toBase)).subschemeι ≫ t) :=
    hN.syntomic.locallyOfFinitePresentation
  obtain ⟨Ψ, hΨ, hcΨ, e, he, hE'⟩ :=
    exists_toric_iso_of_contracted_boundary k₀ b Φ.lattice C' (d.hom ≫ L.toBase) v' hv'
      hF hcanF hzero
  -- Reconstruct in the pullback direction and use the surviving component above zero.
  let : LinearMap.IsPerfPair (Chow.intersectionBilinForm k₀ X) :=
    Chow.isPerfPair_intersectionBilinForm_of_isRationalOver
    k₀ X
  let F := picardIsometryCongr k₀ hT.isClosedPointTower hU.isClosedPointTower G.symm
  have horth (x : E.boundaryOrthogonal k₀) : G x.val ∈ D.boundaryOrthogonal k₀ :=
    (C.isometry_mem_boundaryOrthogonal_iff A hE hD (cycleVertexPerm act).symm G
      (fun j ↦ by simpa only [Equiv.apply_symm_apply] using hclass ((cycleVertexPerm act).symm j))
      x.val).mpr x.property
  obtain ⟨j, hj, hj'⟩ := hlift 0
  refine Fan.exists_iso_of_signed_boundary_period_of_toric_contractions
    k₀ hΦ hc hΨ hcΨ b b A C A' C' hT hU rfl rfl hD hE ?_ ?_
    (Fan.isClosedPointTower_internalBlowupTower k₀ b s c) hL a d (Iso.refl _) e.symm
    ?_ ?_ (by simp) ?_ ⟨?_⟩ hf v v' hv hv' hdistinct hdistinct' hcenters hcenters'
    G F.symm ?_ ?_ ?_ act hsub hsub' gD gE horth (fun x ↦ hperiod x ⟨_, horth x⟩ rfl) j hj hj'
  · exact (hT.radical_comap_toBase hD ((D.over_eq_subschemeι_comp :
      overBase[k₀,D.subscheme] = D.subschemeι ≫ overBase[k₀,X]) ▸
      PrestableFamily.atWorstNodalOfRelativeDimensionOne)).1
  · exact (hU.radical_comap_toBase hE ((E.over_eq_subschemeι_comp :
      overBase[k₀,E.subscheme] = E.subschemeι ≫ overBase[k₀,Y]) ▸
      PrestableFamily.atWorstNodalOfRelativeDimensionOne)).1
  · simp [Fan.finiteFanScheme_over k₀]
  · rw [← he, Iso.symm_hom, Iso.inv_hom_id_assoc]
  · rw [← hE', Iso.symm_hom, ← comap_comp, Iso.inv_hom_id, comap_id]
  · rw [Category.assoc, Fan.finiteFanScheme_over k₀, ha]
    rfl
  · intro x
    have hx := picardIsometryCongr_pullback k₀ hT.isClosedPointTower hU.isClosedPointTower
      G.symm (G (Additive.ofMul x)).toMul
    rw [ofMul_toMul, LinearMap.BilinForm.IsometryEquiv.symm_apply_apply, toMul_ofMul] at hx
    exact (congrArg F.symm hx.symm).trans (LinearMap.BilinForm.IsometryEquiv.symm_apply_apply F _)
  · exact fun j ↦ (congrArg F.symm (hex j)).trans
      (LinearMap.BilinForm.IsometryEquiv.symm_apply_apply F _)
  · exact fun j ↦ (congrArg F.symm (hclasses j).symm).trans
      (LinearMap.BilinForm.IsometryEquiv.symm_apply_apply F _)]]

omit [NeZero (2 : k₀)] in
private theorem prime_self_intersection_ne_neg_two_of_disjoint
    {F : X.IdealSheafData}
    (hroot : withRationalSurface[k₀,X,∀ r : CodimensionOnePoint X, (r : X) ∉ F.support →
      Chow.realIntersectionBilinForm k₀ X (Chow.realPrimeDivisorClass k₀ r)
        (Chow.realPrimeDivisorClass k₀ r) ≠ -2])
    (r : CodimensionOnePoint X) (hr : Disjoint (closure {(r : X)}) F.support) :
    withRationalSurface[k₀,X,Chow.classIntersectionNumber k₀ X
      (primeDivisorClass r) (primeDivisorClass r) ≠ -2] := withRationalSurface[k₀,X,by
  have hout : (r : X) ∉ F.support :=
    fun hs ↦ Set.disjoint_left.mp hr (subset_closure (Set.mem_singleton _)) hs
  change Chow.classIntersectionNumber k₀ X (primeDivisorClass r) (primeDivisorClass r) ≠ -2
  intro h
  apply hroot r hout
  rw [Chow.realPrimeDivisorClass_def, Chow.realIntersectionBilinForm_tmul,
    one_mul, toMul_ofMul, h]
  norm_num]

include A C act hD hE in
/-- For root-free pairs with nef anticanonical boundary of square zero, a toric
presentation of the source and compatibility of the boundary classes and signed
periods suffice to realize the prescribed Picard pullback and branch action. -/
theorem exists_pair_iso_of_root_free_signed_boundary_period_of_toric_presentation_of_nef
  (G : withRationalSurface[k₀,X,withRationalSurface[k₀,Y,LinearMap.BilinForm.IsometryEquiv
      (Chow.intersectionBilinForm k₀ Y) (Chow.intersectionBilinForm k₀ X)]])
  (hclass : withRationalSurface[k₀,X,withRationalSurface[k₀,Y,∀ j,
    G P(E,C.boundaryPrimeEquiv hE (cycleVertexPerm act j)) = P(D,A.boundaryPrimeEquiv hD j)]])
  (hcanD : LineBundleClass.mk hD.toInvertibleSheaf = canonical[k₀,X])
  (hcanE : LineBundleClass.mk hE.toInvertibleSheaf = canonical[k₀,Y])
  (hrootD : withRationalSurface[k₀,X,∀ r : CodimensionOnePoint X, (r : X) ∉ D.support →
    Chow.realIntersectionBilinForm k₀ X (Chow.realPrimeDivisorClass k₀ r)
      (Chow.realPrimeDivisorClass k₀ r) ≠ -2])
  (hrootE : withRationalSurface[k₀,Y,∀ r : CodimensionOnePoint Y, (r : Y) ∉ E.support →
    Chow.realIntersectionBilinForm k₀ Y (Chow.realPrimeDivisorClass k₀ r)
      (Chow.realPrimeDivisorClass k₀ r) ≠ -2])
  (gD : ∀ w : irreducibleComponents (D.subscheme.singularLocus k₀).blowup,
    (D.subscheme.blowupComponent (K := k₀) w).toScheme.genus k₀ = 0)
  (gE : ∀ w : irreducibleComponents (E.subscheme.singularLocus k₀).blowup,
    (E.subscheme.blowupComponent (K := k₀) w).toScheme.genus k₀ = 0)
  (hperiod : withRationalSurface[k₀,X,withRationalSurface[k₀,Y,∀ (x : E.boundaryOrthogonal k₀)
    (y : D.boundaryOrthogonal k₀), G x.val = y.val →
    hE.boundaryPeriod gE C.endpoint_eq (ofAdd x) =
      hD.boundaryPeriod gD A.endpoint_eq (ofAdd y) ^ (cycleOrientationSign act : ℤ)]])
    (hpres : D.HasToricPresentation overBase[k₀,X] b i)
    (hnefD : (canonical[k₀,X])⁻¹.IsNef k₀ overBase[k₀,X]) (hnefE :
      (canonical[k₀,Y])⁻¹.IsNef k₀ overBase[k₀,Y])
    (hsq : Chow.classIntersectionNumber k₀ Y (canonical[k₀,Y])⁻¹ (canonical[k₀,Y])⁻¹ = 0) :
    Nonempty (SignedTorelliPairIso (D := D) (E := E) A C
      (fun L ↦ (G (Additive.ofMul L)).toMul) act) :=
  withRationalSurface[k₀,X,withRationalSurface[k₀,Y,by
  let : IsReduced D.subscheme :=
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := overBase[k₀,D.subscheme])).isReduced
  let : IsReduced E.subscheme :=
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := overBase[k₀,E.subscheme])).isReduced
  let p := ((cycleVertexPerm act).trans (C.boundaryPrimeEquiv hE)).toEmbedding.trans
    E.boundaryPrimeEmbedding
  let q := (A.boundaryPrimeEquiv hD).toEmbedding.trans D.boundaryPrimeEmbedding
  have hp (r : CodimensionOnePoint Y) : (r : Y) ∈ E.support ↔ r ∈ Set.range p := by
    simp only [p, Function.Embedding.coe_trans, Equiv.coe_toEmbedding, EquivLike.range_comp,
      range_boundaryPrimeEmbedding, Set.mem_ofPred_eq]
  have hq (r : CodimensionOnePoint X) : (r : X) ∈ D.support ↔ r ∈ Set.range q := by
    simp only [q, Function.Embedding.coe_trans, Equiv.coe_toEmbedding, EquivLike.range_comp,
      range_boundaryPrimeEmbedding, Set.mem_ofPred_eq]
  have hEff := Chow.map_effectiveClasses_of_nef_anticanonical_isometry k₀ hE hD p q hp hq
    hcanE hcanD hnefE hnefD hsq G hclass
    (prime_self_intersection_ne_neg_two_of_disjoint k₀ hrootE)
    (prime_self_intersection_ne_neg_two_of_disjoint k₀ hrootD)
  obtain ⟨H, hH⟩ := Y.exists_isAmple_of_isProjectiveOver k₀
  exact D.exists_pair_iso_of_root_free_signed_boundary_period_of_toric_presentation
    k₀ A C hD hE act G hclass hcanD hcanE hrootD hrootE gD gE hperiod hpres hH
    ((Chow.isAmple_iff_of_map_effectiveClasses k₀ H G hEff).mpr hH)]]

end RationalSurfaces

end AlgebraicGeometry.Scheme.IdealSheafData
