/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Qsf
public import QPainleve.Geometry.Toric.Fan.Picard.Contraction.Numbered
public import QPainleve.SignedClusterModularGroup.Realization.Presentation.Reference

import QPainleve.Algebra.Cluster.Word.Reindex
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
import QPainleve.AlgebraicGeometry.IdealSheaf.BaseChange
import QPainleve.Geometry.Toric.Fan.Boundary.Numbering
import QPainleve.SignedClusterModularGroup.Realization.Presentation.Group
import QPainleve.SignedClusterModularGroup.Realization.Surface.Numerics
import QPainleve.SignedClusterModularGroup.Realization.Surface.PrimeClass

/-!
# Signed loop substitutions in numbered Picard coordinates

A marked toric reference fiber gives a comparison between signed loop substitutions,
indexed by any equivalent type of center labels, and signed isometries of its numbered
Picard lattice. The target-pair tests may be performed on lifts of the classes in a
surjective bilinear presentation of an ambient lattice. In a toric contraction this
allows testing in the original divisor coefficients before quotienting by linear
equivalence.

The group comparison uses `CompleteToricPresentation.exists_picardGroupEquivs_of_nodal_model`
and `Cluster.signedLoopPullbacksQsfMulEquiv`.
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve.Cluster QPainleve.BlowupTower
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open QPainleve.CharacterTorus Scheme.IdealSheafData LineBundleClass LinearMap

local macro "withFactorialSurface[" k:term "," X:term "," body:term "]" : term =>
  `(let f := $X ↘ Spec (CommRingCat.of $k)
    letI : IsNoetherian $X := isNoetherian_of_finiteType f
    letI : ∀ x : $X, UniqueFactorizationMonoid (($X).presheaf.stalk x) :=
      f.uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    $body)

namespace QPainleve.SignedClusterModularGroup.MarkedReferenceFiber

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]

local notation "S" => Spec (CommRingCat.of k₀)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {X : Scheme} [X.Over (Spec (.of k₀))] [IsIntegral X] [X.IsProjectiveOver k₀]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k₀))] {D : X.IdealSheafData}
  [PrestableFamily (D.subscheme ↘ Spec (.of k₀))] {L : Type} [AddCommGroup L]
    {B : LinearMap.BilinForm ℤ L}
  {A : Scheme.NodalCycleNumbering (X := D.subscheme)
    (Empty.elim : Empty → (D.subscheme ↘ Spec (.of k₀)).smoothLocus) n}
  {μ : B.IsometryEquiv (Chow.intersectionBilinForm k₀ X)}
  (R : MarkedReferenceFiber k₀ i b r A μ) (hD : D.IsEffectiveCartier)

local macro "d" : term =>
  `(withFactorialSurface[k₀,X,fun j ↦ μ.symm (Additive.ofMul (primeDivisorClass
    (D.boundaryPrimeEmbedding (Scheme.NodalCycleNumbering.boundaryPrimeEquiv A hD j))))])

/-- For a marked reference fiber, the signed loop substitution monoid is the signed
isometry group of the numbered boundary classes. The seed labels can be any type
identified with the ordered centers. The numerical tests take place on representatives
of the boundary classes in an ambient bilinear presentation. -/
theorem nonempty_signedLoopSubstitutions_mulEquiv_of_isometry
    [B.IsPerfPair] [Uncountable k₀] [CharZero k₀]
    {ι : Type*} [DecidableEq ι] (o : Fin r ≃ ι) (E : SkewExchangeMatrix ι)
    (hE : E.reindex o.symm = R.exchangeMatrix)
    {U W : Type*} [AddCommGroup U] [AddCommGroup W] {F : LinearMap.BilinForm ℤ U}
    {C : LinearMap.BilinForm ℤ W} (e : B →bᵢ C) (q : F →bᵢ C) (hq : Function.Surjective q)
    (a : ZMod n → U) (ha : ∀ j, q (a j) = e (d j))
    (hprim : ∃ x, F (∑ j, a j) x = 1) (hnef : ∀ j, 0 ≤ F (∑ i, a i) (a j))
    (hsq : F (∑ j, a j) (∑ j, a j) = 0) :
    Nonempty (signedLoopSubstitutions E ≃* signedBoundaryIsometryGroup B d) := by
  let M := R.markedSurface
  let hM := M.isEffectiveCartier_boundaryIdeal
  have hclass : M.boundaryClass hM = d :=
    funext (MarkedSurface.boundaryClass_ofBoundary D A μ R.evaluation hD)
  obtain ⟨hp, hn, hs⟩ := (M.primitive_nef_square_zero_iff_of_isometry hM e q hq a
    (fun j ↦ (ha j).trans (congrArg e (congrFun hclass j).symm))).mpr ⟨hprim, hnef, hsq⟩
  obtain ⟨P, _⟩ := R.presentation.exists_picardGroupEquivs_of_nodal_model
    R.hasNodalModel (Fan.rayExchangeMatrix_matrix b R.presentation.rays) hp hn hs
  let f := (signedLoopPullbacksQsfMulEquiv k₀ E).symm.trans
    ((signedLoopPullbacksReindex k₀ E o.symm).trans (by rw [hE]))
  rw [← hclass]
  exact ⟨f.trans ((MulEquiv.opOp _).trans P.signedEquiv)⟩

end QPainleve.SignedClusterModularGroup.MarkedReferenceFiber

namespace QPainleve.SignedClusterModularGroup

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]

local notation "S" => Spec (CommRingCat.of k₀)

section OrderedTowers

variable {N V ι : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  [Fintype ι] [DecidableEq ι] {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N}
  {X W : Scheme} [X.Over (Spec (.of k₀))] [IsIntegral X] [X.IsProjectiveOver k₀]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k₀))] [Scheme.IsRationalOver (X ↘ Spec (.of k₀))]
  {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ Spec (.of k₀))]
  {n d r : ℕ} [NeZero n] [NeZero (n + d)] {T : BlowupTower X d W}
  {Φ : Fan i} [h₀ : Nonempty Φ.cones]
  [PrestableFamily ((Φ.toricBoundaryIdeal k₀ h₀).subscheme ↘ Spec (.of k₀))]
  (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (A : Scheme.NodalCycleNumbering
    (Empty.elim : Empty → (D.subscheme ↘ Spec (.of k₀)).smoothLocus) n)
  (C : Scheme.NodalCycleNumbering
    (Empty.elim : Empty → ((Φ.toricBoundaryIdeal k₀ h₀).subscheme ↘ Spec (.of k₀)).smoothLocus)
      (n + d))
  (hD : D.IsEffectiveCartier) (o : Fin r ≃ ι) (ρ : ι → ZMod (n + d)) (u : Fin r → k₀ˣ)

local notation "v" => Φ.rayEquivOfNodalCycleNumbering k₀ hΦ C
local notation "s" => (v ∘ ρ ∘ o)
local notation "U" => Fan.internalBlowupTower k₀ b s u
local notation "V₀" => (ZMod (n + d) ⊕ ι → ℤ)
local notation "strict" j:arg => Fan.numberedStrictBoundaryCoefficients ρ j

omit [Scheme.IsRationalOver (X ↘ S)] in
private theorem eq_rayExchangeMatrix_of_reference_rays
    {L : Type} [AddCommGroup L] {H : LinearMap.BilinForm ℤ L}
    {μ : H.IsometryEquiv (Chow.intersectionBilinForm k₀ X)}
    (P : MarkedReferenceFiber k₀ i b r A μ) (t : Fin r → Φ.Ray)
    (hfan : P.presentation.fan = Φ) (hrays : hfan ▸ P.presentation.rays = t) :
    P.exchangeMatrix = Fan.rayExchangeMatrix b t := by
  cases hfan
  obtain rfl : P.presentation.rays = t := hrays
  rfl

omit [Fintype ι] [DecidableEq ι] [NeZero n] [NeZero (n + d)] in
private theorem map_updated_boundary_coefficients {R : Submodule ℤ V₀}
    (B : LinearMap.BilinForm ℤ (V₀ ⧸ R)) (l : List (ZMod (n + d))) :
    let F : LinearMap.BilinForm ℤ V₀ := B.compl₁₂ R.mkQ R.mkQ
    let a := l.map (Fan.numberedStrictBoundaryCoefficients ρ)
    let a' := l.map fun j ↦ R.mkQ (strict j)
    (∀ x ∈ F.orthogonalizeNegOnes a, F x x = -1) →
      (∀ x ∈ B.orthogonalizeNegOnes a', B x x = -1) ∧
      ∀ j, R.mkQ (F.projectOffNegOnes a (strict j)) =
        B.projectOffNegOnes a' (R.mkQ (strict j)) := by
  intro F a a' hs
  have hmap : a.map R.mkQ = a' := List.map_map ..
  have hpair (x y : V₀) : B (R.mkQ x) (R.mkQ y) = F x y :=
    (LinearMap.compl₁₂_apply ..).symm
  constructor
  · rw [← hmap, ← F.map_orthogonalizeNegOnes R.mkQ hpair]
    simpa only [List.forall_mem_map, hpair] using hs
  · intro j
    rw [← hmap]
    exact F.map_projectOffNegOnes R.mkQ hpair a (strict j)

include hc in
open Classical in
/-- Compare signed substitutions with the contracted numbered Picard lattice of a
specified toric presentation. The list of removed rays and the surviving ray
numbering must agree with the given oriented nodal contraction. Both the successive
square-minus-one tests and the three target-pair tests use the original divisor
coefficients. The returned boundary classes are the projected strict classes in
the specified numbering. -/
theorem exists_signedLoopSubstitutions_mulEquiv_of_numbered_contraction
    [Uncountable k₀] [CharZero k₀]
    (hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T)
    (e : (Fan.internalBlowupTower k₀ b (Φ.rayEquivOfNodalCycleNumbering k₀ hΦ C ∘ ρ ∘ o) u).1 ≅ W)
    (he : e.hom ≫ T.toBase ≫ (X ↘ S) = (U).2.toTower.toBase ≫ (Φ.finiteFanSchemeToSpec k₀))
    (hker : ((D.comap T.toBase).radical).comap e.hom = (U).2.boundaryι.ker)
    (g : (Φ.toricBoundaryIdeal k₀ h₀).subscheme ⟶ D.subscheme) [g.IsOver S]
    (hg : g ≫ D.subschemeι = (U).2.boundaryι ≫ e.hom ≫ T.toBase)
    (hsub : g.IsOrientedCycleSubdivision C A)
    (hv : ∀ j, b.detDualEquiv (v j).primitiveGenerator (v (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, (v j).toCone ≤ σ ∧ (v (j + 1)).toCone ≤ σ)
    {R : Submodule ℤ V₀} (B : LinearMap.BilinForm ℤ (V₀ ⧸ R))
    (hR : R = Submodule.span ℤ (Set.range fun a : Fin 2 ↦
      Sum.elim (fun j ↦ b.repr (v j).primitiveGenerator a) 0))
    (hB : B.compl₁₂ R.mkQ R.mkQ =
      Matrix.toBilin' (Fan.numberedInternalBlowupGram ι (fun j ↦ b.repr (v j).primitiveGenerator)))
    (l : List (ZMod (n + d))) (j : ZMod n → ZMod (n + d))
    (hl : ∀ k, k ∈ l ↔ k ∉ Set.range j)
    (hj : withFactorialSurface[k₀,X,∀ a, (e.hom ≫ T.toBase)
      (Fan.internalBlowupBoundaryPrimeEquiv k₀ hΦ b s u (v (j a))).val =
        (A.boundaryPrimeEquiv hD a).val])
    (E : SkewExchangeMatrix ι) (hE : E.reindex o.symm = Fan.rayExchangeMatrix b s) :
    let F : LinearMap.BilinForm ℤ V₀ := B.compl₁₂ R.mkQ R.mkQ
    let a := l.map (Fan.numberedStrictBoundaryCoefficients ρ)
    let P := B.orthogonal (Submodule.span ℤ {x | x ∈ l.map fun k ↦ R.mkQ (strict k)})
    let x := fun k ↦ F.projectOffNegOnes a (strict (j k))
    (∀ y ∈ F.orthogonalizeNegOnes a, F y y = -1) →
    (∃ y, F (∑ k, x k) y = 1) →
    (∀ k, 0 ≤ F (∑ i, x i) (x k)) →
    F (∑ k, x k) (∑ k, x k) = 0 →
    ∃ a : ZMod n → P, (∀ k, (a k).val = R.mkQ (x k)) ∧
      Nonempty (signedLoopSubstitutions E ≃* signedBoundaryIsometryGroup (B.restrict P) a) := by
  let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  let := (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let : IsNormalScheme X := IsNormalScheme.of_uniqueFactorizationMonoid_stalk
  intro F a P x hs hp hn hz
  have hsupp : (D.comap (e.hom ≫ T.toBase)).support = (U).2.boundaryι.ker.support := by
    rw [← hker, ← radical_comap_of_isOpenImmersion _ e.hom, ← comap_comp, support_radical]
  let : IsModification (e.hom ≫ T.toBase) := Fan.isModification_orderedContraction k₀ hΦ b s u hT e
  let ray := Fan.contractedBoundaryRayEmbedding k₀ hΦ b s u (e.hom ≫ T.toBase) hsupp
  have hprime (k : ZMod n) : ray (A.boundaryPrimeEquiv hD k) = v (j k) :=
    (Fan.contractedBoundaryRayEmbedding_eq_iff k₀ hΦ b s u _ hsupp _ _).mpr (hj k)
  have hsurv (k : ZMod (n + d)) : k ∈ l ↔ v k ∉ Set.range ray := by
    have heq : Set.range (ray ∘ A.boundaryPrimeEquiv hD) = Set.range ray := by
      rw [Set.range_comp, (A.boundaryPrimeEquiv hD).surjective.range_eq, Set.image_univ]
    rw [hl k, ← heq]
    simp only [Function.comp_def, hprime, Set.mem_range, Equiv.apply_eq_iff_eq]
  obtain ⟨hs', hpro⟩ := map_updated_boundary_coefficients ρ B l hs
  obtain ⟨μ, hμ⟩ := Fan.exists_numberedContractedPicardIsometry k₀ b hΦ hc v o ρ u
    hT e he hsupp hv B hR hB l hsurv hs'
  let a' := fun k ↦ μ.symm (Additive.ofMul (primeDivisorClass (D.boundaryPrimeEmbedding
    (A.boundaryPrimeEquiv hD k))))
  have ha (k : ZMod n) : (a' k).val = R.mkQ (x k) := by
    have h := hμ (A.boundaryPrimeEquiv hD k)
    rw [hprime, Equiv.symm_apply_apply] at h
    exact h.trans (hpro (j k)).symm
  refine ⟨a', ha, ?_⟩
  obtain ⟨z, hzparam⟩ : ∃ z : GeometricRealization.Point
      (Over.mk (structureMap k₀ (Fin r → ℤ))),
      (fun k ↦ pointsEquiv k₀ _ ⟨Over.Hom.left z, Over.w z⟩
        (Multiplicative.ofAdd (Pi.single k 1))) = u :=
    ⟨centerPoint u, centerPoint_parameters u⟩
  subst u
  obtain ⟨P₀, _, hfan, hrays⟩ :=
    exists_marked_reference_fiber_of_numbered_model A μ hΦ s z hc hT e he hker C g hg hsub hv
  have hmat := hE.trans (eq_rayExchangeMatrix_of_reference_rays A P₀ s hfan hrays).symm
  let : (Chow.intersectionBilinForm k₀ X).IsPerfPair :=
    Chow.isPerfPair_intersectionBilinForm_of_isRationalOver k₀ X
  let : (B.restrict P).IsPerfPair :=
    LinearMap.IsPerfPair.congr (Chow.intersectionBilinForm k₀ X)
      μ.toLinearEquiv μ.toLinearEquiv (B.restrict P)
      (LinearMap.ext₂ fun x y ↦ (LinearMap.compl₁₂_apply ..).trans (μ.symm.map_app y x))
  let inc : B.restrict P →bᵢ B := ⟨P.subtype, fun _ _ ↦ rfl⟩
  let q : F →bᵢ B := ⟨R.mkQ, fun _ _ ↦ LinearMap.compl₁₂_apply ..⟩
  exact P₀.nonempty_signedLoopSubstitutions_mulEquiv_of_isometry hD o E hmat
    inc q R.mkQ_surjective x (fun k ↦ (ha k).symm) hp hn hz

end OrderedTowers

end QPainleve.SignedClusterModularGroup
