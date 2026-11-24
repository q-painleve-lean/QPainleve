/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Projection
public import QPainleve.AlgebraicGeometry.Chow.Nef.Boundary
public import QPainleve.Geometry.Toric.Fan.Boundary.Contraction
public import QPainleve.Geometry.Toric.Fan.Picard.Contraction.Basic

import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.Morphisms.Smooth.Factorial
import QPainleve.Geometry.Toric.Fan.Boundary.StrictTransform
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition
import TauCeti.LinearAlgebra.BilinearForm.Isometry.Basic

/-!
# The boundary in a contracted Picard marking

In an ordered toric model the class of a surviving boundary prime is obtained by
orthogonally projecting the marked strict ray class away from the contracted ray
span. Both the span and the strict ray class are independent of the binomial center
parameters. In particular, this calculation retains the marking when several
ordered centers are infinitely near.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower TopologicalSpace
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] {n : ℕ}
  (hΦ : Φ.IsRegular) (b : Module.Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Z" => Φ.algebraicRealization
local notation "d₂" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "m" => (fun j ↦ LinearMap.toAddMonoidHom
  (b.detDualEquiv (Ray.primitiveGenerator (s j))))
local notation "hm" => (fun j ↦ b.detDualEquiv_self (Ray.primitiveGenerator (s j)))
local notation "hprim" => (fun j ↦ Ray.surjective_detCharacter (s j) b)
local notation "Model" => (Σ Y, WithBoundary (subschemeι (Φ.boundaryIdeal inferInstance)) n Y)
local notation "model" c => internalBlowupTower b s c
local notation "U" c => WithBoundary.toTower (Sigma.snd (model c))
local notation "hU" c => isClosedPointTower_internalBlowupTower b s c
local notation "fZ" => (Φ.algebraicRealization ↘ S)
local notation "prime(" x ")" => (Subtype.mk (Subtype.val x)
  (And.right (mem_boundaryPrimes.mp (Subtype.property x))) : CodimensionOnePoint _)
local notation "cl" ρ:arg => markedBoundaryMap hΦ s (Pi.single ρ 1)

/-- In the ordered Picard marking the actual boundary prime over a ray has the
fixed strict ray class. -/
theorem picardHom_markedBoundaryMap_single_eq_primeDivisorClass [DecidableEq Φ.Ray]
    (c : Fin n → ℂˣ) (ρ : Φ.Ray) :
    let : IsIntegral (model c).1 := isIntegral_internalBlowupTower b s c hΦ
    let : IsNoetherian (model c).1 := (U c).isNoetherian
    let : SmoothOfRelativeDimension 2 fZ :=
      d₂ ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : SmoothOfRelativeDimension 2 ((U c).toBase ≫ fZ) :=
      (hU c).smoothOfRelativeDimension fZ
    let := ((U c).toBase ≫ fZ).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    (U c).picardHom (cl ρ) =
      Additive.ofMul (primeDivisorClass (prime(internalBlowupBoundaryPrimeEquiv hΦ b s c ρ))) := by
  intro _ _ _ _ _
  let j := ρ.boundaryComponentι hΦ ≫ (model c).2.boundaryι
  have : IsIntegral (Φ.rayBoundaryIdeal hΦ ρ).subscheme := by
    rw [rayBoundaryIdeal_def]
    exact isIntegral_subscheme_vanishingIdeal isIrreducible_singleton.closure
  have hI := ker_boundaryComponentι_internalBlowupTower b s c hΦ ρ
  have hs := range_rayComponent_internalBlowupBoundaryPrimeEquiv hΦ b s c ρ
  let x := (internalBlowupBoundaryPrimeEquiv hΦ b s c ρ).val
  have hker : j.ker = vanishingIdeal ⟨closure {x}, isClosed_closure⟩ := by
    rw [j.ker_eq_vanishingIdeal_support]
    congr 1
    exact SetLike.coe_injective ((j.support_ker.trans
      j.isClosedEmbedding.isClosed_range.closure_eq).trans hs)
  have heff := (hU c).isEffectiveCartier_strictTransform fZ
    (Φ.isEffectiveCartier_rayBoundaryIdeal hΦ ρ)
  let Marked (M : Model) := ∀ hM : IsClosedPointTower Z M.2.toTower,
    M.2.toTower.picardHom (cl ρ) = strictRayBoundaryClass hΦ d₂ _ hM ρ
  have hmark : Marked (model c) := by
    rw [internalBlowupTower_eq_alongBoundary]
    intro hM
    exact picardHom_markedBoundaryMap_single hΦ d₂ s m hm hprim c _
      (fun j ↦ (s j).internalCenter_val b (c j)) hM ρ
  rw [hmark (hU c),
    strictRayBoundaryClass_eq _ _ _ _ _ heff, primeDivisorClass_def,
    mk_toInvertibleSheaf_congr _ _ (hI.symm.trans hker)]

variable {X Y : Scheme} [X.Over S] [X.IsProjectiveOver ℂ] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ S)] [Φ.algebraicRealization.IsProjectiveOver ℂ]
  [DecidableEq Φ.Ray]
  {D : X.IdealSheafData} {d : ℕ} {T : QPainleve.BlowupTower X d Y}
  (c : Fin n → ℂˣ) (hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T)
  (e : (internalBlowupTower b s c).1 ≅ Y)
  (he : e.hom ≫ T.toBase ≫ (X ↘ S) =
    (internalBlowupTower b s c).2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap)
  (hD : (D.comap (e.hom ≫ T.toBase)).support =
    (internalBlowupTower b s c).2.boundaryι.ker.support)

local instance : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
local instance : IsNormalScheme X := by
  let := (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  exact IsNormalScheme.of_uniqueFactorizationMonoid_stalk

local notation "p" => (Iso.hom e ≫ toBase T)

omit [DecidableEq Φ.Ray] [Φ.algebraicRealization.IsProjectiveOver ℂ] in
include hΦ hT in
/-- Presenting the top of a specified nodal tower by an ordered toric model gives
a modification of the original surface. -/
theorem isModification_orderedContraction : IsModification p := by
  let : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  let := hT.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (X ↘ S)
  have : IsIntegral Y := hT.isClosedPointTower.isIntegral (X ↘ S)
  let := isIntegral_internalBlowupTower b s c hΦ
  exact inferInstance

local notation "ρₓ" x:arg => contractedBoundaryRayEmbedding hΦ b s c p hD x

omit [Φ.algebraicRealization.IsProjectiveOver ℂ] in
include hT hD in
/-- In the ordered marking, the exceptional summand is generated by the strict
ray classes of the complement of the surviving rays. -/
theorem markedExceptionalSpan_eq_span_compl_survivingRays :
    let : SmoothOfRelativeDimension 2 fZ :=
      d₂ ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : IsModification p := isModification_orderedContraction hΦ b s c hT e
    markedExceptionalSpan ℂ (hU c) T e =
      Submodule.span ℤ ((fun ρ ↦ cl ρ) ''
        (Set.range (contractedBoundaryRayEmbedding hΦ b s c p hD))ᶜ) := by
  intro _ _
  let Span (M : Model) := ∀ (hM : IsClosedPointTower Z M.2.toTower) (f : M.1 ≅ Y),
    (D.comap (f.hom ≫ T.toBase)).support = M.2.boundaryι.ker.support →
    markedExceptionalSpan ℂ hM T f =
      Submodule.span ℤ ((fun ρ ↦ cl ρ) '' {ρ |
        Disjoint ((M.2.toTower.strictTransform (Φ.rayBoundaryIdeal hΦ ρ)).support : Set M.1)
          ((f.hom ≫ T.toBase) ⁻¹ᵁ T.toBase.isoLocus)})
  have hspan : Span (model c) := by
    rw [internalBlowupTower_eq_alongBoundary]
    intro _ f hf
    exact markedExceptionalSpan_eq_span_contractedRays hΦ d₂ s m hm hprim c _
      (fun j ↦ (s j).internalCenter_val b (c j)) hT f hf
  rw [hspan (hU c) e hD]
  congr 2
  ext ρ
  let y := internalBlowupBoundaryPrimeEquiv hΦ b s c ρ
  have hy : y.val ∈ (D.comap p).boundaryPrimes := by
    rw [boundaryPrimes_eq_of_support_eq hD]
    exact y.property
  have hor : ρ ∈ Set.range (contractedBoundaryRayEmbedding hΦ b s c p hD) ↔
      (p) y.val ∈ (p).isoLocus := by
    let := isIntegral_internalBlowupTower b s c hΦ
    constructor
    · rintro ⟨x, rfl⟩
      simpa only [y, contraction_internalBlowupBoundaryPrimeEquiv] using
        (p).mem_isoLocus_of_coheight_eq_one (mem_boundaryPrimes.mp x.property).2
    · intro h
      have hyiso : y.val ∈ (D.comap p).boundaryPrimes ∩ p ⁻¹' ((p).isoLocus : Set X) := ⟨hy, h⟩
      have hx := (D.bijOn_boundaryPrimes_comap_of_subset_isoLocus p
        («U» := (p).isoLocus) Set.Subset.rfl).mapsTo hyiso
      exact ⟨⟨_, hx.1⟩, (contractedBoundaryRayEmbedding_eq_iff hΦ b s c p hD _ ρ).mpr rfl⟩
  rw [Set.mem_compl_iff, hor, Scheme.Hom.isoLocus_comp_of_isIso e.hom T.toBase, Set.mem_ofPred_eq]
  let j := ρ.boundaryComponentι hΦ ≫ (model c).2.boundaryι
  rw [← ker_boundaryComponentι_internalBlowupTower b s c hΦ,
    j.support_ker,
    j.isClosedEmbedding.isClosed_range.closure_eq,
    range_rayComponent_internalBlowupBoundaryPrimeEquiv hΦ b s c, Set.disjoint_left]
  refine ⟨fun h hρ ↦ h (subset_closure (Set.mem_singleton _)) ((p).mem_preimage.mpr hρ), ?_⟩
  intro h _ hx hV
  exact
    h ((p).mem_preimage.mp
      ((specializes_iff_mem_closure.mpr hx).mem_open (p ⁻¹ᵁ T.toBase.isoLocus).isOpen hV))

include hT he hD in
/-- The inverse marking sends a boundary prime to the orthogonal projection of its
strict ray class onto the complement of the exceptional span. -/
theorem contractedPicardMarking_symm_boundaryPrime (x : D.boundaryPrimes) :
    let : SmoothOfRelativeDimension 2 fZ :=
      d₂ ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : IsNoetherian Z := isNoetherian_of_finiteType fZ
    let := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
    let := (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let : IsModification p := isModification_orderedContraction hΦ b s c hT e
    (contractedPicardMarking ℂ hT.isClosedPointTower (hU c) e he).symm
      (Additive.ofMul (primeDivisorClass (prime(x)))) =
      Submodule.projectionOnto _ _ (isCompl_orthogonal_markedExceptionalSpan ℂ
        hT.isClosedPointTower (hU c) e he) (cl (ρₓ x)) := by
  intro _ _ _ _ _
  let : IsIntegral (model c).1 := isIntegral_internalBlowupTower b s c hΦ
  let : IsNoetherian (model c).1 := (U c).isNoetherian
  let : SmoothOfRelativeDimension 2 ((U c).toBase ≫ fZ) :=
    (hU c).smoothOfRelativeDimension fZ
  let := ((U c).toBase ≫ fZ).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let μ := contractedPicardMarking ℂ hT.isClosedPointTower (hU c) e he
  let P := markedExceptionalSpan ℂ (hU c) T e
  let a := μ.symm (Additive.ofMul (primeDivisorClass (prime(x))))
  have hsub : a.val - cl (ρₓ x) ∈ P := by
    apply (SetLike.ext_iff.mp (markedExceptionalSpan_eq_comap_primeDivisorSpanCompl ℂ
      hT.isClosedPointTower (hU c) e) _).mpr
    rw [Submodule.mem_comap, map_sub,
      picardHom_markedBoundaryMap_single_eq_primeDivisorClass hΦ b s c]
    have hpull : (U c).picardHom a.val =
        Additive.ofMul (pullback p (primeDivisorClass (prime(x)))) :=
      picardHom_contractedPicardMarking_symm ℂ hT.isClosedPointTower (hU c) e he _
    rw [hpull]
    have : IsIso (p ∣_ T.toBase.isoLocus) := (p).le_isoLocus_iff.mp (by
      rw [Scheme.Hom.isoLocus_comp_of_isIso e.hom T.toBase])
    apply Scheme.Hom.pullback_primeDivisorClass_sub_mem_primeDivisorSpanCompl
    · exact contraction_internalBlowupBoundaryPrimeEquiv hΦ b s c p hD x
    · rw [← Scheme.Hom.isoLocus_comp_of_isIso e.hom T.toBase]
      exact (p).mem_isoLocus_of_coheight_eq_one (mem_boundaryPrimes.mp x.property).2
  have hzero := Submodule.projectionOnto_apply_of_mem_right
    (isCompl_orthogonal_markedExceptionalSpan ℂ hT.isClosedPointTower (hU c) e he) hsub
  simpa only [map_sub, Submodule.projectionOnto_apply_left, sub_eq_zero] using hzero


variable {X' Y' : Scheme} [X'.Over S] [X'.IsProjectiveOver ℂ] [IsIntegral X']
  [SmoothOfRelativeDimension 2 (X' ↘ S)]
  {D' : X'.IdealSheafData} {d' : ℕ} {T' : QPainleve.BlowupTower X' d' Y'}
  (c' : Fin n → ℂˣ) (hT' : IsNodalBoundaryTower D' (X' ↘ S) (𝟙 X') T')
  (e' : (internalBlowupTower b s c').1 ≅ Y')
  (he' : e'.hom ≫ T'.toBase ≫ (X' ↘ S) =
    (internalBlowupTower b s c').2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap)
  (hD' : (D'.comap (e'.hom ≫ T'.toBase)).support =
    (internalBlowupTower b s c').2.boundaryι.ker.support)

local instance : IsNoetherian X' := isNoetherian_of_finiteType (X' ↘ S)
local instance : IsNormalScheme X' := by
  let := (X' ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  exact IsNormalScheme.of_uniqueFactorizationMonoid_stalk

local notation "p'" => (Iso.hom e' ≫ toBase T')
local notation "ρ'ₓ" x:arg => contractedBoundaryRayEmbedding hΦ b s c' p' hD' x
local notation "B" => (LinearMap.BilinForm.prod (Chow.intersectionBilinForm ℂ Z)
  (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin n → ℤ))))

omit [DecidableEq Φ.Ray] in
include hT he hD hT' he' hD' in
/-- Two center choices with the same surviving rays give isometric marked Picard groups.
The isometry matches the boundary prime classes according to their surviving rays. -/
theorem exists_picardIsometry_of_same_survivingRays :
    let : IsModification p := isModification_orderedContraction hΦ b s c hT e
    let : IsModification p' := isModification_orderedContraction hΦ b s c' hT' e'
    let := (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let := (X' ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    Set.range (contractedBoundaryRayEmbedding hΦ b s c p hD) =
      Set.range (contractedBoundaryRayEmbedding hΦ b s c' p' hD') →
    ∃ g : (Chow.intersectionBilinForm ℂ X).IsometryEquiv (Chow.intersectionBilinForm ℂ X'),
      ∀ (x : D.boundaryPrimes) (y : D'.boundaryPrimes), ρₓ x = ρ'ₓ y →
        g (Additive.ofMul (primeDivisorClass (prime(x)))) =
          Additive.ofMul (primeDivisorClass (prime(y))) := by
  classical
  intro _ _ _ _ hR
  let : SmoothOfRelativeDimension 2 fZ :=
    d₂ ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let : IsNoetherian Z := isNoetherian_of_finiteType fZ
  let P := markedExceptionalSpan ℂ (hU c) T e
  let P' := markedExceptionalSpan ℂ (hU c') T' e'
  have hP : P = P' :=
    (markedExceptionalSpan_eq_span_compl_survivingRays hΦ b s c hT e hD).trans
      (hR ▸ (markedExceptionalSpan_eq_span_compl_survivingRays hΦ b s c' hT' e' hD').symm)
  let μ := contractedPicardMarking ℂ hT.isClosedPointTower (hU c) e he
  let ν := contractedPicardMarking ℂ hT'.isClosedPointTower (hU c') e' he'
  let f : ((B).restrict ((B).orthogonal P)).IsometryEquiv ((B).restrict ((B).orthogonal P')) :=
    { LinearEquiv.ofEq _ _ (congrArg (B).orthogonal hP) with
        map_app' := by
          intro x y
          -- The reindexing changes the submodule proof of each vector.
          change (B) ((LinearEquiv.ofEq _ _ (congrArg (B).orthogonal hP) x).val)
            ((LinearEquiv.ofEq _ _ (congrArg (B).orthogonal hP) y).val) = (B) x.val y.val
          simp only [LinearEquiv.coe_ofEq_apply] }
  refine ⟨(μ.symm.trans f).trans ν, fun x y hxy ↦ ?_⟩
  have hp := isCompl_orthogonal_markedExceptionalSpan ℂ hT.isClosedPointTower (hU c) e he
  have hq := isCompl_orthogonal_markedExceptionalSpan ℂ hT'.isClosedPointTower (hU c') e' he'
  have hproj (a) : f (Submodule.projectionOnto _ _ hp a) =
      Submodule.projectionOnto _ _ hq a := by
    apply Subtype.ext
    -- Equality of the exceptional spans identifies the ambient projections.
    have H (P P' : Submodule ℤ _) (h : P = P')
        (h₁ : IsCompl ((B).orthogonal P) P) (h₂ : IsCompl ((B).orthogonal P') P') :
        (((B).orthogonal P).projectionOnto P h₁ a).val =
          (((B).orthogonal P').projectionOnto P' h₂ a).val := by subst P'; rfl
    exact H P P' hP hp hq
  simp only [LinearMap.BilinForm.IsometryEquiv.trans_apply]
  rw [← ν.apply_symm_apply (Additive.ofMul (primeDivisorClass (prime(y))))]
  apply congrArg ν
  rw [contractedPicardMarking_symm_boundaryPrime hΦ b s c hT e he hD x,
    contractedPicardMarking_symm_boundaryPrime hΦ b s c' hT' e' he' hD' y, hproj, hxy]


local notation "δ(" h ")" => ((LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹)
local notation "χ(" X ")" => Chow.classIntersectionNumber ℂ X

omit [DecidableEq Φ.Ray] in
include hT he hD hT' he' hD' in
/-- The reduced boundaries of two ordered models with the same surviving rays have
primitive nef classes of square zero simultaneously. -/
theorem primitive_nef_square_zero_iff_of_same_survivingRays
    (hCart : D.IsEffectiveCartier) (hCart' : D'.IsEffectiveCartier)
    [IsReduced D.subscheme] [IsReduced D'.subscheme] :
    let : IsModification p := isModification_orderedContraction hΦ b s c hT e
    let : IsModification p' := isModification_orderedContraction hΦ b s c' hT' e'
    Set.range (contractedBoundaryRayEmbedding hΦ b s c p hD) =
      Set.range (contractedBoundaryRayEmbedding hΦ b s c' p' hD') →
    ((TauCeti.IsPrimitive (Additive.ofMul δ(hCart)) ∧
      δ(hCart).IsNef ℂ (X ↘ S) ∧ χ(X) δ(hCart) δ(hCart) = 0) ↔
    (TauCeti.IsPrimitive (Additive.ofMul δ(hCart')) ∧
      δ(hCart').IsNef ℂ (X' ↘ S) ∧ χ(X') δ(hCart') δ(hCart') = 0)) := by
  classical
  intro _ _ hR
  let := (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let := (X' ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  obtain ⟨g, hg⟩ := exists_picardIsometry_of_same_survivingRays hΦ b s c hT e he hD
    c' hT' e' he' hD' hR
  let r := contractedBoundaryRayEmbedding hΦ b s c p hD
  let s' := contractedBoundaryRayEmbedding hΦ b s c' p' hD'
  let β := (Equiv.ofInjective r r.injective).trans
    ((Set.equivOfEq hR).trans (Equiv.ofInjective s' s'.injective).symm)
  have hβ (x : D.boundaryPrimes) : ρₓ x = ρ'ₓ (β x) := by
    let z := Set.equivOfEq hR (Equiv.ofInjective r r.injective x)
    have hz := congrArg Subtype.val ((Equiv.ofInjective s' s'.injective).apply_symm_apply z)
    exact hz.symm
  let I : D.boundaryPrimes ↪ CodimensionOnePoint X :=
    ⟨fun x ↦ prime(x), fun _ _ h ↦ Subtype.ext
      (congrArg (fun q : CodimensionOnePoint _ ↦ q.val) h)⟩
  let I' : D'.boundaryPrimes ↪ CodimensionOnePoint X' :=
    ⟨fun x ↦ prime(x), fun _ _ h ↦ Subtype.ext
      (congrArg (fun q : CodimensionOnePoint _ ↦ q.val) h)⟩
  have hI (x : CodimensionOnePoint X) : (x : X) ∈ D.support ↔ x ∈ Set.range I := by
    exact ⟨fun h ↦ ⟨⟨x, mem_boundaryPrimes.mpr ⟨h, x.property⟩⟩, Subtype.ext rfl⟩,
      fun ⟨y, h⟩ ↦ congrArg Subtype.val h ▸ (mem_boundaryPrimes.mp y.property).1⟩
  have hI' (x : CodimensionOnePoint X') : (x : X') ∈ D'.support ↔
      x ∈ Set.range (β.toEmbedding.trans I') := by
    constructor
    · intro h
      obtain ⟨y, hy⟩ := β.surjective ⟨x, mem_boundaryPrimes.mpr ⟨h, x.property⟩⟩
      exact ⟨y, Subtype.ext (congrArg (fun q : D'.boundaryPrimes ↦ q.val) hy)⟩
    · rintro ⟨y, h⟩
      exact congrArg Subtype.val h ▸ (mem_boundaryPrimes.mp (β y).property).1
  let : Finite D.boundaryPrimes := Finite.of_injective r r.injective
  have hd := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  have hd' := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X' ↘ S) (n := 2)
  let g' : LinearMap.BilinForm.IsometryEquiv (Chow.classIntersectionBilinForm ℂ hd)
      (Chow.classIntersectionBilinForm ℂ hd') :=
    { g.toLinearEquiv with
      map_app' := fun x y ↦ by
        simpa only [Chow.classIntersectionBilinForm_apply, Chow.intersectionBilinForm_apply,
          LinearMap.toFun_eq_coe, LinearEquiv.coe_coe,
          LinearMap.BilinForm.IsometryEquiv.coe_toLinearEquiv] using g.map_app y x }
  exact hCart.primitive_nef_square_zero_iff_of_picardIsometry hCart' hd hd' g' I _ hI hI'
    (fun x ↦ hg x (β x) (hβ x))

end TauCeti.Toric.Fan
