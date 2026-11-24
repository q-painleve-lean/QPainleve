/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Contraction.Boundary
public import QPainleve.LinearAlgebra.BilinearForm.Isometry
import QPainleve.AlgebraicGeometry.Morphisms.Smooth.Factorial

/-!
# Picard marking with a fixed set of contracted rays

The Picard groups of the contractions in an ordered toric family can be marked by
one integral lattice. Its defining submodule uses the fan, the ordered ray labels,
and the fixed set of contracted rays.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Chow (intersectionBilinForm)

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones] {n : ℕ}
  (hΦ : Φ.IsRegular) (b : Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Z" => Φ.algebraicRealization
local notation "fZ" => (Z ↘ S)
local notation "rankTwo" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "smoothZ" =>
  Eq.mpr (congrArg (SmoothOfRelativeDimension 2) (Fan.algebraicRealization_over Φ))
    (Eq.mp (congrArg
      (fun m ↦ SmoothOfRelativeDimension m (Fan.algebraicRealizationStructureMap Φ)) rankTwo)
      (Fan.smoothOfRelativeDimension_algebraicRealizationStructureMap Φ hΦ))
local notation "F" =>
  LinearMap.BilinForm.prod (@intersectionBilinForm ℂ _ _ Z _ _ _ smoothZ)
    (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin n → ℤ)))
local notation "P(" R ")" =>
  Submodule.span ℤ ((fun ρ ↦ markedBoundaryMap hΦ s (Pi.single ρ 1)) '' R)
local notation "K(" R ")" => LinearMap.BilinForm.orthogonal (F) (P(R))

variable {X Y : Scheme} [X.Over S] [X.IsProjectiveOver ℂ] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ S)]
  {D : X.IdealSheafData} {d : ℕ} {T : QPainleve.BlowupTower X d Y}
  (c : Fin n → ℂˣ) (hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T)
  (u : (internalBlowupTower b s c).1 ≅ Y)
  (hu : u.hom ≫ T.toBase ≫ (X ↘ S) =
    (internalBlowupTower b s c).2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap)
  (hD : (D.comap (u.hom ≫ T.toBase)).support =
    (internalBlowupTower b s c).2.boundaryι.ker.support)

local notation "p" => (Iso.hom u ≫ toBase T)
local notation "U" => WithBoundary.toTower (Sigma.snd (internalBlowupTower b s c))
local notation "hU" => isClosedPointTower_internalBlowupTower b s c
local notation "hp" => isModification_orderedContraction hΦ b s c hT u
local notation "μ" => contractedPicardMarking ℂ hT.isClosedPointTower hU u hu

private local instance : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
local instance : IsNormalScheme X := by
  let := (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  exact IsNormalScheme.of_uniqueFactorizationMonoid_stalk

/-- The rays of an ordered model whose strict boundary primes are contracted by
the specified nodal tower. -/
def contractedRaySet : Set Φ.Ray :=
  letI : IsModification p := hp
  (Set.range (contractedBoundaryRayEmbedding hΦ b s c p hD))ᶜ

/-- A contracted ray is one whose strict prime maps into the complement of the
boundary prime set downstairs. -/
theorem mem_contractedRaySet_iff (ρ : Φ.Ray) :
    ρ ∈ contractedRaySet hΦ b s c hT u hD ↔
      p (internalBlowupBoundaryPrimeEquiv hΦ b s c ρ).val ∉ D.boundaryPrimes := by
  let : IsModification p := hp
  rw [contractedRaySet, Set.mem_compl_iff, mem_range_contractedBoundaryRayEmbedding_iff]

variable [Φ.algebraicRealization.IsProjectiveOver ℂ]

open Classical in
/-- A contraction with prescribed contracted rays has a marking by the lattice
orthogonal to their strict classes in toric coordinates. -/
def contractedPicardMarkingOfRaySet (R : Set Φ.Ray)
    (hR : R = contractedRaySet hΦ b s c hT u hD) :
    ((F).restrict (K(R))).IsometryEquiv (intersectionBilinForm ℂ X) := by
  haveI : SmoothOfRelativeDimension 2 fZ := smoothZ
  haveI : IsModification p := hp
  have hP : markedExceptionalSpan ℂ hU T u = P(R) := by
    rw [hR]
    exact markedExceptionalSpan_eq_span_compl_survivingRays hΦ b s c hT u hD
  refine ((LinearMap.BilinForm.IsometryEquiv.refl (F)).ofSubmodules (K(R)) _ ?_).trans (μ)
  -- The identity isometry carries the same ambient vectors between the two submodule types.
  change (K(R)).map LinearMap.id = (F).orthogonal (markedExceptionalSpan ℂ hU T u)
  rw [Submodule.map_id, hP]

open Classical in
/-- In the ordered internal blowup coordinates, the inverse of the fixed ray
marking is pullback along the contraction. -/
theorem coe_contractedPicardMarkingOfRaySet_symm_apply (R : Set Φ.Ray)
    (hR : R = contractedRaySet hΦ b s c hT u hD)
    (L : LineBundleClass X) :
    ((contractedPicardMarkingOfRaySet hΦ b s c hT u hu hD R hR).symm
      (Additive.ofMul L)).val =
      (internalBlowupPicardMarking b s c hΦ).symm
        (Additive.ofMul (LineBundleClass.pullback p L)) := by
  let : SmoothOfRelativeDimension 2 fZ := smoothZ
  apply (internalBlowupPicardMarking b s c hΦ).injective
  rw [LinearEquiv.apply_symm_apply, internalBlowupPicardMarking_apply]
  unfold contractedPicardMarkingOfRaySet
  rw [LinearMap.BilinForm.IsometryEquiv.symm_trans_apply,
    LinearMap.BilinForm.IsometryEquiv.coe_ofSubmodules_symm_apply]
  exact picardHom_contractedPicardMarking_symm ℂ hT.isClosedPointTower hU u hu (Additive.ofMul L)

end TauCeti.Toric.Fan
