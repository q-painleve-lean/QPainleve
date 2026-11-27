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

universe u

variable (k : Type u) [Field k] [IsAlgClosed k]
  {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones] {n : ℕ}
  (hΦ : Φ.IsRegular) (b : Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray)

local notation "S" => Spec (CommRingCat.of k)
local notation "Z" => (Φ.finiteFanScheme k)
local notation "fZ" => (Z ↘ S)
local notation "rankTwo" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "smoothZ" =>
  Eq.mpr (congrArg (SmoothOfRelativeDimension 2) (Fan.finiteFanScheme_over k Φ))
    (Eq.mp (congrArg
      (fun m ↦ SmoothOfRelativeDimension m (Fan.finiteFanSchemeToSpec k Φ)) rankTwo)
      (Fan.smoothOfRelativeDimension_finiteFanSchemeToSpec Φ k hΦ))
local notation "F" =>
  LinearMap.BilinForm.prod (@intersectionBilinForm k _ _ Z _ _ _ smoothZ)
    (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin n → ℤ)))
local notation "P(" R ")" =>
  Submodule.span ℤ ((fun ρ ↦ markedBoundaryMap k hΦ s (Pi.single ρ 1)) '' R)
local notation "K(" R ")" => LinearMap.BilinForm.orthogonal (F) (P(R))

variable {X Y : Scheme} [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  {D : X.IdealSheafData} {d : ℕ} {T : QPainleve.BlowupTower X d Y}
  (c : Fin n → kˣ)
  (hT : IsNodalBoundaryTower D (X ↘ Spec (.of k)) (𝟙 X) T)
  (u : (internalBlowupTower k b s c).1 ≅ Y)
  (hu : u.hom ≫ T.toBase ≫ (X ↘ Spec (.of k)) =
    (internalBlowupTower k b s c).2.toTower.toBase ≫ (Φ.finiteFanScheme k ↘ Spec (.of k)))
  (hD : (D.comap (u.hom ≫ T.toBase)).support =
    (internalBlowupTower k b s c).2.boundaryι.ker.support)

local notation "p" => (Iso.hom u ≫ toBase T)
local notation "U" => WithBoundary.toTower (Sigma.snd (internalBlowupTower k b s c))
local notation "hU" => isClosedPointTower_internalBlowupTower k b s c
local notation "hp" => isModification_orderedContraction k hΦ b s c hT u
local notation "μ" => contractedPicardMarking k hT.isClosedPointTower hU u hu

/-- The rays of an ordered model whose strict boundary primes are contracted by
the specified nodal tower. -/
def contractedRaySet : Set Φ.Ray :=
  let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  let : IsNormalScheme X := (X ↘ S).isNormalScheme_of_smoothOfRelativeDimension_two
  letI : IsModification p := hp
  (Set.range (contractedBoundaryRayEmbedding k hΦ b s c p hD))ᶜ

/-- A contracted ray is one whose strict prime maps into the complement of the
boundary prime set downstairs. -/
theorem mem_contractedRaySet_iff (ρ : Φ.Ray) :
    ρ ∈ contractedRaySet k hΦ b s c hT u hD ↔
      p (internalBlowupBoundaryPrimeEquiv k hΦ b s c ρ).val ∉ D.boundaryPrimes := by
  let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  let : IsNormalScheme X := (X ↘ S).isNormalScheme_of_smoothOfRelativeDimension_two
  let : IsModification p := hp
  rw [contractedRaySet, Set.mem_compl_iff, mem_range_contractedBoundaryRayEmbedding_iff]

variable [(Φ.finiteFanScheme k).IsProjectiveOver k]

open Classical in
/-- A contraction with prescribed contracted rays has a marking by the lattice
orthogonal to their strict classes in toric coordinates. -/
def contractedPicardMarkingOfRaySet (R : Set Φ.Ray)
    (hR : R = contractedRaySet k hΦ b s c hT u hD) :
    ((F).restrict (K(R))).IsometryEquiv (intersectionBilinForm k X) := by
  haveI : SmoothOfRelativeDimension 2 fZ := smoothZ
  have hP : markedExceptionalSpan k hU T u = P(R) := by
    rw [hR]
    exact markedExceptionalSpan_eq_span_compl_survivingRays k hΦ b s c hT u hD
  refine ((LinearMap.BilinForm.IsometryEquiv.refl (F)).ofSubmodules (K(R)) _ ?_).trans (μ)
  -- The identity isometry carries the same ambient vectors between the two submodule types.
  change (K(R)).map LinearMap.id = (F).orthogonal (markedExceptionalSpan k hU T u)
  rw [Submodule.map_id, hP]

open Classical in
/-- In the ordered internal blowup coordinates, the inverse of the fixed ray
marking is pullback along the contraction. -/
theorem coe_contractedPicardMarkingOfRaySet_symm_apply (R : Set Φ.Ray)
    (hR : R = contractedRaySet k hΦ b s c hT u hD)
    (L : LineBundleClass X) :
    ((contractedPicardMarkingOfRaySet k hΦ b s c hT u hu hD R hR).symm
      (Additive.ofMul L)).val =
      (internalBlowupPicardMarking k b s c hΦ).symm
        (Additive.ofMul (LineBundleClass.pullback p L)) := by
  let : SmoothOfRelativeDimension 2 fZ := smoothZ
  apply (internalBlowupPicardMarking k b s c hΦ).injective
  rw [LinearEquiv.apply_symm_apply, internalBlowupPicardMarking_apply]
  unfold contractedPicardMarkingOfRaySet
  rw [LinearMap.BilinForm.IsometryEquiv.symm_trans_apply,
    LinearMap.BilinForm.IsometryEquiv.coe_ofSubmodules_symm_apply]
  exact picardHom_contractedPicardMarking_symm k hT.isClosedPointTower hU u hu (Additive.ofMul L)

end TauCeti.Toric.Fan
