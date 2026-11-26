/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Contraction.Boundary
public import QPainleve.LinearAlgebra.BilinearForm.NegOneProjection

import TauCeti.LinearAlgebra.Matrix.Dual

/-!
# Ordered boundary updates in the contracted Picard marking

A list of rays specifies which strict boundary classes to eliminate. If the list contains
exactly the contracted rays and the successive classes have square −1, the updates compute
the surviving prime classes in the marking. This uses the exceptional-span description and
the boundary-prime projection formula from the contracted Picard marking.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower TauCeti.AlgebraicGeometry
open QPainleve TauCeti LineBundleClass Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] {n : ℕ}
  (hΦ : Φ.IsRegular) (b : Module.Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Z" => Φ.algebraicRealization
local notation "hU" c => isClosedPointTower_internalBlowupTower b s c
local notation "cl" ρ:arg => markedBoundaryMap hΦ s (Pi.single ρ 1)
local notation "B" => LinearMap.BilinForm.prod (Chow.intersectionBilinForm ℂ Z)
  (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin n → ℤ)))

variable {X Y : Scheme} [X.Over S] [X.IsProjectiveOver ℂ] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ S)] [Φ.algebraicRealization.IsProjectiveOver ℂ]
  [DecidableEq Φ.Ray]
  {D : X.IdealSheafData} {d : ℕ} {T : BlowupTower X d Y}
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

local notation "p" => (e.hom ≫ T.toBase)
local notation "μ" => contractedPicardMarking ℂ hT.isClosedPointTower (hU c) e he
local notation "P" => markedExceptionalSpan ℂ (hU c) T e

/-- For a list of the contracted rays with square −1 at each elimination step, the
successive updates of a surviving ray class compute that prime's inverse Picard marking
in the ambient coordinates of the ordered internal blowups. -/
theorem contractedPicardMarking_symm_boundaryPrime_eq_projectOffNegOnes
    (rays : List Φ.Ray) (x : D.boundaryPrimes) :
    let : SmoothOfRelativeDimension 2 (Z ↘ S) :=
      ((Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)) ▸
        Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : IsNoetherian Z := isNoetherian_of_finiteType (Z ↘ S)
    let := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
    let := (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let : IsModification p := isModification_orderedContraction hΦ b s c hT e
    let ρ := contractedBoundaryRayEmbedding hΦ b s c p hD
    let classes := rays.map (fun r ↦ cl r)
    (∀ r, r ∈ rays ↔ r ∉ Set.range ρ) →
    (∀ C ∈ (B).orthogonalizeNegOnes classes, (B) C C = -1) →
    ((μ).symm (Additive.ofMul (primeDivisorClass
      ⟨x.val, (mem_boundaryPrimes.mp x.property).2⟩))).val =
      (B).projectOffNegOnes classes (cl (ρ x)) := by
  intro _ _ _ _ _ ρ classes hrays hsq
  have hspan : Submodule.span ℤ {a | a ∈ classes} = P := by
    rw [markedExceptionalSpan_eq_span_compl_survivingRays hΦ b s c hT e hD]
    congr 1
    ext a
    simp only [classes, ρ, Set.mem_ofPred_eq, List.mem_map, Set.mem_image, Set.mem_compl_iff, hrays]
  have hsymm : (B).IsSymm := by
    refine LinearMap.BilinForm.isSymm_prod_iff.mpr
      ⟨⟨fun a b ↦ ?_⟩, (TauCeti.isSymm_dotProductBilin (R := ℤ) (ι := Fin n)).neg⟩
    simp only [Chow.intersectionBilinForm_apply, Chow.classIntersectionNumber_comm]
  have hprojection (Q : Submodule ℤ _) (hQ : Submodule.span ℤ {a | a ∈ classes} = Q)
      (hcompl : IsCompl ((B).orthogonal Q) Q) :
      (B).projectOffNegOnes classes = ((B).orthogonal Q).projection Q hcompl := by
    subst Q
    exact (B).projectOffNegOnes_eq_projection hsymm.isRefl classes hsq
  have hclass := congrArg Subtype.val (contractedPicardMarking_symm_boundaryPrime
    hΦ b s c hT e he hD x)
  rw [hprojection P hspan (isCompl_orthogonal_markedExceptionalSpan ℂ
    hT.isClosedPointTower (hU c) e he)]
  exact hclass

end TauCeti.Toric.Fan
