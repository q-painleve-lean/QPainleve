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

universe u

variable (k : Type u) [Field k] [IsAlgClosed k] {N V : Type u}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] {n : ℕ}
  (hΦ : Φ.IsRegular) (b : Module.Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray)

local notation "S" => Spec (CommRingCat.of k)
local notation "Z" => (Φ.finiteFanScheme k)
local notation "hU" c => isClosedPointTower_internalBlowupTower k b s c
local notation "cl" ρ:arg => markedBoundaryMap k hΦ s (Pi.single ρ 1)
local notation "B" => LinearMap.BilinForm.prod (Chow.intersectionBilinForm k Z)
  (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin n → ℤ)))

variable {X Y : Scheme} [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))] [(Φ.finiteFanScheme k).IsProjectiveOver k]
  [DecidableEq Φ.Ray]
  {D : X.IdealSheafData} {d : ℕ} {T : BlowupTower X d Y}
  (c : Fin n → kˣ) (hT : IsNodalBoundaryTower D (X ↘ Spec (.of k)) (𝟙 X) T)
  (e : (internalBlowupTower k b s c).1 ≅ Y)
  (he : e.hom ≫ T.toBase ≫ (X ↘ Spec (.of k)) =
    (internalBlowupTower k b s c).2.toTower.toBase ≫ (Φ.finiteFanScheme k ↘ Spec (.of k)))
  (hD : (D.comap (e.hom ≫ T.toBase)).support =
    (internalBlowupTower k b s c).2.boundaryι.ker.support)

local notation "p" => (e.hom ≫ T.toBase)
local notation "μ" => contractedPicardMarking k hT.isClosedPointTower (hU c) e he
local notation "P" => markedExceptionalSpan k (hU c) T e

/-- For a list of the contracted rays with square −1 at each elimination step, the
successive updates of a surviving ray class compute that prime's inverse Picard marking
in the ambient coordinates of the ordered internal blowups. -/
theorem contractedPicardMarking_symm_boundaryPrime_eq_projectOffNegOnes
    (rays : List Φ.Ray) (x : D.boundaryPrimes) :
    let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
    let : IsNormalScheme X := (X ↘ S).isNormalScheme_of_smoothOfRelativeDimension_two
    let : SmoothOfRelativeDimension 2 (Z ↘ S) :=
      (Φ.finiteFanScheme_over k).symm ▸
        (((Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)) ▸
          Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k hΦ)
    let : IsNoetherian Z := isNoetherian_of_finiteType (Z ↘ S)
    let := Φ.uniqueFactorizationMonoid_stalk_finiteFanScheme (R := k) hΦ
    let := (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let : IsModification p := isModification_orderedContraction k hΦ b s c hT e
    let ρ := contractedBoundaryRayEmbedding k hΦ b s c p hD
    let classes := rays.map (fun r ↦ cl r)
    (∀ r, r ∈ rays ↔ r ∉ Set.range ρ) →
    (∀ C ∈ (B).orthogonalizeNegOnes classes, (B) C C = -1) →
    ((μ).symm (Additive.ofMul (primeDivisorClass
      ⟨x.val, (mem_boundaryPrimes.mp x.property).2⟩))).val =
      (B).projectOffNegOnes classes (cl (ρ x)) := by
  intro _ _ _ _ _ _ _ ρ classes hrays hsq
  have hspan : Submodule.span ℤ {a | a ∈ classes} = P := by
    rw [markedExceptionalSpan_eq_span_compl_survivingRays k hΦ b s c hT e hD]
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
    k hΦ b s c hT e he hD x)
  rw [hprojection P hspan (isCompl_orthogonal_markedExceptionalSpan k
    hT.isClosedPointTower (hU c) e he)]
  exact hclass

end TauCeti.Toric.Fan
