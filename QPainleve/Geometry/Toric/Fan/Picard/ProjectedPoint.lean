/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import QPainleve.AlgebraicGeometry.Blowup.Tower.ProjectedPoint
public import QPainleve.Geometry.Toric.Fan.Boundary.InternalCenter
public import QPainleve.Geometry.Toric.Fan.Smooth

import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.Geometry.Toric.Fan.Boundary.Subdivision
import TauCeti.AlgebraicGeometry.RationalPoint.Basic

/-!
# Base orders at retained binomial centers

A common toric subdivision identifies the binomial points of a retained ray on
two regular projective surfaces. On a point resolution through that subdivision,
the first blowups
above these points then have the same total exceptional class and base order.
This is the point-order comparison on the retained fiber in the Hirzebruch
preparation of [Lutz, Proposition 8.11, Case C](https://arxiv.org/abs/2005.05010v3).
-/

public section

open AlgebraicGeometry CategoryTheory Module QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry TauCeti.Toric LineBundleClass Scheme.IdealSheafData

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {Φ Ψ Ω : Fan i} [Nonempty Φ.cones] [Nonempty Ψ.cones]

local notation "X[" A "]" => Fan.algebraicRealization A
local notation "π[" H "]" => FanHom.algebraicMap (Fan.IsSubdivision.toFanHom H)
local notation "S" => Spec (CommRingCat.of ℂ)
local notation "f[" A "]" => (X[A] ↘ S)
local notation "rankTwo(" b ")" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "center(" b "," ρ "," c ")" => Fan.Ray.binomialCenter ρ rankTwo(b)
  (Module.Basis.detDualEquiv_self b (Fan.Ray.primitiveGenerator ρ))
  (Fan.Ray.surjective_detCharacter ρ b) c
local notation "pt(" b "," ρ "," c ")" => center(b,ρ,c) (IsLocalRing.closedPoint ℂ)

variable {Y Z : Scheme} {n m r : ℕ}
  {T : BlowupTower X[Φ] n Y} {R : BlowupTower Y r Z} {U : BlowupTower X[Ψ] m Z}
  [X[Φ].IsProjectiveOver ℂ] [X[Ψ].IsProjectiveOver ℂ]

/-- A binomial point on a common ray of two smooth projective toric surfaces
retains its base order when the specified resolution is refined by a point tower
and then compared to a second resolution through a common subdivision. The
exceptional classes compared on the refinement are total transforms of the first
blowups over the binomial point on each side. The numerical comparison applies
to the negative exceptional coefficient of any pulled-back line bundle. -/
theorem base_order_eq_of_common_subdivision (hT : IsClosedPointTower X[Φ] T)
    (hR : IsClosedPointTower Y R) (hU : IsClosedPointTower X[Ψ] U)
    (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)
    (H : Ω.IsSubdivision Φ) (K : Ω.IsSubdivision Ψ) (g : Z ⟶ X[Ω])
    (hg : g ≫ π[H] = R.toBase ≫ T.toBase) (hg' : g ≫ π[K] = U.toBase)
    (b : Basis (Fin 2) ℤ N) (ρ : Φ.Ray) (τ : Ψ.Ray)
    (hρ : ρ.primitiveGenerator = τ.primitiveGenerator) (c : ℂˣ)
    (j : Fin n) (hj : hT.baseCenter j = pt(b,ρ,c))
    (hfirst : ∀ l < j, hT.baseCenter l ≠ pt(b,ρ,c)) (L : LineBundleClass Y) :
    let : SmoothOfRelativeDimension 2 f[Φ] := by
      rw [Fan.algebraicRealization_over]
      exact rankTwo(b) ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : SmoothOfRelativeDimension 2 f[Ψ] := by
      rw [Fan.algebraicRealization_over]
      exact rankTwo(b) ▸ Ψ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΨ
    let : IsNoetherian X[Φ] := isNoetherian_of_finiteType f[Φ]
    let : IsNoetherian X[Ψ] := isNoetherian_of_finiteType f[Ψ]
    let a := (T.picardMarking hT f[Φ]).symm (Additive.ofMul L)
    let a' := (U.picardMarking hU f[Ψ]).symm (Additive.ofMul (pullback R.toBase L))
    ∃ j' : Fin m, hU.baseCenter j' = pt(b,τ,c) ∧ (∀ l < j', hU.baseCenter l ≠ pt(b,τ,c)) ∧
      pullback R.toBase (T.exceptionalClass j) = U.exceptionalClass j' ∧ -a.2 j = -a'.2 j' := by
  intro hdim hdim' hN hN' a a'
  let := hdim
  let := hdim'
  let := hN
  let := hN'
  have hker {A : Fan i} (J : Ω.IsSubdivision A) (r : A.Ray) :
      (center(b,r,c)).ker.comap π[J] = (center(b,J.liftRay r,c)).ker := by
    have hpb : IsPullback center(b,J.liftRay r,c) (𝟙 S) π[J] center(b,r,c) := by
      simpa only [J.primitiveGenerator_liftRay] using
        J.isPullback_binomialCenter r rankTwo(b)
          (m := (b.detDualEquiv r.primitiveGenerator).toAddMonoidHom)
          (b.detDualEquiv_self _) (r.surjective_detCharacter b) c
    have := r.isClosedImmersion_binomialCenter rankTwo(b) (b.detDualEquiv_self _)
      (r.surjective_detCharacter b) c
    exact (ker_eq_comap_of_isPullback _ hpb).symm
  have hray : H.liftRay ρ = K.liftRay τ := Fan.Ray.primitiveGenerator_injective
    ((H.primitiveGenerator_liftRay ρ).trans (hρ.trans (K.primitiveGenerator_liftRay τ).symm))
  have hI : (center(b,ρ,c)).ker.comap (R.toBase ≫ T.toBase) =
      (center(b,τ,c)).ker.comap U.toBase := by
    rw [← hg, ← hg', comap_comp, comap_comp, hker H ρ, hker K τ, hray]
  rw [(center(b,ρ,c)).ker_eq_ker_fromSpecResidueField,
    (center(b,τ,c)).ker_eq_ker_fromSpecResidueField] at hI
  have hOver : (T.append R).toBase ≫ f[Φ] = U.toBase ≫ f[Ψ] := by
    rw [toBase_append, Fan.algebraicRealization_over, Fan.algebraicRealization_over,
      ← hg, ← hg', Category.assoc, Category.assoc,
      FanHom.algebraicMap_comp_algebraicRealizationStructureMap,
      FanHom.algebraicMap_comp_algebraicRealizationStructureMap]
  have hClosed {A : Fan i} (r : A.Ray) : IsClosed ({pt(b,r,c)} : Set X[A]) :=
    isClosed_singleton_of_section
      (r.binomialCenter_comp_structureMap rankTwo(b) (b.detDualEquiv_self _)
        (r.surjective_detCharacter b) c)
  have hj' := (baseCenter_append_castAdd hT hR j).trans hj
  have hfirst' (l : Fin (n + r)) (hl : l < j.castAdd r) :
      (hT.append hR).baseCenter l ≠ pt(b,ρ,c) := by
    have hlN : l.val < n := (Fin.lt_def.mp hl).trans j.isLt
    rw [← Fin.castAdd_castLT r l hlN, baseCenter_append_castAdd hT hR]
    exact hfirst _ (Fin.lt_def.mpr (Fin.lt_def.mp hl))
  rw [← toBase_append] at hI
  obtain ⟨j', hj'', hfirst'', hC, horder⟩ :=
    (hT.append hR).base_order_eq_of_comap_point_ideal_eq (k := ℂ) hU hOver
      (hClosed ρ) (hClosed τ) hI (j.castAdd r) hj' hfirst' (pullback R.toBase L)
  simp only [hT.picardMarking_symm_pullback_append hR f[Φ] L, Fin.append_left] at horder
  exact ⟨j', hj'', hfirst'', (exceptionalClass_append_castAdd T R j).symm.trans hC, horder⟩

end QPainleve.BlowupTower.IsClosedPointTower
