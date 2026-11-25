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
two regular projective surfaces. On a resolution through that subdivision,
the first blowups above these points have the same total exceptional class and base order.
If the original resolution was refined by more blowups, each added coordinate has order zero.
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

variable {Y W Z : Scheme} {n m r : ℕ}
  {T : BlowupTower X[Φ] n Y} {R : BlowupTower Y r W} {U : BlowupTower X[Ψ] m Z}
  [X[Φ].IsProjectiveOver ℂ] [X[Ψ].IsProjectiveOver ℂ]

-- The point ideals agree on the common subdivision, so the comparison also
-- applies with the two resolutions interchanged.
private theorem first_base_order_eq_of_common_subdivision
    (hT : IsClosedPointTower X[Φ] T) (hU : IsClosedPointTower X[Ψ] U)
    (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)
    (e : Y ≅ Z) (H : Ω.IsSubdivision Φ) (K : Ω.IsSubdivision Ψ) (g : Y ⟶ X[Ω])
    (hg : g ≫ π[H] = T.toBase) (hg' : g ≫ π[K] = e.hom ≫ U.toBase)
    (b : Basis (Fin 2) ℤ N) (ρ : Φ.Ray) (τ : Ψ.Ray)
    (hρ : ρ.primitiveGenerator = τ.primitiveGenerator) (c : ℂˣ)
    (j : Fin n) (hj : hT.baseCenter j = pt(b,ρ,c))
    (hfirst : ∀ l < j, hT.baseCenter l ≠ pt(b,ρ,c)) (L : LineBundleClass Y) :
    let : SmoothOfRelativeDimension 2 f[Φ] :=
      rankTwo(b) ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : SmoothOfRelativeDimension 2 f[Ψ] :=
      rankTwo(b) ▸ Ψ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΨ
    let : IsNoetherian X[Φ] := isNoetherian_of_finiteType f[Φ]
    let : IsNoetherian X[Ψ] := isNoetherian_of_finiteType f[Ψ]
    let a := (T.picardMarking hT f[Φ]).symm (Additive.ofMul L)
    let a' := (U.picardMarking hU f[Ψ]).symm (Additive.ofMul (pullback e.inv L))
    ∃ j' : Fin m, hU.baseCenter j' = pt(b,τ,c) ∧ (∀ l < j', hU.baseCenter l ≠ pt(b,τ,c)) ∧
      T.exceptionalClass j = pullback e.hom (U.exceptionalClass j') ∧ -a.2 j = -a'.2 j' := by
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
  have hI : (center(b,ρ,c)).ker.comap T.toBase =
      (center(b,τ,c)).ker.comap (e.hom ≫ U.toBase) := by
    rw [← hg, ← hg', comap_comp, comap_comp, hker H ρ, hker K τ, hray]
  rw [(center(b,ρ,c)).ker_eq_ker_fromSpecResidueField,
    (center(b,τ,c)).ker_eq_ker_fromSpecResidueField] at hI
  have hOver : e.hom ≫ U.toBase ≫ f[Ψ] = T.toBase ≫ f[Φ] := by
    rw [Fan.algebraicRealization_over, Fan.algebraicRealization_over,
      ← hg, ← Category.assoc e.hom, ← hg', Category.assoc, Category.assoc,
      FanHom.algebraicMap_comp_algebraicRealizationStructureMap,
      FanHom.algebraicMap_comp_algebraicRealizationStructureMap]
  have hClosed {A : Fan i} (r : A.Ray) : IsClosed ({pt(b,r,c)} : Set X[A]) :=
    isClosed_singleton_of_section
      (r.binomialCenter_comp_structureMap rankTwo(b) (b.detDualEquiv_self _)
        (r.surjective_detCharacter b) c)
  exact hT.base_order_eq_of_comap_point_ideal_eq (k := ℂ) hU e hOver
    (hClosed ρ) (hClosed τ) hI j hj hfirst L

/-- A binomial point on a common ray of two smooth projective toric surfaces
retains its base order when the specified resolution is refined by a point tower
and then compared to a second resolution through a common subdivision. The
exceptional classes compared on the refinement are total transforms of the first
blowups over the binomial point on each side. The numerical comparison applies
to the negative exceptional coefficient of any pulled-back line bundle. -/
theorem base_order_eq_of_common_subdivision (hT : IsClosedPointTower X[Φ] T)
    (hR : IsClosedPointTower Y R) (hU : IsClosedPointTower X[Ψ] U)
    (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)
    (e : W ≅ Z) (H : Ω.IsSubdivision Φ) (K : Ω.IsSubdivision Ψ) (g : W ⟶ X[Ω])
    (hg : g ≫ π[H] = R.toBase ≫ T.toBase) (hg' : g ≫ π[K] = e.hom ≫ U.toBase)
    (b : Basis (Fin 2) ℤ N) (ρ : Φ.Ray) (τ : Ψ.Ray)
    (hρ : ρ.primitiveGenerator = τ.primitiveGenerator) (c : ℂˣ)
    (j : Fin n) (hj : hT.baseCenter j = pt(b,ρ,c))
    (hfirst : ∀ l < j, hT.baseCenter l ≠ pt(b,ρ,c)) (L : LineBundleClass Y) :
    let : SmoothOfRelativeDimension 2 f[Φ] :=
      rankTwo(b) ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : SmoothOfRelativeDimension 2 f[Ψ] :=
      rankTwo(b) ▸ Ψ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΨ
    let : IsNoetherian X[Φ] := isNoetherian_of_finiteType f[Φ]
    let : IsNoetherian X[Ψ] := isNoetherian_of_finiteType f[Ψ]
    let a := (T.picardMarking hT f[Φ]).symm (Additive.ofMul L)
    let a' := (U.picardMarking hU f[Ψ]).symm (Additive.ofMul (pullback (e.inv ≫ R.toBase) L))
    ∃ j' : Fin m, hU.baseCenter j' = pt(b,τ,c) ∧ (∀ l < j', hU.baseCenter l ≠ pt(b,τ,c)) ∧
      pullback R.toBase (T.exceptionalClass j) = pullback e.hom (U.exceptionalClass j') ∧
      -a.2 j = -a'.2 j' := by
  intro hdim hdim' hN hN' a a'
  let := hdim
  let := hdim'
  let := hN
  let := hN'
  have hj' := (baseCenter_append_castAdd hT hR j).trans hj
  have hfirst' (l : Fin (n + r)) (hl : l < j.castAdd r) :
      (hT.append hR).baseCenter l ≠ pt(b,ρ,c) := by
    have hlN : l.val < n := (Fin.lt_def.mp hl).trans j.isLt
    rw [← Fin.castAdd_castLT r l hlN, baseCenter_append_castAdd hT hR]
    exact hfirst _ (Fin.lt_def.mpr (Fin.lt_def.mp hl))
  obtain ⟨j', hj'', hfirst'', hC, horder⟩ :=
    first_base_order_eq_of_common_subdivision (hT.append hR) hU hΦ hΨ e H K g
      (hg.trans (toBase_append T R).symm) hg' b ρ τ hρ c (j.castAdd r) hj' hfirst'
      (pullback R.toBase L)
  simp only [hT.picardMarking_symm_pullback_append hR f[Φ] L, Fin.append_left,
    pullback_comp] at horder
  exact ⟨j', hj'', hfirst'', (exceptionalClass_append_castAdd T R j).symm.trans hC, horder⟩

/-- Over a binomial point on a common ray, the first order in the target
resolution is either zero or agrees with the first order over the corresponding
point in the original source tower. This also applies when the common resolution
was obtained by further blowups of the source resolution. -/
theorem base_order_eq_zero_or_exists_of_common_subdivision (hT : IsClosedPointTower X[Φ] T)
    (hR : IsClosedPointTower Y R) (hU : IsClosedPointTower X[Ψ] U)
    (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)
    (e : W ≅ Z) (H : Ω.IsSubdivision Φ) (K : Ω.IsSubdivision Ψ) (g : W ⟶ X[Ω])
    (hg : g ≫ π[H] = R.toBase ≫ T.toBase) (hg' : g ≫ π[K] = e.hom ≫ U.toBase)
    (b : Basis (Fin 2) ℤ N) (ρ : Φ.Ray) (τ : Ψ.Ray)
    (hρ : ρ.primitiveGenerator = τ.primitiveGenerator) (c : ℂˣ)
    (j : Fin m) (hj : hU.baseCenter j = pt(b,τ,c))
    (hfirst : ∀ l < j, hU.baseCenter l ≠ pt(b,τ,c)) (L : LineBundleClass Y) :
    let : SmoothOfRelativeDimension 2 f[Φ] :=
      rankTwo(b) ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : SmoothOfRelativeDimension 2 f[Ψ] :=
      rankTwo(b) ▸ Ψ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΨ
    let : IsNoetherian X[Φ] := isNoetherian_of_finiteType f[Φ]
    let : IsNoetherian X[Ψ] := isNoetherian_of_finiteType f[Ψ]
    let a := (T.picardMarking hT f[Φ]).symm (Additive.ofMul L)
    let a' := (U.picardMarking hU f[Ψ]).symm (Additive.ofMul (pullback (e.inv ≫ R.toBase) L))
    a'.2 j = 0 ∨
      ∃ l : Fin n, hT.baseCenter l = pt(b,ρ,c) ∧ (∀ k < l, hT.baseCenter k ≠ pt(b,ρ,c)) ∧
        -a'.2 j = -a.2 l := by
  intro hdim hdim' hN hN' a a'
  let := hdim
  let := hdim'
  let := hN
  let := hN'
  have hK : (e.inv ≫ g) ≫ π[K] = U.toBase := by
    rw [Category.assoc, hg', Iso.inv_hom_id_assoc]
  have hH : (e.inv ≫ g) ≫ π[H] = e.inv ≫ (T.append R).toBase := by
    rw [Category.assoc, hg, toBase_append]
  obtain ⟨l, hl, hfirst', -, horder⟩ :=
    first_base_order_eq_of_common_subdivision hU (hT.append hR) hΨ hΦ e.symm K H
      (e.inv ≫ g) hK hH b τ ρ hρ.symm c j hj hfirst (pullback (e.inv ≫ R.toBase) L)
  simp only [Iso.symm_inv, pullback_comp, Iso.hom_inv_id_assoc,
    hT.picardMarking_symm_pullback_append hR f[Φ] L] at horder
  -- The coordinates of all steps added on the source resolution are zero.
  refine Fin.addCases (fun k hk hmin hord ↦ Or.inr ⟨k, ?_, ?_, ?_⟩)
    (fun k _ _ hord ↦ Or.inl (by simpa using hord)) l hl hfirst' horder
  · exact (baseCenter_append_castAdd hT hR k).symm.trans hk
  · intro t ht
    have ht' : t.castAdd r < k.castAdd r := by simpa only [Fin.lt_def, Fin.val_castAdd] using ht
    rw [← baseCenter_append_castAdd hT hR t]
    exact hmin _ ht'
  · simpa only [Fin.append_left] using hord

end QPainleve.BlowupTower.IsClosedPointTower
