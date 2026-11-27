/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.InternalBlowup
public import QPainleve.Geometry.Toric.Fan.Logarithmic.StarFactorization

import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.Ramification
import QPainleve.AlgebraicGeometry.IdealSheaf.ClosedImmersion
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.Geometry.Toric.Fan.Boundary.Node
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition

/-!
# Logarithmic projections of ordered internal blowups

The specified projection from an ordered internal blowup model pulls back the toric
boundary to the strict boundary times the ramification ideal. This applies to repeated
centers because each blowup uses the point on the current strict boundary. The resulting
projection can serve as an endpoint for a resolved Sarkisov factorization.

See [Lutz, Definition 8.1 and Theorem 8.4][HKL] for the pole condition and its use
in the factorization of a specified birational map.

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=68
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

universe u

variable (K : Type u) [Field K] [PerfectField K] {N V : Type u}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones]
  (b : Module.Basis (Fin 2) ℤ N) {n : ℕ} (s : Fin n → Φ.Ray) (c : Fin n → Kˣ)

local notation "S" => Spec (CommRingCat.of K)
local notation "D" => Φ.toricBoundaryIdeal K h₀
local notation "U" => internalBlowupTower K b s c
local notation "π" => toBase (WithBoundary.toTower (Sigma.snd U))
local notation "closedTower" => isClosedPointTower_internalBlowupTower K b s c
local notation "base" => Φ.finiteFanSchemeToSpec K
local notation "rankTwo" => (Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2))

/-- The total transform of the toric boundary is the strict boundary times the
ramification ideal of the specified ordered blowdown. The center parameters may repeat. -/
theorem comap_boundaryIdeal_internalBlowupTower
    (hΦ : Φ.IsRegular) (hcart : (D).IsEffectiveCartier) :
    letI : SmoothOfRelativeDimension 2 (Φ.finiteFanScheme K ↘ S) := by
      rw [finiteFanScheme_over K]
      exact rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec K hΦ
    (D).comap π = (U).2.boundaryι.ker *
      (isClosedPointTower_internalBlowupTower K b s c).ramificationIdealSheafToBase K := by
  classical
  have : SmoothOfRelativeDimension 2 base :=
    rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec K hΦ
  have : Smooth base := SmoothOfRelativeDimension.smooth 2 _
  have : SmoothOfRelativeDimension 2 (Φ.finiteFanScheme K ↘ S) := by
    rwa [finiteFanScheme_over K]
  have : IsNoetherian (Φ.finiteFanScheme K) := isNoetherian_of_finiteType base
  -- Quantify over the tower witness so the equality transports its dependent type.
  let HasPoleFactorization (A : Σ Y, WithBoundary (D).subschemeι n Y) :=
    ∀ h : IsClosedPointTower (Φ.finiteFanScheme K) A.2.toTower,
      (D).comap A.2.toTower.toBase = A.2.boundaryι.ker * h.ramificationIdealSheafToBase K
  refine (congrArg HasPoleFactorization (internalBlowupTower_eq_alongBoundary K b s c)).mpr ?_
    (isClosedPointTower_internalBlowupTower K b s c)
  intro hT
  let J (j : Fin n) := (s j).internalCenter K b (c j)
  have hpoints (j : Fin n) : ∃ p : (D).subscheme, IsClosed ({p} : Set (D).subscheme) ∧
      (J j).val = ((D).subscheme.fromSpecResidueField p).ker := by
    simpa only [J, Ray.internalCenter_val] using
      (s j).exists_closedPoint_ker_binomialCenterOnBoundary K rankTwo
        (b.detDualEquiv_self _) ((s j).surjective_detCharacter b) (c j)
  choose p hp hJ using hpoints
  have hreg (j : Fin n) : IsRegularLocalRing ((D).subscheme.presheaf.stalk (p j)) := by
    apply (s j).isRegularLocalRing_stalk_of_mem_support_internalCenter K b (c j)
    rw [hJ, ← SetLike.mem_coe, Scheme.support_ker_fromSpecResidueField_of_isClosed (hp j)]
    exact Set.mem_singleton _
  have he (j : Fin n) : ((J j).val.comap (𝟙 (D).subscheme)).IsEffectiveCartier := by
    simpa only [comap_id] using (J j).property
  have hι : ((𝟙 (D).subscheme) ≫ (D).subschemeι).ker.IsEffectiveCartier := by
    simpa only [Category.id_comp, ker_subschemeι] using hcart
  have hreg' (j : Fin n) (q : (D).subscheme) (hq : (𝟙 (D).subscheme) q = p j) :
      IsRegularLocalRing ((D).subscheme.presheaf.stalk q) := by
    rw [Scheme.Hom.id_base, TopCat.coe_id, id_eq] at hq
    exact hq ▸ hreg j
  have hcoeff := strictTransformCoefficients_alongBoundary (D).subschemeι (𝟙 (D).subscheme) base J p
    hp hJ he hreg' hι hT
  have hstrict := strictTransform_ker_comp_alongBoundary (D).subschemeι (𝟙 (D).subscheme) J he
  simp only [Category.id_comp, ker_subschemeι] at hstrict hcoeff
  simp only [Scheme.Hom.id_base, TopCat.coe_id, Set.range_id, Set.mem_univ, ite_true] at hcoeff
  exact (hT.comap_eq_strictTransform_mul_ramification_of_coefficients_eq_neg_one
    hcart (congrFun hcoeff)).trans (congrArg (· * hT.ramificationIdealSheafToBase K) hstrict)

/-- Ordered internal blowups preserve the anticanonical boundary. The ideal of
the strict boundary represents the canonical class if the original boundary ideal does. -/
theorem canonicalClass_internalBlowupTower (hΦ : Φ.IsRegular) (hD : (D).IsEffectiveCartier)
    (hStrict : (U).2.boundaryι.ker.IsEffectiveCartier) :
    letI : SmoothOfRelativeDimension 2 (Φ.finiteFanScheme K ↘ S) := by
      rw [finiteFanScheme_over K]
      exact rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec K hΦ
    letI : (U).1.Over S := ⟨π ≫ (Φ.finiteFanScheme K ↘ S)⟩
    letI : SmoothOfRelativeDimension 2 ((U).1 ↘ S) :=
      (closedTower).smoothOfRelativeDimension (Φ.finiteFanScheme K ↘ S)
    LineBundleClass.mk hD.toInvertibleSheaf =
        LineBundleClass.mk (QPainleve.canonicalBundle K (Φ.finiteFanScheme K) 2) →
      LineBundleClass.mk hStrict.toInvertibleSheaf =
        LineBundleClass.mk (QPainleve.canonicalBundle K (U).1 2) := by
  intro hK
  have : SmoothOfRelativeDimension 2 (Φ.finiteFanScheme K ↘ S) := by
    rw [finiteFanScheme_over K]
    exact rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec K hΦ
  let : (U).1.Over S := ⟨π ≫ (Φ.finiteFanScheme K ↘ S)⟩
  let : SmoothOfRelativeDimension 2 ((U).1 ↘ S) :=
    (closedTower).smoothOfRelativeDimension (Φ.finiteFanScheme K ↘ S)
  let : (π).IsOver S := ⟨rfl⟩
  let : Smooth (Φ.finiteFanScheme K ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : IsNoetherian (Φ.finiteFanScheme K) := isNoetherian_of_finiteType
    (Φ.finiteFanScheme K ↘ S)
  let hRam := (closedTower).isEffectiveCartier_ramificationIdealSheafToBase K
  let hTot := (closedTower).isEffectiveCartier_totalTransform (Φ.finiteFanScheme K ↘ S) hD
  have hI := comap_boundaryIdeal_internalBlowupTower K b s c hΦ hD
  have hPic : LineBundleClass.pullback π (LineBundleClass.mk hD.toInvertibleSheaf) =
      LineBundleClass.mk hStrict.toInvertibleSheaf * LineBundleClass.mk hRam.toInvertibleSheaf := by
    rw [hD.pullback_mk_toInvertibleSheaf hTot,
      LineBundleClass.mk_toInvertibleSheaf_congr hTot
        (TauCeti.isEffectiveCartier_mul hStrict hRam) hI,
      LineBundleClass.mk_toInvertibleSheaf_mul]
  have hR := (closedTower).ramificationIdealSheafToBase_def K
  have hK' := QPainleve.mk_canonicalBundle_eq_pullback_mul_inv_ramification K π 2 (hR ▸ hRam)
  rw [← LineBundleClass.mk_toInvertibleSheaf_congr hRam _ hR, ← hK, hPic,
    mul_inv_cancel_right] at hK'
  exact hK'.symm

variable {Z : Scheme.{u}} {P : Z.IdealSheafData}

omit [PerfectField K] in
/-- An ideal with the same support as the strict boundary of an ordered internal
model has the pulled-back strict boundary ideal as its radical. -/
theorem radical_eq_comap_internalBlowupBoundary_of_support_eq
    (e : Z ≅ (U).1) (hP : P.support = ((U).2.boundaryι.ker.comap e.hom).support) :
    P.radical = (U).2.boundaryι.ker.comap e.hom := by
  have hker : ((U).2.boundaryι ≫ e.inv).ker = (U).2.boundaryι.ker.comap e.hom := by
    rw [← Scheme.Hom.comap_ker_comp_of_isClosedImmersion ((U).2.boundaryι ≫ e.inv) e.hom,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← vanishingIdeal_support, hP, ← hker]
  exact (Scheme.Hom.ker_eq_vanishingIdeal_support ((U).2.boundaryι ≫ e.inv)).symm

variable [Z.Over (Spec (.of K))] [SmoothOfRelativeDimension 2 (Z ↘ Spec (.of K))]

/-- A resolving surface identified with an ordered internal model has a logarithmic
projection to the original fan. Any ideal with the support of the strict boundary
gives the pole ideal by taking its radical. -/
theorem exists_internalBlowupLogarithmicProjection (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (e : Z ≅ (U).1) (he : e.hom ≫ π ≫ base = Z ↘ S)
    (hP : P.support = ((U).2.boundaryι.ker.comap e.hom).support) :
    ∃ A : LogarithmicProjection K i P.radical,
      A.fan = Φ ∧ A.hom ≍ e.hom ≫ π ∧ IsModification A.hom := by
  let g := e.hom ≫ π
  have : g.IsOver S := ⟨by simpa only [g, finiteFanScheme_over K, Category.assoc] using he⟩
  have : IsModification π := isModification_internalBlowupTower_toBase K b s c hΦ
  have : IsModification g := inferInstanceAs (IsModification (e.hom ≫ π))
  refine ⟨⟨Φ, hΦ, hc, g, inferInstance, inferInstance, ?_⟩, rfl, HEq.rfl, ‹IsModification g›⟩
  have : SmoothOfRelativeDimension 2 (Φ.finiteFanScheme K ↘ S) := by
    rw [finiteFanScheme_over K]
    exact rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec K hΦ
  have hpole := radical_eq_comap_internalBlowupBoundary_of_support_eq K b s c e hP
  let hT := isClosedPointTower_internalBlowupTower K b s c
  have hram := hT.comap_ramificationIdealSheafToBase K e (f := g) rfl
  have ht := congrArg (fun I : (U).1.IdealSheafData ↦ I.comap e.hom)
    (comap_boundaryIdeal_internalBlowupTower K b s c hΦ
      (Φ.isEffectiveCartier_boundaryIdeal K hΦ hc rankTwo))
  simpa only [g, comap_mul, ← comap_comp, ← hpole, hram] using ht

end TauCeti.Toric.Fan
