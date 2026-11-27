/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Period.Restriction

/-!
# Transporting the toric presentation for the boundary period

The ordered internal blowup and the tower formed along the embedded boundary
have the same Picard pullback coordinates and boundary projection.
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable (K : Type) [Field K] [PerfectField K]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones] {r : ℕ}
  (b : Module.Basis (Fin 2) ℤ N) (s : Fin r → Φ.Ray) (hΦ : Φ.IsRegular)
  (c : Multiplicative (Fin r → ℤ) →* Kˣ)

local notation "center" t:arg => (fun j : Fin r ↦ t (ofAdd (Pi.single j 1)))
local notation "J[" t "]" =>
  (fun j : Fin r ↦ Ray.internalCenter K b (s j) (t (ofAdd (Pi.single j 1))))
local notation "M" t:arg => internalBlowupTower K b s (center t)
local notation "π" t:arg => toBase (WithBoundary.toTower (Sigma.snd (M t)))
local notation "ι" t:arg => WithBoundary.boundaryι (Sigma.snd (M t))
local notation "mark" t:arg => internalBlowupPicardMarking K b s (center t) hΦ
local notation "Dtor" => Scheme.IdealSheafData.subscheme (Φ.toricBoundaryIdeal K h₀)

local notation "Dideal" => Φ.toricBoundaryIdeal K h₀
local notation "base" => (Φ.finiteFanSchemeToSpec K)
local notation "rankTwo" => (Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2))
local notation "smoothBase" => cast (congrArg (fun n ↦ SmoothOfRelativeDimension n base) rankTwo)
    (Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec K hΦ)
local notation "model[" t "]" => alongBoundary (subschemeι Dideal) (J[t])
local notation "hModel[" t "]" => isClosedPointTower_alongBoundary_binomialCenters K
  rankTwo s (fun j ↦ LinearMap.toAddMonoidHom (b.detDualEquiv (Ray.primitiveGenerator (s j))))
    (fun j ↦ b.detDualEquiv_self (Ray.primitiveGenerator (s j)))
    (fun j ↦ Ray.surjective_detCharacter (s j) b) (center t) (J[t])
    (fun j ↦ Ray.internalCenter_val K b (s j) (t (ofAdd (Pi.single j 1))))

/-- Transport the specified contraction and its Picard coordinates to the presentation
used to define the marked boundary period. -/
theorem exists_period_presentation
    {X W : Scheme} [X.Over (Spec (.of K))] {D : X.IdealSheafData}
    {l : ℕ} {P : BlowupTower X l W} (e : W ≅ (M c).1)
    (he : e.inv ≫ P.toBase ≫ X ↘ Spec (.of K) = π c ≫ base)
    (hD : ((D.comap P.toBase).comap e.inv).support = (ι c).ker.support)
    (f : Dtor ⟶ D.subscheme) (hf : f ≫ D.subschemeι = ι c ≫ e.inv ≫ P.toBase) :
    letI : SmoothOfRelativeDimension 2 base := smoothBase
    ∃ (a : W ≅ (model[c]).1)
      (_ : a.inv ≫ P.toBase ≫ X ↘ Spec (.of K) =
        (model[c]).2.toTower.toBase ≫ ((Φ.finiteFanScheme K) ↘ Spec (.of K)))
      (ha : ((D.comap P.toBase).comap a.inv).support = (model[c]).2.boundaryι.ker.support),
      f = toricBoundaryToBase K (J[c]) a ha ∧
      ∀ L : LineBundleClass X,
        ((model[c]).2.toTower.picardMarking (hModel[c]) base).symm
          (Additive.ofMul (pullback (a.inv ≫ P.toBase) L)) =
        (mark c).symm (Additive.ofMul (pullback (e.inv ≫ P.toBase) L)) := by
  let : SmoothOfRelativeDimension 2 base := smoothBase
  have transport (U V : Σ Z, WithBoundary (subschemeι Dideal) r Z) (h : U = V)
      (hU : IsClosedPointTower (Φ.finiteFanScheme K) U.2.toTower)
      (hV : IsClosedPointTower (Φ.finiteFanScheme K) V.2.toTower) (i : W ≅ U.1)
      (hi : i.inv ≫ P.toBase ≫ X ↘ Spec (.of K) = U.2.toTower.toBase ≫ base)
      (hs : ((D.comap P.toBase).comap i.inv).support = U.2.boundaryι.ker.support)
      (hf' : f ≫ D.subschemeι = U.2.boundaryι ≫ i.inv ≫ P.toBase) :
      ∃ (a : W ≅ V.1),
        (a.inv ≫ P.toBase ≫ X ↘ Spec (.of K) = V.2.toTower.toBase ≫ base) ∧
        (((D.comap P.toBase).comap a.inv).support = V.2.boundaryι.ker.support) ∧
        (f ≫ D.subschemeι = V.2.boundaryι ≫ a.inv ≫ P.toBase) ∧
        ∀ L : LineBundleClass X,
          (V.2.toTower.picardMarking hV base).symm
            (Additive.ofMul (pullback (a.inv ≫ P.toBase) L)) =
          (U.2.toTower.picardMarking hU base).symm
            (Additive.ofMul (pullback (i.inv ≫ P.toBase) L)) := by
    subst V
    exact ⟨i, hi, hs, hf', fun _ ↦ rfl⟩
  obtain ⟨a, ha, hs, hb, hm⟩ := transport (M c) (model[c])
    (internalBlowupTower_eq_alongBoundary K b s (center c))
    (isClosedPointTower_internalBlowupTower K b s (center c)) (hModel[c]) e he hD hf
  have hmark :
      (M c).2.toTower.picardMarking (isClosedPointTower_internalBlowupTower K b s (center c)) base =
        mark c := by
    ext z : 1
    rw [picardMarking_apply, internalBlowupPicardMarking_apply]
  refine ⟨a, ?_, hs, ?_, fun L ↦ (hm L).trans ?_⟩
  · rw [finiteFanScheme_over]
    exact ha
  · apply (cancel_mono D.subschemeι).mp
    rw [toricBoundaryToBase_comp_subschemeι]
    exact hb
  · rw [hmark]

end TauCeti.Toric.Fan
