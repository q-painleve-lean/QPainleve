/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.Basic
public import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
public import QPainleve.Geometry.Toric.Fan.Boundary.Subdivision

import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Class
import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.Reorder
import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.Transport
import QPainleve.AlgebraicGeometry.Scheme.LocalDimension
import QPainleve.Geometry.Toric.Fan.Smooth

/-!
# Section incidence after inserting a toric corner blowup

A toric link can start at a corner outside the projected centers of a given
resolution. Insert the corner blowup, then identify its strict ray divisor with
the corresponding divisor on the reverse blowup. This comparison transports
the incidences at every retained center, including infinitely near centers.
-/

public section

open AlgebraicGeometry CategoryTheory Module TauCeti.AlgebraicGeometry TauCeti.Toric
open QPainleve QPainleve.BlowupTower LineBundleClass Scheme.IdealSheafData

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ Ω : Fan i}

local notation "X[" Δ "]" => Fan.algebraicRealization Δ
local notation "I[" σ "]" => Scheme.Hom.ker (Fan.distinguishedPointHom _ σ)
local notation "pt" => IsLocalRing.closedPoint ℂ

private theorem rayBoundaryPoint_notMem_cornerIdeal
    (hΦ : Φ.IsRegular) (hN : finrank ℤ N = 2) (σ : Φ.cones) (ρ : Φ.Ray) :
    (Φ.rayBoundaryPoint hΦ ρ).val ∉ (I[σ]).support := by
  let f := Φ.algebraicRealizationStructureMap
  let : SmoothOfRelativeDimension 2 f :=
    hN ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  let : IsLocallyNoetherian X[Φ] := LocallyOfFiniteType.isLocallyNoetherian f
  have hp := Φ.isClosed_singleton_distinguishedPoint σ
  rw [(Φ.distinguishedPointHom σ).ker_eq_ker_fromSpecResidueField, ← SetLike.mem_coe,
    Scheme.support_ker_fromSpecResidueField_of_isClosed hp, Set.mem_singleton_iff]
  intro he
  have hc := coheight_eq_of_isClosed_of_smoothOfRelativeDimension (n := 2) f hp
  have hx := (Φ.rayBoundaryPoint hΦ ρ).property
  rw [he, hc] at hx
  norm_num at hx

/-- After a toric link with an inserted corner, each shared ray divisor retains
its strict-transform coefficients at the transported centers. The first
coefficient is minus the order of the new ray divisor at the reverse corner. -/
theorem strictTransformCoefficients_of_prepended_toric_link
    {n : ℕ} {Y W Z : Scheme} {T : BlowupTower X[Φ] n Y}
    (hT : IsClosedPointTower X[Φ] T)
    (hN : finrank ℤ N = 2) (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (hΩ : Ω.IsRegular)
    (σ : Φ.cones) (τ : Ψ.cones) (s : Ω.IsSubdivision Φ) (t : Ω.IsSubdivision Ψ)
    (g : X[Ω] ≅ (I[σ]).blowup) (g' : X[Ω] ≅ (I[τ]).blowup)
    (hg : g.hom ≫ (I[σ]).blowupToBase = s.toFanHom.algebraicMap)
    (hg' : g'.hom ≫ (I[τ]).blowupToBase = t.toFanHom.algebraicMap)
    (ρ : Φ.Ray) (ρ' : Ψ.Ray) (hρ : ρ.primitiveGenerator = ρ'.primitiveGenerator)
    {L : BlowupTower (I[σ]).blowup n W} {U : BlowupTower (I[τ]).blowup n Z}
    (hL : IsClosedPointTower (I[σ]).blowup L) (hU : IsClosedPointTower (I[τ]).blowup U)
    (lift : W ≅ Z) (hLift : IsLift (g.symm ≪≫ g') L U lift)
    {q : Y} (hq : IsClosed ({q} : Set Y))
    (hI : (I[σ]).comap T.toBase = (Y.fromSpecResidueField q).ker)
    (e : ((I[σ]).comap T.toBase).blowup ≅ W)
    (he : e.hom ≫ L.toBase ≫ (I[σ]).blowupToBase =
      ((I[σ]).comap T.toBase).blowupToBase ≫ T.toBase)
    (hE : pullback e.hom (pullback L.toBase (I[σ]).blowupExceptionalClass) =
      ((I[σ]).comap T.toBase).blowupExceptionalClass)
    (hTail : ∀ j, pullback e.hom (L.exceptionalClass j) =
      pullback ((I[σ]).comap T.toBase).blowupToBase (T.exceptionalClass j)) :
    let J := BlowupTower.nil.snoc (I[τ])
    let hJ : IsClosedPointTower X[Ψ] J := .snoc .nil _
      (Ψ.isClosed_singleton_distinguishedPoint τ)
      (Ψ.distinguishedPointHom τ).ker_eq_ker_fromSpecResidueField
    (hJ.append hU).strictTransformCoefficients (Ψ.rayBoundaryIdeal hΨ ρ') =
      Fin.addCases (fun _ : Fin 1 ↦
        -((Ψ.rayBoundaryIdeal hΨ ρ').stalkOrder (Ψ.distinguishedPointHom τ pt)).toNat)
        (hT.strictTransformCoefficients (Φ.rayBoundaryIdeal hΦ ρ)) := by
  intro J hJ
  let D' := Ψ.rayBoundaryIdeal hΨ ρ'
  let f := X[Φ] ↘ Spec (CommRingCat.of ℂ)
  let : Nonempty Φ.cones := ⟨σ⟩
  let : SmoothOfRelativeDimension 2 f := by
    dsimp only [f]
    rw [Φ.algebraicRealization_over]
    exact hN ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  let : IsNoetherian X[Φ] := isNoetherian_of_finiteType f
  let : TauCeti.AlgebraicGeometry.IsRegular (Φ.rayBoundaryIdeal hΦ ρ).subscheme :=
    Φ.isRegular_rayBoundary hΦ ρ
  have hdim : topologicalKrullDim (Φ.rayBoundaryIdeal hΦ ρ).subscheme = 1 := by
    rw [Φ.rayBoundaryIdeal_def hΦ ρ]
    exact QPainleve.topologicalKrullDim_vanishingIdeal_subscheme ℂ
      (topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)) _
  have hstart : IsClosedPointTower X[Φ] (BlowupTower.nil.snoc (I[σ])) :=
    .snoc .nil _ (Φ.isClosed_singleton_distinguishedPoint σ)
      (Φ.distinguishedPointHom σ).ker_eq_ker_fromSpecResidueField
  have hmove := (hT.snoc q hq hI).strictTransformCoefficients_tail_move_to_front f hstart hL e
    (Fin.last n) (by simpa only [toBase_snoc] using he)
    (by simpa only [exceptionalClass_snoc_last, blowupExceptionalClass_def] using hE)
    (fun l ↦ by rw [Fin.succAbove_last_apply, exceptionalClass_snoc_castSucc]; exact hTail l)
    (Φ.isEffectiveCartier_rayBoundaryIdeal hΦ ρ) hdim
  have hsrc := s.comap_ker_blowupMap_rayBoundaryIdeal hΩ hΦ g hg ρ
    (rayBoundaryPoint_notMem_cornerIdeal hΦ hN σ ρ)
  have htgt := t.comap_ker_blowupMap_rayBoundaryIdeal hΩ hΨ g' hg' ρ'
    (rayBoundaryPoint_notMem_cornerIdeal hΨ hN τ ρ')
  have hray : s.liftRay ρ = t.liftRay ρ' := Fan.Ray.primitiveGenerator_injective
    ((s.primitiveGenerator_liftRay ρ).trans (hρ.trans (t.primitiveGenerator_liftRay ρ').symm))
  have hstrict : ((I[τ]).blowupMap D'.subschemeι).ker.comap (g.symm ≪≫ g').hom =
      ((I[σ]).blowupMap (Φ.rayBoundaryIdeal hΦ ρ).subschemeι).ker := by
    rw [Iso.trans_hom, Iso.symm_hom, comap_comp, htgt, ← hray, ← hsrc, ← comap_comp,
      Iso.inv_hom_id, comap_id]
  have hcoeff := hLift.strictTransformCoefficients_eq hL hU ((I[τ]).blowupMap D'.subschemeι).ker
  rw [hstrict, hmove] at hcoeff
  funext j
  refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) j
  · rw [strictTransformCoefficients_append_castAdd hJ hU, Fin.addCases_left]
    have hk : k = Fin.last 0 := Fin.ext (by omega)
    subst k
    rw [strictTransformCoefficients_snoc_last _ hJ _ (Ψ.isClosed_singleton_distinguishedPoint τ)
      (Ψ.distinguishedPointHom τ).ker_eq_ker_fromSpecResidueField, strictTransform_nil]
  · rw [strictTransformCoefficients_append_natAdd hJ hU, strictTransform_snoc, strictTransform_nil,
      Fin.addCases_right]
    simpa only [Function.comp_apply, Fin.succAbove_last_apply,
      strictTransformCoefficients_snoc_castSucc] using congrFun hcoeff.symm k

end QPainleve.BlowupTower.IsClosedPointTower
