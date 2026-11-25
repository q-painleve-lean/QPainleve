/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Basic
public import QPainleve.Geometry.Toric.Fan.Subdivision
public import QPainleve.Geometry.Toric.Fan.Subdivision.InternalBlowup

import QPainleve.Geometry.Toric.Fan.Picard.Subdivision
import QPainleve.Geometry.Toric.Fan.Subdivision.NodalRefinement

/-!
# Specified nodal refinements of ordered toric models

A nodal tower on an ordered internal blowup model is induced by a subdivision of the
model's toric fan. Each successive center lies above a node of the current toric boundary,
where the internal blowdown is a local isomorphism. The cartesian comparison preserves the
ordered internal centers and their total exceptional classes, including at repeated centers.

For the use of nodal refinements in comparing toric presentations, see
[Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*, §1][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S1
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower
open Scheme.IdealSheafData TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [hΦ₀ : Nonempty Φ.cones]
  (b : Module.Basis (Fin 2) ℤ N) {m : ℕ} (r : Fin m → Φ.Ray) (c : Fin m → ℂˣ)

local notation "s[" Δ "]" => Fan.algebraicRealizationStructureMap Δ
local notation "π[" H "]" => FanHom.algebraicMap (IsSubdivision.toFanHom H)
local notation "base[" A "]" => toBase (WithBoundary.toTower (Sigma.snd A))
local notation "boundary[" A "]" => WithBoundary.boundaryι (Sigma.snd A)
local notation "model" => internalBlowupTower b
local notation "M" => model r c

/-- A specified nodal blowup tower on an ordered internal model is cartesian
over a regular fan subdivision. The refined model uses the same ordered binomial
parameters and the lifts of the same rays. Its identification with the given
tower respects the reduced boundary and pulls back every total internal
exceptional class in the original order. -/
theorem exists_subdivision_of_nodal_tower_on_internal_model
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    {n : ℕ} {Y : Scheme} {T : QPainleve.BlowupTower M.1 n Y}
    (hT : IsNodalBoundaryTower (boundary[M]).ker (base[M] ≫ s[Φ]) (𝟙 _) T) :
    ∃ (Ψ : Fan i) (_ : Ψ.IsRegular) (H : Ψ.IsSubdivision Φ),
      letI := H.nonempty_cones_of_nonempty hΦ₀
      let L := model (H.liftRay ∘ r) c
      ∃ e : L.1 ≅ Y, IsPullback (e.hom ≫ T.toBase) base[L] base[M] π[H] ∧
        (((boundary[M]).ker.comap T.toBase).radical).comap e.hom = (boundary[L]).ker ∧
        ∀ j, LineBundleClass.pullback (e.hom ≫ T.toBase)
          (M.2.toTower.exceptionalClass j) = L.2.toTower.exceptionalClass j := by
  obtain ⟨Ψ, hΨ, H, e, hpb, hboundary⟩ :=
    exists_subdivision_of_nodalBoundaryTower_internalBlowupTower b r c hΦ hc hT
  let : Nonempty Ψ.cones := H.nonempty_cones_of_nonempty hΦ₀
  refine ⟨Ψ, hΨ, H, e, hpb, hboundary, ?_⟩
  intro j
  have hmark := H.pullback_internalBlowupPicardMarking b r c hΨ hΦ _ hpb.w
    (1 : LineBundleClass Φ.algebraicRealization) (Pi.single j 1)
  simpa only [LineBundleClass.pullback_one, ofMul_one, internalBlowupPicardMarking_apply,
    picardHom_apply_single, zpow_one] using hmark

end TauCeti.Toric.Fan
