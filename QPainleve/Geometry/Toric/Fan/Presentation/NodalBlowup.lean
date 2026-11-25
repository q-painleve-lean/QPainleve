/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Presentation.Basic
public import QPainleve.Geometry.Toric.Fan.Subdivision.NodalRefinement

import QPainleve.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced

/-!
# Toric presentations after nodal blowups

Common nodal refinements extend a specified toric presentation to a surface
obtained by nodal blowups. The new fan subdivides the old fan and the ordered
internal centers lift to the corresponding rays.

This is the corner blowup construction used in [Gross, Hacking and Keel,
*Mirror symmetry for log Calabi–Yau surfaces I*, Proposition 1.3][GHK].

[GHK]: https://arxiv.org/html/1106.4977v3#S1.Thmproposition3
-/

public section

open AlgebraicGeometry CategoryTheory Limits QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Module.Basis (Fin 2) ℤ N)
  {m : ℕ} (ρ : Fin m → Φ.Ray) (c : Fin m → ℂˣ)
  (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "s[" Δ "]" => Fan.algebraicRealizationStructureMap Δ
local notation "π[" A "]" => toBase (WithBoundary.toTower (Sigma.snd A))
local notation "I[" A "]" => Scheme.Hom.ker (WithBoundary.boundaryι (Sigma.snd A))
local notation "A" => internalBlowupTower (h₀ := hc.nonempty_cones) b ρ c
local notation "map[" H "]" => FanHom.algebraicMap (IsSubdivision.toFanHom H)

include hΦ in
/-- A specified toric presentation extends across a nodal tower. The new
presentation lies over a subdivision of the original fan with the same ordered
center parameters. The nodal refinement of the new base has length at most
that of the original presentation, and its reduced total boundary is identified
with the strict boundary of the subdivided internal model. -/
theorem exists_toric_presentation_of_nodal_boundary_tower
    {X Y Z : Scheme} {s : X ⟶ S} {D₀ : X.IdealSheafData}
    {n l : ℕ} {T : BlowupTower X n Y} {U : BlowupTower X l Z}
    (hT : IsNodalBoundaryTower D₀ s (𝟙 _) T)
    (hU : IsNodalBoundaryTower D₀ s (𝟙 _) U)
    (e : (A).1 ≅ Y) (he : e.hom ≫ T.toBase ≫ s = π[A] ≫ s[Φ])
    (hD : ((D₀.comap T.toBase).radical).comap e.hom = I[A]) :
    ∃ (Ψ : Fan i) (_ : Ψ.IsRegular) (H : Ψ.IsSubdivision Φ)
      (r : ℕ) (W : Scheme) (R : BlowupTower Z r W),
      r ≤ n ∧
      IsNodalBoundaryTower (D₀.comap U.toBase).radical (U.toBase ≫ s) (𝟙 _) R ∧
      let B := internalBlowupTower (h₀ := H.nonempty_cones_of_nonempty hc.nonempty_cones)
        b (H.liftRay ∘ ρ) c
      ∃ (g : B.1 ≅ W) (f : B.1 ⟶ (A).1),
        IsPullback f π[B] π[A] map[H] ∧
        f ≫ e.hom ≫ T.toBase = g.hom ≫ R.toBase ≫ U.toBase ∧
        g.hom ≫ R.toBase ≫ U.toBase ≫ s = π[B] ≫ s[Ψ] ∧
        (((D₀.comap U.toBase).radical.comap R.toBase).radical).comap g.hom = I[B] := by
  obtain ⟨a, r, M, W, L, R, d, -, hr, hL, hR, hcomm, -⟩ :=
    hT.exists_common_nodal_boundary_tower_refinement hU
  simp only [Category.comp_id] at hL hR
  let E := (D₀.comap T.toBase).radical
  have hL' : IsNodalBoundaryTower E (T.toBase ≫ s) (𝟙 _) L :=
    hL.congr (by simp) (by simp [E])
  let hnil : IsNodalBoundaryTower I[A] (π[A] ≫ s[Φ]) (𝟙 _) (.nil : BlowupTower (A).1 0 (A).1) :=
    .nil
  have hsupport : (E.comap e.hom).support =
      (I[A].comap (.nil : BlowupTower (A).1 0 (A).1).toBase).support := by
    rw [toBase_nil, comap_id]
    exact congrArg (fun J : (A).1.IdealSheafData ↦ J.support) hD
  obtain ⟨P, Q, p, hQ, hq, -⟩ :=
    hnil.exists_append_of_iso hL' e (by simpa only [toBase_nil, Category.id_comp] using he) hsupport
  obtain ⟨Ψ, hΨ, H, g, hg, hgD⟩ :=
    exists_subdivision_of_nodalBoundaryTower_internalBlowupTower b ρ c hΦ hc hQ
  have hp : Q.toBase ≫ e.hom = p.hom ≫ L.toBase := by
    simp only [hq, toBase_nil, Category.comp_id, Category.assoc, Iso.inv_hom_id]
  let a := g ≪≫ p ≪≫ d
  have hproj : (g.hom ≫ Q.toBase) ≫ e.hom ≫ T.toBase =
      a.hom ≫ R.toBase ≫ U.toBase := by
    rw [Category.assoc, reassoc_of% hp, hcomm]
    rfl
  refine ⟨Ψ, hΨ, H, r, W, R, hr, hR.congr (by simp) (by simp),
    a, g.hom ≫ Q.toBase, hg, hproj, ?_, ?_⟩
  · rw [← reassoc_of% hproj, he, ← Category.assoc g.hom Q.toBase, ← Category.assoc, hg.w,
      Category.assoc, FanHom.algebraicMap_comp_algebraicRealizationStructureMap]
  · calc
      _ = (D₀.comap (a.hom ≫ R.toBase ≫ U.toBase)).radical := by
        rw [radical_comap_radical, ← radical_comap_of_isOpenImmersion, ← comap_comp,
          ← comap_comp, Category.assoc]
      _ = ((E.comap e.hom).comap (g.hom ≫ Q.toBase)).radical := by
        simp only [E, ← radical_comap_of_isOpenImmersion (D₀.comap T.toBase) e.hom,
          radical_comap_radical, ← comap_comp, ← hproj]
      _ = _ := by rwa [hD, comap_comp, radical_comap_of_isOpenImmersion]

end TauCeti.Toric.Fan

open TopologicalSpace TauCeti.Toric

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {X : Scheme} {b : Module.Basis (Fin 2) ℤ N}
  {D : X.IdealSheafData} {s : X ⟶ Spec (CommRingCat.of ℂ)} {p : X}

local notation "I" => vanishingIdeal (Closeds.mk (closure (Singleton.singleton p)) isClosed_closure)
local notation "π" => blowupToBase I

/-- A toric presentation extends to the reduced total boundary after blowing up a closed node. -/
theorem HasToricPresentation.nodalBlowup
    (h : D.HasToricPresentation s b i) (hp : IsClosed ({p} : Set X))
    (hn : D.IsNodeOfReducedBoundary s p) :
    (D.comap π).radical.HasToricPresentation (π ≫ s) b i := by
  obtain ⟨Φ, hΦ, hc, m, r, c, n, Z, T, hT, e, he, hD⟩ := (hasToricPresentation_iff ..).mp h
  obtain ⟨Ψ, hΨ, H, l, W, U, -, hU, a, _, _, _, ha, hB⟩ :=
    Fan.exists_toric_presentation_of_nodal_boundary_tower b r c hΦ hc hT
      (IsNodalBoundaryTower.of_node hp hn) e he hD
  refine (hasToricPresentation_iff ..).mpr ⟨Ψ, hΨ, H.isComplete_iff.mpr hc, m, H.liftRay ∘ r, c,
    l, W, U, ?_, a, ?_, ?_⟩
  · simpa only [toBase_snoc, toBase_nil, Category.comp_id] using hU
  · simpa only [toBase_snoc, toBase_nil, Category.comp_id, Category.assoc] using ha
  · simpa only [toBase_snoc, toBase_nil, Category.comp_id] using hB

end AlgebraicGeometry.Scheme.IdealSheafData
