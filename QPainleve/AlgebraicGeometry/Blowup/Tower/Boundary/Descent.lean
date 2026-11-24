/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Isometry.Descent
public import QPainleve.AlgebraicGeometry.Curves.Node.Period.Orientation

import QPainleve.AlgebraicGeometry.IdealSheaf.BaseChange
import QPainleve.AlgebraicGeometry.IdealSheaf.Restriction
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced

/-!
# Descending a reconstructed isomorphism through nodal blowups

If a prescribed Picard isometry matches two ample classes, a realization of its
extension through the nodal blowups descends to the original pairs. The descended
map realizes the prescribed pullback on all Picard classes. Oriented subdivisions
relate the branch order upstairs to the branch order downstairs, even for a
self-node or a two-component cycle.

This is the descent after reconstruction on nodal blowup models in
[Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*,
Theorem 4.7](https://arxiv.org/html/1211.6367v5#S4.Thmtheorem7).
-/

public section

open AlgebraicGeometry CategoryTheory DihedralGroup TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData LineBundleClass

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y V W : Scheme.{u}}
  [IsIntegral X] [IsIntegral Y] [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X.IsProjectiveOver k] [Y.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]
  {m : ℕ} {T : BlowupTower X m V} {U : BlowupTower Y m W}
  {D : X.IdealSheafData} {E : Y.IdealSheafData}

local notation "S" => Spec (CommRingCat.of k)
local notation "D'" => radical (comap D (BlowupTower.toBase T))
local notation "E'" => radical (comap E (BlowupTower.toBase U))

variable (hT : IsClosedPointTower X T) (hU : IsClosedPointTower Y U)
  (I : (Chow.intersectionBilinForm k Y).IsometryEquiv (Chow.intersectionBilinForm k X))
  (e : V ≅ W)
  (hover : T.toBase ≫ (X ↘ Spec (.of k)) = e.hom ≫ U.toBase ≫ (Y ↘ Spec (.of k)))
  {H : LineBundleClass Y} (hH : H.IsAmple) (hI : (I (Additive.ofMul H)).toMul.IsAmple)
  (hpic : ∀ L : LineBundleClass W, pullback e.hom L =
    (picardIsometryCongr k hU hT I (Additive.ofMul L)).toMul)

include hT hU hover hH hI hpic

/-- The isomorphism on point blowup models descends to the original pairs if it
identifies the reduced total boundaries and realizes the extension of a Picard isometry
matching ample classes. The descent realizes the prescribed Picard pullback and is
unique compatibly with the given isomorphism upstairs. -/
theorem existsUnique_boundary_iso_of_picardIsometryCongr
    [IsReduced D.subscheme] [IsReduced E.subscheme] (hboundary : (E').comap e.hom = D') :
    ∃! a : X ≅ Y, T.toBase ≫ a.hom = e.hom ≫ U.toBase ∧ a.hom ≫ (Y ↘ S) = (X ↘ S) ∧
      E.comap a.hom = D ∧
      ∀ L : LineBundleClass Y, pullback a.hom L = (I (Additive.ofMul L)).toMul := by
  obtain ⟨a, ⟨ha, haOver, haPic⟩, hu⟩ :=
    existsUnique_iso_over_of_picardIsometryCongr hT hU I e hover hH hI hpic
  have : Surjective T.toBase := hT.surjective (X ↘ S)
  have hs : ((E.comap a.hom).comap T.toBase).support = (D.comap T.toBase).support := by
    calc
      _ = ((E').comap e.hom).support := by
        rw [← comap_comp, ha, comap_comp, ← radical_comap_of_isOpenImmersion, support_radical]
      _ = _ := by rw [hboundary, support_radical]
  have h := radical_eq_of_support_comap_eq T.toBase hs
  rw [radical_comap_of_isOpenImmersion,
    E.isReduced_subscheme_iff_radical_eq.mp ‹IsReduced E.subscheme›,
    D.isReduced_subscheme_iff_radical_eq.mp ‹IsReduced D.subscheme›] at h
  exact ⟨a, ⟨ha, haOver, h, haPic⟩, fun b hb ↦ hu b ⟨hb.1, hb.2.1, hb.2.2.2⟩⟩

section Orientation

open Scheme (NodalCycleNumbering)

variable [V.Over (Spec (.of k))] [W.Over (Spec (.of k))]
  [PrestableFamily (D.subscheme ↘ Spec (.of k))] [PrestableFamily (E.subscheme ↘ Spec (.of k))]
  [PrestableFamily ((D.comap T.toBase).radical.subscheme ↘ Spec (.of k))]
  [PrestableFamily ((E.comap U.toBase).radical.subscheme ↘ Spec (.of k))]
  {ι₁ ι₂ ι₃ ι₄ : Type*}
  {p₁ : ι₁ → (D.subscheme ↘ Spec (.of k)).smoothLocus}
  {p₂ : ι₂ → (E.subscheme ↘ Spec (.of k)).smoothLocus}
  {p₃ : ι₃ → ((D.comap T.toBase).radical.subscheme ↘ Spec (.of k)).smoothLocus}
  {p₄ : ι₄ → ((E.comap U.toBase).radical.subscheme ↘ Spec (.of k)).smoothLocus}
  {n l : ℕ} [NeZero n] [NeZero l]

local notation "πD" => subschemeMap D' D (BlowupTower.toBase T)
  (le_map_iff_comap_le.mpr (le_radical _))
local notation "πE" => subschemeMap E' E (BlowupTower.toBase U)
  (le_map_iff_comap_le.mpr (le_radical _))

/-- With oriented numberings on the two nodal subdivisions, the descended
isomorphism realizes the prescribed Picard pullback and has the same boundary
orientation sign as the isomorphism upstairs. The square on the boundaries
also commutes, so images of surviving components can be read upstairs. -/
theorem exists_boundary_iso_of_picardIsometryCongr_of_orientedCycleSubdivisions
    (A : NodalCycleNumbering p₁ n) (B : NodalCycleNumbering p₂ n)
    (C : NodalCycleNumbering p₃ l) (F : NodalCycleNumbering p₄ l)
    [Scheme.Hom.IsOver πD S] [Scheme.Hom.IsOver πE S]
    (hπD : (πD).IsOrientedCycleSubdivision C A) (hπE : (πE).IsOrientedCycleSubdivision F B)
    (r : (D').subscheme ≅ (E').subscheme) [r.hom.IsOver S]
    (hr : r.hom ≫ (E').subschemeι = (D').subschemeι ≫ e.hom) :
    ∃ (a : X ≅ Y) (d : D.subscheme ≅ E.subscheme)
      (_ : d.hom.IsOver S),
      T.toBase ≫ a.hom = e.hom ≫ U.toBase ∧ a.hom ≫ (Y ↘ S) = (X ↘ S) ∧
      d.hom ≫ E.subschemeι = D.subschemeι ≫ a.hom ∧
      CommSq r.hom πD πE d.hom ∧
      (∀ L : LineBundleClass Y, pullback a.hom L = (I (Additive.ofMul L)).toMul) ∧
      cycleOrientationSign (d.boundaryCycleAction A B) =
        cycleOrientationSign (r.boundaryCycleAction C F) := by
  have : IsReduced D.subscheme :=
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := D.subscheme ↘ S)).isReduced
  have : IsReduced E.subscheme :=
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := E.subscheme ↘ S)).isReduced
  have hboundary : (E').comap e.hom = D' := by
    have hpb := (IsPullback.of_horiz_isIso ⟨hr⟩).flip
    simpa only [ker_subschemeι] using (ker_eq_comap_of_isPullback (E').subschemeι hpb).symm
  obtain ⟨a, ⟨ha, haOver, hb, haPic⟩, -⟩ :=
    hT.existsUnique_boundary_iso_of_picardIsometryCongr hU I e hover hH hI hpic hboundary
  obtain ⟨d, hd⟩ := E.exists_iso_of_comap_eq_ker a D.subschemeι
    (by simpa only [ker_subschemeι] using hb)
  have hdOver : d.hom.IsOver S := ⟨by
    rw [E.over_eq_subschemeι_comp, reassoc_of% hd, haOver, ← D.over_eq_subschemeι_comp]⟩
  have hsq : CommSq r.hom πD πE d.hom := by
    constructor
    apply (cancel_mono E.subschemeι).mp
    simp only [Category.assoc, subschemeMap_subschemeι, reassoc_of% hr, hd, ← ha]
    rw [← Category.assoc (πD), subschemeMap_subschemeι, Category.assoc]
  exact ⟨a, d, hdOver, ha, haOver, hd, hsq, haPic,
    d.cycleOrientationSign_eq_of_orientedCycleSubdivisions A B C F r hπD hπE hsq⟩

end Orientation

end QPainleve.BlowupTower.IsClosedPointTower
