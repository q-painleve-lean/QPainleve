/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Boundary
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
import QPainleve.AlgebraicGeometry.Blowup.Integral
import QPainleve.AlgebraicGeometry.Blowup.Smooth
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.Noetherian
import TauCeti.AlgebraicGeometry.ResidueField
import TauCeti.AlgebraicGeometry.Scheme.GenericPoint

/-!
# Towers of closed point blowups

A tower of closed point blowups has a reduced closed point as its center on each
intermediate scheme. The final scheme is again an integral smooth surface when the
base is one. In a tower built along a fixed boundary, closed point centers on the
boundary give closed point centers on each current surface.
-/

public section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace TauCeti.AlgebraicGeometry

universe u

namespace QPainleve.BlowupTower

variable {D X Y Z : Scheme.{u}} {m n : ℕ}

/-- Every center of the tower is the reduced subscheme of a closed point of the current scheme. -/
inductive IsClosedPointTower (X : Scheme.{u}) :
    {n : ℕ} → {Y : Scheme.{u}} → BlowupTower X n Y → Prop
  /-- There are no centers in the empty tower. -/
  | nil : IsClosedPointTower X .nil
  /-- Append the blowup of a reduced closed point of the current scheme. -/
  | snoc {n : ℕ} {Y : Scheme.{u}} {T : BlowupTower X n Y} {I : Y.IdealSheafData}
      (hT : IsClosedPointTower X T) (p : Y)
      (hp : IsClosed ({p} : Set Y)) (hI : I = (Y.fromSpecResidueField p).ker) :
      IsClosedPointTower X (T.snoc I)

/-- The final scheme of a blowup tower on a Noetherian scheme is Noetherian. -/
theorem isNoetherian (T : BlowupTower X n Y) [IsNoetherian X] : IsNoetherian Y := by
  induction T with
  | nil => infer_instance
  | snoc _ I ih =>
    have := ih
    exact isNoetherian_of_finiteType I.blowupToBase

namespace IsClosedPointTower

variable {T : BlowupTower X n Y}

/-- A nonempty point tower consists of a point tower followed by the blowup of a reduced
closed point. -/
theorem snoc_iff {I : Y.IdealSheafData} :
    IsClosedPointTower X (T.snoc I) ↔
      IsClosedPointTower X T ∧
        ∃ p : Y, IsClosed ({p} : Set Y) ∧ I = (Y.fromSpecResidueField p).ker := by
  constructor
  · have step {d : ℕ} {W : Scheme.{u}} {S : BlowupTower X d W}
        (hS : IsClosedPointTower X S) :
        match S with
        | .nil => IsClosedPointTower X .nil
        | .snoc U J => IsClosedPointTower X U ∧
            ∃ p, IsClosed ({p} : Set _) ∧ J = (Scheme.fromSpecResidueField _ p).ker := by
      cases hS with
      | nil => exact .nil
      | snoc hU p hp hJ => exact ⟨hU, p, hp, hJ⟩
    exact fun h ↦ step h
  · rintro ⟨hT, p, hp, hI⟩
    exact hT.snoc p hp hI

/-- Two consecutive towers of closed point blowups give a tower of closed point blowups. -/
protected theorem append {U : BlowupTower Y m Z} (hT : IsClosedPointTower X T)
    (hU : IsClosedPointTower Y U) : IsClosedPointTower X (T.append U) := by
  induction hU with
  | nil => simpa only [append_nil] using hT
  | snoc _ p hp hI ih => simpa only [append_snoc] using ih.snoc p hp hI

/-- A tower of closed point blowups preserves smoothness of relative dimension two. -/
theorem smoothOfRelativeDimension {k : Type u} [Field k] [PerfectField k]
    (hT : IsClosedPointTower X T) (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 f] :
    SmoothOfRelativeDimension 2 (T.toBase ≫ f) := by
  induction hT with
  | nil => simpa
  | @snoc _ W S I _ p hp hI ih =>
    subst I
    have := ih
    rw [toBase_snoc, Category.assoc, W.ker_fromSpecResidueField_eq_vanishingIdeal]
    exact Scheme.IdealSheafData.smoothOfRelativeDimension_blowup_closed_point (S.toBase ≫ f) hp

/-- A tower of closed point blowups of an integral Noetherian smooth surface is integral. -/
theorem isIntegral {k : Type u} [Field k] [PerfectField k] [IsIntegral X] [IsNoetherian X]
    (hT : IsClosedPointTower X T) (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 f] :
    IsIntegral Y := by
  induction hT with
  | nil => infer_instance
  | @snoc _ W S I hS p hp hI ih =>
    subst I
    have := ih
    have := S.isNoetherian
    have := hS.smoothOfRelativeDimension f
    have : IsClosedImmersion (W.fromSpecResidueField p) :=
      isClosed_singleton_iff_isClosedImmersion.mp hp
    apply (W.fromSpecResidueField p).ker.isIntegral_blowup_of_nonempty_compl_support
    have hcodim := coheight_eq_of_isClosed_of_smoothOfRelativeDimension (n := 2) (S.toBase ≫ f) hp
    have hne : genericPoint W ≠ p := by
      intro heq
      rw [← heq, (Scheme.isMax_iff_eq_genericPoint.mpr rfl).coheight_eq_zero] at hcodim
      norm_num at hcodim
    refine ⟨genericPoint W, ?_⟩
    rw [← SetLike.mem_coe, Closeds.coe_compl, Set.mem_compl_iff, Scheme.Hom.support_ker,
      Scheme.range_fromSpecResidueField, hp.closure_eq, Set.mem_singleton_iff]
    exact hne

end IsClosedPointTower

/-- A boundary tower whose prescribed centers are reduced closed points of the boundary is a
tower of reduced closed point blowups on the successive ambient schemes. -/
theorem isClosedPointTower_alongBoundary (i : D ⟶ X) [IsClosedImmersion i]
    (J : Fin n → {I : D.IdealSheafData // I.IsEffectiveCartier})
    (hJ : ∀ j, ∃ p : D, IsClosed ({p} : Set D) ∧ (J j).val = (D.fromSpecResidueField p).ker) :
    IsClosedPointTower X (alongBoundary i J).2.toTower := by
  induction n with
  | zero =>
    have heq := congrArg
      (fun P : Σ W, WithBoundary i 0 W ↦ IsClosedPointTower X P.2.toTower)
      (alongBoundary_zero i J)
    refine heq.mpr ?_
    simpa only [WithBoundary.toTower_nil] using (IsClosedPointTower.nil (X := X))
  | succ d ih =>
    let U := alongBoundary i (fun j : Fin d ↦ J j.castSucc)
    let T := U.2
    obtain ⟨p, hp, hcenter⟩ := hJ (Fin.last d)
    have hclosed : IsClosed ({T.boundaryι p} : Set U.1) := by
      simpa using T.boundaryι.isClosedEmbedding.isClosedMap _ hp
    have hmap :
        (J (Fin.last d)).val.map T.boundaryι =
          (U.1.fromSpecResidueField (T.boundaryι p)).ker := by
      rw [hcenter, Scheme.IdealSheafData.map_ker,
        ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, Scheme.Hom.ker_comp_of_isIso]
    have heq := congrArg
      (fun P : Σ W, WithBoundary i (d + 1) W ↦ IsClosedPointTower X P.2.toTower)
      (alongBoundary_succ i J)
    refine heq.mpr ?_
    simp only [WithBoundary.toTower_snoc]
    exact (ih (fun j ↦ J j.castSucc) (fun j ↦ hJ j.castSucc)).snoc _ hclosed hmap

end QPainleve.BlowupTower
