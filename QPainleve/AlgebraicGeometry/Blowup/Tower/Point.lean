/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Boundary
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
import QPainleve.AlgebraicGeometry.Blowup.Descent
import QPainleve.AlgebraicGeometry.Blowup.Integral
import QPainleve.AlgebraicGeometry.Blowup.Smooth
import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
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

/-- The projection of a tower of closed point blowups of a smooth surface over a perfect field
is surjective. -/
theorem surjective {k : Type u} [Field k] [PerfectField k]
    (hT : IsClosedPointTower X T) (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 f] :
    Surjective T.toBase := by
  induction hT with
  | nil => simpa only [toBase_nil] using (inferInstance : Surjective (𝟙 X))
  | @snoc _ W S I hS p hp hI ih =>
    subst I
    have := ih
    let g := S.toBase ≫ f
    have : SmoothOfRelativeDimension 2 g := hS.smoothOfRelativeDimension f
    have : Smooth g := SmoothOfRelativeDimension.smooth 2 g
    have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian g
    have : IsRegularLocalRing (W.presheaf.stalk p) := isRegularLocalRing_stalk_of_smooth g p
    have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq g 2).mp inferInstance).2 p hp
    have : Surjective (W.fromSpecResidueField p).ker.blowupToBase := by
      rw [W.ker_fromSpecResidueField_eq_vanishingIdeal]
      exact Scheme.IdealSheafData.surjective_blowupToBase_point hp hdim
    rw [toBase_snoc]
    infer_instance

/-- The total transform of an effective Cartier divisor on a smooth integral surface
in a tower of blowups at closed points is effective Cartier. -/
theorem isEffectiveCartier_totalTransform {k : Type u} [Field k] [IsIntegral X]
    [PerfectField k] [IsNoetherian X] (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 f]
    (hT : IsClosedPointTower X T) {D : X.IdealSheafData} (hD : D.IsEffectiveCartier) :
    (D.comap T.toBase).IsEffectiveCartier := by
  have : IsIntegral Y := hT.isIntegral f
  have : Surjective T.toBase := hT.surjective f
  exact hD.comap_of_isDominant T.toBase

end IsClosedPointTower

/-- Transport along a tower lift preserves the closed point condition at every stage. -/
theorem IsLift.isClosedPointTower {W : Scheme.{u}} {T : BlowupTower X n Y} {U : BlowupTower Z n W}
    {e : X ≅ Z} {g : Y ≅ W} (h : IsLift e T U g) (hT : IsClosedPointTower X T) :
    IsClosedPointTower Z U := by
  induction hT generalizing W with
  | nil => cases U; exact .nil
  | @snoc m Y T I hT p hp hI ih =>
    cases U with
    | snoc U J =>
      obtain ⟨f, hf, hJ, -⟩ := IsLift.snoc_iff.mp h
      have hcomap : I.comap f.inv = J := by
        rw [← hJ, ← Scheme.IdealSheafData.comap_comp, f.inv_hom_id, Scheme.IdealSheafData.comap_id]
      obtain ⟨q, hq, -, hqJ⟩ :=
        f.inv.exists_comap_ker_fromSpecResidueField_of_isIso_morphismRestrict p hp ⊤ (by simp)
      exact (ih hf).snoc q hq (hcomap.symm.trans (hI ▸ hqJ))

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
      rw [hcenter, T.boundaryι.map_ker_fromSpecResidueField]
    have heq := congrArg
      (fun P : Σ W, WithBoundary i (d + 1) W ↦ IsClosedPointTower X P.2.toTower)
      (alongBoundary_succ i J)
    refine heq.mpr ?_
    simp only [WithBoundary.toTower_snoc]
    exact (ih (fun j ↦ J j.castSucc) (fun j ↦ hJ j.castSucc)).snoc _ hclosed hmap

end QPainleve.BlowupTower
