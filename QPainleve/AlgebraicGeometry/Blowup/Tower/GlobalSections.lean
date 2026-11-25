/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Picard
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base

import QPainleve.AlgebraicGeometry.Blowup.Exceptional.GlobalSections
import TauCeti.AlgebraicGeometry.Cohomology.AffinePushforward
import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme

/-!
# Global sections in a point-blowup marking

A line bundle with nonnegative total-transform exceptional coefficients pushes forward
to the line bundle in its base coordinate. The comparison iterates
`Scheme.IdealSheafData.pointBlowupPushforwardExceptionalTwistIso` and allows infinitely
near centers.
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules LineBundleClass

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {X Y : Scheme.{u}} {n : ℕ} (k : Type u) [Field k] [PerfectField k]
  [X.Over (Spec (.of k))] [smooth : SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  {T : BlowupTower X n Y}

local notation "S" => Spec (CommRingCat.of k)

include smooth in
/-- With nonnegative total-transform exceptional coefficients, direct image along
the tower recovers the line bundle in the base coordinate. -/
theorem nonempty_pushforwardExceptionalTwistIso
    (hT : IsClosedPointTower X T) (L : InvertibleSheaf X) (b : Fin n → ℤ)
    (hb : ∀ j, 0 ≤ b j) (M : InvertibleSheaf Y)
    (hM : mk M = (T.picardHom (Additive.ofMul (mk L), b)).toMul) :
    Nonempty (L.obj ≅ (pushforward T.toBase).obj M.obj) := by
  induction hT with
  | nil =>
    rw [picardHom_nil, toMul_ofMul] at hM
    rw [toBase_nil]
    obtain ⟨e⟩ := mk_eq_mk_iff.mp hM.symm
    exact ⟨e ≪≫ ((pushforwardId X).app M.obj).symm⟩
  | @snoc d Z U J hU p hp hJ ih =>
    subst J
    let : Z.Over S := ⟨U.toBase ≫ X ↘ S⟩
    have hd : SmoothOfRelativeDimension 2 (Z ↘ S) := hU.smoothOfRelativeDimension _
    have : Smooth (Z ↘ S) := hd.smooth 2 _
    have : IsRegular Z := IsRegular.of_smooth (Z ↘ S)
    have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq (Z ↘ S) 2).mp hd).2 p hp
    obtain ⟨A, hA⟩ := mk_surjective (U.picardHom (Additive.ofMul (mk L),
      fun j ↦ b j.castSucc)).toMul
    obtain ⟨e⟩ := ih (fun j ↦ b j.castSucc) (fun j ↦ hb j.castSucc) A hA
    rw [picardHom_snoc_apply_toMul, ← hA] at hM
    let m := (b (Fin.last d)).toNat
    have hm : (m : ℤ) = b (Fin.last d) := Int.toNat_of_nonneg (hb _)
    rw [← hm, Scheme.IdealSheafData.blowupExceptionalClass_def, inv_zpow'] at hM
    let e' := Scheme.IdealSheafData.pointBlowupPushforwardExceptionalTwistIso p hp hdim A m M hM
    rw [toBase_snoc]
    exact ⟨e ≪≫ (pushforward U.toBase).mapIso e' ≪≫
      (pushforwardComp (Z.fromSpecResidueField p).ker.blowupToBase U.toBase).app M.obj⟩

/-- A line bundle whose total-transform exceptional coefficients are nonnegative has
global sections linearly isomorphic to those of its base coordinate. -/
theorem nonempty_cohomologyZeroLinearEquiv_picardHom [Y.Over S] [T.toBase.IsOver S]
    (hT : IsClosedPointTower X T) (L : InvertibleSheaf X) (b : Fin n → ℤ)
    (hb : ∀ j, 0 ≤ b j) (M : InvertibleSheaf Y)
    (hM : mk M = (T.picardHom (Additive.ofMul (mk L), b)).toMul) :
    Nonempty (Cohomology L.obj 0 ≃ₗ[k] Cohomology M.obj 0) := by
  obtain ⟨e⟩ := hT.nonempty_pushforwardExceptionalTwistIso k L b hb M hM
  exact ⟨(cohomologyBaseLinearEquivOfIso k e 0).trans
    (T.toBase.cohomologyZeroPushforwardBaseLinearEquiv (R := k) M.obj)⟩

end QPainleve.BlowupTower.IsClosedPointTower
