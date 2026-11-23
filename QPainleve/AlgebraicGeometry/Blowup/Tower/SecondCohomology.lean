/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Exceptional.SecondCohomology
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Picard

import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme

/-!
# Second cohomology and point-blowup markings

The vanishing of second cohomology for the base coordinate of a Picard marking
implies vanishing on the final surface. If every exceptional coefficient is at most one,
second cohomology is unchanged.
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules LineBundleClass

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {X Y : Scheme.{u}} {n : ℕ} (k : Type u) [Field k] [PerfectField k]
  [X.Over (Spec (.of k))]

include k in
/-- A line bundle in the Picard marking of a closed-point blowup tower has vanishing
second cohomology whenever its base coordinate does. The exceptional coefficients
can be arbitrary integers. -/
theorem subsingleton_cohomology_two_picardHom
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
    {T : BlowupTower X n Y} (hT : IsClosedPointTower X T)
    (L : InvertibleSheaf X) (hL : Subsingleton (Cohomology L.obj 2))
    (b : Fin n → ℤ) (M : InvertibleSheaf Y)
    (hM : mk M = (T.picardHom (Additive.ofMul (mk L), b)).toMul) :
    Subsingleton (Cohomology M.obj 2) := by
  induction hT with
  | nil =>
    rw [picardHom_nil, toMul_ofMul] at hM
    obtain ⟨e⟩ := mk_eq_mk_iff.mp hM
    exact (cohomologyBaseLinearEquivOfIso k e 2).injective.subsingleton
  | @snoc d Z S I hS p hp hI ih =>
    subst I
    let g := S.toBase ≫ X ↘ Spec (.of k)
    let : Z.Over (Spec (.of k)) := ⟨g⟩
    have hd : SmoothOfRelativeDimension 2 g := hS.smoothOfRelativeDimension _
    have : Smooth g := hd.smooth 2 _
    have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
    have : IsRegular Z := IsRegular.of_smooth g
    have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq g 2).mp hd).2 p hp
    obtain ⟨A, hA⟩ := mk_surjective (S.picardHom (Additive.ofMul (mk L),
      fun j ↦ b j.castSucc)).toMul
    rw [picardHom_snoc_apply_toMul, ← hA] at hM
    exact Scheme.IdealSheafData.subsingleton_cohomology_two_pointBlowup_exceptional_twist
      k hp hdim M A (ih (fun j ↦ b j.castSucc) A hA) hM

private theorem nonempty_cohomologyTwoLinearEquiv_picardHom_of_comp
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
    {T : BlowupTower X n Y} (hT : IsClosedPointTower X T)
    (L : InvertibleSheaf X) (b : Fin n → ℤ) (hb : ∀ j, b j ≤ 1)
    (g : Y ⟶ Spec (.of k)) (hg : g = T.toBase ≫ X ↘ Spec (.of k))
    (M : InvertibleSheaf Y) (hM : mk M = (T.picardHom (Additive.ofMul (mk L), b)).toMul) :
    let : Y.Over (Spec (.of k)) := ⟨g⟩
    Nonempty (Cohomology L.obj 2 ≃ₗ[k] Cohomology M.obj 2) := by
  revert g M
  induction hT with
  | nil =>
    intro g hg M hM
    rw [toBase_nil, Category.id_comp] at hg
    subst g
    rw [picardHom_nil, toMul_ofMul] at hM
    obtain ⟨e⟩ := mk_eq_mk_iff.mp hM.symm
    exact ⟨cohomologyBaseLinearEquivOfIso k e 2⟩
  | @snoc d Z S I hS p hp hI ih =>
    subst I
    intro g' hg' M hM
    rw [toBase_snoc, Category.assoc] at hg'
    subst g'
    let g := S.toBase ≫ X ↘ Spec (.of k)
    let : Z.Over (Spec (.of k)) := ⟨g⟩
    have hd : SmoothOfRelativeDimension 2 g := hS.smoothOfRelativeDimension _
    have : Smooth g := hd.smooth 2 _
    have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
    have : IsRegular Z := IsRegular.of_smooth g
    have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq g 2).mp hd).2 p hp
    obtain ⟨A, hA⟩ := mk_surjective (S.picardHom (Additive.ofMul (mk L),
      fun j ↦ b j.castSucc)).toMul
    obtain ⟨e⟩ := ih (fun j ↦ b j.castSucc) (fun j ↦ hb j.castSucc) g rfl A hA
    rw [picardHom_snoc_apply_toMul, ← hA] at hM
    obtain ⟨e'⟩ :=
      Scheme.IdealSheafData.nonempty_cohomologyTwoPointBlowupExceptionalTwistLinearEquiv
        k hp hdim M A hM (hb (Fin.last d))
    exact ⟨e.trans e'⟩

/-- The second cohomology of a marked line bundle agrees with that of its base
coordinate when every total-transform exceptional coefficient is at most one. -/
theorem nonempty_cohomologyTwoLinearEquiv_picardHom
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
    {T : BlowupTower X n Y} (hT : IsClosedPointTower X T)
    (L : InvertibleSheaf X) (b : Fin n → ℤ) (hb : ∀ j, b j ≤ 1) (M : InvertibleSheaf Y)
    (hM : mk M = (T.picardHom (Additive.ofMul (mk L), b)).toMul) :
    let : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ X ↘ Spec (.of k)⟩
    Nonempty (Cohomology L.obj 2 ≃ₗ[k] Cohomology M.obj 2) :=
  nonempty_cohomologyTwoLinearEquiv_picardHom_of_comp k hT L b hb _ rfl M hM

end QPainleve.BlowupTower.IsClosedPointTower
