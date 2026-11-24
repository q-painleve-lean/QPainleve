/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Equiv
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Orthogonal
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Isometry.Basic
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Genus
public import QPainleve.AlgebraicGeometry.Curves.Node.Period.Orientation

/-!
# Period compatibility on nodal auxiliary models

The Picard extension through two ordered nodal blowup towers identifies the
orthogonals of the reduced total boundaries whenever the original isometry
identifies the original boundary orthogonals. The signed period equation holds
on the entire extended orthogonal exactly when it holds on the original one.
This is the period comparison in the corner blowup argument of
[Gross, Hacking and Keel, Theorem 4.7][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S4.Thmtheorem7
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open LineBundleClass Scheme.IdealSheafData LinearMap.BilinForm

universe u v₀ v₁ v₂ v₃

namespace QPainleve.BlowupTower

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y Z W : Scheme.{u}}

local notation "S[" k "]" => Spec (CommRingCat.of k)
local notation "s[" k "," X "]" => (X ↘ Spec (CommRingCat.of k))
local notation "B[" k "," X "]" => Chow.intersectionBilinForm k X
local notation "K[" k "," D "]" => Scheme.IdealSheafData.boundaryOrthogonal D k
local notation "R[" D "," T "]" => radical (comap D (BlowupTower.toBase T))
local notation "π[" D "," T "]" =>
  subschemeMap (R[D,T]) D (BlowupTower.toBase T) (le_map_iff_comap_le.mpr (le_radical _))

variable [X.Over S[k]] [IsIntegral X] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 s[k,X]]
  {D : X.IdealSheafData} {m : ℕ} {T : BlowupTower X m Y}
  (hT : IsNodalBoundaryTower D s[k,X] (𝟙 X) T)

private def reducedBoundaryOrthogonalEquiv :
    let : IsNoetherian X := isNoetherian_of_finiteType s[k,X]
    let : Y.Over S[k] := ⟨T.toBase ≫ s[k,X]⟩
    let : IsIntegral Y := hT.isClosedPointTower.isIntegral s[k,X]
    let : Y.IsProjectiveOver k := T.isProjectiveOver k
    let : SmoothOfRelativeDimension 2 s[k,Y] :=
      hT.isClosedPointTower.smoothOfRelativeDimension s[k,X]
    K[k,D] ≃ₗ[ℤ] K[k,R[D,T]] := by
  intro _ _ _ _ _
  exact (LinearEquiv.ofEq _ _ (D.boundaryOrthogonal_def k)).trans
    ((hT.boundaryOrthogonalIsometry k).toLinearEquiv.trans
      (LinearEquiv.ofEq _ _ (by rw [boundaryOrthogonal_def, support_radical])))

private theorem reducedBoundaryOrthogonalEquiv_apply :
    let : IsNoetherian X := isNoetherian_of_finiteType s[k,X]
    let : Y.Over S[k] := ⟨T.toBase ≫ s[k,X]⟩
    let : IsIntegral Y := hT.isClosedPointTower.isIntegral s[k,X]
    let : Y.IsProjectiveOver k := T.isProjectiveOver k
    let : SmoothOfRelativeDimension 2 s[k,Y] :=
      hT.isClosedPointTower.smoothOfRelativeDimension s[k,X]
    ∀ x : K[k,D],
      (reducedBoundaryOrthogonalEquiv hT x).val =
        Additive.ofMul (pullback T.toBase x.val.toMul) := by
  intro _ _ _ _ _ x
  simp only [reducedBoundaryOrthogonalEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    IsometryEquiv.coe_toLinearEquiv, hT.boundaryOrthogonalIsometry_apply]

private theorem boundaryPeriod_reducedBoundaryOrthogonalEquiv
    [PrestableFamily (D.subscheme ↘ S[k])]
    (hD : D.IsEffectiveCartier)
    (hg : ∀ v : irreducibleComponents (D.subscheme.singularLocus k).blowup,
      (D.subscheme.blowupComponent v).toScheme.genus k = 0)
    {α : Type v₀} {a : α → (D.subscheme ↘ S[k]).smoothLocus} {n : ℕ} [NeZero n]
    (A : Scheme.NodalCycleNumbering a n) :
    let : IsNoetherian X := isNoetherian_of_finiteType s[k,X]
    let : Y.Over S[k] := ⟨T.toBase ≫ s[k,X]⟩
    let : IsIntegral Y := hT.isClosedPointTower.isIntegral s[k,X]
    let : Y.IsProjectiveOver k := T.isProjectiveOver k
    let : SmoothOfRelativeDimension 2 s[k,Y] :=
      hT.isClosedPointTower.smoothOfRelativeDimension s[k,X]
    ∀ [PrestableFamily ((R[D,T]).subscheme ↘ S[k])]
      (hR : (R[D,T]).IsEffectiveCartier)
      (hgr : ∀ v : irreducibleComponents ((R[D,T]).subscheme.singularLocus k).blowup,
        ((R[D,T]).subscheme.blowupComponent v).toScheme.genus k = 0)
      {β : Type v₁} {b : β → ((R[D,T]).subscheme ↘ S[k]).smoothLocus} {l : ℕ} [NeZero l]
      (C : Scheme.NodalCycleNumbering b l), (π[D,T]).IsOrientedCycleSubdivision C A →
      ∀ x : K[k,D],
      hR.boundaryPeriod hgr C.endpoint_eq
        (Multiplicative.ofAdd (reducedBoundaryOrthogonalEquiv hT x)) =
        hD.boundaryPeriod hg A.endpoint_eq (Multiplicative.ofAdd x) := by
  intro _ _ _ _ _ _ hR hgr β b l _ C hC x
  let : (π[D,T]).IsOver S[k] := ⟨by
    rw [D.over_eq_subschemeι_comp, ← Category.assoc, subschemeMap_subschemeι, Category.assoc]
    rfl⟩
  obtain ⟨fν, hν, hnodes, keep, hkeep, hcollapse⟩ := hC
  obtain ⟨hx, hp⟩ := hR.boundaryPeriod_pullback_of_subdivision hD hgr hg
    C.endpoint_eq A.endpoint_eq T.toBase (subschemeMap_subschemeι ..).symm
    hν hnodes keep hkeep hcollapse (Multiplicative.ofAdd x)
  exact (congrArg (fun y : K[k,R[D,T]] ↦
    hR.boundaryPeriod hgr C.endpoint_eq (Multiplicative.ofAdd y))
    (Subtype.ext (reducedBoundaryOrthogonalEquiv_apply hT x))).trans hp

variable [Z.Over S[k]] [IsIntegral Z] [Z.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 s[k,Z]]
  {F : Z.IdealSheafData} {U : BlowupTower Z m W}
  (hU : IsNodalBoundaryTower F s[k,Z] (𝟙 Z) U)
  [PrestableFamily (D.subscheme ↘ S[k])] [PrestableFamily (F.subscheme ↘ S[k])]
  {α : Type v₀} {β : Type v₁}
  {a : α → (D.subscheme ↘ S[k]).smoothLocus} {b : β → (F.subscheme ↘ S[k]).smoothLocus}
  {n₀ n₁ : ℕ} [NeZero n₀] [NeZero n₁]

/-- Extending an isometry through two ordered nodal blowup towers transports the
boundary orthogonals. With the lifted orientations, compatibility of the period
characters with a given sign is equivalent before and after extension. The
statement compares all orthogonal classes and retains the sign for cycles with
one or two components. -/
theorem boundaryPeriod_congr_iff_of_nodal_towers
    (e : B[k,X].IsometryEquiv B[k,Z]) (he : K[k,D].map e.toLinearMap = K[k,F]) (η : ℤˣ)
    (hD : D.IsEffectiveCartier) (hF : F.IsEffectiveCartier)
    (hgD : ∀ v : irreducibleComponents (D.subscheme.singularLocus k).blowup,
      (D.subscheme.blowupComponent v).toScheme.genus k = 0)
    (hgF : ∀ v : irreducibleComponents (F.subscheme.singularLocus k).blowup,
      (F.subscheme.blowupComponent v).toScheme.genus k = 0)
    (A : Scheme.NodalCycleNumbering a n₀) (C : Scheme.NodalCycleNumbering b n₁) :
    let : IsNoetherian X := isNoetherian_of_finiteType s[k,X]
    let : Y.Over S[k] := ⟨T.toBase ≫ s[k,X]⟩
    let : IsNoetherian Z := isNoetherian_of_finiteType s[k,Z]
    let : W.Over S[k] := ⟨U.toBase ≫ s[k,Z]⟩
    let : IsIntegral Y := hT.isClosedPointTower.isIntegral s[k,X]
    let : IsIntegral W := hU.isClosedPointTower.isIntegral s[k,Z]
    let : Y.IsProjectiveOver k := T.isProjectiveOver k
    let : W.IsProjectiveOver k := U.isProjectiveOver k
    let : SmoothOfRelativeDimension 2 s[k,Y] :=
      hT.isClosedPointTower.smoothOfRelativeDimension s[k,X]
    let : SmoothOfRelativeDimension 2 s[k,W] :=
      hU.isClosedPointTower.smoothOfRelativeDimension s[k,Z]
    let : PrestableFamily ((R[D,T]).subscheme ↘ S[k]) :=
      IsNodalBoundaryTower.prestableFamily_radical_comap_toBase hT hD
    let : PrestableFamily ((R[F,U]).subscheme ↘ S[k]) :=
      IsNodalBoundaryTower.prestableFamily_radical_comap_toBase hU hF
    let hD' := (IsNodalBoundaryTower.radical_comap_toBase hT hD
      (D.over_eq_subschemeι_comp (S := S[k]) ▸
        PrestableFamily.atWorstNodalOfRelativeDimensionOne)).1
    let hF' := (IsNodalBoundaryTower.radical_comap_toBase hU hF
      (F.over_eq_subschemeι_comp (S := S[k]) ▸
        PrestableFamily.atWorstNodalOfRelativeDimensionOne)).1
    let hgD' := IsNodalBoundaryTower.genus_blowupComponent_radical_comap_toBase_eq_zero hT hD hgD
    let hgF' := IsNodalBoundaryTower.genus_blowupComponent_radical_comap_toBase_eq_zero hU hF hgF
    let e' : B[k,Y].IsometryEquiv B[k,W] :=
      picardIsometryCongr k hT.isClosedPointTower hU.isClosedPointTower e
    ∀ {γ : Type v₂} {δ : Type v₃}
      {a' : γ → ((R[D,T]).subscheme ↘ S[k]).smoothLocus}
      {b' : δ → ((R[F,U]).subscheme ↘ S[k]).smoothLocus}
      {l₀ l₁ : ℕ} [NeZero l₀] [NeZero l₁]
      (A' : Scheme.NodalCycleNumbering a' l₀) (C' : Scheme.NodalCycleNumbering b' l₁),
      (π[D,T]).IsOrientedCycleSubdivision A' A →
      (π[F,U]).IsOrientedCycleSubdivision C' C →
      ∃ he' : K[k,R[D,T]].map e'.toLinearMap = K[k,R[F,U]],
        (∀ x : K[k,D], hD.boundaryPeriod hgD A.endpoint_eq (Multiplicative.ofAdd x) =
          hF.boundaryPeriod hgF C.endpoint_eq
            (Multiplicative.ofAdd (e.toLinearEquiv.ofSubmodules _ _ he x)) ^ (η : ℤ)) ↔
        ∀ x : K[k,R[D,T]], hD'.boundaryPeriod hgD' A'.endpoint_eq (Multiplicative.ofAdd x) =
          hF'.boundaryPeriod hgF' C'.endpoint_eq
            (Multiplicative.ofAdd (e'.toLinearEquiv.ofSubmodules _ _ he' x)) ^ (η : ℤ) := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ hD' hF' hgD' hgF' e' γ δ a' b' l₀ l₁ _ _ A' C' hA' hC'
  let p := reducedBoundaryOrthogonalEquiv hT
  let q := reducedBoundaryOrthogonalEquiv hU
  let f := e.toLinearEquiv.ofSubmodules _ _ he
  have hsquare (x : K[k,D]) : e' (p x).val = (q (f x)).val := by
    simp only [p, q, f, e', reducedBoundaryOrthogonalEquiv_apply, LinearEquiv.ofSubmodules_apply,
      IsometryEquiv.coe_toLinearEquiv,
      picardIsometryCongr_pullback, ofMul_toMul]
  have he' : K[k,R[D,T]].map e'.toLinearMap = K[k,R[F,U]] := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z, hz⟩ := p.surjective ⟨x, hx⟩
      have hzval : (p z).val = x := congrArg Subtype.val hz
      rw [← hzval]
      exact hsquare z ▸ (q (f z)).property
    · intro hy
      obtain ⟨z, hz⟩ := q.surjective ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := f.surjective z
      exact ⟨(p x).val, (p x).property, (hsquare x).trans (congrArg Subtype.val hz)⟩
  have hperiod (x : K[k,D]) :
      hD.boundaryPeriod hgD A.endpoint_eq (Multiplicative.ofAdd x) =
        hF.boundaryPeriod hgF C.endpoint_eq (Multiplicative.ofAdd (f x)) ^ (η : ℤ) ↔
      hD'.boundaryPeriod hgD' A'.endpoint_eq (Multiplicative.ofAdd (p x)) =
        hF'.boundaryPeriod hgF' C'.endpoint_eq
          (Multiplicative.ofAdd (e'.toLinearEquiv.ofSubmodules _ _ he' (p x))) ^ (η : ℤ) := by
    have haux : e'.toLinearEquiv.ofSubmodules _ _ he' (p x) = q (f x) :=
      Subtype.ext ((LinearEquiv.ofSubmodules_apply e'.toLinearEquiv he' (p x)).trans (hsquare x))
    have hleft := boundaryPeriod_reducedBoundaryOrthogonalEquiv hT hD hgD A hD' hgD' A' hA' x
    have hright := boundaryPeriod_reducedBoundaryOrthogonalEquiv hU hF hgF C hF' hgF' C' hC' (f x)
    have hright' := (congrArg (fun z : K[k,R[F,U]] ↦
      hF'.boundaryPeriod hgF' C'.endpoint_eq (Multiplicative.ofAdd z) ^ (η : ℤ)) haux).trans
        (congrArg (· ^ (η : ℤ)) hright)
    exact ⟨fun h ↦ hleft.trans (h.trans hright'.symm),
      fun h ↦ hleft.symm.trans (h.trans hright')⟩
  refine ⟨he', ?_, ?_⟩
  · intro h y
    obtain ⟨x, rfl⟩ := p.surjective y
    exact (hperiod x).mp (h x)
  · intro h x
    exact (hperiod x).mpr (h (p x))

end QPainleve.BlowupTower
