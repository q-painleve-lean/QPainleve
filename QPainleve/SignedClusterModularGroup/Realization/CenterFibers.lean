/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.CharacterTorus.Fiber
public import QPainleve.SignedClusterModularGroup.Realization.Comparison

/-!
# Comparing realized X maps over the centers

Compare two geometric realizations on the rational centers of a common nonempty
open. If the two target evaluations agree after pullback to each source surface,
then the independent rational X maps coincide. Dominant rational charts identify
the source evaluations with the fibers of the variable-center evaluation, so this
comparison also applies when the charts are given by birational maps.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TauCeti DiagonalizableGroup
open Scheme

universe u

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

open MarkedSurface (surfaceIso)

variable {k : Type u} [Field k] [IsSepClosed k] [Infinite k]
  {A N : Type u} [AddCommGroup A] [AddCommGroup N] [IsAddFG A] [IsAddFG N]
  [Module.Free ℤ A] [Module.Free ℤ N]
  {n : ℕ} [NeZero n] {L₀ L₁ : Type u} [AddCommGroup L₀] [AddCommGroup L₁]
  {B₀ : LinearMap.BilinForm ℤ L₀} {B₁ : LinearMap.BilinForm ℤ L₁}

local notation "S" => Spec (CommRingCat.of k)
local notation "D[" k "," B "]" => groupScheme k (FGCommGrpCat.of (Multiplicative B))

variable {T : Over (Spec (CommRingCat.of k))} {Y : Scheme.{u}} [Y.IsSeparated]
  {P₀ : Point D[k,A].X → MarkedSurface k n B₀ D[k,A].X.left}
  {P₁ : Point T → MarkedSurface k n B₁ Y}
  {C C' : D[k,A].X.left.PartialMap T.left} [IsDominant C.hom] [IsDominant C'.hom]
  [PartialMap.IsOver C D[k,A].X.hom T.hom] [PartialMap.IsOver C' D[k,A].X.hom T.hom]
  {F G : D[k,A].X.left ⤏ Y} [F.IsDominant] [G.IsDominant]

variable [Smooth D[k,A].X.hom]

/-- Two realizations have equal independent X maps if their target evaluations pull back
to the same rational map on the source surface at each rational center of a common
nonempty open. The source charts need only be dominant rational maps, with evaluation
given by the corresponding fibers of the variable-center evaluation for `v`. The charge
map can have arbitrary rank. -/
theorem xMap_eq_of_target_evaluation_eq_on_center_fibers
    (R : GeometricRealization P₀ P₁ C F) (R' : GeometricRealization P₀ P₁ C' G)
    (v : A →+ N) (sY : Y ⟶ S)
    [F.IsOver D[k,A].X.hom sY] [G.IsOver D[k,A].X.hom sY]
    (U : D[k,A].X.left.Opens) [Nonempty U] (hUC : U ≤ C.domain) (hUC' : U ≤ C'.domain)
    (hchart : ∀ p : Point D[k,A].X, (∃ c : S ⟶ U.toScheme, c ≫ U.ι = p.left) →
      ∃ (j : D[k,N].X.left ⤏ (P₀ p).surface) (_ : j.IsDominant),
        j.comp (P₀ p).evaluation =
          (CharacterTorus.evaluationAtCenter k v p.left (Over.w p)).toRationalMap)
    (heq : ∀ (x : CenterPoint C) (x' : CenterPoint C')
      (hs : x ≫ C.domainSource = x' ≫ C'.domainSource),
      (∃ c : S ⟶ U.toScheme, c ≫ U.ι = (x ≫ C.domainSource).left) →
      let r : FiberRealization (P₀ (x ≫ C.domainSource)) (P₁ (x' ≫ C'.domainTarget)) G
        R'.picard R'.boundaryAction := hs ▸ R'.fiber x'
      (surfaceIso (R.fiber x).iso).hom.toRationalMap.comp (P₁ (x ≫ C.domainTarget)).evaluation =
        (surfaceIso r.iso).hom.toRationalMap.comp (P₁ (x' ≫ C'.domainTarget)).evaluation) :
    F = G := by
  refine CharacterTorus.eq_of_compOfDefined_eq_at_centers k U v
    D[k,A].X.hom sY (𝟙 _) (Category.id_comp _) ?_
  intro c hc
  let factor (M : D[k,A].X.left.PartialMap T.left) (hle : U ≤ M.domain) : CenterPoint M :=
    Over.homMk (c ≫ D[k,A].X.left.homOfLE hle) (by simpa using hc)
  have factor_source (M : D[k,A].X.left.PartialMap T.left) (hle : U ≤ M.domain) :
      (factor M hle ≫ M.domainSource).left = c ≫ U.ι := by
    simp [factor]
  let x := factor C hUC
  let x' := factor C' hUC'
  have hp := factor_source C hUC
  have hs : x ≫ C.domainSource = x' ≫ C'.domainSource := by
    ext : 1
    exact hp.trans (factor_source C' hUC').symm
  let p := x ≫ C.domainSource
  obtain ⟨q, hq, heval⟩ := hchart p ⟨c, hp.symm⟩
  let : q.IsDominant := hq
  let r : FiberRealization (P₀ (x ≫ C.domainSource)) (P₁ (x' ≫ C'.domainTarget)) G
      R'.picard R'.boundaryAction := hs ▸ R'.fiber x'
  have hr : (surfaceIso (R.fiber x).iso).hom.toRationalMap.comp
      (P₁ (x ≫ C.domainTarget)).evaluation =
      (surfaceIso r.iso).hom.toRationalMap.comp (P₁ (x' ≫ C'.domainTarget)).evaluation := by
    exact heq x x' hs ⟨c, hp.symm⟩
  have hfixed := CharacterTorus.evaluationAtCenter_congr k v hp
    (hc := Over.w p) (hd := by simpa using hc)
  have hj := heval.trans (congrArg Hom.toRationalMap
    (hfixed.trans (Category.comp_id _).symm))
  rw [← hj]
  exact (R.fiber x).exists_compOfDefined_eq_of_target_evaluation_eq r q hr

end QPainleve.SignedClusterModularGroup.GeometricRealization
