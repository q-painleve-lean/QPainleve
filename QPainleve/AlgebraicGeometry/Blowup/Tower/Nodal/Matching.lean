/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Numbering

import QPainleve.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced

/-!
# Matching numbered nodal blowup towers

A tower of blowups at boundary nodes can be reproduced on another numbered
cycle by blowing up the corresponding node at each stage. The reduced total
boundaries carry compatible oriented subdivisions, and the extension of the
base Picard isometry matches their numbered prime classes. This is the
auxiliary-model step in [Gross, Hacking and Keel, Theorem 4.7][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S4.Thmtheorem7
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData LineBundleClass

universe u v w

namespace QPainleve.BlowupTower

local notation "S(" k ")" => Spec (CommRingCat.of k)
local notation "g(" k ", " X ")" => (X ↘ S(k))
local notation "Pic(" X ")" => Additive (LineBundleClass X)
local notation "B(" k ", " X ")" => Chow.intersectionBilinForm k X
local notation "P(" D ", " a ")" => Additive.ofMul (primeDivisorClass (boundaryPrimeEmbedding D a))
local notation "I(" x ")" => Scheme.Hom.ker (Scheme.fromSpecResidueField _ x)
local notation "π(" x ")" => blowupToBase (I(x))
local notation "R(" D ", " T ")" => radical (comap D (BlowupTower.toBase T))
local notation "β(" E ", " D ", " f ", " h ")" =>
  subschemeMap E D f (le_map_iff_comap_le.mpr h)

variable {k : Type u} [Field k] [IsAlgClosed k] {X Z : Scheme.{u}}
  [X.Over S(k)] [Z.Over S(k)] [IsIntegral X] [IsIntegral Z]
  [X.IsProjectiveOver k] [Z.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (g(k, X))] [SmoothOfRelativeDimension 2 (g(k, Z))]
  {D : X.IdealSheafData} {F : Z.IdealSheafData}
  [PrestableFamily (D.subscheme ↘ S(k))] [PrestableFamily (F.subscheme ↘ S(k))]
  {n : ℕ} [NeZero n] {ι : Type v} {κ : Type w}
  {p : ι → (D.subscheme ↘ S(k)).smoothLocus} {q : κ → (F.subscheme ↘ S(k)).smoothLocus}
  (A : Scheme.NodalCycleNumbering p n) (C : Scheme.NodalCycleNumbering q n)

-- Independent structure morphisms and ideals let the induction use associativity of
-- composition and identify the reduced boundary of a composite with an iterated one.
private abbrev HasMatchingNumberings {Y W : Scheme.{u}}
    (f : Y ⟶ X) (g : W ⟶ Z) (s : Y.Over S(k)) (t : W.Over S(k))
    (E : Y.IdealSheafData) (G : W.IdealSheafData) (l : ℕ)
    (e : Pic(Y) → Pic(W)) : Prop :=
  let : Y.Over S(k) := s
  let : W.Over S(k) := t
  ∀ [IsIntegral Y] [IsIntegral W]
    [SmoothOfRelativeDimension 2 (g(k, Y))] [SmoothOfRelativeDimension 2 (g(k, W))]
    [PrestableFamily (E.subscheme ↘ S(k))] [PrestableFamily (G.subscheme ↘ S(k))] [NeZero l]
    (hE : E.IsEffectiveCartier) (hG : G.IsEffectiveCartier)
    (h : D.comap f ≤ E) (h' : F.comap g ≤ G),
    let : Smooth (g(k, Y)) := SmoothOfRelativeDimension.smooth 2 _
    let : Smooth (g(k, W)) := SmoothOfRelativeDimension.smooth 2 _
    let := LocallyOfFiniteType.isLocallyNoetherian (g(k, Y))
    let := LocallyOfFiniteType.isLocallyNoetherian (g(k, W))
    let := (g(k, Y)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let := (g(k, W)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    ∃ (ι' : Type v) (κ' : Type w)
      (p' : ι' → (E.subscheme ↘ S(k)).smoothLocus)
      (q' : κ' → (G.subscheme ↘ S(k)).smoothLocus)
      (A' : Scheme.NodalCycleNumbering p' l) (C' : Scheme.NodalCycleNumbering q' l),
      (β(E, D, f, h)).IsOrientedCycleSubdivision A' A ∧
      (β(G, F, g, h')).IsOrientedCycleSubdivision C' C ∧
      ∀ a, e P(E, A'.boundaryPrimeEquiv hE a) = P(G, C'.boundaryPrimeEquiv hG a)

private theorem hasMatchingNumberings_nil (e : Pic(X) → Pic(Z))
    (hD : D.IsEffectiveCartier) (hF : F.IsEffectiveCartier)
    (he :
      let := LocallyOfFiniteType.isLocallyNoetherian (g(k, X))
      let := LocallyOfFiniteType.isLocallyNoetherian (g(k, Z))
      let := (g(k, X)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
      let := (g(k, Z)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
      ∀ a, e P(D, A.boundaryPrimeEquiv hD a) = P(F, C.boundaryPrimeEquiv hF a)) :
    HasMatchingNumberings A C (𝟙 X) (𝟙 Z) ‹X.Over S(k)› ‹Z.Over S(k)› D F n e := by
  intro _ _ _ _ _ _ _ _ _ h h' _ _ _ _ _ _
  exact ⟨ι, κ, p, q, A, C, (D.subschemeMap_id _).symm ▸ .id A,
    (F.subschemeMap_id _).symm ▸ .id C, he⟩

omit [IsIntegral X] [IsIntegral Z] [X.IsProjectiveOver k] [Z.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (g(k, X))] [SmoothOfRelativeDimension 2 (g(k, Z))] in
private theorem hasMatchingNumberings_blowup {Y W : Scheme.{u}}
    [Y.Over S(k)] [W.Over S(k)] [IsIntegral Y] [IsIntegral W]
    [Y.IsProjectiveOver k] [W.IsProjectiveOver k]
    [SmoothOfRelativeDimension 2 (g(k, Y))] [SmoothOfRelativeDimension 2 (g(k, W))]
    {E : Y.IdealSheafData} {G : W.IdealSheafData}
    [PrestableFamily (E.subscheme ↘ S(k))] [PrestableFamily (G.subscheme ↘ S(k))]
    (hE : E.IsEffectiveCartier) (hG : G.IsEffectiveCartier)
    {f : Y ⟶ X} {g : W ⟶ Z} (hf : D.comap f ≤ E) (hg : F.comap g ≤ G)
    {l : ℕ} [NeZero l] (e : B(k, Y).IsometryEquiv B(k, W))
    (ih : HasMatchingNumberings A C f g ‹Y.Over S(k)› ‹W.Over S(k)› E G l e)
    {x : Y} (hx : E.IsNodeOfReducedBoundary (g(k, Y)) x) :
    ∃ z : W, ∃ (hx' : IsClosed ({x} : Set Y)) (hz' : IsClosed ({z} : Set W)),
      G.IsNodeOfReducedBoundary (g(k, W)) z ∧
      HasMatchingNumberings A C (π(x) ≫ f) (π(z) ≫ g) ⟨π(x) ≫ g(k, Y)⟩ ⟨π(z) ≫ g(k, W)⟩
        (E.comap (π(x))).radical (G.comap (π(z))).radical (l + 1)
        (picardIsometryCongr k (IsClosedPointTower.snoc .nil x hx' rfl)
          (IsClosedPointTower.snoc .nil z hz' rfl) e) := by
  have : NeZero (l + 1) := ⟨Nat.succ_ne_zero l⟩
  obtain ⟨α, γ, a, c, A', C', hA, hC, he⟩ := @ih
    ‹IsIntegral Y› ‹IsIntegral W›
    ‹SmoothOfRelativeDimension 2 (g(k, Y))› ‹SmoothOfRelativeDimension 2 (g(k, W))›
    ‹PrestableFamily (E.subscheme ↘ S(k))› ‹PrestableFamily (G.subscheme ↘ S(k))›
    ‹NeZero l› hE hG hf hg
  obtain ⟨i, rfl⟩ := A'.exists_ambientNode_eq hx rfl
  refine ⟨C'.ambientNode i, A'.isClosed_ambientNode i, C'.isClosed_ambientNode i,
    C'.isNodeOfReducedBoundary_ambientNode i rfl, ?_⟩
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  let : (I(A'.ambientNode i)).blowup.Over S(k) := ⟨π(A'.ambientNode i) ≫ g(k, Y)⟩
  let : (I(C'.ambientNode i)).blowup.Over S(k) := ⟨π(C'.ambientNode i) ≫ g(k, W)⟩
  obtain ⟨A'', C'', hA', hC', he'⟩ :=
    picardIsometryCongr_nodal_boundaryPrimes_of_numbered_nodes A' C' hE hG i e he
      (PEmpty.elim : PEmpty.{v+1} → _) (PEmpty.elim : PEmpty.{w+1} → _)
  exact ⟨_, _, _, _, A'', C'', subschemeMap_comp _ hf (le_radical _) ▸ hA'.comp hA,
    subschemeMap_comp _ hg (le_radical _) ▸ hC'.comp hC, he'⟩

variable (hD : D.IsEffectiveCartier) (hF : F.IsEffectiveCartier)
  (e : B(k, X).IsometryEquiv B(k, Z))

private abbrev HasMatchingTower {m : ℕ} {Y : Scheme.{u}} {T : BlowupTower X m Y}
    (hT : IsNodalBoundaryTower D (g(k, X)) (𝟙 X) T) : Prop :=
  ∃ (W : Scheme.{u}) (U : BlowupTower Z m W)
    (hU : IsNodalBoundaryTower F (g(k, Z)) (𝟙 Z) U),
    HasMatchingNumberings A C T.toBase U.toBase ⟨T.toBase ≫ g(k, X)⟩ ⟨U.toBase ≫ g(k, Z)⟩
      (R(D, T)) (R(F, U)) (n + m)
      (picardIsometryCongr k hT.isClosedPointTower hU.isClosedPointTower e)

include hD hF in
private theorem hasMatchingTower_snoc {m : ℕ} {Y : Scheme.{u}} {T : BlowupTower X m Y}
    (hT : IsNodalBoundaryTower D (g(k, X)) (𝟙 X) T)
    {x : Y} (hx : IsClosed ({x} : Set Y))
    (hn : (D.comap (T.toBase ≫ 𝟙 X)).IsNodeOfReducedBoundary ((T.toBase ≫ 𝟙 X) ≫ g(k, X)) x)
    (ih : HasMatchingTower A C e hT) :
    HasMatchingTower A C e (hT.snoc x hx rfl hn :
      IsNodalBoundaryTower D (g(k, X)) (𝟙 X) (T.snoc (I(x)))) := by
  obtain ⟨W, U, hU, hmatch⟩ := ih
  have : IsNoetherian X := isNoetherian_of_finiteType (g(k, X))
  have : IsNoetherian Z := isNoetherian_of_finiteType (g(k, Z))
  let : Y.Over S(k) := ⟨T.toBase ≫ g(k, X)⟩
  let : W.Over S(k) := ⟨U.toBase ≫ g(k, Z)⟩
  let : Y.IsProjectiveOver k := T.isProjectiveOver k
  let : W.IsProjectiveOver k := U.isProjectiveOver k
  let : IsIntegral Y := hT.isClosedPointTower.isIntegral (g(k, X))
  let : IsIntegral W := hU.isClosedPointTower.isIntegral (g(k, Z))
  let : SmoothOfRelativeDimension 2 (g(k, Y)) :=
    hT.isClosedPointTower.smoothOfRelativeDimension (g(k, X))
  let : SmoothOfRelativeDimension 2 (g(k, W)) :=
    hU.isClosedPointTower.smoothOfRelativeDimension (g(k, Z))
  have hnd : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ g(k, X)) :=
    PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := D.subscheme ↘ S(k))
  have hnf : AtWorstNodalOfRelativeDimensionOne (F.subschemeι ≫ g(k, Z)) :=
    PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := F.subscheme ↘ S(k))
  let : PrestableFamily ((R(D, T)).subscheme ↘ S(k)) :=
    hT.prestableFamily_radical_comap_toBase hD
  let : PrestableFamily ((R(F, U)).subscheme ↘ S(k)) :=
    hU.prestableFamily_radical_comap_toBase hF
  let : NeZero (n + m) := ⟨by have := NeZero.ne n; omega⟩
  have hs : g(k, Y) = T.toBase ≫ g(k, X) := rfl
  have ht : g(k, W) = U.toBase ≫ g(k, Z) := rfl
  have hn' : (R(D, T)).IsNodeOfReducedBoundary (g(k, Y)) x := by
    simpa only [hs, isNodeOfReducedBoundary_radical, Category.comp_id] using hn
  let e' := picardIsometryCongr k hT.isClosedPointTower hU.isClosedPointTower e
  obtain ⟨z, hx', hz, hnode, hnext⟩ := hasMatchingNumberings_blowup A C
    (hT.radical_comap_toBase hD hnd).1 (hU.radical_comap_toBase hF hnf).1
    (le_radical _) (le_radical _) e' (@hmatch) hn'
  have hnz : (F.comap (U.toBase ≫ 𝟙 Z)).IsNodeOfReducedBoundary
      ((U.toBase ≫ 𝟙 Z) ≫ g(k, Z)) z := by
    rw [Category.comp_id, ← ht]
    exact (isNodeOfReducedBoundary_radical ..).mp hnode
  let hUn := hU.snoc z hz rfl hnz
  refine ⟨_, U.snoc (I(z)), hUn, ?_⟩
  have heq :
      (picardIsometryCongr k (hT.snoc x hx rfl hn).isClosedPointTower hUn.isClosedPointTower e :
        Pic((I(x)).blowup) → Pic((I(z)).blowup)) =
      (picardIsometryCongr k (IsClosedPointTower.snoc .nil x hx' rfl)
        (IsClosedPointTower.snoc .nil z hz rfl) e' :
        Pic((I(x)).blowup) → Pic((I(z)).blowup)) :=
    funext (picardIsometryCongr_snoc_apply k hT.isClosedPointTower hU.isClosedPointTower
      e hx' hz rfl rfl)
  rw [heq, toBase_snoc, toBase_snoc, Category.assoc, Category.assoc, comap_comp, comap_comp,
    Nat.add_succ]
  simp only [radical_comap_radical] at hnext
  exact @hnext

private theorem hasMatchingTower {m : ℕ} {Y : Scheme.{u}} {T : BlowupTower X m Y}
    (hT : IsNodalBoundaryTower D (g(k, X)) (𝟙 X) T)
    (he :
      let := LocallyOfFiniteType.isLocallyNoetherian (g(k, X))
      let := LocallyOfFiniteType.isLocallyNoetherian (g(k, Z))
      let := (g(k, X)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
      let := (g(k, Z)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
      ∀ a, e P(D, A.boundaryPrimeEquiv hD a) = P(F, C.boundaryPrimeEquiv hF a)) :
    HasMatchingTower A C e hT := by
  induction hT with
  | nil =>
    have hredD : IsReduced D.subscheme :=
      (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := D.subscheme ↘ S(k))).isReduced
    have hredF : IsReduced F.subscheme :=
      (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := F.subscheme ↘ S(k))).isReduced
    refine ⟨Z, .nil, .nil, ?_⟩
    have heq : (picardIsometryCongr k IsClosedPointTower.nil IsClosedPointTower.nil e :
        Pic(X) → Pic(Z)) = e := funext (picardIsometryCongr_nil_apply k e)
    rw [heq, toBase_nil, toBase_nil, Category.id_comp, Category.id_comp, comap_id, comap_id,
      Nat.add_zero, D.isReduced_subscheme_iff_radical_eq.mp hredD,
      F.isReduced_subscheme_iff_radical_eq.mp hredF]
    exact @hasMatchingNumberings_nil k _ _ X Z _ _ _ _ _ _ _ _ D F _ _ n _ ι κ p q
      A C e hD hF he
  | @snoc m Y T I hT x hx hI hn ih =>
    subst I
    exact hasMatchingTower_snoc A C hD hF e hT hx hn ih

/-- A specified nodal blowup tower on one numbered Cartier boundary can be matched
by a nodal blowup tower on the other. Both projections induce oriented subdivisions,
and the Picard extension matching the ordered total exceptional classes also matches
every numbered prime of the reduced total boundaries. -/
theorem exists_matching_numbered_nodal_boundary_tower {m : ℕ} {Y : Scheme.{u}}
    {T : BlowupTower X m Y} (hT : IsNodalBoundaryTower D (g(k, X)) (𝟙 X) T)
    (he :
      let := LocallyOfFiniteType.isLocallyNoetherian (g(k, X))
      let := LocallyOfFiniteType.isLocallyNoetherian (g(k, Z))
      let := (g(k, X)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
      let := (g(k, Z)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
      ∀ a, e P(D, A.boundaryPrimeEquiv hD a) = P(F, C.boundaryPrimeEquiv hF a)) :
    ∃ (W : Scheme.{u}) (U : BlowupTower Z m W)
      (hU : IsNodalBoundaryTower F (g(k, Z)) (𝟙 Z) U),
      let E := R(D, T)
      let G := R(F, U)
      let : Y.Over S(k) := ⟨T.toBase ≫ g(k, X)⟩
      let : W.Over S(k) := ⟨U.toBase ≫ g(k, Z)⟩
      let : PrestableFamily (E.subscheme ↘ S(k)) :=
        hT.prestableFamily_radical_comap_toBase hD
      let : PrestableFamily (G.subscheme ↘ S(k)) :=
        hU.prestableFamily_radical_comap_toBase hF
      let : NeZero (n + m) := ⟨by have := NeZero.ne n; omega⟩
      let : IsNoetherian X := isNoetherian_of_finiteType (g(k, X))
      let : IsNoetherian Z := isNoetherian_of_finiteType (g(k, Z))
      let hE := (hT.radical_comap_toBase hD
        (D.over_eq_subschemeι_comp (S := S(k)) ▸
          PrestableFamily.atWorstNodalOfRelativeDimensionOne)).1
      let hG := (hU.radical_comap_toBase hF
        (F.over_eq_subschemeι_comp (S := S(k)) ▸
          PrestableFamily.atWorstNodalOfRelativeDimensionOne)).1
      let s := T.toBase ≫ g(k, X)
      let t := U.toBase ≫ g(k, Z)
      let : IsIntegral Y := hT.isClosedPointTower.isIntegral (g(k, X))
      let : IsIntegral W := hU.isClosedPointTower.isIntegral (g(k, Z))
      let : SmoothOfRelativeDimension 2 s := hT.isClosedPointTower.smoothOfRelativeDimension _
      let : SmoothOfRelativeDimension 2 t := hU.isClosedPointTower.smoothOfRelativeDimension _
      let : Smooth s := SmoothOfRelativeDimension.smooth 2 s
      let : Smooth t := SmoothOfRelativeDimension.smooth 2 t
      let := LocallyOfFiniteType.isLocallyNoetherian s
      let := LocallyOfFiniteType.isLocallyNoetherian t
      let := s.uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
      let := t.uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
      ∃ (ι' : Type v) (κ' : Type w)
        (p' : ι' → (E.subscheme ↘ S(k)).smoothLocus)
        (q' : κ' → (G.subscheme ↘ S(k)).smoothLocus)
        (A' : Scheme.NodalCycleNumbering p' (n + m)) (C' : Scheme.NodalCycleNumbering q' (n + m)),
        (β(E, D, T.toBase, le_radical _)).IsOrientedCycleSubdivision A' A ∧
        (β(G, F, U.toBase, le_radical _)).IsOrientedCycleSubdivision C' C ∧
        ∀ a, picardIsometryCongr k hT.isClosedPointTower hU.isClosedPointTower e
          P(E, A'.boundaryPrimeEquiv hE a) = P(G, C'.boundaryPrimeEquiv hG a) := by
  obtain ⟨W, U, hU, h⟩ := hasMatchingTower A C hD hF e hT he
  refine ⟨W, U, hU, ?_⟩
  intro E G _ _ hEpre hGpre hlen _ _ hE hG s t hY hW hs ht _ _ _ _ _ _
  exact @h hY hW hs ht hEpre hGpre hlen hE hG (le_radical _) (le_radical _)

end QPainleve.BlowupTower
