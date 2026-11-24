/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Boundary
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Isometry
public import QPainleve.AlgebraicGeometry.Curves.Node.Ambient
public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Subdivision

import QPainleve.AlgebraicGeometry.Blowup.Point.BoundaryPrimes
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Branches.Subdivision
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.Noetherian

/-!
# Matching numbered nodal blowups

Given aligned cycle numberings and an isometry matching the numbered boundary
classes, blow up the node with the same index on both sides. Numbering the two
reduced total boundaries from the same cut gives aligned ordered branches and
numbered prime classes for the extended Picard isometry. This is the local step
in the corner blowup argument of [Gross, Hacking and Keel, Theorem 4.7][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S4.Thmtheorem7
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData LineBundleClass

universe u v w

namespace QPainleve.BlowupTower

local notation "S(" k ")" => Spec (CommRingCat.of k)
local notation "g(" k ", " X ")" => (X ↘ S(k))
local notation "B(" k ", " X ")" => Chow.intersectionBilinForm k X
local notation "pointIdeal(" X "," p ")" => Scheme.Hom.ker (Scheme.fromSpecResidueField X p)
local notation "tower(" X "," p ")" => BlowupTower.nil.snoc (pointIdeal(X,p))
local notation "Bnd(" D "," p ")" =>
  radical (comap D (blowupToBase (pointIdeal(_,p))))
local notation "proj(" D "," p ")" =>
  subschemeMap (Bnd(D,p)) D (blowupToBase (pointIdeal(_,p)))
    (le_map_iff_comap_le.mpr (le_radical _))
local notation "node(" D "," A "," i ")" =>
  subschemeι D (subschemeι (Scheme.singularLocus _ (subscheme D))
    (Scheme.NodalCycleNumbering.node A i))
local notation "class(" D "," p ")" =>
  Additive.ofMul (primeDivisorClass (boundaryPrimeEmbedding D p))

/-- The one-step tower blowing up a numbered node is a nodal boundary tower. -/
theorem isNodalBoundaryTower_numbered_node
    {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}} [X.Over S(k)]
    {D : X.IdealSheafData} [PrestableFamily (g(k, D.subscheme))]
    {n : ℕ} [NeZero n] {ι : Type v} {p : ι → (g(k, D.subscheme)).smoothLocus}
    (A : Scheme.NodalCycleNumbering p n) (i : ZMod n) :
    IsNodalBoundaryTower D (g(k, X)) (𝟙 X) (tower(X,node(D,A,i))) := by
  refine .snoc .nil _ (A.isClosed_singleton_subschemeι_node i) rfl ?_
  simpa only [toBase_nil, comap_id, Category.id_comp] using
    A.isNodeOfReducedBoundary_subschemeι_node (g(k, X)) D.over_eq_subschemeι_comp i

section OneSurface

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over S(k)]
  {D : X.IdealSheafData} [PrestableFamily (g(k, D.subscheme))]
  {n : ℕ} [NeZero n] {ι : Type v} {p : ι → (g(k, D.subscheme)).smoothLocus}
  (A : Scheme.NodalCycleNumbering p n) (i : ZMod n)

private theorem exists_numbered_nodal_subdivision [IsIntegral X] [QuasiCompact (g(k, X))]
    [SmoothOfRelativeDimension 2 (g(k, X))] (hD : D.IsEffectiveCartier) (I : X.IdealSheafData)
    (hI : I = pointIdeal(X,node(D,A,i))) :
    let p := node(D,A,i)
    let R := (D.comap I.blowupToBase).radical
    let : I.blowup.Over S(k) := ⟨I.blowupToBase ≫ g(k, X)⟩
    ∀ [PrestableFamily (g(k, R.subscheme))]
      {ι' : Type w} (d' : ι' → (g(k, R.subscheme)).smoothLocus),
      ∃ A' : Scheme.NodalCycleNumbering d' (n + 1),
        Scheme.Hom.IsOrientedCycleSubdivision
          (R.subschemeMap D I.blowupToBase (le_map_iff_comap_le.mpr (le_radical _))) A' A ∧
        ∀ a : ZMod (n + 1),
          I.blowupToBase (R.subschemeι (A'.componentGenericPoint a)) =
          if a.val < n then D.subschemeι (A.componentGenericPoint ((a.val : ZMod n) + (i + 1)))
          else p := by
  let z := (D.subscheme.singularLocus k).subschemeι (A.node i)
  have hz : z ∈ (D.subscheme.singularLocus k).support :=
    (D.subscheme.singularLocus k).range_subschemeι.le (Set.mem_range_self _)
  rw [X.ker_fromSpecResidueField_eq_vanishingIdeal] at hI
  subst I
  intro p R over _ _ d'
  obtain ⟨A', hA', hproj⟩ := D.exists_isOrientedCycleSubdivision_nodalBlowup_at
    (A.isClosed_singleton_subschemeι_node i) hz D.over_eq_subschemeι_comp
    R.over_eq_subschemeι_comp hD A i rfl d'
  refine ⟨A', hA', fun a ↦ ?_⟩
  have h := congrArg D.subschemeι (hproj a)
  rw [← Scheme.Hom.comp_apply, subschemeMap_subschemeι, Scheme.Hom.comp_apply] at h
  split_ifs at h ⊢ <;> exact h

end OneSurface

section Isometry

variable {k : Type u} [Field k] [IsAlgClosed k] {X Z : Scheme.{u}}
  [X.Over S(k)] [Z.Over S(k)] [IsIntegral X] [IsIntegral Z]
  [X.IsProjectiveOver k] [Z.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (g(k, X))] [SmoothOfRelativeDimension 2 (g(k, Z))]
  {D : X.IdealSheafData} {F : Z.IdealSheafData}
  [PrestableFamily (g(k, D.subscheme))] [PrestableFamily (g(k, F.subscheme))]
  {n : ℕ} [NeZero n] {ι : Type v} {κ : Type w}
  {d : ι → (g(k, D.subscheme)).smoothLocus} {f : κ → (g(k, F.subscheme)).smoothLocus}
  (A : Scheme.NodalCycleNumbering d n) (C : Scheme.NodalCycleNumbering f n) (i : ZMod n)
  (hD : D.IsEffectiveCartier) (hF : F.IsEffectiveCartier)

private theorem map_prime_after_blowup_of_projection
    (hD : D.IsEffectiveCartier) (hF : F.IsEffectiveCartier) {p : X} {q : Z}
    (hp : IsClosed ({p} : Set X)) (hq : IsClosed ({q} : Set Z))
    (hpn : D.IsNodeOfReducedBoundary (g(k, X)) p)
    (hqn : F.IsNodeOfReducedBoundary (g(k, Z)) q)
    (σ : D.boundaryPrimes ≃ F.boundaryPrimes)
    (hcenter : ∀ a : D.boundaryPrimes, p ∈ closure {a.val} ↔ q ∈ closure {(σ a).val})
    (e : B(k, X).IsometryEquiv B(k, Z))
    (he : letI := (g(k, X)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
          letI := (g(k, Z)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
          letI := LocallyOfFiniteType.isLocallyNoetherian (g(k, X))
          letI := LocallyOfFiniteType.isLocallyNoetherian (g(k, Z))
          ∀ a, e class(D,a) = class(F,σ a)) :
    let T := tower(X,p)
    let U := tower(Z,q)
    let hT : IsClosedPointTower X T := .snoc .nil p hp rfl
    let hU : IsClosedPointTower Z U := .snoc .nil q hq rfl
    let : IsNoetherian X := isNoetherian_of_finiteType (g(k, X))
    let : IsNoetherian Z := isNoetherian_of_finiteType (g(k, Z))
    let := T.isNoetherian
    let := U.isNoetherian
    let := hT.smoothOfRelativeDimension (g(k, X))
    let := hU.smoothOfRelativeDimension (g(k, Z))
    let := hT.isIntegral (g(k, X))
    let := hU.isIntegral (g(k, Z))
    let := (T.toBase ≫ g(k, X)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let := (U.toBase ≫ g(k, Z)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    ∀ (a : (Bnd(D,p)).boundaryPrimes) (b : (Bnd(F,q)).boundaryPrimes),
      (let π := (pointIdeal(X,p)).blowupToBase
       let τ := (pointIdeal(Z,q)).blowupToBase
       (π a.val = p ∧ τ b.val = q) ∨
         (∃ c : D.boundaryPrimes, π a.val = c.val ∧ τ b.val = (σ c).val)) →
      picardIsometryCongr k hT hU e class(Bnd(D,p),a) = class(Bnd(F,q),b) := by
  have : IsNoetherian X := isNoetherian_of_finiteType (g(k, X))
  have : IsNoetherian Z := isNoetherian_of_finiteType (g(k, Z))
  have hnd : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ g(k, X)) := by
    rw [← D.over_eq_subschemeι_comp]
    exact PrestableFamily.atWorstNodalOfRelativeDimensionOne
  have hnf : AtWorstNodalOfRelativeDimensionOne (F.subschemeι ≫ g(k, Z)) := by
    rw [← F.over_eq_subschemeι_comp]
    exact PrestableFamily.atWorstNodalOfRelativeDimensionOne
  obtain ⟨σ', hσ'⟩ := picardIsometryCongr_nodal_boundaryPrimes σ hcenter e he hp hq hD hF
    hnd hnf hpn hqn
  intro T U hT hU _ _ _ _ _ _ _ _ _ _ a b hab
  let π := (pointIdeal(X,p)).blowupToBase
  let τ := (pointIdeal(Z,q)).blowupToBase
  let a' : (D.comap π).boundaryPrimes :=
    Set.equivOfEq (boundaryPrimes_eq_of_support_eq (support_radical _)) a
  let b' : (F.comap τ).boundaryPrimes :=
    Set.equivOfEq (boundaryPrimes_eq_of_support_eq (support_radical _)) b
  have ha' : a'.val = a.val := (rfl)
  have hb' : b'.val = b.val := (rfl)
  have hne (c : D.boundaryPrimes) : c.val ≠ p := by
    intro hc
    have h := (mem_boundaryPrimes.mp c.property).2
    rw [hc, coheight_eq_of_isClosed_of_smoothOfRelativeDimension (n := 2) (g(k, X)) hp] at h
    norm_num at h
  have hproj : τ (σ' a').val = τ b'.val := by
    rcases (hσ' a').2 with ⟨hx, hy⟩ | ⟨c, hx, hy⟩ <;>
      rcases hab with ⟨hx', hy'⟩ | ⟨c', hx', hy'⟩
    · exact hy.trans (hb' ▸ hy').symm
    · exact (hne c' (hx'.symm.trans (ha' ▸ hx))).elim
    · exact (hne c (hx.symm.trans (ha'.symm ▸ hx'))).elim
    · have hc : c = c' := Subtype.ext (hx.symm.trans (ha'.symm ▸ hx'))
      exact hy.trans (by rw [hc, hb', hy'])
  have hb'' : σ' a' = b' := Subtype.ext
    (F.injOn_blowupToBase_boundaryPrimes_comap_pointBlowup (g(k, Z)) hq
      (mem_support_of_isNodeOfReducedBoundary hqn) (σ' a').property b'.property hproj)
  have haPrime : (D.comap π).boundaryPrimeEmbedding a' = (Bnd(D,p)).boundaryPrimeEmbedding a :=
    Subtype.ext (by simpa only [coe_boundaryPrimeEmbedding] using ha')
  have hbPrime : (F.comap τ).boundaryPrimeEmbedding b' = (Bnd(F,q)).boundaryPrimeEmbedding b :=
    Subtype.ext (by simpa only [coe_boundaryPrimeEmbedding] using hb')
  rw [← haPrime, ← hbPrime, ← hb'']
  exact (hσ' a').1

/-- Blow up the same numbered node on two surfaces whose Picard isometry matches the
numbered boundary classes. The oriented subdivisions admit aligned cycle numberings for
which the extended isometry matches every reduced total boundary class. Both numberings start
at the strict transforms of component `i + 1` and end at the exceptional components. -/
theorem picardIsometryCongr_of_numbered_nodal_blowups
    (e : B(k, X).IsometryEquiv B(k, Z))
    (he : letI := (g(k, X)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
          letI := (g(k, Z)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
          letI := LocallyOfFiniteType.isLocallyNoetherian (g(k, X))
          letI := LocallyOfFiniteType.isLocallyNoetherian (g(k, Z))
          ∀ j, e class(D,A.boundaryPrimesEquiv hD j) = class(F,C.boundaryPrimesEquiv hF j)) :
    let p := node(D,A,i)
    let q := node(F,C,i)
    let T := tower(X,p)
    let U := tower(Z,q)
    let J := pointIdeal(X,p)
    let K := pointIdeal(Z,q)
    let hT := isNodalBoundaryTower_numbered_node A i
    let hU := isNodalBoundaryTower_numbered_node C i
    let : IsNoetherian X := isNoetherian_of_finiteType (g(k, X))
    let : IsNoetherian Z := isNoetherian_of_finiteType (g(k, Z))
    let := T.isNoetherian
    let := U.isNoetherian
    let := hT.isClosedPointTower.smoothOfRelativeDimension (g(k, X))
    let := hU.isClosedPointTower.smoothOfRelativeDimension (g(k, Z))
    let := hT.isClosedPointTower.isIntegral (g(k, X))
    let := hU.isClosedPointTower.isIntegral (g(k, Z))
    let := (T.toBase ≫ g(k, X)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let := (U.toBase ≫ g(k, Z)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let : J.blowup.Over S(k) := ⟨J.blowupToBase ≫ g(k, X)⟩
    let : K.blowup.Over S(k) := ⟨K.blowupToBase ≫ g(k, Z)⟩
    let : PrestableFamily (g(k, (Bnd(D,p)).subscheme)) := by
      rw [over_eq_subschemeι_comp]
      have h := hT.prestableFamily_radical_comap_toBase hD
      rw [toBase_snoc, toBase_nil, Category.comp_id] at h
      exact h
    let : PrestableFamily (g(k, (Bnd(F,q)).subscheme)) := by
      rw [over_eq_subschemeι_comp]
      have h := hU.prestableFamily_radical_comap_toBase hF
      rw [toBase_snoc, toBase_nil, Category.comp_id] at h
      exact h
    let hD' : (Bnd(D,p)).IsEffectiveCartier := by
      have hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ g(k, X)) :=
        (D.over_eq_subschemeι_comp (S := S(k))) ▸
          PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := g(k, D.subscheme))
      simpa only [toBase_snoc, toBase_nil, Category.comp_id] using
        (hT.radical_comap_toBase hD hN).1
    let hF' : (Bnd(F,q)).IsEffectiveCartier := by
      have hN : AtWorstNodalOfRelativeDimensionOne (F.subschemeι ≫ g(k, Z)) :=
        (F.over_eq_subschemeι_comp (S := S(k))) ▸
          PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := g(k, F.subscheme))
      simpa only [toBase_snoc, toBase_nil, Category.comp_id] using
        (hU.radical_comap_toBase hF hN).1
    ∀ {ι' : Type v} {κ' : Type w}
      (d' : ι' → (g(k, (Bnd(D,p)).subscheme)).smoothLocus)
      (f' : κ' → (g(k, (Bnd(F,q)).subscheme)).smoothLocus),
      ∃ (A' : Scheme.NodalCycleNumbering d' (n + 1)) (C' : Scheme.NodalCycleNumbering f' (n + 1)),
        (proj(D,p)).IsOrientedCycleSubdivision A' A ∧
        (proj(F,q)).IsOrientedCycleSubdivision C' C ∧
        ∀ j : ZMod (n + 1),
          let l := (j.val : ZMod n) + (i + 1)
          J.blowupToBase ((Bnd(D,p)).subschemeι (A'.componentGenericPoint j)) =
            (if j.val < n then D.subschemeι (A.componentGenericPoint l) else p) ∧
          K.blowupToBase ((Bnd(F,q)).subschemeι (C'.componentGenericPoint j)) =
            (if j.val < n then F.subschemeι (C.componentGenericPoint l) else q) ∧
          picardIsometryCongr k hT.isClosedPointTower hU.isClosedPointTower e
            class(Bnd(D,p),A'.boundaryPrimesEquiv hD' j) =
              class(Bnd(F,q),C'.boundaryPrimesEquiv hF' j) := by
  intro p q T U J K hT hU _ _ _ _ _ _ _ _ _ _ _ _ _ _ hD' hF' _ _ d' f'
  let := (g(k, X)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let := (g(k, Z)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  obtain ⟨A', hA', hp'⟩ := exists_numbered_nodal_subdivision A i hD J rfl d'
  obtain ⟨C', hC', hq'⟩ := exists_numbered_nodal_subdivision C i hF K rfl f'
  let σ := (A.boundaryPrimesEquiv hD).symm.trans (C.boundaryPrimesEquiv hF)
  have hσ (j : ZMod n) : σ (A.boundaryPrimesEquiv hD j) = C.boundaryPrimesEquiv hF j := by
    simp [σ]
  have hcenter (a : D.boundaryPrimes) : p ∈ closure {a.val} ↔ q ∈ closure {(σ a).val} := by
    obtain ⟨j, rfl⟩ := (A.boundaryPrimesEquiv hD).surjective a
    rw [hσ]
    exact (A.subschemeι_node_mem_closure_boundaryPrimesEquiv_iff hD i j).trans
      (C.subschemeι_node_mem_closure_boundaryPrimesEquiv_iff hF i j).symm
  have he' (a : D.boundaryPrimes) : e class(D,a) = class(F,σ a) := by
    obtain ⟨j, rfl⟩ := (A.boundaryPrimesEquiv hD).surjective a
    rw [hσ]
    exact he j
  refine ⟨A', C', hA', hC', fun j ↦ ⟨hp' j, hq' j, ?_⟩⟩
  apply map_prime_after_blowup_of_projection hD hF
    (A.isClosed_singleton_subschemeι_node i) (C.isClosed_singleton_subschemeι_node i)
    (A.isNodeOfReducedBoundary_subschemeι_node (g(k, X)) D.over_eq_subschemeι_comp i)
    (C.isNodeOfReducedBoundary_subschemeι_node (g(k, Z)) F.over_eq_subschemeι_comp i)
    σ hcenter e he'
  simp only [Scheme.NodalCycleNumbering.boundaryPrimesEquiv_apply_val]
  by_cases hj : j.val < n
  · let l : ZMod n := (j.val : ZMod n) + (i + 1)
    refine Or.inr ⟨A.boundaryPrimesEquiv hD l, ?_, ?_⟩
    · simpa only [Scheme.NodalCycleNumbering.boundaryPrimesEquiv_apply_val, hj, ite_true]
        using hp' j
    · simpa only [hσ, Scheme.NodalCycleNumbering.boundaryPrimesEquiv_apply_val, hj, ite_true]
        using hq' j
  · exact Or.inl ⟨by simpa only [hj, ite_false] using hp' j,
      by simpa only [hj, ite_false] using hq' j⟩

end Isometry

end QPainleve.BlowupTower
