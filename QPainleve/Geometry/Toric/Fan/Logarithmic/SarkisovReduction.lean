/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Factorization
public import QPainleve.Geometry.Toric.Fan.ProjectiveSpace.Plane
public import TauCeti.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Boundary
import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import QPainleve.AlgebraicGeometry.Morphisms.Modification.Birational
import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic
import QPainleve.Geometry.Toric.Fan.Logarithmic.CommonResolution
import QPainleve.Geometry.Toric.Fan.StarSubdivision.Tower

/-!
# Plane reduction of resolved Sarkisov factorizations

Both ends of a specified toric change of presentation can be reduced to the
projective plane on one nodal blowup tower. A resolved factorization between
the plane projections then extends to the original projections.

This is the reduction to a plane target in [Lutz, Theorem 8.4][HKL].
The construction uses `exists_common_nodal_resolution_of_toric_changes`
and concatenates the paths of regular partial composites.

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=73
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan.LogarithmicProjection

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" Φ "]" => Fan.algebraicRealization Φ
local notation "π[" H "]" => FanHom.algebraicMap (IsSubdivision.toFanHom H)

variable {Z : Scheme} [Z.Over S] [IsIntegral Z] [SmoothOfRelativeDimension 2 (Z ↘ S)]
  {D : Z.IdealSheafData}

/-- The two specified projections admit a Sarkisov path on a nodal blowup
tower of their common source. The endpoints are the pullbacks of the specified
projections and all vertices share the reduced total boundary as pole ideal. -/
def HasResolvedSarkisovFactorization [IsNoetherian Z] (A B : LogarithmicProjection i D) : Prop :=
  ∃ (n : ℕ) (W : Scheme) (T : BlowupTower Z n W)
    (hT : IsNodalBoundaryTower D (Z ↘ S) (𝟙 Z) T),
    letI : W.Over S := ⟨T.toBase ≫ Z ↘ S⟩
    letI : IsIntegral W := hT.isClosedPointTower.isIntegral (Z ↘ S)
    letI : SmoothOfRelativeDimension 2 (W ↘ S) :=
      hT.isClosedPointTower.smoothOfRelativeDimension (Z ↘ S)
    ∃ A' B' : LogarithmicProjection i (D.comap T.toBase).radical,
      A'.fan = A.fan ∧ A'.hom ≍ T.toBase ≫ A.hom ∧
      B'.fan = B.fan ∧ B'.hom ≍ T.toBase ≫ B.hom ∧ Nonempty (SarkisovPath A' B')

variable {A B : LogarithmicProjection i D}

/-- A resolved Sarkisov factorization is witnessed by one nodal tower and a path
between the two lifted projections. -/
theorem hasResolvedSarkisovFactorization_iff [IsNoetherian Z] :
    HasResolvedSarkisovFactorization A B ↔
      ∃ (n : ℕ) (W : Scheme) (T : BlowupTower Z n W)
        (hT : IsNodalBoundaryTower D (Z ↘ S) (𝟙 Z) T),
        letI : W.Over S := ⟨T.toBase ≫ Z ↘ S⟩
        letI : IsIntegral W := hT.isClosedPointTower.isIntegral (Z ↘ S)
        letI : SmoothOfRelativeDimension 2 (W ↘ S) :=
          hT.isClosedPointTower.smoothOfRelativeDimension (Z ↘ S)
        ∃ A' B' : LogarithmicProjection i (D.comap T.toBase).radical,
          A'.fan = A.fan ∧ A'.hom ≍ T.toBase ≫ A.hom ∧
          B'.fan = B.fan ∧ B'.hom ≍ T.toBase ≫ B.hom ∧ Nonempty (SarkisovPath A' B') := Iff.rfl

/-- A resolved factorization has the specified rational map whenever its original
projections realize that map. The lifted projections determine this equality
by dominance, independently of the chosen nodal tower. -/
theorem HasResolvedSarkisovFactorization.exists_path_of_comp_eq [IsNoetherian Z]
    (h : HasResolvedSarkisovFactorization A B) {f : X[A.fan] ⤏ X[B.fan]}
    (hf : A.hom.toRationalMap.comp f = B.hom.toRationalMap) :
    ∃ (n : ℕ) (W : Scheme) (T : BlowupTower Z n W)
      (hT : IsNodalBoundaryTower D (Z ↘ S) (𝟙 Z) T),
      letI : W.Over S := ⟨T.toBase ≫ Z ↘ S⟩
      letI : IsIntegral W := hT.isClosedPointTower.isIntegral (Z ↘ S)
      letI : SmoothOfRelativeDimension 2 (W ↘ S) :=
        hT.isClosedPointTower.smoothOfRelativeDimension (Z ↘ S)
      ∃ (A' B' : LogarithmicProjection i (D.comap T.toBase).radical)
        (p : SarkisovPath A' B'),
        A'.fan = A.fan ∧ A'.hom ≍ T.toBase ≫ A.hom ∧
        B'.fan = B.fan ∧ B'.hom ≍ T.toBase ≫ B.hom ∧ p.rationalMap ≍ f := by
  obtain ⟨n, W, T, hT, A', B', hA, hAcomp, hB, hBcomp, ⟨p⟩⟩ :=
    hasResolvedSarkisovFactorization_iff.mp h
  refine ⟨n, W, T, hT, A', B', p, hA, hAcomp, hB, hBcomp, ?_⟩
  let : W.Over S := ⟨T.toBase ≫ Z ↘ S⟩
  let : IsIntegral W := hT.isClosedPointTower.isIntegral (Z ↘ S)
  let : SmoothOfRelativeDimension 2 (W ↘ S) :=
    hT.isClosedPointTower.smoothOfRelativeDimension (Z ↘ S)
  let : IsModification T.toBase :=
    hT.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (Z ↘ S)
  rcases A' with ⟨Φ, hΦ, hcΦ, a, ha, hda, hpa⟩
  rcases B' with ⟨Ψ, hΨ, hcΨ, b, hb, hdb, hpb⟩
  dsimp only at hA hB
  subst Φ Ψ
  apply heq_of_eq
  refine (p.rationalMap_eq_iff f).mpr ?_
  have lift_eq (a' : W ⟶ X[A.fan]) [IsDominant a'] (b' : W ⟶ X[B.fan])
      (ha' : a' = T.toBase ≫ A.hom) (hb' : b' = T.toBase ≫ B.hom) :
      a'.toRationalMap.comp f = b'.toRationalMap := by
    subst a' b'
    have h := congrArg (fun g ↦ T.toBase.toRationalMap.comp g) hf
    simpa only [← Scheme.RationalMap.comp_assoc, Scheme.RationalMap.comp_toRationalMap,
      Scheme.Hom.toRationalMap_compHom] using h
  exact lift_eq a b (eq_of_heq hAcomp) (eq_of_heq hBcomp)

private theorem exists_star_path_to_coarsening
    (A : LogarithmicProjection i D) (hN : Module.finrank ℤ N = 2)
    {Ω Ψ : Fan i} (J : Ω.IsSubdivision A.fan) (K : Ω.IsSubdivision Ψ)
    (hΩ : Ω.IsRegular) (hΨ : Ψ.IsRegular) (hcΨ : Ψ.IsComplete)
    (g : Z ⟶ X[Ω]) (he : g ≫ π[J] = A.hom)
    (h : letI := hcΨ.nonempty_cones
      ∃ hOver : (g ≫ π[K]) ≫ Fan.algebraicRealizationStructureMap Ψ = Z ↘ S,
        letI : (g ≫ π[K]).IsOver S := ⟨hOver⟩
        letI : Smooth (Z ↘ S) := SmoothOfRelativeDimension.smooth 2 _
        IsModification (g ≫ π[K]) ∧
          (Ψ.boundaryIdeal inferInstance).comap (g ≫ π[K]) =
            D * ramificationIdealSheaf ℂ (g ≫ π[K])) :
    ∃ C : LogarithmicProjection i D,
      C.fan = Ψ ∧ IsModification C.hom ∧ Nonempty (Quiver.Path A C) := by
  let : Nonempty Ψ.cones := hcΨ.nonempty_cones
  let : Nonempty Ω.cones := J.nonempty_cones_of_nonempty A.isComplete.nonempty_cones
  obtain ⟨hOver, hMod, hpole⟩ := h
  let : (g ≫ π[K]).IsOver S := ⟨hOver⟩
  let : IsModification (g ≫ π[K]) := hMod
  let C : LogarithmicProjection i D :=
    ⟨Ψ, hΨ, hcΨ, g ≫ π[K], inferInstance, inferInstance, hpole⟩
  let : IsModification π[J] :=
    J.isModification_algebraicMap A.isRegular hΩ A.isComplete.nonempty_cones hN
  let : IsDominant (g ≫ π[J]) := he.symm ▸ A.isDominant
  let : IsDominant g := IsModification.isDominant_of_comp g π[J]
  obtain ⟨p, -, -⟩ :=
    exists_resolved_toric_star_factorization A C hN hΩ J K g he (rfl : g ≫ π[K] = C.hom)
  exact ⟨C, rfl, hMod, ⟨p⟩⟩

private theorem hasResolvedSarkisovFactorization_of_append [IsNoetherian Z]
    (A B : LogarithmicProjection i D) {m n : ℕ} {Y W : Scheme}
    {T : BlowupTower Z m Y} {U : BlowupTower Y n W}
    (hT : IsNodalBoundaryTower D (Z ↘ S) (𝟙 Z) T)
    (hU : IsNodalBoundaryTower (D.comap T.toBase).radical (T.toBase ≫ Z ↘ S) (𝟙 Y) U) :
    letI : Y.Over S := ⟨T.toBase ≫ Z ↘ S⟩
    letI : SmoothOfRelativeDimension 2 (Y ↘ S) :=
      hT.isClosedPointTower.smoothOfRelativeDimension (Z ↘ S)
    letI : IsNoetherian Y := T.isNoetherian
    letI : IsIntegral Y := hT.isClosedPointTower.isIntegral (Z ↘ S)
    letI : W.Over S := ⟨U.toBase ≫ Y ↘ S⟩
    letI : SmoothOfRelativeDimension 2 (W ↘ S) :=
      hU.isClosedPointTower.smoothOfRelativeDimension (Y ↘ S)
    letI : IsIntegral W := hU.isClosedPointTower.isIntegral (Y ↘ S)
    ∀ (A' B' : LogarithmicProjection i (((D.comap T.toBase).radical).comap U.toBase).radical),
      A'.fan = A.fan → A'.hom ≍ U.toBase ≫ T.toBase ≫ A.hom →
      B'.fan = B.fan → B'.hom ≍ U.toBase ≫ T.toBase ≫ B.hom →
      SarkisovPath A' B' → HasResolvedSarkisovFactorization A B := by
  intro A' B' hA hAcomp hB hBcomp p
  let : IsNoetherian Y := T.isNoetherian
  let : IsIntegral Y := hT.isClosedPointTower.isIntegral (Z ↘ S)
  let : SmoothOfRelativeDimension 2 (T.toBase ≫ Z ↘ S) :=
    hT.isClosedPointTower.smoothOfRelativeDimension (Z ↘ S)
  let : IsIntegral W := hU.isClosedPointTower.isIntegral (T.toBase ≫ Z ↘ S)
  have hAppend : IsNodalBoundaryTower D (Z ↘ S) (𝟙 Z) (T.append U) := hT.append
    (hU.congr (by simp only [Category.id_comp, Category.comp_id])
      (by simp only [comap_id, support_radical, Category.comp_id]))
  let P (f : W ⟶ Z) (s : W ⟶ S) (hs : SmoothOfRelativeDimension 2 s)
      (R : W.IdealSheafData) : Prop :=
    letI : W.Over S := ⟨s⟩
    letI : SmoothOfRelativeDimension 2 (W ↘ S) := hs
    ∃ A' B' : LogarithmicProjection i R,
      A'.fan = A.fan ∧ A'.hom ≍ f ≫ A.hom ∧
      B'.fan = B.fan ∧ B'.hom ≍ f ≫ B.hom ∧ Nonempty (SarkisovPath A' B')
  have hTransport {f g : W ⟶ Z} {s t : W ⟶ S} {hs : SmoothOfRelativeDimension 2 s}
      {ht : SmoothOfRelativeDimension 2 t} {R R' : W.IdealSheafData}
      (hfg : f = g) (hst : s = t) (hR : R = R') : P f s hs R = P g t ht R' := by
    subst g t R'
    rfl
  have hs : (T.append U).toBase ≫ Z ↘ S = U.toBase ≫ T.toBase ≫ Z ↘ S := by
    rw [toBase_append, Category.assoc]
  have hR : (D.comap (T.append U).toBase).radical =
      ((D.comap T.toBase).radical.comap U.toBase).radical := by
    rw [toBase_append, radical_comap_radical, comap_comp]
  refine hasResolvedSarkisovFactorization_iff.mpr ⟨m + n, W, T.append U, hAppend, ?_⟩
  exact (hTransport (hs := hAppend.isClosedPointTower.smoothOfRelativeDimension (Z ↘ S))
    (ht := hU.isClosedPointTower.smoothOfRelativeDimension _) (toBase_append T U) hs hR).mpr
    ⟨A', B', hA, by simpa only [Category.assoc] using hAcomp,
      hB, by simpa only [Category.assoc] using hBcomp, ⟨p⟩⟩

open scoped Sarkisov in
private theorem hasResolvedSarkisovFactorization_of_star_paths
    (A B : LogarithmicProjection i D) (hRank : Module.finrank ℤ N = 2)
    (hD : D.IsEffectiveCartier)
    (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ Z ↘ S))
    [IsNoetherian Z] {m : ℕ} {Y : Scheme} {T : BlowupTower Z m Y}
    (hT : IsNodalBoundaryTower D (Z ↘ S) (𝟙 Z) T) :
    letI : Y.Over S := ⟨T.toBase ≫ Z ↘ S⟩
    letI : IsIntegral Y := hT.isClosedPointTower.isIntegral (Z ↘ S)
    letI : SmoothOfRelativeDimension 2 (Y ↘ S) :=
      hT.isClosedPointTower.smoothOfRelativeDimension (Z ↘ S)
    letI : IsNoetherian Y := T.isNoetherian
    ∀ {A₀ B₀ A₁ B₁ : LogarithmicProjection i (D.comap T.toBase).radical},
      A₀.fan = A.fan → A₀.hom ≍ T.toBase ≫ A.hom →
      B₀.fan = B.fan → B₀.hom ≍ T.toBase ≫ B.hom →
      @Quiver.Path _ instQuiver A₀ A₁ → @Quiver.Path _ instQuiver B₀ B₁ →
      HasResolvedSarkisovFactorization A₁ B₁ → HasResolvedSarkisovFactorization A B := by
  intro A₀ B₀ A₁ B₁ hA₀ hA hB₀ hB p q hMiddle
  let : Y.Over S := ⟨T.toBase ≫ Z ↘ S⟩
  let : IsIntegral Y := hT.isClosedPointTower.isIntegral (Z ↘ S)
  let : SmoothOfRelativeDimension 2 (Y ↘ S) :=
    hT.isClosedPointTower.smoothOfRelativeDimension (Z ↘ S)
  let : IsNoetherian Y := T.isNoetherian
  obtain ⟨n, W, U, hU, A₂, B₂, hA₂, hAcomp, hB₂, hBcomp, ⟨r⟩⟩ :=
    hasResolvedSarkisovFactorization_iff.mp hMiddle
  let : W.Over S := ⟨U.toBase ≫ Y ↘ S⟩
  let : IsIntegral W := hU.isClosedPointTower.isIntegral (Y ↘ S)
  let : SmoothOfRelativeDimension 2 (W ↘ S) :=
    hU.isClosedPointTower.smoothOfRelativeDimension (Y ↘ S)
  let : U.toBase.IsOver S := ⟨rfl⟩
  let : IsModification U.toBase :=
    hU.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (Y ↘ S)
  obtain ⟨hR, hNodeR⟩ := hT.radical_comap_toBase hD hNode
  have hPole := hU.comap_eq_radical_mul_ramificationIdealSheaf_of_iso hR hNodeR
    (Iso.refl W) U.toBase (Category.id_comp _)
  let F := precomposeSarkisov (i := i) hRank U.toBase hPole
  have hMiddleEndpoint (L : LogarithmicProjection i (D.comap T.toBase).radical)
      (M : LogarithmicProjection i ((D.comap T.toBase).radical.comap U.toBase).radical)
      (hFan : M.fan = L.fan) (hHom : M.hom ≍ U.toBase ≫ L.hom) : F.obj L = M :=
    LogarithmicProjection.ext ((precomposeSarkisov_obj_fan ..).trans hFan.symm)
      ((precomposeSarkisov_obj_hom ..).trans hHom.symm)
  let p' : SarkisovPath (F.obj A₀) A₂ :=
    hMiddleEndpoint A₁ A₂ hA₂ hAcomp ▸ F.mapPath (SarkisovPath.ofStar p)
  let qRev : @Quiver.Path _ instQuiver B₁ B₀ := @Quiver.Path.reverse _ instQuiver _ _ _ q
  let q' : SarkisovPath B₂ (F.obj B₀) :=
    hMiddleEndpoint B₁ B₂ hB₂ hBcomp ▸ F.mapPath (SarkisovPath.ofStar qRev)
  have hEnds (L : LogarithmicProjection i (D.comap T.toBase).radical)
      (M : LogarithmicProjection i D) (hFan : L.fan = M.fan)
      (h : L.hom ≍ T.toBase ≫ M.hom) :
      (F.obj L).hom ≍ U.toBase ≫ T.toBase ≫ M.hom := by
    apply (precomposeSarkisov_obj_hom ..).trans
    congr 1
    exact congrArg Fan.algebraicRealization hFan
  let path : SarkisovPath (F.obj A₀) (F.obj B₀) :=
    @Quiver.Path.comp _ sarkisovQuiver _ _ _ p'
      (@Quiver.Path.comp _ sarkisovQuiver _ _ _ r q')
  exact hasResolvedSarkisovFactorization_of_append A B hT hU _ _
    ((precomposeSarkisov_obj_fan ..).trans hA₀) (hEnds A₀ A hA₀ hA)
    ((precomposeSarkisov_obj_fan ..).trans hB₀) (hEnds B₀ B hB₀ hB) path

/-- To factor the specified change of presentation between arbitrary complete
regular rank-two toric targets, it suffices to factor the changes between
projective plane targets. Both plane projections lie on one nodal refinement
and are modifications. Any further nodal refinement used by the plane
factorization carries both end paths and the middle path. -/
theorem exists_resolved_sarkisov_factorization_of_plane
    (b : Module.Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)
    (hPlane : ∀ {Y : Scheme} [Y.Over S] [IsIntegral Y] [Y.IsProjectiveOver ℂ]
      [SmoothOfRelativeDimension 2 (Y ↘ S)] {R : Y.IdealSheafData},
      letI : IsNoetherian Y := isNoetherian_of_finiteType (Y ↘ S)
      R.IsEffectiveCartier →
      AtWorstNodalOfRelativeDimensionOne (R.subschemeι ≫ Y ↘ S) →
      ∀ (C E : LogarithmicProjection i R) [IsModification C.hom] [IsModification E.hom],
        C.fan = projectiveSpace b hi → E.fan = projectiveSpace b hi →
        HasResolvedSarkisovFactorization C E)
    [Z.IsProjectiveOver ℂ] (A B : LogarithmicProjection i D)
    [IsModification A.hom] [IsModification B.hom] (hD : D.IsEffectiveCartier)
    (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ Z ↘ S)) :
    letI : IsNoetherian Z := isNoetherian_of_finiteType (Z ↘ S)
    HasResolvedSarkisovFactorization A B := by
  let : IsNoetherian Z := isNoetherian_of_finiteType (Z ↘ S)
  let plane := projectiveSpace b hi
  let hplane := isRegular_projectiveSpace b hi
  let hcplane := isComplete_projectiveSpace b hi
  let : Nonempty plane.cones := hcplane.nonempty_cones
  let hRank := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  let L : Bool → LogarithmicProjection i D := fun j ↦ cond j B A
  let : ∀ j, IsModification (L j).hom := by
    intro j
    cases j <;> assumption
  let : ∀ j, (L j).hom.IsOver S := fun j ↦ (L j).isOver
  obtain ⟨n, Y, T, hT, h⟩ := exists_common_nodal_resolution_of_toric_changes
    (fun _ : Bool ↦ b) (fun j ↦ (L j).isRegular) (fun j ↦ (L j).isComplete)
    (fun _ ↦ hplane) (fun _ ↦ hcplane) (fun j ↦ (L j).hom) hD hNode
    (fun j ↦ (L j).comap_boundaryIdeal)
  let : Y.Over S := ⟨T.toBase ≫ Z ↘ S⟩
  let : IsIntegral Y := hT.isClosedPointTower.isIntegral (Z ↘ S)
  let : SmoothOfRelativeDimension 2 (Y ↘ S) :=
    hT.isClosedPointTower.smoothOfRelativeDimension (Z ↘ S)
  let : Y.IsProjectiveOver ℂ := T.isProjectiveOver ℂ
  let : T.toBase.IsOver S := ⟨rfl⟩
  let : IsModification T.toBase :=
    hT.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (Z ↘ S)
  have hPole := hT.comap_eq_radical_mul_ramificationIdealSheaf_of_iso hD hNode
    (Iso.refl Y) T.toBase (Category.id_comp _)
  let L' (j : Bool) := precomposeProjection hRank T.toBase hPole (L j)
  have hPath (j : Bool) : ∃ C : LogarithmicProjection i (D.comap T.toBase).radical,
      C.fan = plane ∧ IsModification C.hom ∧ Nonempty (Quiver.Path (L' j) C) := by
    obtain ⟨Ω, J, K, g, hΩ, -, -, he, hq⟩ := h j
    exact exists_star_path_to_coarsening (L' j) hRank J K hΩ hplane hcplane g he ((hq plane K).2.imp
      fun _ hm ↦ hm hplane)
  obtain ⟨C, hC, hModC, ⟨p⟩⟩ := hPath false
  obtain ⟨E, hE, hModE, ⟨q⟩⟩ := hPath true
  let : IsModification C.hom := hModC
  let : IsModification E.hom := hModE
  obtain ⟨hR, hNodeR⟩ := hT.radical_comap_toBase hD hNode
  exact hasResolvedSarkisovFactorization_of_star_paths A B hRank hD hNode hT
    rfl HEq.rfl rfl HEq.rfl p q (hPlane hR hNodeR C E hC hE)

end TauCeti.Toric.Fan.LogarithmicProjection
