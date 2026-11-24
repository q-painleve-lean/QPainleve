/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.InternalBlowup
public import QPainleve.Geometry.Toric.Fan.Logarithmic.Factorization
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

import Mathlib.Combinatorics.Quiver.Covering
import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic
import QPainleve.Geometry.Toric.Fan.Logarithmic.Isomorphism
import QPainleve.Geometry.Toric.Fan.Logarithmic.Morphism
import QPainleve.Geometry.Toric.Fan.Logarithmic.OrderedStarPath
import QPainleve.Geometry.Toric.Fan.Logarithmic.ResolvedMutation
import QPainleve.Geometry.Toric.Fan.Scheme
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition

/-!
# Ordered presentations along resolved Sarkisov paths

A resolved Sarkisov path transports an ordered internal blowup presentation along
its specified regular projections. The subdivisions, center parameters and frames
may vary, while the ordered blowup count and resolving surface stay fixed.

The comparison uses the resolved links of [Lutz, Theorem 8.4][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=68
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory PointedCone
open QPainleve.BlowupTower TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan.LogarithmicProjection

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" Φ "]" => Fan.algebraicRealization Φ
local notation "π[" H "]" => FanHom.algebraicMap (IsSubdivision.toFanHom H)
local notation "tower[" H "," b "," r "," c "]" =>
  @Fan.internalBlowupTower _ _ _ _ _ _ _ (IsSubdivision.nonempty_cones_of_nonempty H
    inferInstance) b _ r c
local notation "base[" T "]" => QPainleve.BlowupTower.toBase (WithBoundary.toTower (Sigma.snd T))

variable {Z : Scheme} [Z.Over S] [SmoothOfRelativeDimension 2 (Z ↘ S)]
  {D : Z.IdealSheafData} {A B : LogarithmicProjection i D} {m : ℕ}

/-- An ordered internal blowup tower over a regular subdivision that presents
the specified projection and its strict pole boundary on the resolving surface. -/
@[ext]
structure OrderedToricModel (A : LogarithmicProjection i D) (m : ℕ) where
  /-- The intermediate fan before the ordered internal blowups. -/
  fan : Fan i
  /-- The intermediate fan is regular. -/
  regular : fan.IsRegular
  /-- The toric part of the projection. -/
  subdivision : fan.IsSubdivision A.fan
  /-- The lattice frame for the binomial centers. -/
  basis : Module.Basis (Fin 2) ℤ N
  /-- The boundary rays of the centers, in blowup order. -/
  rays : Fin m → fan.Ray
  /-- The binomial parameters, in the same order. -/
  parameters : Fin m → ℂˣ
  /-- The identification of the last blowup with the resolving surface. -/
  iso : (tower[subdivision,basis,rays,parameters]).1 ≅ Z
  /-- The given regular projection factors through the ordered tower. -/
  hom_eq : iso.hom ≫ A.hom = base[tower[subdivision,basis,rays,parameters]] ≫ π[subdivision]
  /-- The strict boundary is the preimage of the common pole ideal. -/
  pole_eq : D.comap iso.hom = (tower[subdivision,basis,rays,parameters]).2.boundaryι.ker

open scoped Sarkisov

namespace OrderedToricModel

/-- The fan of an ordered model is nonempty, since it subdivides a complete fan. -/
instance (U : OrderedToricModel A m) : Nonempty U.fan.cones :=
  U.subdivision.nonempty_cones_of_nonempty A.isComplete.nonempty_cones

/-- The ordered internal blowups of a model before its toric projection. -/
abbrev tower (U : OrderedToricModel A m) :=
  U.fan.internalBlowupTower U.basis U.rays U.parameters

/-- The regular projection to the intermediate fan of the ordered model. -/
def hom (U : OrderedToricModel A m) : Z ⟶ X[U.fan] :=
  U.iso.inv ≫ base[U.tower]

/-- The refined projection is the ordered blowdown in the chosen resolving identification. -/
theorem hom_def (U : OrderedToricModel A m) :
    U.hom = U.iso.inv ≫ base[U.tower] := (rfl)

/-- Composing the refined projection with the subdivision recovers the specified projection. -/
@[reassoc (attr := simp)]
theorem hom_comp_subdivision (U : OrderedToricModel A m) :
    U.hom ≫ π[U.subdivision] = A.hom := by
  rw [U.hom_def, Category.assoc, ← U.hom_eq, Iso.inv_hom_id_assoc]

instance (U : OrderedToricModel A m) : IsModification U.hom := by
  let : IsModification (base[U.tower]) :=
    U.fan.isModification_internalBlowupTower_toBase U.basis U.rays U.parameters U.regular
  rw [U.hom_def]
  infer_instance

instance (U : OrderedToricModel A m) : U.hom.IsOver S :=
  ⟨by
    rw [U.fan.algebraicRealization_over,
      ← U.subdivision.toFanHom.algebraicMap_comp_algebraicRealizationStructureMap,
      ← Category.assoc, U.hom_comp_subdivision, ← A.fan.algebraicRealization_over, comp_over]⟩

/-- The projection to the intermediate fan has the same pole ideal as the original one. -/
abbrev refinedProjection [IsIntegral Z] (U : OrderedToricModel A m) :
    LogarithmicProjection i D where
  fan := U.fan
  isRegular := U.regular
  isComplete := U.subdivision.isComplete_iff.mpr A.isComplete
  hom := U.hom
  isOver := inferInstance
  isDominant := inferInstance
  comap_boundaryIdeal := by
    have hN : Module.finrank ℤ N = 2 := by
      simpa using Module.finrank_eq_card_basis U.basis
    apply (U.subdivision.comap_boundaryIdeal_eq_mul_ramificationIdealSheaf_comp_iff
      A.isRegular U.regular A.isComplete hN U.hom D).mp
    simpa only [U.hom_comp_subdivision] using A.comap_boundaryIdeal

@[simp]
theorem refinedProjection_fan [IsIntegral Z] (U : OrderedToricModel A m) :
    U.refinedProjection.fan = U.fan := (rfl)

/-- The refined logarithmic projection uses the given ordered blowdown. -/
@[simp]
theorem refinedProjection_hom [IsIntegral Z] (U : OrderedToricModel A m) :
    U.refinedProjection.hom = U.hom := (rfl)

private theorem exists_model_of_starStep [IsIntegral Z] [Z.IsProjectiveOver ℂ]
    (U : OrderedToricModel A m) (step : StarStep A B) :
    ∃ W : OrderedToricModel B m,
      Nonempty (SarkisovStep U.refinedProjection W.refinedProjection) := by
  let p := @Quiver.Path.cons _ instQuiver A A B (@Quiver.Path.nil _ instQuiver A) step
  have h := exists_subdivisions_of_toric_internal_factorization p
    U.basis U.regular U.subdivision U.rays U.parameters U.iso U.hom_eq U.pole_eq B
    (@Quiver.Path.end_mem_vertices _ instQuiver A B p)
  obtain ⟨-, H, hH⟩ := h
  let W : OrderedToricModel B m :=
    ⟨U.fan, U.regular, H, U.basis, U.rays, U.parameters, U.iso, hH, U.pole_eq⟩
  refine ⟨W, ⟨⟨(𝟙 X[U.fan] : X[U.fan] ⟶ X[U.fan]).toRationalMap, ?_, ?_⟩⟩⟩
  · simpa only [FanEquiv.toFanHom_refl, FanHom.algebraicMap_id, Fan.torusTranslation_one,
      Iso.refl_hom, Category.id_comp] using
        IsSarkisovLink.toricIso (FanEquiv.refl U.fan) 1
  · simp only [Scheme.RationalMap.comp_toRationalMap, Scheme.Hom.toRationalMap_compHom,
      Category.comp_id]
    rfl

private theorem exists_tower_in_basis (U : OrderedToricModel A m)
    (b : Module.Basis (Fin 2) ℤ N) :
    ∃ (u : Fin m → ℂˣ) (e : (U.fan.internalBlowupTower b U.rays u).1 ≅ Z),
      let T := U.fan.internalBlowupTower b U.rays u
      e.hom ≫ A.hom = base[T] ≫ π[U.subdivision] ∧
        D.comap e.hom = T.2.boundaryι.ker ∧ e.inv ≫ base[T] = U.hom := by
  obtain ⟨u, hu⟩ := exists_internalBlowupTower_eq_of_basis U.basis U.rays U.parameters b
  exact ⟨u, hu.symm ▸ Exists.intro U.iso ⟨U.hom_eq, U.pole_eq, U.hom_def.symm⟩⟩

private theorem exists_model_of_mutation [IsIntegral Z]
    (U : OrderedToricModel A m) (b : Module.Basis (Fin 2) ℤ N)
    (ρ : A.fan.Ray) (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ A.fan.cones) (c : ℂˣ)
    (hFan : B.fan = A.fan.mutationFan b ρ.primitiveGenerator_ne_zero
      ρ.hull_primitiveGenerator_mem hOpp)
    (hMap : A.hom.toRationalMap.comp
      (A.fan.mutationPartialMap b (c : ℂ) ρ.primitiveGenerator_ne_zero
        ρ.hull_primitiveGenerator_mem hOpp).toRationalMap =
      (cast (congrArg (fun Φ : Fan i ↦ Z ⟶ X[Φ]) hFan) B.hom).toRationalMap) :
    ∃ W : OrderedToricModel B m,
      Nonempty (SarkisovStep U.refinedProjection W.refinedProjection) := by
  cases B
  next Φ hΦ hc r hOver hDom hBoundary =>
    dsimp only at hFan
    subst Φ
    simp only [cast_eq] at hMap
    obtain ⟨u, e, he, hPole, href⟩ := U.exists_tower_in_basis b
    obtain ⟨n, hm, k, -, -, -, g, hproj, hpole, hrat, -, -⟩ :=
      A.exists_ordered_toric_mutation_model_of_factorization b ρ hOpp c U.regular
        U.subdivision U.rays u r hMap e he hPole
    subst m
    let σ := U.subdivision.liftRay ρ
    let opp := U.subdivision.hull_neg_primitiveGenerator_liftRay_mem ρ hOpp
    let Ψ := U.fan.mutationFan b σ.primitiveGenerator_ne_zero σ.hull_primitiveGenerator_mem opp
    let K := U.subdivision.mutation b
      (U.subdivision.primitiveGenerator_liftRay ρ) ρ.primitiveGenerator_ne_zero
      σ.primitiveGenerator_ne_zero ρ.hull_primitiveGenerator_mem hOpp
      σ.hull_primitiveGenerator_mem opp
    let hreg : Ψ.IsRegular :=
      (U.fan.isRegular_mutationFan_iff b σ.primitiveGenerator_ne_zero
        σ.hull_primitiveGenerator_mem opp).mpr U.regular
    let reverseRay := U.fan.mutationFanCenterRays b (fun _ : Unit ↦ σ) () opp ()
    let rays : Fin (n + 1) → Ψ.Ray := Fin.cons reverseRay
      (fun l ↦ U.fan.mutationFanRayEquiv b σ.primitiveGenerator_ne_zero
        σ.hull_primitiveGenerator_mem opp (U.rays (k.succAbove l)))
    let params : Fin (n + 1) → ℂˣ := Fin.cons c⁻¹ (fun l ↦ u (k.succAbove l) *
      c ^ max (b.det ![(U.rays (k.succAbove l)).primitiveGenerator, σ.primitiveGenerator]) 0)
    let C : LogarithmicProjection i D := ⟨_, hΦ, hc, r, hOver, hDom, hBoundary⟩
    let W : OrderedToricModel C (n + 1) :=
      ⟨Ψ, hreg, K, b, rays, params, g.symm ≪≫ e, hproj, hpole⟩
    let f := (U.fan.mutationPartialMap b (c : ℂ) σ.primitiveGenerator_ne_zero
      σ.hull_primitiveGenerator_mem opp).toRationalMap
    refine ⟨W, ⟨⟨f, .mutation b σ c opp, ?_⟩⟩⟩
    have : IsDominant (base[U.fan.internalBlowupTower b U.rays u]) :=
      (U.fan.isModification_internalBlowupTower_toBase b U.rays u U.regular).isDominant
    -- The source reparametrization leaves the refined projection unchanged.
    change U.hom.toRationalMap.comp f = W.hom.toRationalMap
    let t := base[U.fan.internalBlowupTower b U.rays u]
    let : IsIntegral (U.fan.internalBlowupTower b U.rays u).1 :=
      U.fan.isIntegral_internalBlowupTower b U.rays u U.regular
    calc
      _ = (e.inv.toRationalMap.comp t.toRationalMap).comp f := by
        congr 1
        simpa only [Scheme.RationalMap.comp_toRationalMap, Scheme.Hom.toRationalMap_compHom]
          using congrArg Scheme.Hom.toRationalMap href.symm
      _ = _ := by
        rw [Scheme.RationalMap.comp_assoc, hrat, Scheme.RationalMap.comp_toRationalMap,
          Scheme.Hom.toRationalMap_compHom, W.hom_def]
        rfl

private theorem exists_model_of_iso [IsIntegral Z]
    (U : OrderedToricModel A m) (f : FanEquiv A.fan B.fan)
    (χ : Multiplicative (N →+ ℤ) →* ℂˣ)
    (h : A.hom.toRationalMap.comp
      (f.toFanHom.algebraicMap ≫ (B.fan.torusTranslation χ).hom).toRationalMap =
        B.hom.toRationalMap) :
    ∃ W : OrderedToricModel B m,
      Nonempty (SarkisovStep U.refinedProjection W.refinedProjection) := by
  obtain ⟨g, hg, hproj, hPole, -, -⟩ := exists_ordered_toric_iso_model f χ h
    U.basis U.regular U.subdivision U.rays U.parameters U.iso U.hom_eq U.pole_eq
  let Θ := U.fan.mapEquiv B.fan.lattice f.latticeEquiv
  let F := U.fan.mapEquivIso B.fan.lattice f.latticeEquiv
  let K := f.isSubdivision_mapEquiv U.subdivision
  let b := U.basis.map F.latticeEquiv.toIntLinearEquiv
  let s := F.rayEquiv ∘ U.rays
  let c := fun j ↦ U.parameters j / χ (Multiplicative.ofAdd
    (b.detDualEquiv (s j).primitiveGenerator).toAddMonoidHom)
  let W : OrderedToricModel B m :=
    ⟨Θ, F.isRegular_iff.mpr U.regular, K, b, s, c, g.symm ≪≫ U.iso, hproj, hPole⟩
  let : Nonempty Θ.cones := K.nonempty_cones_of_nonempty B.isComplete.nonempty_cones
  let f := F.toFanHom.algebraicMap ≫ (Θ.torusTranslation χ).hom
  refine ⟨W, ⟨⟨f.toRationalMap, .toricIso F χ, ?_⟩⟩⟩
  -- The ordered tower lift is an equality of regular representatives.
  change U.hom.toRationalMap.comp f.toRationalMap = W.hom.toRationalMap
  rw [Scheme.RationalMap.comp_toRationalMap, Scheme.Hom.toRationalMap_compHom,
    U.hom_def, W.hom_def, Category.assoc]
  exact congrArg Scheme.Hom.toRationalMap (congrArg (U.iso.inv ≫ ·) hg.hom_toBase.symm)

end OrderedToricModel

/-- Normalize a logarithmic modification into an ordered internal model after
a regular toric subdivision of its target. -/
theorem exists_ordered_toric_model [IsIntegral Z] [Z.IsProjectiveOver ℂ]
    (A : LogarithmicProjection i D) [IsModification A.hom] (b : Module.Basis (Fin 2) ℤ N) :
    ∃ m, Nonempty (OrderedToricModel A m) := by
  obtain ⟨Θ, hΘ, J, m, r, c, e, he, hD⟩ :=
    A.fan.exists_toric_internal_factorization_of_boundary_comap_eq b A.isRegular A.isComplete
      (IsModification.birationalOver A.hom) A.comap_boundaryIdeal
  exact ⟨m, ⟨⟨Θ, hΘ, J, b, r, c, e, he, hD⟩⟩⟩

variable [IsIntegral Z]

/-- An ordered model of the source of a resolved link transports to an ordered
model of its specified target projection with the same number of centers. -/
theorem SarkisovStep.exists_ordered_toric_model [Z.IsProjectiveOver ℂ] (e : SarkisovStep A B)
    (U : OrderedToricModel A m) :
    ∃ W : OrderedToricModel B m,
      Nonempty (SarkisovStep U.refinedProjection W.refinedProjection) := by
  rcases e with ⟨f, hf, h⟩
  cases A
  cases B
  cases hf with
  | blowup H =>
    apply U.exists_model_of_starStep (.blowup H ?_)
    let (F : Fan i) : X[F].IsSeparated := F.isSeparated_algebraicRealization
    apply Scheme.Hom.toRationalMap_injective
    have hh := congrArg (fun f ↦ f.compHom π[H.isSubdivision]) h
    rw [← Scheme.RationalMap.comp_toRationalMap, Scheme.RationalMap.comp_assoc,
      H.isSubdivision.toRationalMap_algebraicMap, denseTorusPartialIso_toRationalMap_comp,
      denseTorusPartialIso_self_toRationalMap, Scheme.RationalMap.comp_id,
      Scheme.Hom.toRationalMap_compHom] at hh
    exact hh.symm
  | blowdown H =>
    apply U.exists_model_of_starStep (.blowdown H ?_)
    let (F : Fan i) : X[F].IsSeparated := F.isSeparated_algebraicRealization
    apply Scheme.Hom.toRationalMap_injective
    rwa [← H.isSubdivision.toRationalMap_algebraicMap, Scheme.RationalMap.comp_toRationalMap,
      Scheme.Hom.toRationalMap_compHom] at h
  | mutation b ρ c hOpp =>
    exact U.exists_model_of_mutation b ρ hOpp c rfl h
  | toricIso f χ =>
    exact U.exists_model_of_iso f χ h

/-- The quiver of specified projections together with chosen ordered presentations.
An edge pairs an original resolved link with a link on the refined fans. -/
abbrev presentationQuiver (m : ℕ) :
    Quiver (Σ C : LogarithmicProjection i D, OrderedToricModel C m) where
  Hom U W := SarkisovStep U.1 W.1 × SarkisovStep U.2.refinedProjection W.2.refinedProjection

scoped[Sarkisov] attribute [instance]
  TauCeti.Toric.Fan.LogarithmicProjection.presentationQuiver

/-- Forget the ordered presentation of a projection and retain its original links. -/
@[simps]
abbrev forgetPresentation (m : ℕ) :
    @Prefunctor _ (presentationQuiver (i := i) (D := D) m)
      (LogarithmicProjection i D) sarkisovQuiver where
  obj := Sigma.fst
  map e := e.1

/-- Read a path of ordered presentations as links on their intermediate fans. -/
@[simps]
abbrev refinePresentation (m : ℕ) :
    @Prefunctor _ (presentationQuiver (i := i) (D := D) m)
      (LogarithmicProjection i D) sarkisovQuiver where
  obj U := U.2.refinedProjection
  map e := e.2

/-- The composite on the ordered models is the specified composite on the original
fans, after the two endpoint subdivision projections. This applies in particular
to each prefix of a path of ordered presentations. -/
theorem SarkisovPath.subdivision_comp_rationalMap (p : SarkisovPath A B)
    (U : OrderedToricModel A m) (W : OrderedToricModel B m)
    (q : SarkisovPath U.refinedProjection W.refinedProjection) :
    π[U.subdivision].toRationalMap.comp p.rationalMap =
      q.rationalMap.comp π[W.subdivision].toRationalMap := by
  apply U.hom.toRationalMap.comp_left_injective
  dsimp only
  calc
    _ = A.hom.toRationalMap.comp p.rationalMap := by
      rw [← Scheme.RationalMap.comp_assoc]
      congr 1
      simp only [Scheme.RationalMap.comp_toRationalMap, Scheme.Hom.toRationalMap_compHom,
        U.hom_comp_subdivision]
    _ = B.hom.toRationalMap := p.comp_rationalMap
    _ = (W.hom ≫ π[W.subdivision]).toRationalMap :=
      congrArg Scheme.Hom.toRationalMap W.hom_comp_subdivision.symm
    _ = (U.hom.toRationalMap.comp q.rationalMap).compHom π[W.subdivision] := by
      rw [q.comp_rationalMap, Scheme.Hom.toRationalMap_compHom]
    _ = _ := by
      rw [← Scheme.RationalMap.comp_toRationalMap, Scheme.RationalMap.comp_assoc]

/-- Every resolved path lifts to a path of ordered presentations starting from the
specified ordered model. Forgetting the ordered presentations recovers the given path.
On the refined fans every link has a regular representative on the same resolving
surface with the same pole ideal, and the composite commutes with the two endpoint
subdivisions. -/
theorem SarkisovPath.exists_ordered_toric_models [Z.IsProjectiveOver ℂ] (p : SarkisovPath A B)
    (U : OrderedToricModel A m) :
    ∃ (W : OrderedToricModel B m)
      (q : @Quiver.Path _ (presentationQuiver m) ⟨A, U⟩ ⟨B, W⟩),
      (forgetPresentation m).mapPath q = p ∧
        π[U.subdivision].toRationalMap.comp p.rationalMap =
          (SarkisovPath.rationalMap ((refinePresentation m).mapPath q)).comp
            π[W.subdivision].toRationalMap := by
  let F := forgetPresentation (i := i) (D := D) m
  have hF : ∀ U, Function.Surjective (F.star U) := by
    rintro ⟨C, M⟩ ⟨E, e⟩
    obtain ⟨W, ⟨f⟩⟩ := e.exists_ordered_toric_model M
    exact ⟨⟨⟨E, W⟩, e, f⟩, rfl⟩
  obtain ⟨⟨⟨C, W⟩, q⟩, hq⟩ := F.pathStar_surjective hF ⟨A, U⟩ ⟨B, p⟩
  -- Path stars package the terminal vertex together with the path to it.
  change (⟨C, F.mapPath q⟩ : @Quiver.PathStar _ sarkisovQuiver A) = ⟨B, p⟩ at hq
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp hq
  exact ⟨W, q, eq_of_heq h, p.subdivision_comp_rationalMap U W _⟩

end TauCeti.Toric.Fan.LogarithmicProjection
