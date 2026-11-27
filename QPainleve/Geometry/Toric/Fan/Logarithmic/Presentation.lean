/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.InternalBlowup
public import QPainleve.Geometry.Toric.Fan.Logarithmic.Factorization
public import QPainleve.Geometry.Toric.Fan.Mutation.Boundary
public import QPainleve.Geometry.Toric.Fan.Mutation.Subdivision
public import QPainleve.Geometry.Toric.Fan.Subdivision
public import QPainleve.Geometry.Toric.Fan.Subdivision.Equiv
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

import Mathlib.Combinatorics.Quiver.Covering
import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic
import QPainleve.Geometry.Toric.Fan.Logarithmic.Isomorphism
import QPainleve.Geometry.Toric.Fan.Logarithmic.Morphism
import QPainleve.Geometry.Toric.Fan.Logarithmic.OrderedStarPath
import QPainleve.Geometry.Toric.Fan.Logarithmic.ResolvedMutation
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

variable {k : Type} [Field k] [IsAlgClosed k]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

local notation "S" => Spec (CommRingCat.of k)
local notation "X[" Φ "]" => Fan.finiteFanScheme k Φ
local notation "π[" H "]" => FanHom.finiteFanSchemeHom k (IsSubdivision.toFanHom H)
local notation "tower[" H "," b "," r "," c "]" =>
  @Fan.internalBlowupTower k _ _ _ _ _ _ _ _ (IsSubdivision.nonempty_cones_of_nonempty H
    inferInstance) b _ r c
local notation "base[" T "]" => QPainleve.BlowupTower.toBase (WithBoundary.toTower (Sigma.snd T))

variable {Z : Scheme} [Z.Over (Spec (.of k))] [SmoothOfRelativeDimension 2 (Z ↘ Spec (.of k))]
  {D : Z.IdealSheafData} {A B : LogarithmicProjection k i D} {m : ℕ}

/-- An ordered internal blowup tower over a regular subdivision that presents
the specified projection and its strict pole boundary on the resolving surface. -/
@[ext]
structure OrderedToricModel (A : LogarithmicProjection k i D) (m : ℕ) where
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
  parameters : Fin m → kˣ
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
  U.fan.internalBlowupTower k U.basis U.rays U.parameters

/-- The toric and total exceptional coordinates mark the Picard group of the
common resolving surface in the given ordered model. -/
def picardMarking (U : OrderedToricModel A m) :
    (Additive (LineBundleClass X[U.fan]) × (Fin m → ℤ)) ≃ₗ[ℤ] Additive (LineBundleClass Z) :=
  (U.fan.internalBlowupPicardMarking k U.basis U.rays U.parameters U.regular).trans
    (LineBundleClass.pullbackEquiv U.iso.symm).toAdditive.toIntLinearEquiv

/-- The ordered marking pulls the marked classes of the internal blowup tower
to the specified resolving surface. -/
@[simp]
theorem picardMarking_apply (U : OrderedToricModel A m)
    (a : Additive (LineBundleClass X[U.fan]) × (Fin m → ℤ)) :
    U.picardMarking a = Additive.ofMul (LineBundleClass.pullback U.iso.inv
      (U.fan.internalBlowupPicardMarking k U.basis U.rays U.parameters U.regular a).toMul) := by
  simp [picardMarking]

/-- The regular projection to the intermediate fan of the ordered model. -/
def hom (U : OrderedToricModel A m) : Z ⟶ X[U.fan] :=
  U.iso.inv ≫ base[U.tower]

omit [IsAlgClosed k] in
/-- The refined projection is the ordered blowdown in the chosen resolving identification. -/
theorem hom_def (U : OrderedToricModel A m) :
    U.hom = U.iso.inv ≫ base[U.tower] := (rfl)

omit [IsAlgClosed k] in
/-- Composing the refined projection with the subdivision recovers the specified projection. -/
@[reassoc (attr := simp)]
theorem hom_comp_subdivision (U : OrderedToricModel A m) :
    U.hom ≫ π[U.subdivision] = A.hom := by
  rw [U.hom_def, Category.assoc, ← U.hom_eq, Iso.inv_hom_id_assoc]

instance (U : OrderedToricModel A m) : IsModification U.hom := by
  let : IsModification (base[U.tower]) :=
    U.fan.isModification_internalBlowupTower_toBase k U.basis U.rays U.parameters U.regular
  rw [U.hom_def]
  infer_instance

instance (U : OrderedToricModel A m) : U.hom.IsOver S :=
  ⟨by
    rw [U.fan.finiteFanScheme_over k,
      ← U.subdivision.toFanHom.finiteFanSchemeHom_comp_finiteFanSchemeToSpec k,
      ← Category.assoc, U.hom_comp_subdivision, ← A.fan.finiteFanScheme_over k, comp_over]⟩

/-- The projection to the intermediate fan has the same pole ideal as the original one. -/
abbrev refinedProjection [IsIntegral Z] (U : OrderedToricModel A m) :
    LogarithmicProjection k i D where
  fan := U.fan
  isRegular := U.regular
  isComplete := U.subdivision.isComplete_iff.mpr A.isComplete
  hom := U.hom
  isOver := inferInstance
  isDominant := inferInstance
  comap_boundaryIdeal := by
    have hN : Module.finrank ℤ N = 2 := by
      simpa using Module.finrank_eq_card_basis U.basis
    apply (U.subdivision.comap_boundaryIdeal_eq_mul_ramificationIdealSheaf_comp_iff k
      A.isRegular U.regular A.isComplete hN U.hom D).mp
    simpa only [U.hom_comp_subdivision] using A.comap_boundaryIdeal

@[simp]
theorem refinedProjection_fan [IsIntegral Z] (U : OrderedToricModel A m) :
    U.refinedProjection.fan = U.fan := (rfl)

/-- The refined logarithmic projection uses the given ordered blowdown. -/
@[simp]
theorem refinedProjection_hom [IsIntegral Z] (U : OrderedToricModel A m) :
    U.refinedProjection.hom = U.hom := (rfl)

private theorem exists_model_of_starStep [IsIntegral Z] [Z.IsProjectiveOver k]
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
  · simpa only [FanEquiv.toFanHom_refl, FanHom.finiteFanSchemeHom_id k, Fan.torusTranslationIso_one,
      Iso.refl_hom, Category.id_comp] using
        IsSarkisovLink.toricIso (k := k) (FanEquiv.refl U.fan) 1
  · simp only [Scheme.RationalMap.comp_toRationalMap, Scheme.Hom.toRationalMap_compHom,
      Category.comp_id]
    rfl

omit [IsAlgClosed k] in
private theorem exists_tower_in_basis (U : OrderedToricModel A m)
    (b : Module.Basis (Fin 2) ℤ N) :
    ∃ (u : Fin m → kˣ) (e : (U.fan.internalBlowupTower k b U.rays u).1 ≅ Z),
      let T := U.fan.internalBlowupTower k b U.rays u
      e.hom ≫ A.hom = base[T] ≫ π[U.subdivision] ∧
        D.comap e.hom = T.2.boundaryι.ker ∧ e.inv ≫ base[T] = U.hom := by
  obtain ⟨u, hu⟩ := exists_internalBlowupTower_eq_of_basis k U.basis U.rays U.parameters b
  exact ⟨u, hu.symm ▸ Exists.intro U.iso ⟨U.hom_eq, U.pole_eq, U.hom_def.symm⟩⟩

/-- Transport an ordered model in the mutation frame. The returned link uses the lifted
mutation ray, and the pivot label and terminal marking record the ordered mutation.
The boundary comparison takes place inside the common resolving surface. -/
theorem exists_model_of_mutation_in_basis [IsIntegral Z]
    (U : OrderedToricModel A m)
    (ρ : A.fan.Ray) (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ A.fan.cones) (c : kˣ)
    (hFan : B.fan = A.fan.mutationFan U.basis ρ.primitiveGenerator_ne_zero
      ρ.hull_primitiveGenerator_mem hOpp)
    (hMap : A.hom.toRationalMap.comp
      (A.fan.mutationPartialMap k U.basis (c : k) ρ.primitiveGenerator_ne_zero
        ρ.hull_primitiveGenerator_mem hOpp).toRationalMap =
      (cast (congrArg (fun Φ : Fan i ↦ Z ⟶ X[Φ]) hFan) B.hom).toRationalMap) :
    let b := U.basis
    let σ := U.subdivision.liftRay ρ
    let opp := U.subdivision.hull_neg_primitiveGenerator_liftRay_mem ρ hOpp
    let Ψ := U.fan.mutationFan b σ.primitiveGenerator_ne_zero σ.hull_primitiveGenerator_mem opp
    let K : Ψ.IsSubdivision B.fan := hFan.symm ▸ U.subdivision.mutation b
      (U.subdivision.primitiveGenerator_liftRay ρ) ρ.primitiveGenerator_ne_zero
      σ.primitiveGenerator_ne_zero ρ.hull_primitiveGenerator_mem hOpp
      σ.hull_primitiveGenerator_mem opp
    let hreg : Ψ.IsRegular :=
      (U.fan.isRegular_mutationFan_iff b σ.primitiveGenerator_ne_zero
        σ.hull_primitiveGenerator_mem opp).mpr U.regular
    ∃ (n : ℕ) (hm : n + 1 = m) (pivot : Fin (n + 1)),
      let a := U.rays ∘ finCongr hm
      let u := U.parameters ∘ finCongr hm
      let rays : Fin (n + 1) → Ψ.Ray :=
        Fin.cons (U.fan.mutationFanCenterRays b (fun _ : Unit ↦ σ) () opp ())
          (fun l ↦ U.fan.mutationFanRayEquiv b σ.primitiveGenerator_ne_zero
            σ.hull_primitiveGenerator_mem opp (a (pivot.succAbove l)))
      let params : Fin (n + 1) → kˣ := Fin.cons c⁻¹ (fun l ↦ u (pivot.succAbove l) *
        c ^ max (b.det ![(a (pivot.succAbove l)).primitiveGenerator, σ.primitiveGenerator]) 0)
      let T := tower[K,b,rays,params]
      a pivot = σ ∧ u pivot = c ∧
        ∃ (e : T.1 ≅ Z) (he : e.hom ≫ B.hom = base[T] ≫ π[K])
          (hP : D.comap e.hom = T.2.boundaryι.ker),
          let W : OrderedToricModel B (n + 1) := ⟨Ψ, hreg, K, b, rays, params, e, he, hP⟩
          (Ray.mutationBoundaryIso b σ opp c U.regular).hom ≫ W.tower.2.boundaryι ≫ W.iso.hom =
            U.tower.2.boundaryι ≫ U.iso.hom ∧
          ∃ step : SarkisovStep U.refinedProjection W.refinedProjection,
            step.rationalMap = (U.fan.mutationPartialMap k b (c : k)
              σ.primitiveGenerator_ne_zero σ.hull_primitiveGenerator_mem opp).toRationalMap := by
  cases B
  next Φ hΦ hc r hOver hDom hBoundary =>
    dsimp only at hFan
    subst Φ
    simp only [cast_eq] at hMap
    obtain ⟨n, hm, pivot, hk, hc', -, g, hproj, hpole, hrat, hboundary, -⟩ :=
      A.exists_ordered_toric_mutation_model_of_factorization U.basis ρ hOpp c U.regular
        U.subdivision U.rays U.parameters r hMap U.iso U.hom_eq U.pole_eq
    refine ⟨n, hm, pivot, hk, hc', g.symm ≪≫ U.iso, hproj, hpole, ?_⟩
    intro W
    refine ⟨?_, ⟨_, .mutation U.basis _ c _, ?_⟩, rfl⟩
    · have hb := congrArg (· ≫ g.inv ≫ U.iso.hom) hboundary.symm
      dsimp only [W, OrderedToricModel.tower, Function.comp_apply]
      simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] using hb
    let : IsDominant (base[U.tower]) :=
      (U.fan.isModification_internalBlowupTower_toBase k U.basis U.rays U.parameters
        U.regular).isDominant
    let : IsIntegral U.tower.1 :=
      U.fan.isIntegral_internalBlowupTower k U.basis U.rays U.parameters U.regular
    change U.hom.toRationalMap.comp _ = W.hom.toRationalMap
    have hWho : W.hom = U.iso.inv ≫ g.hom ≫ base[W.tower] :=
      W.hom_def.trans (Category.assoc U.iso.inv g.hom _)
    simp only [U.hom_def, hWho, ← Scheme.Hom.toRationalMap_compHom,
      ← Scheme.RationalMap.comp_toRationalMap, Scheme.RationalMap.comp_assoc]
    congr 1

private theorem exists_model_of_mutation [IsIntegral Z]
    (U : OrderedToricModel A m) (b : Module.Basis (Fin 2) ℤ N)
    (ρ : A.fan.Ray) (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ A.fan.cones) (c : kˣ)
    (hFan : B.fan = A.fan.mutationFan b ρ.primitiveGenerator_ne_zero
      ρ.hull_primitiveGenerator_mem hOpp)
    (hMap : A.hom.toRationalMap.comp
      (A.fan.mutationPartialMap k b (c : k) ρ.primitiveGenerator_ne_zero
        ρ.hull_primitiveGenerator_mem hOpp).toRationalMap =
      (cast (congrArg (fun Φ : Fan i ↦ Z ⟶ X[Φ]) hFan) B.hom).toRationalMap) :
    ∃ W : OrderedToricModel B m,
      Nonempty (SarkisovStep U.refinedProjection W.refinedProjection) := by
  obtain ⟨u, e, he, hP, href⟩ := U.exists_tower_in_basis b
  let U' : OrderedToricModel A m :=
    ⟨U.fan, U.regular, U.subdivision, b, U.rays, u, e, he, hP⟩
  have hRef : U'.refinedProjection = U.refinedProjection :=
    LogarithmicProjection.ext rfl (heq_of_eq (U'.hom_def.trans href))
  obtain ⟨n, hm, k, -, -, e', he', hP', -, step, -⟩ :=
    U'.exists_model_of_mutation_in_basis ρ hOpp c hFan hMap
  subst m
  exact ⟨_, ⟨hRef ▸ step⟩⟩

/-- Transport an ordered model and its marking along a fan equivalence and a translation.
The refined projections commute with the translated fan map as regular morphisms. -/
theorem exists_model_of_iso [IsIntegral Z]
    (U : OrderedToricModel A m) (f : FanEquiv A.fan B.fan)
    (χ : Multiplicative (N →+ ℤ) →* kˣ)
    (h : A.hom.toRationalMap.comp
      (f.toFanHom.finiteFanSchemeHom k ≫ (B.fan.torusTranslationIso k χ).hom).toRationalMap =
        B.hom.toRationalMap) :
    let Θ := U.fan.mapEquiv B.fan.lattice f.latticeEquiv
    let F := U.fan.mapEquivIso B.fan.lattice f.latticeEquiv
    let K := f.isSubdivision_mapEquiv U.subdivision
    let b := U.basis.map F.latticeEquiv.toIntLinearEquiv
    let s := F.rayEquiv ∘ U.rays
    let c := fun j ↦ U.parameters j / χ (Multiplicative.ofAdd
      (b.detDualEquiv (s j).primitiveGenerator).toAddMonoidHom)
    let T := tower[K,b,s,c]
    ∃ (e : T.1 ≅ Z) (he : e.hom ≫ B.hom = base[T] ≫ π[K])
      (hP : D.comap e.hom = T.2.boundaryι.ker),
      let W : OrderedToricModel B m := ⟨Θ, F.isRegular_iff.mpr U.regular, K, b, s, c, e, he, hP⟩
      letI : Nonempty Θ.cones := K.nonempty_cones_of_nonempty B.isComplete.nonempty_cones
      let t := F.toFanHom.finiteFanSchemeHom k ≫ (Θ.torusTranslationIso k χ).hom
      U.hom ≫ t = W.hom ∧ Nonempty (SarkisovStep U.refinedProjection W.refinedProjection) := by
  intro Θ F K b s c T
  obtain ⟨g, hg, hproj, hPole, -, -⟩ := exists_ordered_toric_iso_model f χ h
    U.basis U.regular U.subdivision U.rays U.parameters U.iso U.hom_eq U.pole_eq
  refine ⟨g.symm ≪≫ U.iso, hproj, hPole, ?_⟩
  intro W t
  let : Nonempty Θ.cones := K.nonempty_cones_of_nonempty B.isComplete.nonempty_cones
  have ht : U.hom ≫ t = W.hom := by
    simp only [U.hom_def, W.hom_def, W, Iso.trans_inv, Iso.symm_inv, Category.assoc]
    simpa only [Iso.trans_hom, FanEquiv.finiteFanSchemeIso_hom, t] using
      congrArg (U.iso.inv ≫ ·) hg.hom_toBase.symm
  refine ⟨ht, ⟨⟨t.toRationalMap, .toricIso F χ, ?_⟩⟩⟩
  change U.hom.toRationalMap.comp t.toRationalMap = W.hom.toRationalMap
  rw [Scheme.RationalMap.comp_toRationalMap, Scheme.Hom.toRationalMap_compHom, ht]

end OrderedToricModel

/-- Normalize a logarithmic modification into an ordered internal model after
a regular toric subdivision of its target. -/
theorem exists_ordered_toric_model [IsIntegral Z] [Z.IsProjectiveOver k]
    (A : LogarithmicProjection k i D) [IsModification A.hom] (b : Module.Basis (Fin 2) ℤ N) :
    ∃ m, Nonempty (OrderedToricModel A m) := by
  obtain ⟨Θ, hΘ, J, m, r, c, e, he, hD⟩ :=
    A.fan.exists_toric_internal_factorization_of_boundary_comap_eq k b A.isRegular A.isComplete
      (IsModification.birationalOver A.hom) A.comap_boundaryIdeal
  exact ⟨m, ⟨⟨Θ, hΘ, J, b, r, c, e, he, hD⟩⟩⟩

variable [IsIntegral Z]

/-- An ordered model of the source of a resolved link transports to an ordered
model of its specified target projection with the same number of centers. -/
theorem SarkisovStep.exists_ordered_toric_model [Z.IsProjectiveOver k] (e : SarkisovStep A B)
    (U : OrderedToricModel A m) :
    ∃ W : OrderedToricModel B m,
      Nonempty (SarkisovStep U.refinedProjection W.refinedProjection) := by
  rcases e with ⟨f, hf, h⟩
  cases A
  cases B
  cases hf with
  | blowup H =>
    apply U.exists_model_of_starStep (.blowup H ?_)
    let (F : Fan i) : X[F].IsSeparated := F.isSeparated_finiteFanScheme k
    apply Scheme.Hom.toRationalMap_injective
    have hh := congrArg (fun f ↦ f.compHom π[H.isSubdivision]) h
    rw [← Scheme.RationalMap.comp_toRationalMap, Scheme.RationalMap.comp_assoc,
      H.isSubdivision.toRationalMap_finiteFanSchemeHom k, denseTorusPartialIso_toRationalMap_comp,
      denseTorusPartialIso_self_toRationalMap, Scheme.RationalMap.comp_id,
      Scheme.Hom.toRationalMap_compHom] at hh
    exact hh.symm
  | blowdown H =>
    apply U.exists_model_of_starStep (.blowdown H ?_)
    let (F : Fan i) : X[F].IsSeparated := F.isSeparated_finiteFanScheme k
    apply Scheme.Hom.toRationalMap_injective
    rwa [← H.isSubdivision.toRationalMap_finiteFanSchemeHom k,
      Scheme.RationalMap.comp_toRationalMap,
      Scheme.Hom.toRationalMap_compHom] at h
  | mutation b ρ c hOpp =>
    exact U.exists_model_of_mutation b ρ hOpp c rfl h
  | toricIso f χ =>
    obtain ⟨_, _, _, -, hStep⟩ := U.exists_model_of_iso f χ h
    exact ⟨_, hStep⟩

/-- The quiver of specified projections together with chosen ordered presentations.
An edge pairs an original resolved link with a link on the refined fans. -/
abbrev presentationQuiver (m : ℕ) :
    Quiver (Σ C : LogarithmicProjection k i D, OrderedToricModel C m) where
  Hom U W := SarkisovStep U.1 W.1 × SarkisovStep U.2.refinedProjection W.2.refinedProjection

scoped[Sarkisov] attribute [instance]
  TauCeti.Toric.Fan.LogarithmicProjection.presentationQuiver

/-- Forget the ordered presentation of a projection and retain its original links. -/
@[simps]
abbrev forgetPresentation (m : ℕ) :
    @Prefunctor _ (presentationQuiver (k := k) (i := i) (D := D) m)
      (LogarithmicProjection k i D) sarkisovQuiver where
  obj := Sigma.fst
  map e := e.1

/-- Read a path of ordered presentations as links on their intermediate fans. -/
@[simps]
abbrev refinePresentation (m : ℕ) :
    @Prefunctor _ (presentationQuiver (k := k) (i := i) (D := D) m)
      (LogarithmicProjection k i D) sarkisovQuiver where
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
theorem SarkisovPath.exists_ordered_toric_models [Z.IsProjectiveOver k] (p : SarkisovPath A B)
    (U : OrderedToricModel A m) :
    ∃ (W : OrderedToricModel B m)
      (q : @Quiver.Path _ (presentationQuiver m) ⟨A, U⟩ ⟨B, W⟩),
      (forgetPresentation m).mapPath q = p ∧
        π[U.subdivision].toRationalMap.comp p.rationalMap =
          (SarkisovPath.rationalMap ((refinePresentation m).mapPath q)).comp
            π[W.subdivision].toRationalMap := by
  let F := forgetPresentation (k := k) (i := i) (D := D) m
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
