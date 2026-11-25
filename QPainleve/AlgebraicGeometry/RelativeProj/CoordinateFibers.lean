/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.CoordinateChange
public import QPainleve.AlgebraicGeometry.RelativeProj.LineBundle.Pullback

import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.LineBundle.BaseChange
import TauCeti.AlgebraicGeometry.LineBundle.ProjectiveLine

/-!
# Prescribing two fibers of a split projective bundle

A projective linear change of coordinates on the base projective line lifts to a
split projective bundle and preserves the sections of both summand quotients.
Consequently an ordered pair of fibers can be sent to the coordinate fibers
while retaining the chosen sections. This is the fiber comparison for the
two-fiber case of [Gross, Hacking and Keel, Proposition 1.3][GHK].

[GHK]: https://arxiv.org/html/1106.4977v3#S1.Thmproposition3
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open TauCeti.AlgebraicGeometry GradedQuasicoherentAlgebra
open Scheme.IdealSheafData

universe u

namespace TauCeti.AlgebraicGeometry.projectiveLine

variable {k : Type u} [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "P" => projectiveLine k
local notation "𝒜" => gradedSymmetricAlgebra P
local notation "ℒ" => FiniteLocallyFreeSheaf.toQuasicoherent P
local notation "p[" i "]" => polynomialPoint k (RingHom.id k) i 0

private theorem nonempty_summand_iso_pullback (L : FiniteLocallyFreeSheaf.FixedRank P 1)
    {e : P ≅ P}
    (he : e.hom ≫ (P ↘ S) = (P ↘ S)) :
    Nonempty (((ℒ).obj L.obj) ≅ (QuasicoherentSheaf.pullback e.hom).obj ((ℒ).obj L.obj)) := by
  let N := (FiniteLocallyFreeSheaf.FixedRank.toInvertible P).obj L
  have h : LineBundleClass.pullback e.hom (LineBundleClass.mk N) = LineBundleClass.mk N := by
    apply Additive.ofMul.injective
    apply (picardDegreeEquiv k).injective
    simpa only [picardDegreeEquiv_apply, toMul_ofMul] using
      LineBundleClass.eulerDegree_pullback_of_isIso e.hom he (LineBundleClass.mk N)
  rw [LineBundleClass.pullback_mk, LineBundleClass.mk_eq_mk_iff] at h
  obtain ⟨i⟩ := h
  refine ⟨ObjectProperty.isoMk (C := (P).Modules) _ ?_⟩
  simpa only [QuasicoherentSheaf.pullback_obj_obj, FiniteLocallyFreeSheaf.toQuasicoherent_obj_obj,
    InvertibleSheaf.pullback_obj_obj, N, FiniteLocallyFreeSheaf.FixedRank.toInvertible_obj_obj]
    using i.symm

private theorem pullback_isoMk_comp {X : Scheme.{u}} {f : X ⟶ X} {F G : QuasicoherentSheaf X}
    (E : @Iso X.Modules _ F.obj ((Scheme.Modules.pullback f).obj F.obj))
    (i : G ≅ (QuasicoherentSheaf.pullback f).obj G) (q : F ⟶ G)
    (h : E.hom ≫ (Scheme.Modules.pullback f).map q.hom =
      q.hom ≫ i.hom.hom ≫ eqToHom (QuasicoherentSheaf.pullback_obj_obj f G)) :
    let e : F ≅ (QuasicoherentSheaf.pullback f).obj F :=
      ObjectProperty.isoMk (C := X.Modules) _ (E ≪≫
        eqToIso (QuasicoherentSheaf.pullback_obj_obj f F).symm)
    e.hom ≫ (QuasicoherentSheaf.pullback f).map q = q ≫ i.hom := by
  intro e
  apply InducedCategory.hom_ext
  have he : e.hom.hom =
      E.hom ≫ eqToHom (QuasicoherentSheaf.pullback_obj_obj f F).symm := rfl
  erw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    QuasicoherentSheaf.pullback_map_hom, he, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp, ← Category.assoc, h, Category.assoc, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id]

private theorem exists_pullback_iso_of_splitting (L M : FiniteLocallyFreeSheaf.FixedRank P 1)
    (f : P ⟶ P)
    {F : QuasicoherentSheaf P}
    (a : @Iso (P).Modules _ F.obj (biprod (C := (P).Modules) L.obj.obj M.obj.obj))
    (i : ((ℒ).obj L.obj) ≅ (QuasicoherentSheaf.pullback f).obj ((ℒ).obj L.obj))
    (j : ((ℒ).obj M.obj) ≅ (QuasicoherentSheaf.pullback f).obj ((ℒ).obj M.obj)) :
    let q : F ⟶ ((ℒ).obj L.obj) := ObjectProperty.homMk (C := (P).Modules) (a.hom ≫ biprod.fst)
    let r : F ⟶ ((ℒ).obj M.obj) := ObjectProperty.homMk (C := (P).Modules) (a.hom ≫ biprod.snd)
    ∃ e : F ≅ (QuasicoherentSheaf.pullback f).obj F,
      e.hom ≫ (QuasicoherentSheaf.pullback f).map q = q ≫ i.hom ∧
      e.hom ≫ (QuasicoherentSheaf.pullback f).map r = r ≫ j.hom := by
  intro q r
  let T := Scheme.Modules.pullback f
  let := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts T
  let b := T.mapBiprod L.obj.obj M.obj.obj
  let ι : QuasicoherentSheaf P ⥤ (P).Modules :=
    (SheafOfModules.isQuasicoherent (P).ringCatSheaf).ι
  let i' : L.obj.obj ≅ T.obj L.obj.obj :=
    ι.mapIso i ≪≫ eqToIso (QuasicoherentSheaf.pullback_obj_obj f ((ℒ).obj L.obj))
  let j' : M.obj.obj ≅ T.obj M.obj.obj :=
    ι.mapIso j ≪≫ eqToIso (QuasicoherentSheaf.pullback_obj_obj f ((ℒ).obj M.obj))
  let E := a ≪≫ biprod.mapIso i' j' ≪≫ b.symm ≪≫ T.mapIso a.symm
  let e : F ≅ (QuasicoherentSheaf.pullback f).obj F :=
    ObjectProperty.isoMk (C := (P).Modules) _ (E ≪≫
      eqToIso (QuasicoherentSheaf.pullback_obj_obj f F).symm)
  have h₁ : b.hom ≫ biprod.fst = T.map biprod.fst := by
    rw [Functor.mapBiprod_hom, biprod.lift_fst]
  have h₂ : b.hom ≫ biprod.snd = T.map biprod.snd := by
    rw [Functor.mapBiprod_hom, biprod.lift_snd]
  have hE : E.hom ≫ T.map a.hom ≫ b.hom = a.hom ≫ (biprod.mapIso i' j').hom := by
    have he : E.hom = ((a.hom ≫ (biprod.mapIso i' j').hom) ≫ b.inv) ≫ T.map a.inv := rfl
    erw [he, Category.assoc, ← T.map_comp_assoc, a.inv_hom_id, T.map_id, Category.id_comp,
      Category.assoc, b.inv_hom_id, Category.comp_id]
  refine ⟨e, pullback_isoMk_comp E i q ?_, pullback_isoMk_comp E j r ?_⟩
  · have he : E.hom ≫ T.map (a.hom ≫ biprod.fst) =
        (a.hom ≫ biprod.fst) ≫ i'.hom := by
      erw [T.map_comp, ← h₁, ← Category.assoc, ← Category.assoc, hE,
        Category.assoc, biprod.mapIso_hom, biprod.map_fst, ← Category.assoc]
    erw [← Category.assoc]
    exact he
  · have he : E.hom ≫ T.map (a.hom ≫ biprod.snd) =
        (a.hom ≫ biprod.snd) ≫ j'.hom := by
      erw [T.map_comp, ← h₂, ← Category.assoc, ← Category.assoc, hE,
        Category.assoc, biprod.mapIso_hom, biprod.map_snd, ← Category.assoc]
    erw [← Category.assoc]
    exact he

private theorem comap_fiber_ideal {Y : Scheme.{u}} {π : Y ⟶ P} {e : P ≅ P} {E : Y ≅ Y}
    (hE : E.hom ≫ π = π ≫ e.hom) (p z : S ⟶ P)
    (hz : p ≫ e.hom = z) : (z.ker.comap π).comap E.hom = p.ker.comap π := by
  rw [← comap_comp, hE, comap_comp, ← hz, Scheme.Hom.comap_ker_comp_of_isClosedImmersion p e.hom]

/-- On the projectivization of a direct sum of two line bundles over the projective
line, an ordered pair of distinct rational fibers can be sent to the two coordinate
fibers by an automorphism preserving both sections induced by the summand quotients.
The fiber comparison is scheme-theoretic. -/
theorem exists_split_projective_bundle_iso_normalizing_fibers
    (L M : FiniteLocallyFreeSheaf.FixedRank P 1)
    {F : QuasicoherentSheaf P}
    (a : @Iso (P).Modules _ F.obj (biprod (C := (P).Modules) L.obj.obj M.obj.obj))
    {p q : S ⟶ P} (hp : p ≫ (P ↘ S) = 𝟙 S) (hq : q ≫ (P ↘ S) = 𝟙 S) (hpq : p ≠ q) :
    let fst : F ⟶ ((ℒ).obj L.obj) := ObjectProperty.homMk (C := (P).Modules) (a.hom ≫ biprod.fst)
    let snd : F ⟶ ((ℒ).obj M.obj) := ObjectProperty.homMk (C := (P).Modules) (a.hom ≫ biprod.snd)
    let hEpi := @IsIso.epi_of_iso (P).Modules _ _ _ a.hom a.isIso_hom
    let : Epi fst.hom := @epi_comp (P).Modules _ _ _ _ a.hom hEpi biprod.fst inferInstance
    let : Epi snd.hom := @epi_comp (P).Modules _ _ _ _ a.hom hEpi biprod.snd inferInstance
    let s := L.relativeProjSectionOfQuotient fst
    let t := M.relativeProjSectionOfQuotient snd
    let π := ((𝒜).obj F).obj.relativeProjToBase
    ∃ (e : P ≅ P) (E : ((𝒜).obj F).obj.relativeProj ≅ ((𝒜).obj F).obj.relativeProj),
      e.hom ≫ (P ↘ S) = (P ↘ S) ∧
      E.hom ≫ π = π ≫ e.hom ∧
      s ≫ E.hom = e.hom ≫ s ∧ t ≫ E.hom = e.hom ≫ t ∧
      (p[0].ker.comap π).comap E.hom = p.ker.comap π ∧
      (p[1].ker.comap π).comap E.hom = q.ker.comap π := by
  intro fst snd _ hfst hsnd s t π
  let : Epi fst.hom := hfst
  let : Epi snd.hom := hsnd
  obtain ⟨g, hp₀, hq₁⟩ := exists_linearEquiv_comp_eq_coordinatePoints hp hq hpq
  let e := Proj.symmetricAlgebraMapIso k g
  have he : e.hom ≫ (P ↘ S) = (P ↘ S) := by
    rw [SymmetricAlgebra.over_eq_projToSpec]
    exact Proj.symmetricAlgebraMapIso_hom_projToSpec k g
  obtain ⟨i⟩ := nonempty_summand_iso_pullback L he
  obtain ⟨j⟩ := nonempty_summand_iso_pullback M he
  obtain ⟨h, hi, hj⟩ := exists_pullback_iso_of_splitting L M e.hom a i j
  let E := QuasicoherentSheaf.projectivizationIsoOfPullback e h
  have hE : E.hom ≫ π = π ≫ e.hom :=
    QuasicoherentSheaf.projectivizationIsoOfPullback_hom_toBase e h
  refine ⟨e, E, he, hE,
    ?_, ?_,
    comap_fiber_ideal hE p p[0] hp₀, comap_fiber_ideal hE q p[1] hq₁⟩
  · rw [QuasicoherentSheaf.projectivizationIsoOfPullback_hom]
    exact (L.isPullback_relativeProjSectionOfQuotient e.hom L h i fst fst hi).w
  · rw [QuasicoherentSheaf.projectivizationIsoOfPullback_hom]
    exact (M.isPullback_relativeProjSectionOfQuotient e.hom M h j snd snd hj).w

end TauCeti.AlgebraicGeometry.projectiveLine
