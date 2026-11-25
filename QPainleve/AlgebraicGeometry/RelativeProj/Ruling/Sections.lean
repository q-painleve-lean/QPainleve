/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RelativeProj.ProjectiveLineCharts
public import TauCeti.AlgebraicGeometry.IntersectionNumber.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import QPainleve.AlgebraicGeometry.RelativeProj.CoordinateFibers
import QPainleve.AlgebraicGeometry.RelativeProj.DisjointSections.Geometric
import QPainleve.AlgebraicGeometry.RelativeProj.Ruling.Isomorphism
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.LineBundle.ProjectiveLine

/-!
# Split projective-line rulings with prescribed sections

On a projective-line ruling, two disjoint sections can be taken as the summand
sections of a split bundle. A change of coordinates on the base also takes two
distinct specified fibers to the coordinate fibers. The isomorphism identifies
the ideal sheaves of these four components, as needed for the ruled case of
[Gross, Hacking and Keel, Proposition 1.3][GHK].

[GHK]: https://arxiv.org/html/1106.4977v3#S1.Thmproposition3
-/

public section

open AlgebraicGeometry CategoryTheory Limits
open TauCeti.AlgebraicGeometry

universe u

variable {k : Type u} [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "P" => projectiveLine k
local notation "L[" a "]" => Functor.obj (InvertibleSheaf.toFixedRankOne P)
  (Proj.symmetricAlgebraTwistingBundle k (Fin 2 → k) a)
local notation "F[" V "]" =>
  Functor.obj (FiniteLocallyFreeSheaf.toQuasicoherent P) (ObjectProperty.FullSubcategory.obj V)
local notation "B[" a "," b "]" => F[FiniteLocallyFreeSheaf.FixedRank.biprod L[a] L[b]]
local notation "A[" F "]" => ObjectProperty.FullSubcategory.obj
  (Functor.obj (gradedSymmetricAlgebra P) F)
local notation "σ[" a "," b ";" j "]" => projectiveLine.relativeProjSplitTwistingSection k a b j
local notation "c[" j "]" => projectiveLine.polynomialPoint k (RingHom.id k) j 0
local notation "π[" a "," b "]" => CommMon.relativeProjToBase A[B[a,b]]

open Scheme.IdealSheafData

namespace TauCeti.AlgebraicGeometry.projectiveLine

private theorem exists_iso_comp_splitTwisting_projections
    {V : FiniteLocallyFreeSheaf.FixedRank P 2} {a b : ℤ}
    (q : F[V] ⟶ F[L[a]]) (r : F[V] ⟶ F[L[b]]) [IsIso (biprod.lift q r)] :
    ∃ e : F[V] ≅ B[a,b],
      e.hom ≫ splitTwistingFst k a b = q ∧ e.hom ≫ splitTwistingSnd k a b = r := by
  let ι : QuasicoherentSheaf P ⥤ (P).Modules := ObjectProperty.ι _
  let : ι.Additive := ⟨rfl⟩
  let := preservesBinaryBiproducts_of_preservesBiproducts ι
  let m := ι.mapBiprod F[L[a]] F[L[b]]
  let n := (L[a]).biprodObjIso L[b]
  let e₀ : B[a,b] ≅ F[L[a]] ⊞ F[L[b]] :=
    ObjectProperty.isoMk (C := (P).Modules) _ (n ≪≫ m.symm)
  let e := asIso (biprod.lift q r) ≪≫ e₀.symm
  let q' : V.obj.obj ⟶ (L[a]).obj.obj := q.hom
  let r' : V.obj.obj ⟶ (L[b]).obj.obj := r.hom
  have he : e.hom.hom ≫ n.hom = biprod.lift q' r' := by
    have h : e.hom.hom = (biprod.lift q r).hom ≫ m.hom ≫ n.inv := by rfl
    erw [h, Category.assoc, Category.assoc, n.inv_hom_id, Category.comp_id]
    exact biprod.map_lift_mapBiprod ι _ _ q r
  refine ⟨e, InducedCategory.hom_ext ?_, InducedCategory.hom_ext ?_⟩
  · erw [ObjectProperty.FullSubcategory.comp_hom, splitTwistingFst_hom,
      ← Category.assoc, he]
    exact biprod.lift_fst q' r'
  · erw [ObjectProperty.FullSubcategory.comp_hom, splitTwistingSnd_hom,
      ← Category.assoc, he]
    exact biprod.lift_snd q' r'

/-- A rank-two projective bundle over the projective line with two ordered disjoint
sections is isomorphic over the base to a split twisting bundle whose summand
sections are the given sections in their prescribed order. -/
theorem exists_relativeProj_iso_biprod_twistingSheaf_of_disjoint_sections
    (V : FiniteLocallyFreeSheaf.FixedRank P 2) (s t : P ⟶ A[F[V]].relativeProj)
    (hs : s ≫ A[F[V]].relativeProjToBase = 𝟙 P)
    (ht : t ≫ A[F[V]].relativeProjToBase = 𝟙 P)
    (hd : Disjoint (Set.range s) (Set.range t)) :
    ∃ (a b : ℤ) (e : A[B[a,b]].relativeProj ≅ A[F[V]].relativeProj),
      e.hom ≫ A[F[V]].relativeProjToBase = A[B[a,b]].relativeProjToBase ∧
      σ[a,b;0] ≫ e.hom = s ∧ σ[a,b;1] ≫ e.hom = t := by
  let T : InvertibleSheaf A[F[V]].relativeProj :=
    ⟨A[F[V]].relativeProjTwistingSheaf 1, inferInstance⟩
  let M := (InvertibleSheaf.pullback s).obj T
  let N := (InvertibleSheaf.pullback t).obj T
  let a := M.eulerDegree k
  let b := N.eulerDegree k
  have htwist (K : InvertibleSheaf P) :
      Nonempty (K.obj ≅ (L[K.eulerDegree k]).obj.obj) := by
    simpa only [InvertibleSheaf.toFixedRankOne_obj_obj, ObjectProperty.ιOfLE_obj_obj,
      Proj.symmetricAlgebraTwistingBundle_obj] using
        (nonempty_iso_twistingSheaf_iff k K (K.eulerDegree k)).mpr rfl
  obtain ⟨i⟩ := htwist M
  obtain ⟨j⟩ := htwist N
  have i' : (Scheme.Modules.pullback s).obj (A[F[V]].relativeProjTwistingSheaf 1) ≅
      (L[a]).obj.obj := (eqToIso (InvertibleSheaf.pullback_obj_obj s T)).symm ≪≫ i
  have j' : (Scheme.Modules.pullback t).obj (A[F[V]].relativeProjTwistingSheaf 1) ≅
      (L[b]).obj.obj := (eqToIso (InvertibleSheaf.pullback_obj_obj t T)).symm ≪≫ j
  obtain ⟨q, r, hq, hr, hsplit, hs', ht'⟩ :=
    V.exists_split_projective_bundle_iso_of_disjoint_sections s t hs ht hd L[a] L[b] i' j'
  let := hq
  let := hr
  let := hsplit
  obtain ⟨e, h₀, h₁⟩ := exists_iso_comp_splitTwisting_projections q r
  let γ : A[F[V]] ≅ A[B[a,b]] :=
    (ObjectProperty.ι _).mapIso ((gradedSymmetricAlgebra P).mapIso e)
  refine ⟨a, b, CommMon.relativeProjMapIso γ, CommMon.relativeProjMapIso_hom_relativeProjToBase γ,
    ?_, ?_⟩
  · rw [relativeProjSplitTwistingSection_zero]
    simpa only [γ, h₀, hs'] using (L[a]).relativeProjSectionOfQuotient_comp_relativeProjMapIso
      e (splitTwistingFst k a b)
  · rw [relativeProjSplitTwistingSection_one]
    simpa only [γ, h₁, ht'] using (L[b]).relativeProjSectionOfQuotient_comp_relativeProjMapIso
      e (splitTwistingSnd k a b)

private theorem exists_splitTwisting_iso_normalizing_fibers (a b : ℤ)
    {y z : S ⟶ P} (hy : y ≫ P ↘ S = 𝟙 S) (hz : z ≫ P ↘ S = 𝟙 S) (hyz : y ≠ z) :
    let π := A[B[a,b]].relativeProjToBase
    ∃ (g : P ≅ P) (e : A[B[a,b]].relativeProj ≅ A[B[a,b]].relativeProj),
      g.hom ≫ P ↘ S = P ↘ S ∧ e.hom ≫ π = π ≫ g.hom ∧
      σ[a,b;0] ≫ e.hom = g.hom ≫ σ[a,b;0] ∧ σ[a,b;1] ≫ e.hom = g.hom ≫ σ[a,b;1] ∧
      (c[0].ker.comap π).comap e.hom = y.ker.comap π ∧
      (c[1].ker.comap π).comap e.hom = z.ker.comap π := by
  dsimp only
  let n := (L[a]).biprodObjIso L[b]
  let fst : B[a,b] ⟶ F[L[a]] := ObjectProperty.homMk (C := (P).Modules) (n.hom ≫ biprod.fst)
  let snd : B[a,b] ⟶ F[L[b]] := ObjectProperty.homMk (C := (P).Modules) (n.hom ≫ biprod.snd)
  have hfst : fst = splitTwistingFst k a b :=
    InducedCategory.hom_ext (splitTwistingFst_hom k a b).symm
  have hsnd : snd = splitTwistingSnd k a b :=
    InducedCategory.hom_ext (splitTwistingSnd_hom k a b).symm
  obtain ⟨g, e, hg, he, h₀, h₁, hy', hz'⟩ :=
    exists_split_projective_bundle_iso_normalizing_fibers L[a] L[b] (F := B[a,b]) n hy hz hyz
  refine ⟨g, e, hg, he, ?_, ?_, hy', hz'⟩
  · simpa only [relativeProjSplitTwistingSection_zero, ← hfst] using h₀
  · simpa only [relativeProjSplitTwistingSection_one, ← hsnd] using h₁

end TauCeti.AlgebraicGeometry.projectiveLine

namespace AlgebraicGeometry.Scheme.Hom

variable {X : Scheme.{u}}

/-- A projective-line ruling with a line bundle of fiber degree one and two disjoint sections
is isomorphic over the base to a split twisting bundle, with the sections corresponding
to the two summand sections in their given order. -/
theorem exists_iso_split_relativeProj_of_disjoint_sections
    [IsAlgClosed k] [X.Over S] [X.IsProjectiveOver k] (f : X ⟶ P) [f.IsOver S] [Flat f]
    (M : InvertibleSheaf X)
    (hf : ∀ y : P, IsClosed ({y} : Set P) →
      ∃ e : P ≅ f.fiber y, e.hom ≫ f.fiberι y ≫ X ↘ S = P ↘ S ∧
        LineBundleClass.intersectionNumber k (e.hom ≫ f.fiberι y) (LineBundleClass.mk M) = 1)
    (s t : P ⟶ X) (hs : s ≫ f = 𝟙 P) (ht : t ≫ f = 𝟙 P)
    (hd : Disjoint (Set.range s) (Set.range t)) :
    ∃ (a b : ℤ) (e : A[B[a,b]].relativeProj ≅ X),
      e.hom ≫ f = A[B[a,b]].relativeProjToBase ∧
      σ[a,b;0] ≫ e.hom = s ∧ σ[a,b;1] ≫ e.hom = t := by
  obtain ⟨V, -, i, hi, -⟩ := f.exists_iso_relativeProj_of_ruling M hf
  have hs' : (s ≫ i.hom) ≫ A[F[V]].relativeProjToBase = 𝟙 P := by
    rw [Category.assoc, hi, hs]
  have ht' : (t ≫ i.hom) ≫ A[F[V]].relativeProjToBase = 𝟙 P := by
    rw [Category.assoc, hi, ht]
  have hrange (v : P ⟶ X) : Set.range (v ≫ i.hom) = i.hom '' Set.range v :=
    Set.range_comp i.hom v
  have hd' : Disjoint (Set.range (s ≫ i.hom)) (Set.range (t ≫ i.hom)) := by
    rw [hrange, hrange, Set.disjoint_image_iff i.hom.injective]
    exact hd
  obtain ⟨a, b, e, he, h₀, h₁⟩ :=
    projectiveLine.exists_relativeProj_iso_biprod_twistingSheaf_of_disjoint_sections V
      (s ≫ i.hom) (t ≫ i.hom) hs' ht' hd'
  refine ⟨a, b, e ≪≫ i.symm, ?_, ?_, ?_⟩
  · rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← hi, Iso.inv_hom_id_assoc, he]
  · rw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, h₀, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  · rw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, h₁, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]

/-- A projective-line ruling with a line bundle of fiber degree one, two disjoint sections
and two distinct rational fibers has a split presentation carrying these to
the ordered summand sections and coordinate fibers. The product of the four ideals
is carried scheme-theoretically, and the change of base coordinates is over the field. -/
theorem exists_iso_split_relativeProj_of_disjoint_sections_and_fibers
    [IsAlgClosed k] [X.Over S] [X.IsProjectiveOver k] (f : X ⟶ P) [f.IsOver S] [Flat f]
    (M : InvertibleSheaf X)
    (hf : ∀ y : P, IsClosed ({y} : Set P) →
      ∃ e : P ≅ f.fiber y, e.hom ≫ f.fiberι y ≫ X ↘ S = P ↘ S ∧
        LineBundleClass.intersectionNumber k (e.hom ≫ f.fiberι y) (LineBundleClass.mk M) = 1)
    (s t : P ⟶ X) (hs : s ≫ f = 𝟙 P) (ht : t ≫ f = 𝟙 P)
    (hd : Disjoint (Set.range s) (Set.range t))
    {y z : S ⟶ P} (hy : y ≫ P ↘ S = 𝟙 S) (hz : z ≫ P ↘ S = 𝟙 S) (hyz : y ≠ z) :
    ∃ (a b : ℤ) (g : P ≅ P) (i : X ≅ A[B[a,b]].relativeProj),
      let π := A[B[a,b]].relativeProjToBase
      g.hom ≫ P ↘ S = P ↘ S ∧ i.hom ≫ π = f ≫ g.hom ∧
      s ≫ i.hom = g.hom ≫ σ[a,b;0] ∧ t ≫ i.hom = g.hom ≫ σ[a,b;1] ∧
      (σ[a,b;0].ker * σ[a,b;1].ker * (c[0].ker.comap π) * (c[1].ker.comap π)).comap i.hom =
        s.ker * t.ker * (y.ker.comap f) * (z.ker.comap f) := by
  obtain ⟨a, b, e, he, h₀, h₁⟩ := f.exists_iso_split_relativeProj_of_disjoint_sections
    M hf s t hs ht hd
  obtain ⟨g, u, hg, hu, hs', ht', hy', hz'⟩ :=
    projectiveLine.exists_splitTwisting_iso_normalizing_fibers a b hy hz hyz
  let i := e.symm ≪≫ u
  have hu' : i.hom = e.inv ≫ u.hom := rfl
  have hπ : e.inv ≫ π[a,b] = f := by rw [← he, Iso.inv_hom_id_assoc]
  have hi : i.hom ≫ π[a,b] = f ≫ g.hom := by
    rw [hu', Category.assoc, hu, ← Category.assoc, hπ]
  have hsi : s ≫ i.hom = g.hom ≫ σ[a,b;0] := by
    simp only [i, Iso.trans_hom, Iso.symm_hom, ← h₀, Category.assoc, Iso.hom_inv_id_assoc, hs']
  have hti : t ≫ i.hom = g.hom ≫ σ[a,b;1] := by
    simp only [i, Iso.trans_hom, Iso.symm_hom, ← h₁, Category.assoc, Iso.hom_inv_id_assoc, ht']
  have hker (s' : P ⟶ X) (t' : P ⟶ A[B[a,b]].relativeProj) (h : s' ≫ i.hom = g.hom ≫ t') :
      t'.ker.comap i.hom = s'.ker := by
    rw [← s'.comap_ker_comp_of_isClosedImmersion i.hom, h, ker_comp_of_isIso]
  have hyi : (c[0].ker.comap π[a,b]).comap i.hom = y.ker.comap f := by
    rw [hu', comap_comp, hy', ← comap_comp, hπ]
  have hzi : (c[1].ker.comap π[a,b]).comap i.hom = z.ker.comap f := by
    rw [hu', comap_comp, hz', ← comap_comp, hπ]
  refine ⟨a, b, g, i, hg, hi, hsi, hti, ?_⟩
  simp only [comap_mul, hker s _ hsi, hker t _ hti, hyi, hzi]

end AlgebraicGeometry.Scheme.Hom
