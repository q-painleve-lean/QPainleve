/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.TwistingTransition
public import QPainleve.AlgebraicGeometry.RelativeProj.ProjectiveBundle
public import QPainleve.AlgebraicGeometry.RelativeProj.LineBundle.Basic
public import TauCeti.RingTheory.MvPolynomial.HomogeneousLocalization

import Mathlib.LinearAlgebra.Basis.Fin
import QPainleve.AlgebraicGeometry.RelativeProj.SectionCoordinates
import TauCeti.Algebra.Category.ModuleCat.Biproducts

/-!
# Polynomial charts of split projective bundles on the projective line

The standard generators of the two twisting summands give polynomial charts
of the quotient-convention projective bundle of `𝒪(a) ⊞ 𝒪(b)`. Over the common
base chart the transition sends the two homogeneous variables to their multiples
by `t^a` and `t^b`, where `t = X₁/X₀` is the base coordinate. Thus the fiber
ratio changes by `t^(a-b)` when the first summand supplies its numerator.
This gives the coordinate transition used in the Hirzebruch surface construction.

The charts use `QuasicoherentSheaf.relativeProjPolynomialChart`, with the
quotient convention of [Stacks, Section 27.21][stacks-01OA].

[stacks-01OA]: https://stacks.math.columbia.edu/tag/01OA
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace TauCeti.AlgebraicGeometry.projectiveLine

variable (R : Type u) [CommRing R]

local notation "P" => projectiveLine R
local notation "𝒜" => TauCeti.SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)
local notation "U[" i "]" => Proj.basicOpen 𝒜 (coord R i)
local notation "line[" n "]" =>
  Functor.obj (InvertibleSheaf.toFixedRankOne (projectiveLine R))
    (Proj.symmetricAlgebraTwistingBundle R (Fin 2 → R) n)
local notation "F[" a "," b "]" =>
  Functor.obj (FiniteLocallyFreeSheaf.toQuasicoherent (projectiveLine R))
    (ObjectProperty.FullSubcategory.obj (FiniteLocallyFreeSheaf.FixedRank.biprod line[a] line[b]))

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

private abbrev twistingModule (n : ℤ) : (P).Modules := Proj.twistingSheaf 𝒜 n

local notation "T[" n "]" => twistingModule R n
local notation "TS[" a "," b "]" =>
  @biprod (Scheme.Modules (projectiveLine R)) _ _ (twistingModule R a) (twistingModule R b) _

private def twistingModuleIso (n : ℤ) : line[n].obj.obj ≅ T[n] :=
  eqToIso (by rw [InvertibleSheaf.toFixedRankOne_obj_obj, ObjectProperty.ιOfLE_obj_obj,
    Proj.symmetricAlgebraTwistingBundle_obj])

private def splitTwistingSheafIso (a b : ℤ) :
    (F[a,b]).obj ≅ TS[a,b] :=
  line[a].biprodObjIso line[b] ≪≫
    biprod.mapIso (C := (P).Modules) (twistingModuleIso R a) (twistingModuleIso R b)

private def splitTwistingSectionsIso (a b : ℤ) (V : (P).Opens) :
    (Scheme.Modules.sectionsFunctor V).obj (F[a,b]).obj ≅
      ModuleCat.of Γ(P, V) (Γ(T[a], V) × Γ(T[b], V)) :=
  let S := Scheme.Modules.sectionsFunctor V
  S.mapIso (splitTwistingSheafIso R a b) ≪≫
    S.mapBiprod T[a] T[b] ≪≫ ModuleCat.biprodIsoProd (S.obj T[a]) (S.obj T[b])

/-- The frame on a subopen of the `i`th standard chart of the projective line, with one
basis vector for the standard generator of each twisting summand. -/
def splitTwistingFrame (a b : ℤ) (i : Fin 2) {V : (P).Opens} (h : V ≤ U[i]) :
    Module.Basis (ULift.{u} (Fin 2)) Γ(P, V)
      ((Scheme.Modules.sectionsFunctor V).obj (F[a,b]).obj) :=
  ((Module.Basis.finTwoProd Γ(P, V)).reindex Equiv.ulift.symm).map
    ((Proj.twistingSheaf.chartSectionsLinearEquiv a (coord R i) (coord_mem R i) V h).prodCongr
      (Proj.twistingSheaf.chartSectionsLinearEquiv b (coord R i) (coord_mem R i) V h) ≪≫ₗ
        (splitTwistingSectionsIso R a b V).symm.toLinearEquiv)

private theorem splitTwistingSectionsIso_inv_pair (a b : ℤ) (V : (P).Opens)
    (x : Γ(T[a], V)) (y : Γ(T[b], V)) :
    (splitTwistingSectionsIso R a b V).inv (x, y) =
      (splitTwistingSheafIso R a b).inv.val.app (op V)
        ((biprod.inl : T[a] ⟶ TS[a,b]).val.app (op V) x +
          (biprod.inr : T[b] ⟶ TS[a,b]).val.app (op V) y) := by
  let S := Scheme.Modules.sectionsFunctor V
  let e := S.mapBiprod T[a] T[b]
  let f := ModuleCat.biprodIsoProd (S.obj T[a]) (S.obj T[b])
  have hxy : f.inv (x, y) =
      (biprod.inl : S.obj T[a] ⟶ S.obj T[a] ⊞ S.obj T[b]) x +
        (biprod.inr : S.obj T[b] ⟶ S.obj T[a] ⊞ S.obj T[b]) y := by
    apply (ConcreteCategory.bijective_of_isIso f.hom).injective
    rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply]
    have hinl : f.hom ((biprod.inl : S.obj T[a] ⟶ S.obj T[a] ⊞ S.obj T[b]) x) = (x, 0) :=
      ConcreteCategory.congr_hom (ModuleCat.inl_comp_biprodIsoProd_hom (S.obj T[a]) (S.obj T[b])) x
    have hinr : f.hom ((biprod.inr : S.obj T[b] ⟶ S.obj T[a] ⊞ S.obj T[b]) y) = (0, y) :=
      ConcreteCategory.congr_hom (ModuleCat.inr_comp_biprodIsoProd_hom (S.obj T[a]) (S.obj T[b])) y
    rw [map_add, hinl, hinr]
    exact Prod.ext (add_zero x).symm (zero_add y).symm
  have hl : biprod.inl ≫ e.inv = S.map (biprod.inl : T[a] ⟶ TS[a,b]) := by
    simp [e]
  have hr : biprod.inr ≫ e.inv = S.map (biprod.inr : T[b] ⟶ TS[a,b]) := by
    simp [e]
  -- The composite of the section comparison isomorphisms acts in reverse order.
  change S.map (splitTwistingSheafIso R a b).inv (e.inv (f.inv (x, y))) = _
  rw [hxy, map_add]
  exact congrArg (S.map (splitTwistingSheafIso R a b).inv)
    (congrArg₂ (· + ·) (ConcreteCategory.congr_hom hl x) (ConcreteCategory.congr_hom hr y))

private theorem splitTwistingFrame_zero (a b : ℤ) (i : Fin 2) {V : (P).Opens} (h : V ≤ U[i]) :
    splitTwistingFrame R a b i h ⟨0⟩ =
      ((biprod.inl : T[a] ⟶ TS[a,b]) ≫ (splitTwistingSheafIso R a b).inv).val.app (op V)
        (Proj.twistingSheaf.chartGenerator a (coord R i) (coord_mem R i) V h) := by
  simp only [splitTwistingFrame, Module.Basis.map_apply, Module.Basis.reindex_apply,
    Equiv.symm_symm, Equiv.ulift_apply, Module.Basis.finTwoProd_zero,
    LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, map_zero,
    Proj.twistingSheaf.chartSectionsLinearEquiv_apply, one_smul]
  let g := Proj.twistingSheaf.chartGenerator a (coord R i) (coord_mem R i) V h
  have he := splitTwistingSectionsIso_inv_pair R a b V g 0
  have hz : (biprod.inr : T[b] ⟶ TS[a,b]).val.app (op V) (0 : Γ(T[b], V)) = 0 :=
    map_zero (ModuleCat.Hom.hom ((biprod.inr : T[b] ⟶ TS[a,b]).val.app (op V)))
  rw [hz, add_zero] at he
  exact he.trans (Scheme.Modules.Hom.comp_val_app_apply _ _ _ _).symm

private theorem splitTwistingFrame_one (a b : ℤ) (i : Fin 2) {V : (P).Opens} (h : V ≤ U[i]) :
    splitTwistingFrame R a b i h ⟨1⟩ =
      ((biprod.inr : T[b] ⟶ TS[a,b]) ≫ (splitTwistingSheafIso R a b).inv).val.app (op V)
        (Proj.twistingSheaf.chartGenerator b (coord R i) (coord_mem R i) V h) := by
  simp only [splitTwistingFrame, Module.Basis.map_apply, Module.Basis.reindex_apply,
    Equiv.symm_symm, Equiv.ulift_apply, Module.Basis.finTwoProd_one,
    LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, map_zero,
    Proj.twistingSheaf.chartSectionsLinearEquiv_apply, one_smul]
  let g := Proj.twistingSheaf.chartGenerator b (coord R i) (coord_mem R i) V h
  have he := splitTwistingSectionsIso_inv_pair R a b V 0 g
  have hz : (biprod.inl : T[a] ⟶ TS[a,b]).val.app (op V) (0 : Γ(T[a], V)) = 0 :=
    map_zero (ModuleCat.Hom.hom ((biprod.inl : T[a] ⟶ TS[a,b]).val.app (op V)))
  rw [hz, zero_add] at he
  exact he.trans (Scheme.Modules.Hom.comp_val_app_apply _ _ _ _).symm

local notation "L[" n "]" =>
  Functor.obj (FiniteLocallyFreeSheaf.toQuasicoherent (projectiveLine R))
    (ObjectProperty.FullSubcategory.obj line[n])
private abbrev splitTwistingLineModule (n : ℤ) : (P).Modules := (L[n]).obj

local notation "M[" n "]" => splitTwistingLineModule R n

/-- The quotient onto the first twisting summand of the split bundle. -/
def splitTwistingFst (a b : ℤ) : F[a,b] ⟶ L[a] :=
  ObjectProperty.homMk (C := (P).Modules)
    ((splitTwistingSheafIso R a b).hom ≫ (biprod.fst : TS[a,b] ⟶ T[a]) ≫
      (twistingModuleIso R a).inv)

/-- The quotient onto the second twisting summand of the split bundle. -/
def splitTwistingSnd (a b : ℤ) : F[a,b] ⟶ L[b] :=
  ObjectProperty.homMk (C := (P).Modules)
    ((splitTwistingSheafIso R a b).hom ≫ (biprod.snd : TS[a,b] ⟶ T[b]) ≫
      (twistingModuleIso R b).inv)

/-- The first quotient is the first projection under the fixed-rank direct sum comparison. -/
theorem splitTwistingFst_hom (a b : ℤ) :
    (splitTwistingFst R a b).hom = (line[a].biprodObjIso line[b]).hom ≫ biprod.fst := by
  calc
    _ = (splitTwistingSheafIso R a b).hom ≫ (biprod.fst : TS[a,b] ⟶ T[a]) ≫
        (twistingModuleIso R a).inv := rfl
    _ = _ := by
      erw [splitTwistingSheafIso, Iso.trans_hom, Category.assoc,
        biprod.mapIso_hom (C := (P).Modules), biprod.map_fst_assoc (C := (P).Modules),
        Iso.hom_inv_id, Category.comp_id]
      rfl

/-- The second quotient is the second projection under the fixed-rank direct sum comparison. -/
theorem splitTwistingSnd_hom (a b : ℤ) :
    (splitTwistingSnd R a b).hom = (line[a].biprodObjIso line[b]).hom ≫ biprod.snd := by
  calc
    _ = (splitTwistingSheafIso R a b).hom ≫ (biprod.snd : TS[a,b] ⟶ T[b]) ≫
        (twistingModuleIso R b).inv := rfl
    _ = _ := by
      erw [splitTwistingSheafIso, Iso.trans_hom, Category.assoc,
        biprod.mapIso_hom (C := (P).Modules), biprod.map_snd_assoc (C := (P).Modules),
        Iso.hom_inv_id, Category.comp_id]
      rfl

instance (a b : ℤ) : Epi (splitTwistingFst R a b).hom := by
  exact @epi_comp (P).Modules _ _ _ _ (splitTwistingSheafIso R a b).hom
    (@IsIso.epi_of_iso (P).Modules _ _ _ _ (splitTwistingSheafIso R a b).isIso_hom)
    _ (@epi_comp (P).Modules _ _ _ _ (biprod.fst : TS[a,b] ⟶ T[a]) inferInstance
      (twistingModuleIso R a).inv
      (@IsIso.epi_of_iso (P).Modules _ _ _ _ (twistingModuleIso R a).isIso_inv))

instance (a b : ℤ) : Epi (splitTwistingSnd R a b).hom := by
  exact @epi_comp (P).Modules _ _ _ _ (splitTwistingSheafIso R a b).hom
    (@IsIso.epi_of_iso (P).Modules _ _ _ _ (splitTwistingSheafIso R a b).isIso_hom)
    _ (@epi_comp (P).Modules _ _ _ _ (biprod.snd : TS[a,b] ⟶ T[b]) inferInstance
      (twistingModuleIso R b).inv
      (@IsIso.epi_of_iso (P).Modules _ _ _ _ (twistingModuleIso R b).isIso_inv))

/-- The sections of the split projective bundle determined by projection onto each
twisting summand, indexed in the same order as the two homogeneous coordinates. -/
def relativeProjSplitTwistingSection (a b : ℤ) (j : Fin 2) :
    P ⟶ ((gradedSymmetricAlgebra P).obj F[a,b]).obj.relativeProj :=
  Fin.cases (line[a].relativeProjSectionOfQuotient (splitTwistingFst R a b))
    (fun _ ↦ line[b].relativeProjSectionOfQuotient (splitTwistingSnd R a b)) j

@[simp]
theorem relativeProjSplitTwistingSection_zero (a b : ℤ) :
    relativeProjSplitTwistingSection R a b 0 =
      line[a].relativeProjSectionOfQuotient (splitTwistingFst R a b) :=
  (rfl)

@[simp]
theorem relativeProjSplitTwistingSection_one (a b : ℤ) :
    relativeProjSplitTwistingSection R a b 1 =
      line[b].relativeProjSectionOfQuotient (splitTwistingSnd R a b) :=
  (rfl)

@[reassoc (attr := simp)]
theorem relativeProjSplitTwistingSection_toBase (a b : ℤ) (j : Fin 2) :
    relativeProjSplitTwistingSection R a b j ≫
      ((gradedSymmetricAlgebra P).obj F[a,b]).obj.relativeProjToBase = 𝟙 _ := by
  fin_cases j
  · exact (line[a]).relativeProjSectionOfQuotient_toBase (splitTwistingFst R a b)
  · exact (line[b]).relativeProjSectionOfQuotient_toBase (splitTwistingSnd R a b)

private def twistingLineFrame (a : ℤ) (i : Fin 2) {V : (P).Opens} (h : V ≤ U[i]) :
    Module.Basis (ULift.{u} (Fin 1)) Γ(P, V)
      ((Scheme.Modules.sectionsFunctor V).obj L[a].obj) :=
  (Module.Basis.singleton (ULift.{u} (Fin 1)) Γ(P, V)).map
    (Proj.twistingSheaf.chartSectionsLinearEquiv a (coord R i) (coord_mem R i) V h ≪≫ₗ
      ((Scheme.Modules.sectionsFunctor V).mapIso (twistingModuleIso R a).symm).toLinearEquiv)

private theorem twistingLineFrame_apply (a : ℤ) (i : Fin 2) {V : (P).Opens} (h : V ≤ U[i]) :
    twistingLineFrame R a i h ⟨0⟩ = ((Scheme.Modules.sectionsFunctor V).map
        (twistingModuleIso R a).inv)
      (Proj.twistingSheaf.chartGenerator a (coord R i) (coord_mem R i) V h) := by
  rw [twistingLineFrame, Module.Basis.map_apply, Module.Basis.singleton_apply]
  -- The sections functor and section modules have the same underlying sections.
  change ((Scheme.Modules.sectionsFunctor V).map (twistingModuleIso R a).inv)
    (Proj.twistingSheaf.chartSectionsLinearEquiv a (coord R i) (coord_mem R i) V h 1) = _
  rw [Proj.twistingSheaf.chartSectionsLinearEquiv_apply, one_smul]

private theorem splitTwistingFst_frame
    (a b : ℤ) (i : Fin 2) {V : (P).Opens} (h : V ≤ U[i]) :
    let S := Scheme.Modules.sectionsFunctor V
    let q := (S.map (splitTwistingFst R a b).hom).hom
    let f := splitTwistingFrame R a b i h
    q (f ⟨0⟩) = twistingLineFrame R a i h ⟨0⟩ ∧ q (f ⟨1⟩) = 0 := by
  dsimp only
  let G := splitTwistingSheafIso R a b
  let S := Scheme.Modules.sectionsFunctor V
  have hfst : (splitTwistingFst R a b).hom =
      G.hom ≫ (biprod.fst : TS[a,b] ⟶ T[a]) ≫ (twistingModuleIso R a).inv := rfl
  constructor
  · rw [splitTwistingFrame_zero, twistingLineFrame_apply]
    have he : ((biprod.inl : T[a] ⟶ TS[a,b]) ≫ G.inv) ≫ (splitTwistingFst R a b).hom =
        (twistingModuleIso R a).inv := by
      erw [Category.assoc, hfst, G.inv_hom_id_assoc, biprod.inl_fst_assoc]
    have h := ConcreteCategory.congr_hom (congrArg (fun f : T[a] ⟶ M[a] ↦ S.map f) he)
      (Proj.twistingSheaf.chartGenerator a (coord R i) (coord_mem R i) V h)
    erw [S.map_comp, ConcreteCategory.comp_apply] at h
    exact h
  · rw [splitTwistingFrame_one]
    have he : ((biprod.inr : T[b] ⟶ TS[a,b]) ≫ G.inv) ≫ (splitTwistingFst R a b).hom =
        (0 : T[b] ⟶ M[a]) := by
      erw [Category.assoc, hfst, G.inv_hom_id_assoc, biprod.inr_fst_assoc, zero_comp]
    have h := ConcreteCategory.congr_hom (congrArg (fun f : T[b] ⟶ M[a] ↦ S.map f) he)
      (Proj.twistingSheaf.chartGenerator b (coord R i) (coord_mem R i) V h)
    erw [S.map_comp, ConcreteCategory.comp_apply, Functor.map_zero] at h
    exact h

private theorem splitTwistingSnd_frame
    (a b : ℤ) (i : Fin 2) {V : (P).Opens} (h : V ≤ U[i]) :
    let S := Scheme.Modules.sectionsFunctor V
    let q := (S.map (splitTwistingSnd R a b).hom).hom
    let f := splitTwistingFrame R a b i h
    q (f ⟨1⟩) = twistingLineFrame R b i h ⟨0⟩ ∧ q (f ⟨0⟩) = 0 := by
  dsimp only
  let G := splitTwistingSheafIso R a b
  let S := Scheme.Modules.sectionsFunctor V
  have hsnd : (splitTwistingSnd R a b).hom =
      G.hom ≫ (biprod.snd : TS[a,b] ⟶ T[b]) ≫ (twistingModuleIso R b).inv := rfl
  constructor
  · rw [splitTwistingFrame_one, twistingLineFrame_apply]
    have he : ((biprod.inr : T[b] ⟶ TS[a,b]) ≫ G.inv) ≫ (splitTwistingSnd R a b).hom =
        (twistingModuleIso R b).inv := by
      erw [Category.assoc, hsnd, G.inv_hom_id_assoc, biprod.inr_snd_assoc]
    have h := ConcreteCategory.congr_hom (congrArg (fun f : T[b] ⟶ M[b] ↦ S.map f) he)
      (Proj.twistingSheaf.chartGenerator b (coord R i) (coord_mem R i) V h)
    erw [S.map_comp, ConcreteCategory.comp_apply] at h
    exact h
  · rw [splitTwistingFrame_zero]
    have he : ((biprod.inl : T[a] ⟶ TS[a,b]) ≫ G.inv) ≫ (splitTwistingSnd R a b).hom =
        (0 : T[a] ⟶ M[b]) := by
      erw [Category.assoc, hsnd, G.inv_hom_id_assoc, biprod.inl_snd_assoc, zero_comp]
    have h := ConcreteCategory.congr_hom (congrArg (fun f : T[a] ⟶ M[b] ↦ S.map f) he)
      (Proj.twistingSheaf.chartGenerator a (coord R i) (coord_mem R i) V h)
    erw [S.map_comp, ConcreteCategory.comp_apply, Functor.map_zero] at h
    exact h

/-- In a standard affine split frame, projection onto a summand gives the corresponding
coordinate section, with normalized affine coordinate zero. -/
theorem ker_polynomialPoint_eq_comap_relativeProjSplitTwistingSection
    (a b : ℤ) (i j : Fin 2) (V : (P).AffineZariskiSite) (h : V.toOpens ≤ U[i]) :
    let A := Γ(P, V.toOpens)
    (polynomialPoint A (RingHom.id A) j 0).ker =
      (relativeProjSplitTwistingSection R a b j).ker.comap (((Pi.basisFun A (Fin 2)).reindex
        (Equiv.ulift.symm : Fin 2 ≃ ULift.{u} (Fin 2))).polynomialProjIso.inv ≫
        (F[a,b]).relativeProjPolynomialChart V (splitTwistingFrame R a b i h)) := by
  dsimp only
  fin_cases j
  · obtain ⟨h₀, h₁⟩ := splitTwistingFst_frame R a b i h
    exact (line[a]).ker_polynomialPoint_eq_comap_relativeProjSectionOfQuotient
      (splitTwistingFst R a b) V (splitTwistingFrame R a b i h) (twistingLineFrame R a i h)
      0 0 h₀ (h₁.trans (zero_smul _ _).symm)
  · obtain ⟨h₁, h₀⟩ := splitTwistingSnd_frame R a b i h
    exact (line[b]).ker_polynomialPoint_eq_comap_relativeProjSectionOfQuotient
      (splitTwistingSnd R a b) V (splitTwistingFrame R a b i h) (twistingLineFrame R b i h)
      1 0 h₁ (h₀.trans (zero_smul _ _).symm)

/-- Restricting a frame within the same standard chart gives the frame on the smaller open. -/
theorem restrict_splitTwistingFrame (a b : ℤ) (i : Fin 2) {V W : (P).Opens}
    (j : W ⟶ V) (h : V ≤ U[i]) (l : ULift.{u} (Fin 2)) :
    (FiniteLocallyFreeSheaf.FixedRank.biprod line[a] line[b]).obj.obj.val.map j.op
        (splitTwistingFrame R a b i h l) =
      splitTwistingFrame R a b i (j.le.trans h) l := by
  obtain ⟨l⟩ := l
  have hl : l = 0 ∨ l = 1 := by fin_cases l <;> decide
  rcases hl with rfl | rfl
  · rw [splitTwistingFrame_zero, splitTwistingFrame_zero]
    let φ := (biprod.inl : T[a] ⟶ TS[a,b]) ≫ (splitTwistingSheafIso R a b).inv
    have he := PresheafOfModules.naturality_apply φ.val j.op
      (Proj.twistingSheaf.chartGenerator a (coord R i) (coord_mem R i) V h)
    exact he.symm.trans (congrArg (φ.val.app (op W))
      (Proj.twistingSheaf.res_chartGenerator a (coord R i) (coord_mem R i) V h j))
  · rw [splitTwistingFrame_one, splitTwistingFrame_one]
    let φ := (biprod.inr : T[b] ⟶ TS[a,b]) ≫ (splitTwistingSheafIso R a b).inv
    have he := PresheafOfModules.naturality_apply φ.val j.op
      (Proj.twistingSheaf.chartGenerator b (coord R i) (coord_mem R i) V h)
    exact he.symm.trans (congrArg (φ.val.app (op W))
      (Proj.twistingSheaf.res_chartGenerator b (coord R i) (coord_mem R i) V h j))

/-- On the overlap, the chart-one frame vector in summand `l` is the corresponding
chart-zero vector multiplied by the base coordinate to that summand's degree. -/
theorem splitTwistingFrame_one_eq_smul_splitTwistingFrame_zero (a b : ℤ) {V : (P).Opens}
    (h₀ : V ≤ U[0]) (h₁ : V ≤ U[1]) (l : ULift.{u} (Fin 2)) :
    splitTwistingFrame R a b 1 h₁ l =
      (↑(affineCoordinateUnit R h₀ h₁ ^ (if l.down = 0 then a else b)) : Γ(P, V)) •
        splitTwistingFrame R a b 0 h₀ l := by
  obtain ⟨l⟩ := l
  have hl : l = 0 ∨ l = 1 := by fin_cases l <;> decide
  rcases hl with rfl | rfl
  · simp only [ite_true, splitTwistingFrame_zero,
      chartGenerator_one_eq_smul_chartGenerator_zero R a h₀ h₁]
    exact map_smul (ModuleCat.Hom.hom
      (((biprod.inl : T[a] ⟶ TS[a,b]) ≫ (splitTwistingSheafIso R a b).inv).val.app (op V))) _ _
  · simp only [show (1 : Fin 2) ≠ 0 by decide, ite_false, splitTwistingFrame_one,
      chartGenerator_one_eq_smul_chartGenerator_zero R b h₀ h₁]
    exact map_smul (ModuleCat.Hom.hom
      (((biprod.inr : T[b] ⟶ TS[a,b]) ≫ (splitTwistingSheafIso R a b).inv).val.app (op V))) _ _

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Restriction from a polynomial chart in the chart-one frame to the chart-zero
frame on the overlap scales each variable by the corresponding power of `X₁/X₀`.
The coefficient homomorphism is restriction of regular functions. -/
theorem polynomialSectionsRestrict_splitTwistingFrame
    (a b : ℤ) {U V : (P).AffineZariskiSite} (j : V ⟶ U) (h₁ : U.toOpens ≤ U[1])
    (h₀ : V.toOpens ≤ U[0]) :
    let hVU : V.toOpens ≤ U.toOpens := Scheme.AffineZariskiSite.toOpens_mono j.le
    ((F[a,b]).polynomialSectionsRestrict
      (splitTwistingFrame R a b 1 h₁) j (splitTwistingFrame R a b 0 h₀)).toRingHom =
      MvPolynomial.eval₂Hom
        (MvPolynomial.C.comp (((P).presheaf.map (homOfLE hVU).op).hom))
        (fun l : ULift.{u} (Fin 2) ↦
          (↑(affineCoordinateUnit R h₀ (hVU.trans h₁) ^
            (if l.down = 0 then a else b)) : Γ(P, V.toOpens)) • MvPolynomial.X l) := by
  dsimp only
  apply MvPolynomial.ringHom_ext
  · intro r
    rw [MvPolynomial.eval₂Hom_C]
    exact (F[a,b]).polynomialSectionsRestrict_C
      (splitTwistingFrame R a b 1 h₁) j (splitTwistingFrame R a b 0 h₀) r
  · intro l
    rw [MvPolynomial.eval₂Hom_X']
    have hVU : V.toOpens ≤ U.toOpens := Scheme.AffineZariskiSite.toOpens_mono j.le
    have h := (F[a,b]).polynomialSectionsRestrict_X
      (splitTwistingFrame R a b 1 h₁) j (splitTwistingFrame R a b 0 h₀) l
    have hres : (F[a,b]).obj.val.map
        ((Scheme.AffineZariskiSite.toOpensFunctor (P)).map j).op
          (splitTwistingFrame R a b 1 h₁ l) =
        splitTwistingFrame R a b 1 (hVU.trans h₁) l :=
      restrict_splitTwistingFrame R a b 1 (homOfLE hVU) h₁ l
    rw [hres, splitTwistingFrame_one_eq_smul_splitTwistingFrame_zero R
      a b h₀ (hVU.trans h₁), map_smul, Module.Basis.repr_self,
      Finsupp.smul_single_one, Finsupp.sum_single_index (by simp)] at h
    exact h

open HomogeneousLocalization in
/-- In the affine fiber chart where the second coordinate is nonzero, the split
bundle transition multiplies the normalized first coordinate by `t^(a-b)`.
The coordinate is computed in the localization at the second homogeneous variable. -/
theorem polynomialSectionsRestrict_splitTwistingFrame_awayXRatio
    (a b : ℤ) {U V : (P).AffineZariskiSite} (j : V ⟶ U) (h₁ : U.toOpens ≤ U[1])
    (h₀ : V.toOpens ≤ U[0]) :
    let t := affineCoordinateUnit R h₀ (Scheme.AffineZariskiSite.toOpens_mono j.le |>.trans h₁)
    let κ := ULift.{u} (Fin 2)
    let x : MvPolynomial κ Γ(P, V.toOpens) := MvPolynomial.X ⟨1⟩
    let ψ := algebraMap (MvPolynomial κ Γ(P, V.toOpens)) (Localization.Away x)
    let f := ((F[a,b]).polynomialSectionsRestrict
      (splitTwistingFrame R a b 1 h₁) j (splitTwistingFrame R a b 0 h₀)).toRingHom
    ∃ h : IsUnit ((ψ.comp f) (MvPolynomial.X ⟨1⟩)),
      Away.lift (MvPolynomial.homogeneousSubmodule κ Γ(P, U.toOpens)) (ψ.comp f) h
        (TauCeti.MvPolynomial.awayXRatio (R := Γ(P, U.toOpens)) (σ := κ) ⟨1⟩ ⟨0⟩) =
      ψ (MvPolynomial.C ↑(t ^ (a - b))) *
        algebraMap (Away (MvPolynomial.homogeneousSubmodule κ Γ(P, V.toOpens)) x)
          (Localization.Away x)
          (TauCeti.MvPolynomial.awayXRatio (R := Γ(P, V.toOpens)) (σ := κ) ⟨1⟩ ⟨0⟩) := by
  intro t κ x ψ f
  have hX (i : κ) : (ψ.comp f) (MvPolynomial.X i) =
      ψ (MvPolynomial.C ↑(t ^ (if i.down = 0 then a else b))) * ψ (MvPolynomial.X i) := by
    dsimp only [RingHom.comp_apply, f]
    rw [polynomialSectionsRestrict_splitTwistingFrame R a b j h₁ h₀, MvPolynomial.eval₂Hom_X']
    rw [Algebra.smul_def, MvPolynomial.algebraMap_eq, map_mul]
  let s := (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away x) x).unit
  let c := Units.map (ψ.comp MvPolynomial.C).toMonoidHom
  have hs : (s : Localization.Away x) = ψ x := IsUnit.unit_spec _
  have hc (v : Γ(P, V.toOpens)ˣ) : ↑(c v) = ψ (MvPolynomial.C ↑v) := rfl
  have hunit : ↑(c (t ^ b) * s) = (ψ.comp f) (MvPolynomial.X ⟨1⟩) := by
    rw [hX, Units.val_mul, hc, hs]
    rfl
  have hu : IsUnit ((ψ.comp f) (MvPolynomial.X ⟨1⟩)) := ⟨_, hunit⟩
  have heu : hu.unit = c (t ^ b) * s := Units.ext (hu.unit_spec.trans hunit.symm)
  refine ⟨hu, ?_⟩
  rw [TauCeti.MvPolynomial.awayXRatio_def (R := Γ(P, U.toOpens)), Away.lift_mk,
    pow_one, heu, hX, TauCeti.MvPolynomial.val_awayXRatio]
  simp only [ite_true, mul_inv_rev, Units.val_mul]
  have hinv : (↑s⁻¹ : Localization.Away x) = IsLocalization.Away.invSelf x := by
    apply s.mul_right_inj.mp
    rw [Units.mul_inv, hs, IsLocalization.Away.mul_invSelf]
  have hcoeff : (↑(c (t ^ b))⁻¹ : Localization.Away x) = ψ (MvPolynomial.C ↑(t ^ (-b))) := by
    rw [zpow_neg, ← hc, map_inv]
  rw [hinv, hcoeff, sub_eq_add_neg, zpow_add, Units.val_mul, map_mul, map_mul]
  let A := ψ (MvPolynomial.C ↑(t ^ a))
  let B := ψ (MvPolynomial.C ↑(t ^ (-b)))
  let X₀ := ψ (MvPolynomial.X ⟨0⟩)
  let X₁inv : Localization.Away x := IsLocalization.Away.invSelf x
  calc
    (A * X₀) * (X₁inv * B) = (A * X₀) * (B * X₁inv) :=
      congrArg ((A * X₀) * ·) (mul_comm X₁inv B)
    _ = (A * B) * (X₀ * X₁inv) := mul_mul_mul_comm A X₀ B X₁inv
    _ = (A * B) * (X₁inv * X₀) := congrArg ((A * B) * ·) (mul_comm X₀ X₁inv)

end TauCeti.AlgebraicGeometry.projectiveLine
