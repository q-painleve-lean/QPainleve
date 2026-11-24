/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Center
public import QPainleve.Algebra.Cluster.Word.RationalMap
public import QPainleve.SignedClusterModularGroup.Realization.Basic

/-!
# The geometric realization of signed X inversion

The pair and its Picard marking stay fixed as the boundary numbering reverses
and each X coordinate is inverted. On a family the center character is inverted
as well, so the two frames refer to the same ordered centers. The reflection fixes
component zero and exchanges the branches at each reindexed node.

The signed generator is the simultaneous inversion of Bershtein, Gavrylenko and
Marshakov, [*Cluster integrable systems, q-Painlevé equations and their quantization*,
§3.1](https://arxiv.org/abs/1711.02063).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative
open QPainleve.CharacterTorus QPainleve.Cluster
open TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.PartialMap

universe u

namespace QPainleve.SignedClusterModularGroup

variable {k : Type u} [Field k] [IsSepClosed k] [Infinite k]
  {ι : Type u} {n : ℕ} [NeZero n] {L : Type u} [AddCommGroup L]
  {B : LinearMap.BilinForm ℤ L}

local notation "A" => (ι → ℤ)
local notation "XTor" => scheme k (ι →₀ ℤ)
local notation "invX" => map k (AddEquiv.toAddMonoidHom (AddEquiv.neg (ι →₀ ℤ)))

namespace FiberRealization

variable [Finite ι] [DecidableEq ι]

/-- The identity of a marked pair realizes the signed inversion step between the
original and opposite frames. Its Picard pullback is the identity and its action
on the numbered branches is the reflection fixing component zero. -/
def invert (M : MarkedSurface k n B XTor) (E : SkewExchangeMatrix ι) :
    FiberRealization M M.invert
      ((Generator.invert.toStep E).toPath.xRationalMap k) (.refl B) (.sr 0) :=
  have hIso : MarkedSurface.surfaceIso (M := M) (N := M.invert) (Iso.refl M.pair) =
      Iso.refl M.surface := MarkedSurface.surfaceIso_refl (M := M)
  { iso := Iso.refl M.pair
    picard_eq a := by
      have ha : LinearMap.BilinForm.IsometryEquiv.refl B a = a := rfl
      rw [ha, hIso, Iso.refl_hom, MarkedSurface.invert_picardMarking]
      exact congrArg Additive.ofMul (LineBundleClass.pullback_id (M.picardMarking a).toMul).symm
    boundaryAction_eq := M.boundaryCycleAction_invert_refl
    evaluation_eq := by
      rw [Quiver.Path.xRationalMap_invert]
      obtain ⟨h, he⟩ := M.evaluation.compOfDefined_toRationalMap invX
      refine ⟨h, he.trans ?_⟩
      simp only [hIso, Iso.refl_hom, MarkedSurface.invert_evaluation]
      exact (RationalMap.id_comp (M.evaluation.compHom invX)).symm }

@[simp]
theorem invert_iso (M : MarkedSurface k n B XTor) (E : SkewExchangeMatrix ι) :
    (invert M E).iso = Iso.refl M.pair := (rfl)

end FiberRealization

namespace GeometricRealization

local notation "Centers" => Over.mk (structureMap k A)

variable [Fintype ι] [DecidableEq ι]

local notation "invertStep" E:arg => Quiver.Hom.toPath (Generator.invert.toStep E)
local notation "centerMap" E:arg => Scheme.Hom.toPartialMap
  (CategoryTheory.Iso.hom (Quiver.Path.centerIso k (invertStep E)))
local notation "centerOver" E:arg => Quiver.Path.centerIsoOver k (invertStep E)

local instance (E : SkewExchangeMatrix ι) : IsDominant (centerMap E).hom := by
  rw [Hom.toPartialMap_hom]
  exact ⟨((scheme k A).topIso ≪≫ (invertStep E).centerIso k).hom.surjective.denseRange⟩

local instance (E : SkewExchangeMatrix ι) :
    (centerMap E).IsOver (Over.mk (structureMap k A)).hom (Over.mk (structureMap k A)).hom :=
  Hom.isOver_toPartialMap ((invertStep E).centerIso_hom_structureMap k)

omit [IsSepClosed k] [Infinite k] in
private theorem domainTarget_comp_centerIsoOver_inv (E : SkewExchangeMatrix ι) :
    (centerMap E).domainTarget (X := Centers) (Y := Centers) ≫ (centerOver E).inv =
      (centerMap E).domainSource (X := Centers) (Y := Centers) := by
  have h : (centerMap E).domainTarget (X := Centers) (Y := Centers) =
      (centerMap E).domainSource (X := Centers) (Y := Centers) ≫ (centerOver E).hom := by
    apply Over.OverMorphism.ext
    simp only [domainTarget_left, domainSource_left, Over.comp_left,
      Quiver.Path.centerIsoOver_hom_left, Hom.toPartialMap_hom, Scheme.topIso_hom]
    rfl
  rw [h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The signed inversion step has a geometric realization on the entire center torus.
The opposite family reads a center at the inverse character in the original family.
The construction keeps the underlying surface, including any specified nodal contraction. -/
def invert (E : SkewExchangeMatrix ι) (P : Point Centers → MarkedSurface k n B XTor) :
    GeometricRealization (T₀ := Centers) (T₁ := Centers) P
      (fun c ↦ (P (c ≫ (centerOver E).inv)).invert)
      (centerMap E) ((invertStep E).xRationalMap k) where
  picard := .refl B
  boundaryAction := .sr 0
  fiber c := by
    simpa only [Category.assoc, domainTarget_comp_centerIsoOver_inv] using
      FiberRealization.invert
        (P (c ≫ (centerMap E).domainSource (X := Centers) (Y := Centers))) E

@[simp]
theorem invert_picard (E : SkewExchangeMatrix ι) (P : Point Centers → MarkedSurface k n B XTor) :
    (invert E P).picard = .refl B := (rfl)

@[simp]
theorem invert_boundaryAction (E : SkewExchangeMatrix ι)
    (P : Point Centers → MarkedSurface k n B XTor) :
    (invert E P).boundaryAction = .sr 0 := (rfl)

end GeometricRealization

end QPainleve.SignedClusterModularGroup
