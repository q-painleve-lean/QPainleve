/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Center
public import QPainleve.Algebra.Cluster.Word.Chart
public import QPainleve.SignedClusterModularGroup.Realization.Basic

/-!
# Geometric realization of label permutations

A permutation relabels the center and evaluation coordinates of a marked family.
The pair at the transported center is the original pair, with the same marking and
numbering of the boundary branches. In particular the realization applies to a
family with specified nodal contractions.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry TauCeti.LaurentRing
open QPainleve.CharacterTorus QPainleve.Cluster
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.PartialMap

universe u

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

variable {k : Type u} [Field k] [IsSepClosed k] [Infinite k]
  {ι : Type u} {n : ℕ} [NeZero n]
  {L : Type u} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}

local notation "A" => (ι → ℤ)
local notation "Centers" => Over.mk (structureMap k A)
local notation "XTor" => scheme k (ι →₀ ℤ)
local notation "renameX" σ:arg =>
  Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (rename (R := k) σ)))
local notation "permuteWord" E:arg σ:arg =>
  Quiver.Hom.toPath (Generator.toStep (Generator.permute σ) E)
local notation "centerOver" E:arg σ:arg => Quiver.Path.centerIsoOver k (permuteWord E σ)
local notation "centerMap" E:arg σ:arg => Scheme.Hom.toPartialMap
  (CategoryTheory.Iso.hom (Quiver.Path.centerIso k (permuteWord E σ)))

attribute [local instance] nonempty_centerTorus smooth_centerTorus

variable [Fintype ι] [DecidableEq ι]

local instance (E : SkewExchangeMatrix ι) (σ : Equiv.Perm ι) :
    (centerMap E σ).IsOver (Over.mk (structureMap k A)).hom (Over.mk (structureMap k A)).hom :=
  Hom.isOver_toPartialMap ((permuteWord E σ).centerIso_hom_structureMap k)

/-- Relabel a marked family over the entire center torus. At each target center,
the family uses the original pair at the inverse-permuted center and renames its
independent X coordinates by the same permutation. -/
def permute (E : SkewExchangeMatrix ι) (σ : Equiv.Perm ι)
    (P : Point Centers → MarkedSurface k n B XTor) :
    GeometricRealization (T₀ := Centers) (T₁ := Centers) P
      (fun c ↦ (P (c ≫ (centerOver E σ).inv)).compEvaluation (renameX σ))
      (centerMap E σ) ((permuteWord E σ).xRationalMap k) where
  picard := .refl B
  boundaryAction := 1
  fiber c := by
    have h := domainTarget_toPartialMap (centerOver E σ).hom
      ((permuteWord E σ).centerIsoOver_hom_left k)
    simpa only [Category.assoc, h, Iso.hom_inv_id, Category.comp_id,
      Quiver.Path.xRationalMap_permute] using
      FiberRealization.compEvaluation
        (P (c ≫ (centerMap E σ).domainSource (X := Centers) (Y := Centers))) (renameX σ)

@[simp]
theorem permute_picard (E : SkewExchangeMatrix ι) (σ : Equiv.Perm ι)
    (P : Point Centers → MarkedSurface k n B XTor) :
    (permute E σ P).picard = .refl B := (rfl)

@[simp]
theorem permute_boundaryAction (E : SkewExchangeMatrix ι) (σ : Equiv.Perm ι)
    (P : Point Centers → MarkedSurface k n B XTor) :
    (permute E σ P).boundaryAction = 1 := (rfl)

end QPainleve.SignedClusterModularGroup.GeometricRealization
