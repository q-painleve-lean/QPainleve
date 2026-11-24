/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Ruling.FiberDegree
public import QPainleve.AlgebraicGeometry.RelativeProj.SplitBundle

import QPainleve.AlgebraicGeometry.RelativeProj.Ruling.Isomorphism

/-!
# Split projective bundles from rational rulings

A flat projective-line ruling on a smooth projective rational surface is a
split projective bundle over the projective line. The comparison is over the
given ruling and supplies the split bundle used in the Hirzebruch description.
See [Vakil, *Complex Algebraic Surfaces*, Class 17, §2][Vakil].

[Vakil]: https://math.stanford.edu/~vakil/02-245/sclass17A.pdf#page=4
-/

public section

open CategoryTheory
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}

local notation "S" => Spec (CommRingCat.of k)
local notation "P" => projectiveLine k
local notation "L[" a "]" => Functor.obj (InvertibleSheaf.toFixedRankOne P)
  (Proj.symmetricAlgebraTwistingBundle k (Fin 2 → k) a)

/-- A flat ruling with projective-line closed fibers on a smooth projective rational
surface is isomorphic over the given base to the projectivization of a sum of two
twisting bundles on the projective line. -/
theorem exists_iso_split_relativeProj_of_projectiveLine_fibers
    [X.Over S] [X.IsProjectiveOver k] [SmoothOfRelativeDimension 2 (X ↘ S)]
    [IsRationalOver (X ↘ S)] (f : X ⟶ P) [f.IsOver S] [Flat f]
    (h : ∀ y : P, IsClosed ({y} : Set P) →
      ∃ e : P ≅ f.fiber y, e.hom ≫ f.fiberι y ≫ X ↘ S = P ↘ S) :
    ∃ (a b : ℤ), b ≤ a ∧
      let V := FiniteLocallyFreeSheaf.FixedRank.biprod L[a] L[b]
      let F := (FiniteLocallyFreeSheaf.toQuasicoherent P).obj V.obj
      let A := ((gradedSymmetricAlgebra P).obj F).obj
      ∃ e : X ≅ A.relativeProj, e.hom ≫ A.relativeProjToBase = f := by
  obtain ⟨L, hL⟩ := f.exists_line_bundle_of_projectiveLine_fibers h
  obtain ⟨V, _, e, he, _⟩ := f.exists_iso_relativeProj_of_ruling L hL
  obtain ⟨a, b, hab, s, hs⟩ := projectiveLine.exists_relativeProj_iso_biprod_twistingSheaf V
  exact ⟨a, b, hab, e ≪≫ s, by simpa only [Iso.trans_hom, Category.assoc, hs] using he⟩

end AlgebraicGeometry.Scheme.Hom
