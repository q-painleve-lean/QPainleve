/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RelativeProj.Ruling.Basic

import QPainleve.AlgebraicGeometry.RelativeProj.Degree

/-!
# Projective bundle isomorphism of a ruling

For a flat projective-line ruling over the projective line, the evaluation of a
line bundle of fiber degree one gives a polarized isomorphism with the
projectivization of its rank-two direct image. This is the projective bundle
construction in [Vakil, *Complex Algebraic Surfaces*, Class 17, §2][Vakil].

[Vakil]: https://math.stanford.edu/~vakil/02-245/sclass17A.pdf#page=4
-/

public section

open CategoryTheory
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
  (f : X ⟶ projectiveLine k) [f.IsOver (Spec (.of k))] [Flat f]

local notation "S" => Spec (CommRingCat.of k)
local notation "P" => projectiveLine k

/-- A line bundle of degree one on the closed fibers of a flat projective-line ruling
over the projective line identifies the ruling with the projectivization of its direct
image. The isomorphism is over the base and pulls the degree-one twist back to the
original line bundle. -/
theorem exists_iso_relativeProj_of_ruling (L : InvertibleSheaf X)
    (h : ∀ y : P, IsClosed ({y} : Set P) → ∃ e : P ≅ f.fiber y,
      e.hom ≫ f.fiberι y ≫ X ↘ S = P ↘ S ∧
        LineBundleClass.intersectionNumber k (e.hom ≫ f.fiberι y) (LineBundleClass.mk L) = 1) :
    ∃ (V : FiniteLocallyFreeSheaf.FixedRank P 2),
      V.obj.obj = (Modules.pushforward f).obj L.obj ∧
      let F := (FiniteLocallyFreeSheaf.toQuasicoherent P).obj V.obj
      let A := ((gradedSymmetricAlgebra P).obj F).obj
      ∃ e : X ≅ A.relativeProj, e.hom ≫ A.relativeProjToBase = f ∧
        Nonempty ((Modules.pullback e.hom).obj (A.relativeProjTwistingSheaf 1) ≅ L.obj) := by
  obtain ⟨V, hV, g, hg, _, _, q, _, _, hq⟩ := f.exists_relativeProjHom_of_ruling L h
  let F := (FiniteLocallyFreeSheaf.toQuasicoherent P).obj V.obj
  let A := ((gradedSymmetricAlgebra P).obj F).obj
  let E := (InvertibleSheaf.toFixedRankOne X).obj L
  let O : InvertibleSheaf A.relativeProj := ⟨A.relativeProjTwistingSheaf 1, inferInstance⟩
  have hE : E.obj.obj = L.obj := by
    dsimp only [E]
    rw [InvertibleSheaf.toFixedRankOne_obj_obj, ObjectProperty.ιOfLE_obj_obj]
  have hpol : (Modules.pullback g).obj O.obj ≅ L.obj := by
    rw [hq]
    exact E.relativeProjHomOfQuotientPullbackTwistingSheafOneIso f q ≪≫ eqToIso hE
  have hclass : LineBundleClass.pullback g (LineBundleClass.mk O) = LineBundleClass.mk L := by
    rw [LineBundleClass.pullback_mk, LineBundleClass.mk_eq_mk_iff]
    exact ⟨hpol⟩
  have : IsProper (f ≫ P ↘ S) := by
    rw [comp_over f S]
    infer_instance
  have : IsProper f := IsProper.of_comp f (P ↘ S)
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace (P ↘ S)
  have : IsIso g := V.isIso_of_projectiveLine_fibers_of_pullback_twistingSheaf g hg _ hclass h
  exact ⟨V, hV, asIso g, hg, ⟨hpol⟩⟩

end AlgebraicGeometry.Scheme.Hom
