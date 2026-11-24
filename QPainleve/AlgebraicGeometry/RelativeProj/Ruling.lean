/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RelativeProj.Quotient
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.FiberGeneration
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.Ruling

import TauCeti.AlgebraicGeometry.RelativeProj.Proper

/-!
# The morphism from a ruling to its projective bundle

For a ruling by projective lines, a line bundle of fiber degree one supplies
a rank-two direct image. Evaluation defines a proper morphism over the base
to the relative projective spectrum of its symmetric algebra. The construction
uses the degree-one line bundle in [Vakil, *Complex Algebraic Surfaces*, Class 17, §2][Vakil].

[Vakil]: https://math.stanford.edu/~vakil/02-245/sclass17A.pdf#page=4
-/

public section

open CategoryTheory Limits
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
  (f : X ⟶ projectiveLine k) [f.IsOver (Spec (.of k))] [Flat f]

local notation "S" => Spec (CommRingCat.of k)
local notation "P" => projectiveLine k

/-- The degree-one line bundle on a projective-line ruling defines a proper map over the base
to the projectivization of its rank-two direct image. The line quotient defining the map is
the counit of pullback and pushforward under the direct-image identification. -/
theorem exists_relativeProjHom_of_ruling (L : InvertibleSheaf X)
    (h : ∀ y : P, IsClosed ({y} : Set P) → ∃ e : P ≅ f.fiber y,
      e.hom ≫ f.fiberι y ≫ X ↘ S = P ↘ S ∧
        LineBundleClass.intersectionNumber k (e.hom ≫ f.fiberι y) (LineBundleClass.mk L) = 1) :
    ∃ (V : FiniteLocallyFreeSheaf.FixedRank P 2)
      (hV : V.obj.obj = (Modules.pushforward f).obj L.obj),
      let F := (FiniteLocallyFreeSheaf.toQuasicoherent P).obj V.obj
      let E := (InvertibleSheaf.toFixedRankOne X).obj L
      let A := ((gradedSymmetricAlgebra P).obj F).obj
      ∃ (g : X ⟶ A.relativeProj) (hg : g ≫ A.relativeProjToBase = f),
        IsProper g ∧ IsClosedImmersion
          (pullback.lift (𝟙 X) g ((Category.id_comp f).trans hg.symm)) ∧
        ∃ (q : (QuasicoherentSheaf.pullback f).obj F ⟶
            (FiniteLocallyFreeSheaf.toQuasicoherent X).obj E.obj) (_ : Epi q.hom),
          q.hom = eqToHom (QuasicoherentSheaf.pullback_obj_obj f F) ≫
            (Modules.pullback f).map (eqToHom (show F.obj = _ from hV)) ≫
            (Modules.pullbackPushforwardAdjunction f).counit.app L.obj ≫
            eqToHom (by
              dsimp only [E]
              rw [Functor.id_obj, FiniteLocallyFreeSheaf.toQuasicoherent_obj_obj,
                InvertibleSheaf.toFixedRankOne_obj_obj, ObjectProperty.ιOfLE_obj_obj]) ∧
          g = E.relativeProjHomOfQuotient f q := by
  obtain ⟨V, hV⟩ := f.exists_rankTwo_pushforward_of_projectiveLine_fibers L h
  let F := (FiniteLocallyFreeSheaf.toQuasicoherent P).obj V.obj
  let A := (gradedSymmetricAlgebra P).obj F
  let E := (InvertibleSheaf.toFixedRankOne X).obj L
  have hF : F.obj = (Modules.pushforward f).obj L.obj := hV
  have hE : ((FiniteLocallyFreeSheaf.toQuasicoherent X).obj E.obj).obj = L.obj := by
    rw [FiniteLocallyFreeSheaf.toQuasicoherent_obj_obj, InvertibleSheaf.toFixedRankOne_obj_obj,
      ObjectProperty.ιOfLE_obj_obj]
  have : IsProper (f ≫ P ↘ S) := by
    rw [comp_over f S]
    infer_instance
  have : IsProper f := IsProper.of_comp f (P ↘ S)
  let c := (Modules.pullbackPushforwardAdjunction f).counit.app L.obj
  have : Epi c := f.epi_ruling_evaluation L fun y hy ↦ by
    obtain ⟨e, -, he⟩ := h y hy
    exact ⟨e, he.symm ▸ (by decide : (0 : ℤ) ≤ 1)⟩
  let e₁ := eqToIso (QuasicoherentSheaf.pullback_obj_obj f F)
  let e₂ := (Modules.pullback f).mapIso (eqToIso hF)
  let e₃ := eqToIso hE.symm
  let q : (QuasicoherentSheaf.pullback f).obj F ⟶
      (FiniteLocallyFreeSheaf.toQuasicoherent X).obj E.obj :=
    ObjectProperty.homMk (e₁.hom ≫ e₂.hom ≫ c ≫ e₃.hom)
  have : Epi q.hom := by
    dsimp only [q, ObjectProperty.homMk_hom]
    exact epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ e₁.isIso_hom)
      (epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ e₂.isIso_hom)
        (epi_comp' ‹Epi c› (@IsIso.epi_of_iso _ _ _ _ _ e₃.isIso_hom)))
  let g := E.relativeProjHomOfQuotient f q
  have hg : g ≫ A.obj.relativeProjToBase = f := E.relativeProjHomOfQuotient_toBase f q
  have : IsProper (g ≫ A.obj.relativeProjToBase) := hg ▸ ‹IsProper f›
  exact ⟨V, hV, g, hg, IsProper.of_comp g A.obj.relativeProjToBase,
    E.isClosedImmersion_pullback_lift_relativeProjHomOfQuotient f q, q, inferInstance, rfl, rfl⟩

end AlgebraicGeometry.Scheme.Hom
