/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Ruling.ProjectiveBundle
public import QPainleve.Geometry.Toric.Fan.Ruling.Hirzebruch.SplitBundle
public import TauCeti.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Basic

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.MinimalModel
import QPainleve.Geometry.Toric.Fan.Hirzebruch.Minimal

/-!
# Hirzebruch models of rational ruled surfaces

A flat projective-line ruling on a smooth projective rational complex surface
is the character ruling of a complete regular Hirzebruch fan. The resulting
classification of minimal rational surfaces follows
[Vakil, *Complex Algebraic Surfaces*, Class 17, §2][Vakil].

[Vakil]: https://math.stanford.edu/~vakil/02-245/sclass17A.pdf#page=3
-/

public section

open CategoryTheory Module TauCeti.AlgebraicGeometry TauCeti.Toric

namespace AlgebraicGeometry.Scheme

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {X : Scheme}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "P" => projectiveLine ℂ

/-- A flat ruling with projective-line closed fibers on a smooth projective rational
complex surface is isomorphic over the given base to a Hirzebruch character ruling.
The fan can be taken in any prescribed rank-two lattice basis. -/
theorem Hom.exists_hirzebruch_model_of_projectiveLine_fibers
    [X.Over S] [X.IsProjectiveOver ℂ] [SmoothOfRelativeDimension 2 (X ↘ S)]
    [IsRationalOver (X ↘ S)] (f : X ⟶ P) [f.IsOver S] [Flat f]
    (b : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)
    (hf : ∀ y : P, IsClosed ({y} : Set P) →
      ∃ e : P ≅ f.fiber y, e.hom ≫ f.fiberι y ≫ X ↘ S = P ↘ S) :
    ∃ (Φ : Fan i) (_ : Φ.IsRegular) (_ : Φ.IsComplete) (n : ℕ) (r : Fin 4 ≃ Φ.Ray)
      (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (n : ℤ) • b 0 - b 1])
      (g : Φ.algebraicRealization ≅ X),
      g.hom ≫ f = Φ.characterRuling (b.coord 1).toAddMonoidHom
        (Fan.nonneg_or_nonpos_hirzebruch_ruling_character b (n : ℤ) r hr) := by
  obtain ⟨a, a', -, e, he⟩ := f.exists_iso_split_relativeProj_of_projectiveLine_fibers hf
  obtain ⟨Φ, hΦ, hc, r, hr, g, hg, -⟩ :=
    Fan.exists_hirzebruch_model_of_split_twisting b hi a a'
  refine ⟨Φ, hΦ, hc, (a' - a).natAbs, r, hr, g ≪≫ e.symm, ?_⟩
  rwa [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← he, Iso.inv_hom_id_assoc]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A smooth projective rational complex surface without exceptional curves of the
first kind is isomorphic over `ℂ` to the projective plane or to a Hirzebruch surface
of index zero or at least two. The Hirzebruch model is realized by its complete
regular fan in the prescribed rank-two lattice basis. -/
theorem exists_iso_projectivePlane_or_hirzebruch (X : Scheme) [X.Over S]
    [X.IsProjectiveOver ℂ] [SmoothOfRelativeDimension 2 (X ↘ S)] [IsRationalOver (X ↘ S)]
    (b : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)
    (hmin : ∀ E : X.IdealSheafData, ¬ E.IsExceptionalCurveOfFirstKind) :
    let A := MvPolynomial.homogeneousSubmodule (ULift (Fin 3)) ℂ
    (∃ e : X ≅ Proj A, e.hom ≫ Proj.toSpecCoeff A = X ↘ S) ∨
      ∃ (Φ : Fan i) (_ : Φ.IsRegular) (_ : Φ.IsComplete) (n : ℕ) (r : Fin 4 ≃ Φ.Ray)
        (e : Φ.algebraicRealization ≅ X),
        n ≠ 1 ∧
        (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (n : ℤ) • b 0 - b 1] ∧
        e.hom ≫ X ↘ S = Φ.algebraicRealizationStructureMap := by
  rcases X.exists_iso_projectivePlane_or_ruling ℂ hmin with
    hplane | ⟨f, hf, -, hfFlat, -, hclosed⟩
  · exact Or.inl hplane
  have hfibers (y : P) (hy : IsClosed ({y} : Set P)) :
      ∃ e : P ≅ f.fiber y, e.hom ≫ f.fiberι y ≫ X ↘ S = P ↘ S := by
    obtain ⟨e, he⟩ := hclosed y hy
    exact ⟨e.symm, by rw [Iso.symm_hom, ← he, Iso.inv_hom_id_assoc]⟩
  obtain ⟨Φ, hΦ, hc, n, r, hr, e, he⟩ :=
    f.exists_hirzebruch_model_of_projectiveLine_fibers b hi hfibers
  refine Or.inr ⟨Φ, hΦ, hc, n, r, e, ?_, hr, ?_⟩
  · intro hn
    let J := Φ.rayBoundaryIdeal hΦ (r 0)
    have hJ : J.IsExceptionalCurveOfFirstKind :=
      (Φ.isExceptionalCurveOfFirstKind_iff_of_hirzebruch b n hΦ hc r hr J).2 ⟨hn, rfl⟩
    exact hmin (J.comap e.inv) (hJ.comap_of_isIso e.inv)
  · rw [← comp_over f S, ← Category.assoc, he, comp_over, Fan.algebraicRealization_over]

end AlgebraicGeometry.Scheme
