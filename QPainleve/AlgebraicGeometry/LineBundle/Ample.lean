/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Ample
public import TauCeti.AlgebraicGeometry.LineBundle.Power
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import QPainleve.AlgebraicGeometry.LineBundle.GlobalGeneration
import QPainleve.AlgebraicGeometry.LineBundle.Pullback
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections.Affine
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections.TwistingSheaf
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Pullback

/-!
# Realizing ample powers as projective twists

An ample line bundle on a scheme proper over an affine base has a positive power which
pulls back from the tautological line bundle on projective space along a finite morphism.
Choose the sections of the power to have affine nonvanishing opens. The resulting
projective morphism is affine on the standard cover, and properness then makes it finite.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.SymmetricAlgebra

universe u

namespace TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} {R : Type u} [CommRing R]

/-- Pullback by an affine morphism preserves ampleness. -/
theorem pullback_of_isAffineHom {Y : Scheme.{u}} {a : LineBundleClass Y}
    (ha : a.IsAmple) (g : X ⟶ Y) [IsAffineHom g] :
    (LineBundleClass.pullback g a).IsAmple := by
  have := ha.compactSpace
  refine ⟨QuasiCompact.compactSpace_of_compactSpace g, fun x ↦ ?_⟩
  obtain ⟨n, hn, L, hL, s, hx, hU⟩ := ha.exists_isAffineOpen_nonvanishingLocus (g x)
  let P := (InvertibleSheaf.pullback g).obj L
  have hP : LineBundleClass.mk P = (LineBundleClass.pullback g a) ^ n := by
    rw [← LineBundleClass.pullback_pow, ← hL, LineBundleClass.pullback_mk]
  let A := (Scheme.Modules.pullback g).obj L.obj
  have htop : (⊤ : X.Opens) ≤ g ⁻¹ᵁ (⊤ : Y.Opens) := by simp
  let t : Γ(A, ⊤) := g.pullbackSectionsLE L.obj ⊤ ⊤ htop s
  have ht : A.nonvanishingLocus t = g ⁻¹ᵁ L.obj.nonvanishingLocus s := by
    dsimp only [t, A]
    rw [g.pullbackSectionsLE_apply, Scheme.Modules.nonvanishingLocus_map,
      Scheme.Modules.nonvanishingLocus_pullbackSections, top_inf_eq]
  let e : A ≅ P.obj := eqToIso (InvertibleSheaf.pullback_obj_obj g L).symm
  refine ⟨n, hn, P, hP, e.hom.app ⊤ t, ?_, ?_⟩
  · rw [Scheme.Modules.nonvanishingLocus_hom_app, ht]
    exact hx
  · rw [Scheme.Modules.nonvanishingLocus_hom_app, ht]
    exact hU.preimage g

/-- Some positive power of an ample line bundle on a scheme proper over an affine base is
the pullback of 𝒪(1) along a finite morphism to projective space over the base. -/
theorem exists_finite_to_proj_tensorPow {L : InvertibleSheaf X}
    (hL : (LineBundleClass.mk L).IsAmple) (f : X ⟶ Spec (.of R)) [IsProper f] :
    ∃ (d : ℕ) (_ : 0 < d) (ι : Type u) (_ : Finite ι)
      (g : X ⟶ Proj (homogeneousSubmodule R (ι →₀ R))),
      IsFinite g ∧ g ≫ projToSpec R (ι →₀ R) = f ∧
      Nonempty ((L.tensorPow d).obj ≅ (Scheme.Modules.pullback g).obj
        (Proj.twistingSheaf (homogeneousSubmodule R (ι →₀ R)) 1)) := by
  classical
  obtain ⟨d, hd, S, hS, hCover⟩ := hL.exists_finset_isAffineOpen_nonvanishingLocus_tensorPow
  let M := (L.tensorPow d).obj
  choose hAffine s hs using fun i : S ↦ hCover i i.property
  have hs' (i : S) : M.nonvanishingLocus (s i) = i := hs i
  have h : (⨆ i : S, M.nonvanishingLocus (s i)) = ⊤ := by
    simp_rw [hs']
    exact (sSup_eq_iSup' (S : Set X.Opens)).symm.trans hS
  let p := M.toProjectiveSpace f s h
  let φ := MvPolynomial.symmetricPresentation R (S : Type u)
  have hφ := MvPolynomial.symmetricPresentation_surjective R (S : Type u)
  let hIrrel := HomogeneousIdeal.irrelevant_le_map_of_surjective _ hφ
  let j := Proj.map φ hIrrel
  have hj : j ≫ projToSpec R (S →₀ R) =
      Proj.toSpecCoeff (MvPolynomial.homogeneousSubmodule (S : Type u) R) := by
    rw [projToSpec_def, ← Proj.toSpecCoeff_def]
    apply Proj.map_toSpecCoeff
    intro r
    apply Subtype.ext
    exact MvPolynomial.symmetricPresentation_algebraMap R _ r
  let g := p ≫ j
  have hg : g ≫ projToSpec R (S →₀ R) = f := by
    rw [Category.assoc, hj]
    exact M.toProjectiveSpace_toSpecCoeff f s h
  have : IsAffineHom p :=
    (M.isAffineHom_toProjectiveSpace_iff f s h).mpr (fun i ↦ (hs' i).symm ▸ hAffine i)
  have : IsClosedImmersion j := Proj.isClosedImmersion_map φ hIrrel hφ
  have : IsAffineHom g := inferInstanceAs (IsAffineHom (p ≫ j))
  have : IsProper (g ≫ projToSpec R (S →₀ R)) := hg.symm ▸ ‹IsProper f›
  have hfinite : IsFinite g := IsFinite.iff_isProper_and_isAffineHom.mpr
    ⟨IsProper.of_comp g (projToSpec R (S →₀ R)), inferInstance⟩
  obtain ⟨e, _⟩ := M.exists_iso_pullbackTwistingSheaf_toProjectiveSpace f s h
  let b : Module.Basis S R (S →₀ R) := Finsupp.basisSingleOne
  let e' := Proj.pullbackTwistingSheafIso φ hIrrel (SymmetricAlgebra.ι R (S →₀ R) ∘ b)
    (fun _ ↦ ι_mem_homogeneousSubmodule R (S →₀ R) _) (iSup_basicOpen_ι_eq_top R _ b b.span_eq) 1
  exact ⟨d, hd, S, inferInstance, g, hfinite, hg, ⟨e.symm ≪≫
    (Scheme.Modules.pullback p).mapIso e'.symm ≪≫ (Scheme.Modules.pullbackComp p j).app _⟩⟩

end TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple
