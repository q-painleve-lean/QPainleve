/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Ample
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Invertible
public import TauCeti.AlgebraicGeometry.LineBundle.GlobalGeneration.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.Power
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import QPainleve.AlgebraicGeometry.CartierDivisor.ZeroDivisor
import QPainleve.AlgebraicGeometry.LineBundle.GlobalGeneration
import QPainleve.AlgebraicGeometry.LineBundle.Pullback
import QPainleve.AlgebraicGeometry.LineBundle.TensorProduct
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections.Affine
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections.TwistingSheaf
import TauCeti.AlgebraicGeometry.Morphisms.RelativeDimension
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Pullback
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Ample

/-!
# Positive powers of ample line bundles

An ample line bundle on a scheme proper over an affine base has a positive power which
pulls back from the tautological line bundle on projective space along a finite morphism.
Choose the sections of the power to have affine nonvanishing opens. The resulting
projective morphism is affine on the standard cover, and properness then makes it finite.

Conversely, a projective scheme over an affine base has an ample line bundle.

Tensoring an ample line bundle by a globally generated one preserves ampleness
([Stacks Project, Lemma 28.27.5](https://stacks.math.columbia.edu/tag/0890)).

On a positive-dimensional proper integral scheme over a field, some positive power of
an ample class is the class of a nonempty effective Cartier divisor. This uses the
affine nonvanishing locus argument of
[Stacks Project, Lemma 33.44.14](https://stacks.math.columbia.edu/tag/0B5X).
-/

public section

open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.SymmetricAlgebra

universe u

namespace TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} {R : Type u} [CommRing R]

/-- The tensor product of an ample line bundle and a globally generated line bundle is ample. -/
theorem mul_mk_of_isGloballyGenerated {a : LineBundleClass X} (ha : a.IsAmple)
    {L : InvertibleSheaf X} (hL : L.IsGloballyGenerated) : (a * LineBundleClass.mk L).IsAmple := by
  refine ⟨ha.compactSpace, fun x ↦ ?_⟩
  obtain ⟨n, hn, M, hM, s, hx, hV⟩ := ha.exists_isAffineOpen_nonvanishingLocus x
  obtain ⟨t, ht⟩ := InvertibleSheaf.isGloballyGenerated_iff.mp hL x
  let N := L.tensorPow n
  let tₙ := (L.tensorPowObjIso n).inv.app ⊤ (Scheme.Modules.tensorPowSection t n)
  have htₙ : N.obj.nonvanishingLocus tₙ = L.obj.nonvanishingLocus t :=
    (Scheme.Modules.nonvanishingLocus_hom_app (L.tensorPowObjIso n).symm _).trans
      (Scheme.Modules.nonvanishingLocus_tensorPowSection _ hn)
  let V := M.obj.nonvanishingLocus s
  let e := M.tensorProductObjIso N
  let z := e.inv.app ⊤ (Scheme.Modules.tmulRight M.obj tₙ s)
  have hz : (M.tensorProduct N).obj.nonvanishingLocus z = V ⊓ N.obj.nonvanishingLocus tₙ :=
    (Scheme.Modules.nonvanishingLocus_hom_app e.symm _).trans
      (Scheme.Modules.nonvanishingLocus_tmulRight s tₙ)
  refine ⟨n, hn, M.tensorProduct N, by simp [N, hM, mul_pow], z, ?_, ?_⟩
  · rw [hz, htₙ]
    exact ⟨hx, ht⟩
  · rw [hz, ← Scheme.Modules.nonvanishingLocus_map V.leTop]
    exact hV.nonvanishingLocus _

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

/-- On a positive-dimensional proper integral scheme over a field, a positive power of
an ample line-bundle class is represented by a nonempty effective Cartier divisor. -/
theorem exists_effectiveCartier_pow_ne_top {k : Type u} [Field k] {a : LineBundleClass X}
    (ha : a.IsAmple) (f : X ⟶ Spec (.of k)) [IsProper f] [IsIntegral X]
    (hX : 0 < topologicalKrullDim X) :
    ∃ (n : ℕ) (_ : 0 < n) (I : X.IdealSheafData) (hI : I.IsEffectiveCartier),
      I ≠ ⊤ ∧ (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹ = a ^ n := by
  obtain ⟨n, hn, L, hL, s, hx, hAffine⟩ :=
    ha.exists_isAffineOpen_nonvanishingLocus (genericPoint X)
  have hs : s ≠ 0 := by
    intro hz
    simp [hz, Scheme.Modules.nonvanishingLocus_zero] at hx
  let I := L.zeroIdeal s
  let hI := L.isEffectiveCartier_zeroIdeal hs
  refine ⟨n, hn, I, hI, ?_, ?_⟩
  · intro htop
    have hsupport : (L.zeroIdeal s).support = ⊥ :=
      (Scheme.IdealSheafData.support_eq_bot_iff _).mpr htop
    have hU : L.obj.nonvanishingLocus s = ⊤ := by
      apply top_unique
      intro y _
      exact (L.mem_nonvanishingLocus_iff_notMem_support_zeroIdeal s y).mpr (by
        rw [hsupport]
        exact Set.notMem_empty y)
    have : IsAffine (↑(⊤ : X.Opens)) := hU ▸ hAffine
    have : IsAffine X := IsAffine.of_isIso X.topIso.inv
    have : IsFinite f := IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
    exact (not_le_of_gt hX) ((relativeDimensionLE_iff_of_field f).mp
      (inferInstance : RelativeDimensionLE 0 f))
  · let hD := L.isEffective_zeroDivisor hs
    have hEq := (hD.isEffectiveCartier_idealSheaf.toCartierDivisor_eq_iff hI).mpr
      (L.idealSheaf_zeroDivisor hs)
    rw [← hI.toLineBundleClass_toCartierDivisor, ← hEq, hD.toCartierDivisor_idealSheaf,
      L.toLineBundleClass_zeroDivisor hs, hL]

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

namespace AlgebraicGeometry.Scheme

/-- A scheme projective over an affine base has an ample line bundle class. -/
theorem exists_isAmple_of_isProjectiveOver (X : Scheme.{u}) (R : Type u) [CommRing R]
    [X.Over (Spec (.of R))] [X.IsProjectiveOver R] :
    ∃ A : LineBundleClass X, A.IsAmple := by
  obtain ⟨M, _, _, _, i, _, _⟩ := IsProjectiveOver.exists_isClosedImmersion (R := R) (X := X)
  have h := TauCeti.SymmetricAlgebra.isAmple_twistingSheaf R M Nat.one_pos
  exact ⟨_, h.pullback_of_isAffineHom i⟩

end AlgebraicGeometry.Scheme
