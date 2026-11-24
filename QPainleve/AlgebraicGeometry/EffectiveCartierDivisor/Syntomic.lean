/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
public import TauCeti.AlgebraicGeometry.Morphisms.Syntomic.Basic
import Mathlib.RingTheory.RingHom.StandardSmooth
import QPainleve.RingTheory.Syntomic.Hypersurface
import TauCeti.AlgebraicGeometry.IdealSheaf.Affine
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.StandardSmooth
import TauCeti.AlgebraicGeometry.Pullback.Carrier
import TauCeti.AlgebraicGeometry.Scheme.SpecOver

/-!
# Cartier divisors in smooth schemes over a field

An effective Cartier divisor in a smooth scheme over a field is syntomic of relative
dimension one less than its ambient scheme.
-/

public section

open CategoryTheory Limits Opposite TauCeti TauCeti.AlgebraicGeometry
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

variable {k : Type u} [Field k] {X : Scheme.{u}} {n : ℕ}
  (s : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension (n + 1) s] {D : X.IdealSheafData}

private theorem exists_standardSmooth_cartier_chart (hD : D.IsEffectiveCartier) (x : X) :
    ∃ (U : X.affineOpens) (_ : x ∈ U.val) (f : Γ(X, U)),
      f ∈ Γ(X, U)⁰ ∧ D.ideal U = Ideal.span {f} ∧
        let := s.sectionsAlgebra U.val
        _root_.Algebra.IsStandardSmoothOfRelativeDimension (n + 1) k Γ(X, U) := by
  obtain ⟨U, hxU, hU⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension_appLE_top s (n + 1) x
  obtain ⟨V, -, hxV, f, hf, hD'⟩ := hD.exists_eq_span_singleton_le U.val hxU
  obtain ⟨r, hr, hxr⟩ := U.property.exists_basicOpen_le ⟨x, hxV⟩ hxU
  let W : X.affineOpens := ⟨X.basicOpen r, U.property.basicOpen r⟩
  let f' := (X.presheaf.map (homOfLE hr).op) f
  have hreg := V.property.isSMulRegular_map hr hf
  refine ⟨W, hxr, f', ?_, D.ideal_eq_span_singleton_of_le hr hD', ?_⟩
  · exact isRegular_iff_mem_nonZeroDivisors.mp (Commute.isRegular_iff (Commute.all _) |>.mpr hreg)
  let := s.sectionsAlgebra U.val
  let := s.sectionsAlgebra W.val
  have hUk : (algebraMap k Γ(X, U)).IsStandardSmoothOfRelativeDimension (n + 1) := by
    rw [s.algebraMap_sections U.val, CommRingCat.hom_comp]
    exact (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n + 1)).right _
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv hU
  have : IsLocalization.Away r Γ(X, W) := U.property.isLocalization_basicOpen r
  apply (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := n + 1)).mp
  have hres := (s.resₐ (X.basicOpen_le r)).comp_algebraMap
  rw [← hres, ← AlgHom.toRingHom_eq_coe, s.resₐ_toRingHom]
  exact (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway
    (n + 1)).right _ r _ hUk

omit [SmoothOfRelativeDimension (n + 1) s] in
private theorem exists_syntomic_chart_of_standardSmooth
    (p : D.subscheme) (U : X.affineOpens) (hp : D.subschemeι p ∈ U.val)
    (f : Γ(X, U)) (hf : f ∈ Γ(X, U)⁰) (heq : D.ideal U = Ideal.span {f})
    (hA : let := s.sectionsAlgebra U.val
      _root_.Algebra.IsStandardSmoothOfRelativeDimension (n + 1) k Γ(X, U)) :
    ∃ (W : Scheme.{u}) (j : W ⟶ D.subscheme), IsOpenImmersion j ∧ p ∈ Set.range j ∧
      SyntomicOfRelativeDimension n (j ≫ D.subschemeι ≫ s) := by
  let A := Γ(X, U)
  let B := A ⧸ Ideal.span {f}
  let := s.sectionsAlgebra U.val
  let π : Spec (.of B) ⟶ Spec A :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
  let i := U.property.fromSpec
  have : IsOpenImmersion i := U.property.isOpenImmersion_fromSpec
  let I := D.comap i
  let j := I.subschemeMap D i (le_map_comap _ _)
  have H : IsPullback I.subschemeι j i D.subschemeι :=
    isPullback_of_isClosedImmersion _ _ _ _ (by simp [j]) (by simp [I])
  have hj : IsOpenImmersion j :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) H inferInstance
  have hp' : p ∈ Set.range j := by
    rw [Scheme.Pullback.range_snd_of_isPullback H, U.property.range_fromSpec]
    exact hp
  have : IsClosedImmersion π := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hker : I.subschemeι.ker = π.ker := by
    dsimp only [I, i, π]
    rw [ker_subschemeι, D.comap_fromSpec_eq_ofIdealTop U.property, heq, Scheme.Hom.ker_Spec_map,
      CommRingCat.hom_ofHom, Ideal.mk_ker]
  let e := IsClosedImmersion.lift I.subschemeι π hker.le
  have : IsIso e := IsClosedImmersion.isIso_lift _ _ hker
  have : Nontrivial B := by
    obtain ⟨z, -⟩ := hp'
    exact (inv e z).nontrivial
  have := hA
  have : Algebra.IsStandardSyntomicOfRelativeDimension n k B :=
    QPainleve.isStandardSyntomicOfRelativeDimension_quotient_span_singleton hf
  refine ⟨_, j, hj, hp', ?_⟩
  rw [← H.w_assoc]
  have hi := s.fromSpec_toSpec U.property
  rw [show i ≫ s = _ from hi]
  apply (MorphismProperty.cancel_left_of_respectsIso (P := @SyntomicOfRelativeDimension n) e _).mp
  rw [IsClosedImmersion.lift_fac_assoc, ← Spec.map_comp]
  exact inferInstanceAs (SyntomicOfRelativeDimension n
    (Spec.map (CommRingCat.ofHom (algebraMap k B))))

variable {s}

/-- An effective Cartier divisor in a smooth scheme over a field is syntomic of
relative dimension one less than that of the ambient scheme. -/
theorem syntomicOfRelativeDimension_subschemeι_comp (hD : D.IsEffectiveCartier) :
    SyntomicOfRelativeDimension n (D.subschemeι ≫ s) := by
  have h (p : D.subscheme) := hD.exists_standardSmooth_cartier_chart (n := n) s (D.subschemeι p)
  choose U hU f hf heq hA using h
  choose W j hOpen hMem hSyn using
    fun p ↦ exists_syntomic_chart_of_standardSmooth s p (U p) (hU p) (f p) (hf p) (heq p) (hA p)
  let (p : D.subscheme) : IsOpenImmersion (j p) := hOpen p
  exact IsZariskiLocalAtSource.of_openCover (P := @SyntomicOfRelativeDimension n)
    (Scheme.Cover.mkOfCovers D.subscheme W j (fun p ↦ ⟨p, hMem p⟩)) hSyn

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
