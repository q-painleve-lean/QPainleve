/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RelativeProj.ProjectiveBundle
public import TauCeti.AlgebraicGeometry.RelativeProj.ClosedImmersion
public import TauCeti.AlgebraicGeometry.RelativeProj.TwistingSheaf.Pullback
public import TauCeti.AlgebraicGeometry.RelativeProj.TwistingSheaf.Pushforward

import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic
import TauCeti.AlgebraicGeometry.Modules.Pushforward.Basic
import TauCeti.AlgebraicGeometry.Modules.Sheaf
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Basic

/-!
# Relative projectivization of a line bundle

The projectivization of an invertible sheaf is its base scheme, and its
degree-one twisting sheaf corresponds to the original invertible sheaf.
An epimorphism onto a line bundle therefore induces a closed section of the
source projective bundle, with tautological twist given by the quotient.

We use the quotient convention of [Stacks, Section 27.21][stacks-01OA].
The comparison uses the affine polynomial charts of projective bundles and
the native map `CommMon.relativeProjToTwistingSheaf`.

[stacks-01OA]: https://stacks.math.columbia.edu/tag/01OA
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.FixedRank

attribute [local instance] MvPolynomial.gradedAlgebra

open GradedQuasicoherentAlgebra CategoryTheory.CommMon

variable {X : Scheme.{u}} (E : FixedRank X 1) {F : QuasicoherentSheaf X}

local notation "ℒ[" E "]" =>
  Functor.obj (FiniteLocallyFreeSheaf.toQuasicoherent X) (ObjectProperty.FullSubcategory.obj E)
local notation "𝒜[" F "]" =>
  ObjectProperty.FullSubcategory.obj (Functor.obj (gradedSymmetricAlgebra X) F)
local notation "φ[" q "]" =>
  InducedCategory.Hom.hom (CategoryTheory.Functor.map (gradedSymmetricAlgebra X) q)

/-- The structure morphism of the projectivization of a rank-one vector bundle is an
isomorphism. -/
instance isIso_relativeProjToBase_rankOne : IsIso 𝒜[ℒ[E]].relativeProjToBase := by
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms Scheme) ?_
  intro x
  obtain ⟨U, hx, _, j, hj, _⟩ := exists_relativeProjPolynomialChart E (W := ⊤) (x := x) trivial
  let h := isPullback_morphismRestrict 𝒜[ℒ[E]].relativeProjToBase U.toOpens
  let e := hj.isoIsPullback _ _ h
  refine ⟨U.toOpens, hx, ?_⟩
  rw [MorphismProperty.isomorphisms.iff]
  have : IsIso (e.hom ≫ (𝒜[ℒ[E]].relativeProjToBase ∣_ U.toOpens)) := by
    rw [hj.isoIsPullback_hom_fst _ _ h]
    infer_instance
  exact IsIso.of_isIso_comp_left e.hom _

section Twist

open Proj

variable (U : X.AffineZariskiSite)

local notation "𝒢[" U "]" =>
  gradedSectionsGrading 𝒜[ℒ[E]] (Scheme.AffineZariskiSite.toOpens U)

private theorem basicOpen_eq_top_of_rankOne_generator (s : Γ(𝒜[ℒ[E]].X 1, U.toOpens))
    (hs : Function.Surjective fun c : Γ(X, U.toOpens) ↦ c • s) :
    basicOpen 𝒢[U] (DirectSum.of _ 1 s) = ⊤ := by
  refine top_unique ?_
  rw [← iSup_basicOpen_eq_top_of_adjoin_eq_top 𝒢[U]
    (isGeneratedInDegreeOne_iff.mp (isGeneratedInDegreeOne_gradedSymmetricAlgebra ℒ[E])
      U.toOpens U.property)]
  refine iSup_le fun a ↦ ?_
  obtain ⟨t, ht⟩ := DirectSum.mem_summand.mp a.property
  obtain ⟨c, rfl⟩ := hs t
  apply basicOpen_mono
  refine ⟨algebraMap Γ(X, U.toOpens) _ c, ?_⟩
  rw [_root_.mul_comm, ← Algebra.smul_def, ← ht, ← DirectSum.lof_eq_of Γ(X, U.toOpens), map_smul]
  rfl

private theorem bijective_relativeProjToTwistingSheaf_app
    (b : Module.Basis (ULift.{u} (Fin 1)) Γ(X, U.toOpens) Γ(𝒜[ℒ[E]].X 1, U.toOpens)) :
    Function.Bijective
      ((𝒜[ℒ[E]].relativeProjToTwistingSheaf (rfl : ((1 : ℕ) : ℤ) = 1)).app U.toOpens) := by
  let p := 𝒜[ℒ[E]].relativeProjToBase
  let j : Proj 𝒢[U] ⟶ 𝒜[ℒ[E]].relativeProj := 𝒜[ℒ[E]].relativeProjCover.f U
  let W : (Proj 𝒢[U]).Opens := j ⁻¹ᵁ (p ⁻¹ᵁ U.toOpens)
  let s := b default
  let f := DirectSum.of (fun n ↦ Γ(𝒜[ℒ[E]].X n, U.toOpens)) 1 s
  have hb : Function.Bijective fun c : Γ(X, U.toOpens) ↦ c • s := by
    have he (c : Γ(X, U.toOpens)) : b.equivFun.symm (fun _ ↦ c) = c • s := by
      rw [b.equivFun_symm_apply]
      simp [s]
      rfl
    rw [← funext he]
    exact b.equivFun.symm.bijective.comp (Equiv.funUnique _ _).symm.bijective
  let σ := (𝒜[ℒ[E]].relativeProjToTwistingSheaf (rfl : ((1 : ℕ) : ℤ) = 1)).app U.toOpens
  let τ (t : Γ(𝒜[ℒ[E]].relativeProjTwistingSheaf 1, p ⁻¹ᵁ U.toOpens)) :
      Γ(twistingSheaf 𝒢[U] 1, W) :=
    ((𝒜[ℒ[E]].relativeProjTwistingSheafGlueData 1).π U).app (p ⁻¹ᵁ U.toOpens) t
  have hτ : Function.Bijective τ := (𝒜[ℒ[E]].relativeProjTwistingSheafGlueData 1).bijective_π_app
    (𝒜[ℒ[E]].bijective_relativeProjTwistingSheafGlueData_map_app 1)
    (𝒜[ℒ[E]].relativeProjToBase_preimage U).le
  have hp : IsIso (p.app U.toOpens) :=
    p.isIso_app _ (by rw [Scheme.Hom.opensRange_of_isIso p]; exact le_top)
  have : IsOpenImmersion j := 𝒜[ℒ[E]].isOpenImmersion_relativeProjCover_f U
  have hj : IsIso (j.app (p ⁻¹ᵁ U.toOpens)) :=
    j.isIso_app _ (𝒜[ℒ[E]].relativeProjToBase_preimage U).le
  let e := twistingSheaf.chartSectionsLinearEquiv 1 f (𝒜[ℒ[E]].of_mem_gradedSectionsGrading 1 s) W
    (basicOpen_eq_top_of_rankOne_generator E U s hb.surjective ▸ le_top)
  have he : τ (σ s) = e 1 := by
    refine (π_app_relativeProjToTwistingSheaf_app 𝒜[ℒ[E]] rfl U s).trans ?_
    simp only [e, twistingSheaf.chartSectionsLinearEquiv_apply, one_smul]
    apply twistingSheaf.ext
    intro x
    -- The gluing diagram's chart and the projective spectrum have the same points.
    erw [toTwistingSheaf_apply_apply, twistingSheaf.chartGenerator_apply]
    simp [f]
    rfl
  have h (c : Γ(X, U.toOpens)) :
      τ (σ (c • s)) = e (j.app (p ⁻¹ᵁ U.toOpens) (p.app U.toOpens c)) := by
    have hσ := (𝒜[ℒ[E]].relativeProjToTwistingSheaf (rfl : ((1 : ℕ) : ℤ) = 1)).app_smul c s
    have hτ' := ((𝒜[ℒ[E]].relativeProjTwistingSheafGlueData 1).π U).app_smul
      (p.app U.toOpens c) (σ s)
    refine (congrArg τ (hσ.trans (pushforward_obj_smul p _ c (σ s)))).trans ?_
    refine hτ'.trans ((pushforward_obj_smul j _ _ _).trans ?_)
    let r := j.app (p ⁻¹ᵁ U.toOpens) (p.app U.toOpens c)
    exact (congrArg (fun t ↦ r • t) he).trans
      ((e.map_smul r 1).symm.trans (congrArg e (mul_one r)))
  have hcomp : Function.Bijective (fun c : Γ(X, U.toOpens) ↦ τ (σ (c • s))) := by
    rw [funext h]
    exact e.bijective.comp ((ConcreteCategory.bijective_of_isIso (j.app _)).comp
      (ConcreteCategory.bijective_of_isIso (p.app _)))
  exact (Function.Bijective.of_comp_iff' hτ σ).mp
    ((Function.Bijective.of_comp_iff (τ ∘ σ) hb).mp hcomp)

private def degreeOneIso : 𝒜[ℒ[E]].X 1 ≅ E.obj.obj :=
  eqToIso (degree_obj_obj ((gradedSymmetricAlgebra X).obj ℒ[E]) 1).symm ≪≫
    (ObjectProperty.ι _).mapIso ((gradedSymmetricAlgebraDegreeOneIso X).app ℒ[E])

/-- For a rank-one bundle, the tautological map from the degree-one part of the
symmetric algebra to the direct image of the relative twist is an isomorphism. -/
instance isIso_relativeProjToTwistingSheaf_rankOne :
    IsIso (𝒜[ℒ[E]].relativeProjToTwistingSheaf (rfl : ((1 : ℕ) : ℤ) = 1)) := by
  let I := {U : X.AffineZariskiSite // Nonempty
    (Module.Basis (ULift.{u} (Fin 1)) Γ(X, U.toOpens) Γ(𝒜[ℒ[E]].X 1, U.toOpens))}
  let B (U : I) := U.val.toOpens
  have hB : TopologicalSpace.Opens.IsBasis (Set.range B) := by
    rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
    intro W x hx
    obtain ⟨V, hV, hxV, hVW, ⟨b⟩⟩ := E.exists_isAffineOpen_basis_sections_le hx
    let e := ((Scheme.Modules.sectionsFunctor V).mapIso (degreeOneIso E).symm).toLinearEquiv
    exact ⟨V, ⟨⟨⟨V, hV⟩, ⟨b.map e⟩⟩, rfl⟩, hxV, hVW⟩
  refine Scheme.Modules.Hom.isIso_of_isBasis _ hB fun U ↦ ?_
  obtain ⟨b⟩ := U.property
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    (bijective_relativeProjToTwistingSheaf_app E U.val b)

/-- Transporting the relative twist of degree one of a line bundle to the base
recovers the original line bundle. -/
def relativeProjTwistingSheafOneIso :
    (Scheme.Modules.pullback (inv 𝒜[ℒ[E]].relativeProjToBase)).obj
      (𝒜[ℒ[E]].relativeProjTwistingSheaf 1) ≅ E.obj.obj := by
  let p := 𝒜[ℒ[E]].relativeProjToBase
  exact (Scheme.Hom.pullbackIsoPushforwardInv (inv p)).app _ ≪≫
    (Scheme.Modules.pushforwardCongr (IsIso.inv_inv (f := p))).app _ ≪≫
    (asIso (𝒜[ℒ[E]].relativeProjToTwistingSheaf (rfl : ((1 : ℕ) : ℤ) = 1))).symm ≪≫
    degreeOneIso E

end Twist

private theorem epi_symmetricQuotient_one (q : F ⟶ ℒ[E]) [Epi q.hom] :
    Epi (φ[q].hom.hom 1) := by
  let e := gradedSymmetricAlgebraDegreeOneIso X
  let ι : QuasicoherentSheaf X ⥤ X.Modules := ObjectProperty.ι _
  have h := congrArg (fun f ↦ ι.map f) (e.inv.naturality q)
  simp only [Functor.map_comp, Functor.comp_map, Functor.id_map] at h
  have hi : IsIso (ι.map (e.inv.app ℒ[E])) := Functor.map_isIso ι _
  have hq : Epi (ι.map q ≫ ι.map (e.inv.app ℒ[E])) :=
    epi_comp' ‹Epi q.hom› (@IsIso.epi_of_iso _ _ _ _ _ hi)
  exact epi_hom_hom_of_epi_degree_map ((gradedSymmetricAlgebra X).map q) 1
    (@epi_of_epi_fac _ _ _ _ _ _ _ _ hq h.symm)

private theorem irrelevant_le_map_symmetricQuotient (q : F ⟶ ℒ[E]) [Epi q.hom]
    (U : X.Opens) (hU : IsAffineOpen U) :
    HomogeneousIdeal.irrelevant (𝒜[ℒ[E]].gradedSectionsGrading U) ≤
      (HomogeneousIdeal.irrelevant (𝒜[F].gradedSectionsGrading U)).map
        (gradedSectionsGradedHom φ[q] U) := by
  let := epi_symmetricQuotient_one E q
  exact irrelevant_le_map_of_epi_one φ[q] (isGeneratedInDegreeOne_gradedSymmetricAlgebra _) U hU

/-- A quotient onto a line bundle gives a section of the relative projective spectrum of
the symmetric algebra, in the quotient convention. -/
def relativeProjSectionOfQuotient (q : F ⟶ ℒ[E]) [Epi q.hom] : X ⟶ 𝒜[F].relativeProj :=
  inv 𝒜[ℒ[E]].relativeProjToBase ≫
    relativeProjMap φ[q] (irrelevant_le_map_symmetricQuotient E q)

/-- The morphism defined by a line quotient is a section over the base. -/
@[reassoc (attr := simp)]
theorem relativeProjSectionOfQuotient_toBase (q : F ⟶ ℒ[E]) [Epi q.hom] :
    E.relativeProjSectionOfQuotient q ≫ 𝒜[F].relativeProjToBase = 𝟙 X := by
  simp [relativeProjSectionOfQuotient]

/-- The section defined by a line quotient is a closed immersion. -/
instance isClosedImmersion_relativeProjSectionOfQuotient (q : F ⟶ ℒ[E]) [Epi q.hom] :
    IsClosedImmersion (E.relativeProjSectionOfQuotient q) := by
  let := epi_symmetricQuotient_one E q
  have : IsClosedImmersion (relativeProjMap φ[q] (irrelevant_le_map_symmetricQuotient E q)) :=
    isClosedImmersion_relativeProjMap_of_epi_one φ[q]
      (isGeneratedInDegreeOne_gradedSymmetricAlgebra _)
  rw [relativeProjSectionOfQuotient]
  infer_instance

/-- The section associated to a line quotient pulls the tautological twist back
to the quotient line bundle. -/
def relativeProjSectionOfQuotientPullbackTwistingSheafOneIso
    (q : F ⟶ ℒ[E]) [Epi q.hom] :
    (Scheme.Modules.pullback (E.relativeProjSectionOfQuotient q)).obj
      (𝒜[F].relativeProjTwistingSheaf 1) ≅ E.obj.obj := by
  rw [relativeProjSectionOfQuotient]
  let i := inv 𝒜[ℒ[E]].relativeProjToBase
  let g := relativeProjMap φ[q] (irrelevant_le_map_symmetricQuotient E q)
  exact (Scheme.Modules.pullbackComp i g).symm.app _ ≪≫
    (Scheme.Modules.pullback i).mapIso
      (asIso (relativeProjTwistingSheafMap φ[q] (irrelevant_le_map_symmetricQuotient E q) 1)) ≪≫
    E.relativeProjTwistingSheafOneIso

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.FixedRank
