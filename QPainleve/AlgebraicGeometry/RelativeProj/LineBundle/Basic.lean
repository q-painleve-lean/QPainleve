/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RelativeProj.Isomorphism
public import QPainleve.AlgebraicGeometry.RelativeProj.ProjectiveBundle
public import QPainleve.AlgebraicGeometry.RelativeProj.Pullback
public import TauCeti.AlgebraicGeometry.RelativeProj.ClosedImmersion
public import TauCeti.AlgebraicGeometry.RelativeProj.TwistingSheaf.Pullback
public import TauCeti.AlgebraicGeometry.RelativeProj.TwistingSheaf.Pushforward

import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import QPainleve.AlgebraicGeometry.Modules.Pullback.DirectImage
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Sections
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
  Functor.obj (FiniteLocallyFreeSheaf.toQuasicoherent _) (ObjectProperty.FullSubcategory.obj E)
local notation "𝒜[" F "]" =>
  ObjectProperty.FullSubcategory.obj (Functor.obj (gradedSymmetricAlgebra _) F)
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
    exact toTwistingSheaf_one_eq_chartGenerator
      ⟨f, 𝒜[ℒ[E]].of_mem_gradedSectionsGrading 1 s⟩ W
      (basicOpen_eq_top_of_rankOne_generator E U s hb.surjective ▸ le_top)
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
  let h := IsIso.inv_hom_id p
  let T := 𝒜[ℒ[E]].relativeProjTwistingSheaf 1
  let := Scheme.Modules.isIso_pushforwardToPullback_app_of_isIso h T
  exact (asIso ((Scheme.Modules.pushforwardToPullback h).app T)).symm ≪≫
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

/-- A line quotient induces a graded symmetric-algebra map defined on all of the
projectivization of the quotient line bundle. -/
theorem irrelevant_le_map_symmetricQuotient (q : F ⟶ ℒ[E]) [Epi q.hom]
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
  let i := inv 𝒜[ℒ[E]].relativeProjToBase
  let g := relativeProjMap φ[q] (irrelevant_le_map_symmetricQuotient E q)
  -- Read the section as the composite used by the pullback comparison.
  change (Scheme.Modules.pullback (i ≫ g)).obj (𝒜[F].relativeProjTwistingSheaf 1) ≅ E.obj.obj
  exact (Scheme.Modules.pullbackComp i g).symm.app _ ≪≫
    (Scheme.Modules.pullback i).mapIso
      (asIso (relativeProjTwistingSheafMap φ[q] (irrelevant_le_map_symmetricQuotient E q) 1)) ≪≫
    E.relativeProjTwistingSheafOneIso

/-- Restricting the direct image of the first twist to the section of a line quotient
amounts to pushing forward the twisting-sheaf comparison along the projective map
of the quotient. The twist of the quotient projectivization is then identified with
the quotient line bundle. -/
theorem pushforwardToPullback_app_relativeProjSectionOfQuotient
    (q : F ⟶ ℒ[E]) [Epi q.hom] :
    let A := 𝒜[ℒ[E]]
    let B := 𝒜[F]
    let f := B.relativeProjToBase
    let hq := E.irrelevant_le_map_symmetricQuotient q
    let g := relativeProjMap φ[q] hq
    let τ := (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
      (relativeProjTwistingSheafMap φ[q] hq 1)
    (Scheme.Modules.pushforwardToPullback (E.relativeProjSectionOfQuotient_toBase q)).app
        (B.relativeProjTwistingSheaf 1) ≫
      (E.relativeProjSectionOfQuotientPullbackTwistingSheafOneIso q).hom =
    (Scheme.Modules.pushforward f).map τ ≫
      (Scheme.Modules.pushforwardComp g f).hom.app (A.relativeProjTwistingSheaf 1) ≫
      (Scheme.Modules.pushforwardCongr (relativeProjMap_relativeProjToBase φ[q] hq)).hom.app
        (A.relativeProjTwistingSheaf 1) ≫
      (asIso (A.relativeProjToTwistingSheaf (rfl : ((1 : ℕ) : ℤ) = 1))).inv ≫
      (eqToIso (degree_obj_obj ((gradedSymmetricAlgebra X).obj ℒ[E]) 1).symm ≪≫
        (ObjectProperty.ι _).mapIso ((gradedSymmetricAlgebraDegreeOneIso X).app ℒ[E])).hom := by
  intro A B f hq g τ
  let p := A.relativeProjToBase
  let T := A.relativeProjTwistingSheaf 1
  let hi := IsIso.inv_hom_id p
  let := Scheme.Modules.isIso_pushforwardToPullback_app_of_isIso hi T
  let P := Scheme.Modules.pushforwardToPullback hi
  let σ := A.relativeProjToTwistingSheaf (rfl : ((1 : ℕ) : ℤ) = 1)
  have hcancel : P.app T ≫ E.relativeProjTwistingSheafOneIso.hom =
      (asIso σ).inv ≫ (degreeOneIso E).hom := by
    simp only [relativeProjTwistingSheafOneIso, Iso.trans_hom, Iso.symm_hom, asIso_inv]
    exact IsIso.hom_inv_id_assoc _ _
  have hs : (inv p ≫ g) ≫ f = 𝟙 X := E.relativeProjSectionOfQuotient_toBase q
  -- Expanding the section and the isomorphism together keeps the pullback types aligned.
  change (Scheme.Modules.pushforwardToPullback hs).app (B.relativeProjTwistingSheaf 1) ≫
    (Scheme.Modules.pullbackComp (inv p) g).inv.app (B.relativeProjTwistingSheaf 1) ≫
    (Scheme.Modules.pullback (inv p)).map (relativeProjTwistingSheafMap φ[q] hq 1) ≫
    E.relativeProjTwistingSheafOneIso.hom = _
  rw [Scheme.Modules.pushforwardToPullback_app_comp_pullbackComp_inv_app_assoc
      (inv p) g (relativeProjMap_relativeProjToBase φ[q] hq) hi _,
    hcancel]
  rfl

/-- The affine projective morphism of the quotient on sections, followed by
the source chart, factors through the relative section of the line quotient. -/
@[reassoc]
theorem projSymmetricAlgebraSectionsIso_hom_comp_relativeProjSectionOfQuotient
    (q : F ⟶ ℒ[E]) [Epi q.hom] (U : X.AffineZariskiSite)
    (hq : let f := ((Scheme.Modules.sectionsFunctor U.toOpens).map q.hom).hom
      HomogeneousIdeal.irrelevant
          (TauCeti.SymmetricAlgebra.homogeneousSubmodule Γ(X, U.toOpens)
            ((Scheme.Modules.sectionsFunctor U.toOpens).obj E.obj.obj)) ≤
        (HomogeneousIdeal.irrelevant
          (TauCeti.SymmetricAlgebra.homogeneousSubmodule Γ(X, U.toOpens)
            ((Scheme.Modules.sectionsFunctor U.toOpens).obj F.obj))).map
              (SymmetricAlgebra.gradedMap Γ(X, U.toOpens) f)) :
    let p := 𝒜[ℒ[E]].relativeProjToBase
    let f := ((Scheme.Modules.sectionsFunctor U.toOpens).map q.hom).hom
    Proj.map (SymmetricAlgebra.gradedMap Γ(X, U.toOpens) f) hq ≫
        (F.projSymmetricAlgebraSectionsIso U).hom ≫ 𝒜[F].relativeProjCover.f U =
      (ℒ[E].projSymmetricAlgebraSectionsIso U).hom ≫ 𝒜[ℒ[E]].relativeProjCover.f U ≫
        p ≫ E.relativeProjSectionOfQuotient q := by
  dsimp only
  let j := (ℒ[E].projSymmetricAlgebraSectionsIso U).hom
  let c := 𝒜[F].relativeProjCover.f U
  let c' := 𝒜[ℒ[E]].relativeProjCover.f U
  let hφ := irrelevant_le_map_symmetricQuotient E q
  let f := relativeProjMap φ[q] hφ
  let g := (relativeProjFunctorMap φ[q] hφ).app U
  have hchart := QuasicoherentSheaf.projSymmetricAlgebraSectionsIso_hom_comp_relativeProjMap
    U q hφ hq
  have hcover : c' ≫ f = g ≫ c := relativeProjCover_f_relativeProjMap φ[q] hφ U
  calc
    _ = (j ≫ g) ≫ c := (Category.assoc ..).symm.trans (congrArg (· ≫ c) hchart.symm)
    _ = j ≫ c' ≫ f := (Category.assoc ..).trans (congrArg (j ≫ ·) hcover.symm)
    _ = _ := by simp only [relativeProjSectionOfQuotient, IsIso.hom_inv_id_assoc, j, c', f]

/-- Taking a quotient section commutes with changing the source bundle by an
isomorphism. -/
@[reassoc]
theorem relativeProjSectionOfQuotient_comp_relativeProjMapIso {G : QuasicoherentSheaf X}
    (e : G ≅ F) (q : F ⟶ ℒ[E]) [Epi q.hom] :
    let : Epi (e.hom ≫ q).hom := by
      let incl : QuasicoherentSheaf X ⥤ SheafOfModules X.ringCatSheaf := ObjectProperty.ι _
      exact epi_comp' (Functor.map_isIso incl e.hom).epi_of_iso ‹Epi q.hom›
    let eAlg : 𝒜[G] ≅ 𝒜[F] :=
      (ObjectProperty.ι _).mapIso ((gradedSymmetricAlgebra X).mapIso e)
    E.relativeProjSectionOfQuotient q ≫ (relativeProjMapIso eAlg).hom =
      E.relativeProjSectionOfQuotient (e.hom ≫ q) := by
  simp only [relativeProjSectionOfQuotient, relativeProjMapIso_hom, Category.assoc]
  congr 1
  simp only [Functor.mapIso_hom, ObjectProperty.ι_map, Functor.map_comp]
  exact (relativeProjMap_comp _ _ _ _ _).symm

section Pullback

variable {Y : Scheme.{u}} (f : X ⟶ Y) (E' : FixedRank Y 1) {F' : QuasicoherentSheaf Y}
  (i : F ≅ (QuasicoherentSheaf.pullback f).obj F')
  (j : ℒ[E] ≅ (QuasicoherentSheaf.pullback f).obj ℒ[E'])

/-- The section of a projectivization associated to a line quotient is carried
to the corresponding section under base change when the quotient maps
commute with the chosen pullback identifications. -/
@[reassoc]
theorem relativeProjSectionOfQuotient_comp_projectionOfPullback
    (q : F ⟶ ℒ[E]) (q' : F' ⟶ ℒ[E']) [Epi q.hom] [Epi q'.hom]
    (h : i.hom ≫ (QuasicoherentSheaf.pullback f).map q' = q ≫ j.hom) :
    E.relativeProjSectionOfQuotient q ≫
        QuasicoherentSheaf.projectivizationProjectionOfPullback f i =
      f ≫ E'.relativeProjSectionOfQuotient q' := by
  let e := QuasicoherentSheaf.projectivizationProjectionOfPullback f j
  have hbase : inv 𝒜[ℒ[E]].relativeProjToBase ≫ e =
      f ≫ inv 𝒜[ℒ[E']].relativeProjToBase := by
    apply (cancel_mono 𝒜[ℒ[E']].relativeProjToBase).mp
    simp only [e, Category.assoc, QuasicoherentSheaf.projectivizationProjectionOfPullback_toBase,
      IsIso.inv_hom_id_assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [relativeProjSectionOfQuotient, relativeProjSectionOfQuotient, Category.assoc,
    QuasicoherentSheaf.projectivizationProjectionOfPullback_naturality f i j q q' h,
    ← Category.assoc, hbase, Category.assoc]

end Pullback

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.FixedRank
