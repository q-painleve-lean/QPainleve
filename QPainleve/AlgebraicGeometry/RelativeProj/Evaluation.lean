/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeProj.TwistingSheaf.Pushforward
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections
public import TauCeti.AlgebraicGeometry.LineBundle.Pullback

import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Sections
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GeneratingSections
import TauCeti.AlgebraicGeometry.Modules.Pushforward.Basic

/-!
# The tautological quotient on relative Proj

The adjoint of the degree-one map to the direct image of the twist is surjective
when degree-one standard opens cover each affine chart. On such an open, the
homogeneous element defining the open gives a basis of the twisting sheaf.
For symmetric algebras this supplies the tautological line quotient of a
projective bundle. See the [Stacks Project, Lemma 27.16.11][stacks-01O4].

[stacks-01O4]: https://stacks.math.columbia.edu/tag/01O4
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits DirectSum Opposite
open TauCeti.AlgebraicGeometry

namespace CategoryTheory.CommMon

universe u

variable {X : Scheme.{u}} (A : CommMon (GradedObject ℕ X.Modules))
  [∀ n, (A.X n).IsQuasicoherent]

local notation "p" => relativeProjToBase A
local notation "L" => relativeProjTwistingSheaf A 1
local notation "σ" => relativeProjToTwistingSheaf A (rfl : ((1 : ℕ) : ℤ) = 1)
local notation "𝒢[" U "]" => gradedSectionsGrading A (Scheme.AffineZariskiSite.toOpens U)
local notation "j[" U "]" => colimit.ι A.relativeProjGluingData.functor U

/-- The degree-one evaluation on the relative projective spectrum, adjoint to the
map sending a homogeneous section to its section of the twisting sheaf. -/
def relativeProjEvaluation : (Scheme.Modules.pullback p).obj (A.X 1) ⟶ L :=
  ((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv _ _).symm σ

/-- The adjoint of the evaluation is the degree-one map to the direct image of the twist. -/
@[simp]
theorem homEquiv_relativeProjEvaluation :
    (Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv _ _ A.relativeProjEvaluation =
      σ :=
  Equiv.apply_symm_apply _ _

/-- Evaluation sends the pullback of a local homogeneous section to its section of the twist,
restricted to the given open. -/
theorem relativeProjEvaluation_app_pullbackSectionsLE (U : X.Opens)
    (W : A.relativeProj.Opens) (hle : W ≤ p ⁻¹ᵁ U) (s : Γ(A.X 1, U)) :
    A.relativeProjEvaluation.app W ((p).pullbackSectionsLE (A.X 1) U W hle s) =
      (L).presheaf.map (homOfLE hle).op ((σ).app U s) := by
  have hU : A.relativeProjEvaluation.app (p ⁻¹ᵁ U) ((p).pullbackSections (A.X 1) U s) =
      (σ).app U s := by
    rw [← Scheme.Modules.pullbackPushforwardAdjunction_homEquiv_app_apply,
      A.homEquiv_relativeProjEvaluation]
  rw [Scheme.Hom.pullbackSectionsLE_apply]
  exact (A.relativeProjEvaluation.mapPresheaf.naturality_apply (homOfLE hle).op
    ((p).pullbackSections (A.X 1) U s)).trans (congrArg _ hU)

private theorem surjective_relativeProjEvaluation_app (U : X.AffineZariskiSite)
    (r : 𝒢[U] 1) :
    Function.Surjective (A.relativeProjEvaluation.app (j[U] ''ᵁ Proj.basicOpen 𝒢[U] r)) := by
  let j : Proj 𝒢[U] ⟶ A.relativeProj := j[U]
  let : IsOpenImmersion j := A.isOpenImmersion_relativeProjCover_f U
  let B := Proj.basicOpen 𝒢[U] r
  let W : A.relativeProj.Opens := j ''ᵁ B
  let W₀ := p ⁻¹ᵁ U.toOpens
  have hW : W ≤ j.opensRange := j.image_le_opensRange B
  have hle : W ≤ W₀ := hW.trans (A.relativeProjToBase_preimage U).symm.le
  have hB : j ⁻¹ᵁ W = B := j.preimage_image_eq B
  let M := Proj.twistingSheaf 𝒢[U] 1
  let π : L ⟶ (Scheme.Modules.pushforward j).obj M := (A.relativeProjTwistingSheafGlueData 1).π U
  have hπ : Function.Bijective (π.app W) :=
    (A.relativeProjTwistingSheafGlueData 1).bijective_π_app
      (A.bijective_relativeProjTwistingSheafGlueData_map_app 1) hW
  obtain ⟨s, hs⟩ := DirectSum.mem_summand.mp r.property
  let v := (p).pullbackSectionsLE (A.X 1) U.toOpens W hle s
  have hv : π.app W (A.relativeProjEvaluation.app W v) =
      Proj.toTwistingSheaf 𝒢[U] rfl (j ⁻¹ᵁ W) r := by
    have h₂ := π.mapPresheaf.naturality_apply (homOfLE hle).op ((σ).app U.toOpens s)
    have h₃ := A.π_app_relativeProjToTwistingSheaf_app rfl U s
    let res := M.presheaf.map (homOfLE (j.preimage_mono hle)).op
    have h₁ := A.relativeProjEvaluation_app_pullbackSectionsLE U.toOpens W hle s
    exact (congrArg (π.app W) h₁).trans (h₂.trans ((congrArg res h₃).trans
      ((Proj.res_toTwistingSheaf rfl _ _).trans (congrArg _ (Subtype.ext hs)))))
  let e := Proj.twistingSheaf.chartSectionsLinearEquiv (𝒜 := 𝒢[U]) 1
    (r : ⨁ n, Γ(A.X n, U.toOpens)) r.property (j ⁻¹ᵁ W) hB.le
  have he : e 1 = Proj.toTwistingSheaf 𝒢[U] rfl (j ⁻¹ᵁ W) r := by
    simpa only [e, Proj.twistingSheaf.chartSectionsLinearEquiv_apply, one_smul] using
      (Proj.toTwistingSheaf_one_eq_chartGenerator r (j ⁻¹ᵁ W) hB.le).symm
  intro t
  obtain ⟨a, ha⟩ := e.surjective (π.app W t)
  let : IsIso (j.app W) := j.isIso_app W hW
  obtain ⟨c, hc⟩ := (ConcreteCategory.bijective_of_isIso (j.app W)).surjective a
  refine ⟨c • v, hπ.injective ?_⟩
  refine (congrArg (π.app W) (A.relativeProjEvaluation.app_smul c v)).trans ?_
  refine (π.app_smul c (A.relativeProjEvaluation.app W v)).trans ?_
  refine (pushforward_obj_smul j M c _).trans ?_
  rw [hv, hc, ← he, ← e.map_smul, smul_eq_mul, mul_one, ha]

/-- The degree-one evaluation is an epimorphism when degree-one standard opens cover
every affine chart of the relative projective spectrum. -/
theorem epi_relativeProjEvaluation_of_iSup_eq_top
    (h : ∀ U : X.Opens, IsAffineOpen U →
      ⨆ f : A.gradedSectionsGrading U 1, Proj.basicOpen (A.gradedSectionsGrading U) f = ⊤) :
    Epi A.relativeProjEvaluation := by
  let I := Σ U : X.AffineZariskiSite, 𝒢[U] 1
  let j (U : X.AffineZariskiSite) : Proj 𝒢[U] ⟶ A.relativeProj := j[U]
  let (U : X.AffineZariskiSite) : IsOpenImmersion (j U) := A.isOpenImmersion_relativeProjCover_f U
  let W (i : I) : A.relativeProj.Opens := j i.1 ''ᵁ Proj.basicOpen 𝒢[i.1] i.2
  have hW (i : I) : IsAffineOpen (W i) :=
    (j i.1).isAffineOpen_iff_of_isOpenImmersion.mpr
      (Proj.isAffineOpen_basicOpen _ _ i.2.property Nat.one_pos)
  have hcover : ⨆ i, W i = ⊤ := by
    rw [iSup_sigma]
    refine (iSup_congr fun U ↦ ?_).trans A.relativeProjCover.iSup_opensRange
    simp only [W]
    exact ((j U).image_iSup _).symm.trans
      ((congrArg _ (h U.toOpens U.property)).trans (j U).image_top_eq_opensRange)
  exact A.relativeProjEvaluation.epi_of_forall_surjective_app hW hcover
    (fun i ↦ A.surjective_relativeProjEvaluation_app i.1 i.2)

/-- On the relative projective spectrum of an algebra generated in degree one,
the pullback of its degree-one part surjects onto the first twisting sheaf. -/
theorem epi_relativeProjEvaluation (h : A.IsGeneratedInDegreeOne) :
    Epi A.relativeProjEvaluation :=
  A.epi_relativeProjEvaluation_of_iSup_eq_top fun U hU ↦
    Proj.iSup_basicOpen_eq_top_of_adjoin_eq_top _ (isGeneratedInDegreeOne_iff.mp h U hU)

end CategoryTheory.CommMon

namespace TauCeti.AlgebraicGeometry.QuasicoherentSheaf

open GradedQuasicoherentAlgebra

universe u

variable {X Y : Scheme.{u}} (F : QuasicoherentSheaf X)

local notation "A" => ObjectProperty.FullSubcategory.obj (Functor.obj (gradedSymmetricAlgebra X) F)
local notation "p" => CommMon.relativeProjToBase A

/-- For a morphism to the projective bundle of `F` over `f`, pull back the tautological
quotient to a map from `f^* F` onto the pullback of the first twisting sheaf. -/
def relativeProjLineQuotient (g : Y ⟶ CommMon.relativeProj A) {f : Y ⟶ X} (h : g ≫ p = f) :
    (Scheme.Modules.pullback f).obj F.obj ⟶
      (Scheme.Modules.pullback g).obj (CommMon.relativeProjTwistingSheaf A 1) :=
  let e := eqToIso (degree_obj_obj ((gradedSymmetricAlgebra X).obj F) 1).symm ≪≫
    (ObjectProperty.ι _).mapIso ((gradedSymmetricAlgebraDegreeOneIso X).app F)
  (Scheme.Modules.pullbackCongr h).inv.app F.obj ≫
    (Scheme.Modules.pullbackComp g p).inv.app F.obj ≫
    (Scheme.Modules.pullback g).map
      ((Scheme.Modules.pullback p).map e.inv ≫ CommMon.relativeProjEvaluation A)

/-- The line quotient is the pullback of the degree-one evaluation, using the
canonical identification of the first symmetric power with the original sheaf. -/
theorem relativeProjLineQuotient_def (g : Y ⟶ CommMon.relativeProj A) {f : Y ⟶ X}
    (h : g ≫ p = f) :
    let e := eqToIso (degree_obj_obj ((gradedSymmetricAlgebra X).obj F) 1).symm ≪≫
      (ObjectProperty.ι _).mapIso ((gradedSymmetricAlgebraDegreeOneIso X).app F)
    F.relativeProjLineQuotient g h =
      (Scheme.Modules.pullbackCongr h).inv.app F.obj ≫
        (Scheme.Modules.pullbackComp g p).inv.app F.obj ≫
        (Scheme.Modules.pullback g).map
          ((Scheme.Modules.pullback p).map e.inv ≫ CommMon.relativeProjEvaluation A) :=
  (rfl)

/-- The tautological quotient remains an epimorphism after pullback along any morphism
to the projective bundle. Its codomain is invertible by `SheafOfModules.isInvertible_pullback`. -/
theorem epi_relativeProjLineQuotient (g : Y ⟶ CommMon.relativeProj A) {f : Y ⟶ X} (h : g ≫ p = f) :
    Epi (F.relativeProjLineQuotient g h) := by
  let e := eqToIso (degree_obj_obj ((gradedSymmetricAlgebra X).obj F) 1).symm ≪≫
    (ObjectProperty.ι _).mapIso ((gradedSymmetricAlgebraDegreeOneIso X).app F)
  have hEval := CommMon.epi_relativeProjEvaluation A
    (isGeneratedInDegreeOne_gradedSymmetricAlgebra F)
  let : (Scheme.Modules.pullback g).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (Scheme.Modules.pullbackPushforwardAdjunction g)
  have hCoeff : Epi ((Scheme.Modules.pullback p).map e.inv) :=
    @IsIso.epi_of_iso _ _ _ _ _ ((Scheme.Modules.pullback p).mapIso e).isIso_inv
  let : Epi ((Scheme.Modules.pullback p).map e.inv ≫ CommMon.relativeProjEvaluation A) :=
    epi_comp' hCoeff hEval
  rw [F.relativeProjLineQuotient_def g h]
  exact epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ ((Scheme.Modules.pullbackCongr h).app _).isIso_inv)
    (epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ ((Scheme.Modules.pullbackComp g p).app _).isIso_inv)
      (Functor.map_epi (Scheme.Modules.pullback g) _))

end TauCeti.AlgebraicGeometry.QuasicoherentSheaf
