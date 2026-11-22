/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Fiber
public import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
public import TauCeti.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import QPainleve.AlgebraicGeometry.Blowup.Exceptional.TwistingSheaf
import QPainleve.AlgebraicGeometry.Blowup.RegularPair
import TauCeti.AlgebraicGeometry.Blowup.BaseChange
import TauCeti.AlgebraicGeometry.Blowup.Pullback
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.Pullback
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Pullback
import TauCeti.AlgebraicGeometry.Scheme.LocalSpectrum

/-!
# Exceptional curves of point blowups

The conormal bundle of the exceptional line is its twisting sheaf `𝒪(1)`.
This identifies the exceptional divisor of a two-dimensional regular point blowup
as a curve of the first kind.

The comparison uses Tau Ceti's `Proj.pullbackTwistingSheafIso` for the graded maps
from the Rees algebra to the homogeneous coordinate ring of the exceptional line.

## References

* [The Stacks Project, Lemma 54.3.1](https://stacks.math.columbia.edu/tag/0AGQ).
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits RingTheory.Sequence
open TauCeti.AlgebraicGeometry

universe u

namespace QPainleve

open AlgebraicGeometry

variable {R : Type u} [CommRing R] {I : Ideal R} {a b : R}

/-- Under the exceptional projective-line comparison for a weakly regular pair, the
exceptional ideal restricts to `𝒪(1)`. -/
def affineBlowupExceptionalPullbackIdealIso
    (hab : IsWeaklyRegular R [a, b]) (hI : Ideal.ofList [a, b] = I) :
    (Scheme.Modules.pullback ((affineBlowupExceptionalIsoProjectiveLine hab hI).inv ≫
      (affineBlowupExceptionalIdeal R I).subschemeι)).obj
      (affineBlowupExceptionalIdeal R I).sheaf ≅
      Proj.twistingSheaf
        (TauCeti.SymmetricAlgebra.homogeneousSubmodule (R ⧸ I) (Fin 2 → R ⧸ I)) 1 :=
  (Scheme.Modules.pullback _).mapIso (affineBlowupExceptionalIdealIsoTwistingSheaf R I) ≪≫
    affineBlowupExceptionalPullbackTwistingSheafIso hab hI 1

end QPainleve

namespace AlgebraicGeometry.Scheme.IdealSheafData

open QPainleve

variable {X : Scheme.{u}}

/-- On the exceptional projective line of a weakly regular pair on an affine open,
the ideal of the scheme blowup's exceptional divisor restricts to `𝒪(1)`. -/
def blowupChartPullbackExceptionalIdealIso (J : X.IdealSheafData)
    {U : X.Opens} (hU : IsAffineOpen U) {a b : Γ(X, U)}
    (hab : IsWeaklyRegular Γ(X, U) [a, b]) (hJ : Ideal.ofList [a, b] = J.ideal ⟨U, hU⟩) :
    let I := J.ideal ⟨U, hU⟩
    let S := Γ(X, U) ⧸ I
    (Scheme.Modules.pullback ((affineBlowupExceptionalIsoProjectiveLine hab hJ).inv ≫
      (affineBlowupExceptionalIdeal Γ(X, U) I).subschemeι ≫ J.blowupChart hU)).obj
      (J.comap J.blowupToBase).sheaf ≅
      Proj.twistingSheaf (TauCeti.SymmetricAlgebra.homogeneousSubmodule S (Fin 2 → S)) 1 := by
  dsimp only
  let E := J.comap J.blowupToBase
  let chart := J.blowupChart hU
  let j := (affineBlowupExceptionalIsoProjectiveLine hab hJ).inv ≫
    (affineBlowupExceptionalIdeal Γ(X, U) (J.ideal ⟨U, hU⟩)).subschemeι
  have hE : E.comap chart = affineBlowupExceptionalIdeal Γ(X, U) (J.ideal ⟨U, hU⟩) := by
    rw [J.comap_blowupChart_comap_blowupToBase hU, affineBlowupExceptionalIdeal_def,
      toSpecCoeff_reesAlgebra]
    rfl
  refine (Scheme.Modules.pullbackCongr (Category.assoc _ _ _).symm).app _ ≪≫
    ((Scheme.Modules.pullbackComp j chart).app E.sheaf).symm ≪≫
    (Scheme.Modules.pullback j).mapIso
      (asIso (E.pullbackSheafHom chart) ≪≫ eqToIso (congrArg sheaf hE)) ≪≫
    affineBlowupExceptionalPullbackIdealIso hab hJ

private theorem ker_residue_on_stalkSpec {X : Scheme.{u}} (p : X) :
    let Y := Spec (X.presheaf.stalk p)
    (Spec.map (X.residue p)).ker.ideal ⟨⊤, isAffineOpen_top Y⟩ =
      RingHom.ker ((X.residue p).hom.comp (Scheme.ΓSpecIso (X.presheaf.stalk p)).hom.hom) := by
  dsimp only
  let q := Spec.map (X.residue p)
  rw [q.ker_apply]
  -- Identify the sections on the inverse image of the top open with global sections.
  change RingHom.ker q.appTop.hom = _
  have h := Scheme.ΓSpecIso_naturality (X.residue p)
  rw [← RingHom.ker_comp_of_injective q.appTop.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (X.residueField p)).hom).injective,
    ← CommRingCat.hom_comp, h, CommRingCat.hom_comp]

private theorem specMap_quotient_stalkSections (p : X)
    {A : Ideal Γ(Spec (X.presheaf.stalk p), ⊤)}
    (ψ : (Γ(Spec (X.presheaf.stalk p), ⊤) ⧸ A) →+* X.residueField p)
    (hψ : ψ.comp (Ideal.Quotient.mk A) =
      (X.residue p).hom.comp (Scheme.ΓSpecIso (X.presheaf.stalk p)).hom.hom) :
    Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk A)) ≫
      (isAffineOpen_top (Spec (X.presheaf.stalk p))).fromSpec = Spec.map (X.residue p) := by
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  have h : CommRingCat.ofHom (Ideal.Quotient.mk A) ≫ CommRingCat.ofHom ψ =
      (Scheme.ΓSpecIso (X.presheaf.stalk p)).hom ≫ X.residue p :=
    CommRingCat.hom_ext hψ
  rw [Category.assoc, h, Iso.inv_hom_id_assoc]

private theorem exists_stalkSpec_blowup_fiber (p : X)
    [IsRegularLocalRing (X.presheaf.stalk p)] (hdim : ringKrullDim (X.presheaf.stalk p) = 2)
    (J : (Spec (X.presheaf.stalk p)).IdealSheafData) (hJ : J = (Spec.map (X.residue p)).ker) :
    let E := J.comap J.blowupToBase
    ∃ j : projectiveLine (X.residueField p) ⟶ J.blowup,
      IsPullback j (projectiveLine (X.residueField p) ↘ Spec (.of (X.residueField p)))
        J.blowupToBase (Spec.map (X.residue p)) ∧
      Nonempty ((Scheme.Modules.pullback j).obj E.sheaf ≅ Proj.twistingSheaf
        (TauCeti.SymmetricAlgebra.homogeneousSubmodule (X.residueField p)
          (Fin 2 → X.residueField p)) 1) := by
  dsimp only
  let R := X.presheaf.stalk p
  let k : Type u := X.residueField p
  let Y := Spec R
  let q := Spec.map (X.residue p)
  let hU := isAffineOpen_top Y
  let T := Γ(Y, ⊤)
  let A := J.ideal ⟨⊤, hU⟩
  let e := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  let φ : T →+* k := (X.residue p).hom.comp e
  have hA : A = RingHom.ker φ := by
    exact (congrArg (fun K : Y.IdealSheafData ↦ K.ideal ⟨⊤, hU⟩) hJ).trans
      (ker_residue_on_stalkSpec p)
  have : IsLocalRing T := e.symm.isLocalRing
  have : IsRegularLocalRing T := IsRegularLocalRing.of_ringEquiv e.symm
  have hφ : Function.Surjective φ := (X.residue_surjective p).comp e.surjective
  have hmax : A = IsLocalRing.maximalIdeal T :=
    hA.trans (IsLocalRing.ker_eq_maximalIdeal φ hφ)
  have hd : ringKrullDim T = 2 := (ringKrullDim_eq_of_ringEquiv e).trans hdim
  obtain ⟨a, b, hspan, hab, _, _⟩ :=
    QPainleve.exists_affineBlowupChartOfSpanPair_cover (A := T) hd
  have habA : Ideal.ofList [a, b] = A := by simpa [hmax, Ideal.span_insert] using hspan
  let S := T ⧸ A
  let ψ : S ≃+* k := (Ideal.quotEquivOfEq hA).trans
    (φ.quotientKerEquivOfSurjective hφ)
  let : Algebra S k := ψ.toRingHom.toAlgebra
  let l := projectiveLine.baseChangeProjection S k
  let j₀ := (affineBlowupExceptionalIsoProjectiveLine hab habA).inv ≫
    (affineBlowupExceptionalIdeal T A).subschemeι ≫ J.blowupChart hU
  have hq := specMap_quotient_stalkSections p ψ.toRingHom (by
    ext x
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe]
    -- The quotient map lifts the residue map through its kernel.
    rfl)
  have hj₀ := J.isPullback_blowupChart_projectiveLine hU hab habA
  have hj := (projectiveLine.isPullback_baseChangeProjection S k).paste_horiz hj₀
  have hj' : IsPullback (l ≫ j₀) (projectiveLine k ↘ Spec (.of k)) J.blowupToBase q := by
    simpa only [hq] using hj
  refine ⟨l ≫ j₀, hj', ⟨?_⟩⟩
  let E := J.comap J.blowupToBase
  have twist : (Scheme.Modules.pullback l).obj
      (Proj.twistingSheaf (TauCeti.SymmetricAlgebra.homogeneousSubmodule S (Fin 2 → S)) 1) ≅
      Proj.twistingSheaf (TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Fin 2 → k)) 1 := by
    dsimp only [l]
    rw [projectiveLine.baseChangeProjection_eq_map]
    exact asIso (Proj.pullbackTwistingSheafMap _ _ 1)
  exact ((Scheme.Modules.pullbackComp l j₀).app E.sheaf).symm ≪≫
    (Scheme.Modules.pullback l).mapIso (J.blowupChartPullbackExceptionalIdealIso hU hab habA) ≪≫
    twist

/-- Over the spectrum of the local ring at a closed regular point of dimension two, the
exceptional projective line maps to the native blowup with its conormal twist. The map lies
over the residue-field point, and the square with the blowup projection is cartesian. -/
private theorem exists_isPullback_pointBlowup (p : X) (hp : IsClosed ({p} : Set X))
    [IsRegularLocalRing (X.presheaf.stalk p)] (hdim : ringKrullDim (X.presheaf.stalk p) = 2) :
    let I := (X.fromSpecResidueField p).ker
    let E := I.comap I.blowupToBase
    ∃ j : projectiveLine (X.residueField p) ⟶ I.blowup,
      IsPullback j (projectiveLine (X.residueField p) ↘ Spec (.of (X.residueField p)))
        I.blowupToBase (X.fromSpecResidueField p) ∧
      Nonempty ((Scheme.Modules.pullback j).obj E.sheaf ≅ Proj.twistingSheaf
        (TauCeti.SymmetricAlgebra.homogeneousSubmodule (X.residueField p)
          (Fin 2 → X.residueField p)) 1) := by
  dsimp only
  let g := X.fromSpecStalk p
  let q := Spec.map (X.residue p)
  let I := (X.fromSpecResidueField p).ker
  let J := I.comap g
  let E := I.comap I.blowupToBase
  let E₀ := J.comap J.blowupToBase
  let m := I.blowupMap g
  have : IsClosedImmersion (X.fromSpecResidueField p) :=
    isClosed_singleton_iff_isClosedImmersion.mp hp
  have hg : Flat g := Flat.of_stalkMap g fun x ↦
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (g.stalkMap x))
  have hcenter : IsPullback q (𝟙 _) g (X.fromSpecResidueField p) :=
    IsPullback.of_vert_isIso_mono ⟨by simp [q, g, Scheme.fromSpecResidueField]⟩
  have hJ : J = q.ker := (ker_eq_comap_of_isPullback _ hcenter).symm
  obtain ⟨j, hj, ⟨twist⟩⟩ := exists_stalkSpec_blowup_fiber p hdim J hJ
  have hs := I.isPullback_blowupMap_of_flat g
  have hm : Flat m := MorphismProperty.IsStableUnderBaseChange.of_isPullback hs hg
  have hE : E.comap m = E₀ := I.comap_comap_blowupMap g
  refine ⟨j ≫ m, hj.paste_horiz hs.flip, ⟨?_⟩⟩
  exact ((Scheme.Modules.pullbackComp j m).app E.sheaf).symm ≪≫
    (Scheme.Modules.pullback j).mapIso
      (asIso (E.pullbackSheafHom m) ≪≫ eqToIso (congrArg sheaf hE)) ≪≫
    twist

/-- The exceptional divisor of the blowup of a closed point with two-dimensional regular
local ring is a projective line over its residue field. The restriction of the exceptional
ideal along this isomorphism is the conormal bundle `𝒪(1)`, and its dual is the normal bundle
`𝒪(-1)`. -/
theorem exists_iso_projectiveLine_pullback_exceptionalIdeal_of_closedPoint
    (p : X) (hp : IsClosed ({p} : Set X)) [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) :
    let I := (X.fromSpecResidueField p).ker
    let E := I.comap I.blowupToBase
    ∃ e : projectiveLine (X.residueField p) ≅ E.subscheme,
      IsPullback (e.hom ≫ E.subschemeι)
        (projectiveLine (X.residueField p) ↘ Spec (.of (X.residueField p)))
        I.blowupToBase (X.fromSpecResidueField p) ∧
      let κ : Type u := X.residueField p
      let 𝒜 := TauCeti.SymmetricAlgebra.homogeneousSubmodule κ (Fin 2 → κ)
      let L := (InvertibleSheaf.pullback (e.hom ≫ E.subschemeι)).obj
        I.isEffectiveCartier_comap_blowupToBase.toInvertibleSheaf
      Nonempty (L.obj ≅ Proj.twistingSheaf 𝒜 1) ∧
        Nonempty (L.dual.obj ≅ Proj.twistingSheaf 𝒜 (-1)) := by
  dsimp only
  let I := (X.fromSpecResidueField p).ker
  let E := I.comap I.blowupToBase
  have : IsClosedImmersion (X.fromSpecResidueField p) :=
    isClosed_singleton_iff_isClosedImmersion.mp hp
  obtain ⟨j, hj, htwist⟩ := exists_isPullback_pointBlowup p hp hdim
  have : IsClosedImmersion j :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hj.flip inferInstance
  have hker : E.subschemeι.ker = j.ker := by
    rw [E.ker_subschemeι, ker_eq_comap_of_isPullback _ hj]
  have := IsClosedImmersion.isIso_lift E.subschemeι j hker
  let e := asIso (IsClosedImmersion.lift E.subschemeι j hker.le)
  have he : e.hom ≫ E.subschemeι = j := IsClosedImmersion.lift_fac _ _ _
  let L := (InvertibleSheaf.pullback (e.hom ≫ E.subschemeι)).obj
    I.isEffectiveCartier_comap_blowupToBase.toInvertibleSheaf
  have hL : Nonempty (L.obj ≅ Proj.twistingSheaf
      (TauCeti.SymmetricAlgebra.homogeneousSubmodule (X.residueField p)
        (Fin 2 → X.residueField p)) 1) := by
    simpa only [L, InvertibleSheaf.pullback_obj_obj, IsEffectiveCartier.toInvertibleSheaf_obj, he]
      using htwist
  refine ⟨e, he.symm ▸ hj, hL, ?_⟩
  have hdeg := (projectiveLine.nonempty_iso_twistingSheaf_iff (X.residueField p) L 1).mp hL
  apply (projectiveLine.nonempty_iso_twistingSheaf_iff (X.residueField p) L.dual (-1)).mpr
  rw [← LineBundleClass.eulerDegree_mk, ← LineBundleClass.inv_mk, projectiveLine.eulerDegree_inv,
    LineBundleClass.eulerDegree_mk, hdeg]

/-- The exceptional divisor in the blowup of a closed point with two-dimensional
regular local ring is an exceptional curve of the first kind. -/
theorem isExceptionalCurveOfFirstKind_comap_blowupToBase_of_closedPoint
    (p : X) (hp : IsClosed ({p} : Set X)) [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) :
    let I := (X.fromSpecResidueField p).ker
    (I.comap I.blowupToBase).IsExceptionalCurveOfFirstKind := by
  let I := (X.fromSpecResidueField p).ker
  obtain ⟨e, -, he, -⟩ :=
    exists_iso_projectiveLine_pullback_exceptionalIdeal_of_closedPoint p hp hdim
  exact ⟨I.isEffectiveCartier_comap_blowupToBase, X.residueField p, inferInstance, e, he⟩

/-- The exceptional divisor over a closed rational point with two-dimensional regular local
ring has self-intersection `-1` over the base field. -/
theorem intersectionNumber_exceptional_of_closedPoint
    (k : Type u) [Field k] [X.Over (Spec (.of k))]
    (p : X) (hp : IsClosed ({p} : Set X)) [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2)
    (hrat : IsIso (X.fromSpecResidueField p ≫ (X ↘ Spec (.of k)))) :
    let I := (X.fromSpecResidueField p).ker
    let E := I.comap I.blowupToBase
    let : E.subscheme.Over (Spec (.of k)) :=
      ⟨E.subschemeι ≫ I.blowupToBase ≫ (X ↘ Spec (.of k))⟩
    LineBundleClass.intersectionNumber k E.subschemeι
      (LineBundleClass.mk I.isEffectiveCartier_comap_blowupToBase.toInvertibleSheaf)⁻¹ = -1 := by
  dsimp only
  let I := (X.fromSpecResidueField p).ker
  let E := I.comap I.blowupToBase
  let κ : Type u := X.residueField p
  let c : Spec (.of κ) ⟶ Spec (.of k) :=
    X.fromSpecResidueField p ≫ (X ↘ Spec (.of k))
  let : Algebra k κ := (Spec.preimage c).hom.toAlgebra
  have hc : Spec.map (CommRingCat.ofHom (algebraMap k κ)) = c := Spec.map_preimage c
  have : IsIso (Spec.map (CommRingCat.ofHom (algebraMap k κ))) := hc.symm ▸ hrat
  let b := projectiveLine.baseChangeProjection k κ
  have hb := projectiveLine.isPullback_baseChangeProjection k κ
  have : IsIso b := hb.isIso_fst_of_isIso
  obtain ⟨e, he, -⟩ := exists_iso_projectiveLine_pullback_exceptionalIdeal_of_closedPoint p hp hdim
  let : E.subscheme.Over (Spec (.of k)) :=
    ⟨E.subschemeι ≫ I.blowupToBase ≫ (X ↘ Spec (.of k))⟩
  let : (projectiveLine κ).Over (Spec (.of k)) := ⟨(projectiveLine κ ↘ Spec (.of κ)) ≫ c⟩
  have : b.IsOver (Spec (.of k)) := ⟨by
    -- Use the specified structure map through the residue field on the source.
    change b ≫ (projectiveLine k ↘ Spec (.of k)) = (projectiveLine κ ↘ Spec (.of κ)) ≫ c
    exact hb.w.trans (congrArg ((projectiveLine κ ↘ Spec (.of κ)) ≫ ·) hc)⟩
  have : e.hom.IsOver (Spec (.of k)) := ⟨by
    -- Use the two structure maps just defined on the exceptional curve and the line.
    change e.hom ≫ E.subschemeι ≫ I.blowupToBase ≫ (X ↘ Spec (.of k)) =
      (projectiveLine κ ↘ Spec (.of κ)) ≫ c
    simpa only [Category.assoc] using congrArg (· ≫ (X ↘ Spec (.of k))) he.w⟩
  have h₀ : Module.finrank k
      (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
        (InvertibleSheaf.trivial E.subscheme).obj 0) = 1 := by
    rw [← Scheme.Hom.finrank_cohomology_trivial_of_isIso e.hom k 0,
      Scheme.Hom.finrank_cohomology_trivial_of_isIso b k 0,
      projectiveLine.finrank_cohomology_zero_trivial]
  have hE := isExceptionalCurveOfFirstKind_comap_blowupToBase_of_closedPoint p hp hdim
  rw [hE.intersectionNumber_self k, h₀]
  rfl

/-- The exceptional divisor of the blowup of any closed point of a smooth surface over an
algebraically closed field has self-intersection `-1`. -/
theorem intersectionNumber_exceptional_of_smoothSurface
    (k : Type u) [Field k] [IsAlgClosed k] [X.Over (Spec (.of k))]
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
    (p : X) (hp : IsClosed ({p} : Set X)) :
    let I := (X.fromSpecResidueField p).ker
    let E := I.comap I.blowupToBase
    let : E.subscheme.Over (Spec (.of k)) :=
      ⟨E.subschemeι ≫ I.blowupToBase ≫ (X ↘ Spec (.of k))⟩
    LineBundleClass.intersectionNumber k E.subschemeι
      (LineBundleClass.mk I.isEffectiveCartier_comap_blowupToBase.toInvertibleSheaf)⁻¹ = -1 := by
  let f := X ↘ Spec (.of k)
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  have : IsRegular X := IsRegular.of_smooth f
  have hd := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq f 2).mp inferInstance).2 p hp
  have hr : IsIso (X.fromSpecResidueField p ≫ f) := by
    rw [← SpecMap_residueFieldIsoBase_inv f p hp]
    infer_instance
  exact intersectionNumber_exceptional_of_closedPoint k p hp hd hr

end AlgebraicGeometry.Scheme.IdealSheafData
