/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.VectorBundle.SectionZeroLocus
public import TauCeti.AlgebraicGeometry.VectorBundle.FixedRank

import TauCeti.Algebra.Homology.ShortComplex.ShortExact
import TauCeti.AlgebraicGeometry.LineBundle.Dual
import TauCeti.AlgebraicGeometry.LineBundle.Pullback
import TauCeti.AlgebraicGeometry.Modules.Pullback.Quasicoherent
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Cokernels
import TauCeti.AlgebraicGeometry.Modules.Tensor.Product
import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Basic

/-!
# Line subbundles of vector bundles

A morphism from a line bundle that is nonzero in every residue-field fiber
identifies that line bundle with a subbundle. On an affine scheme the dual
evaluation at a nowhere-zero section admits a lift of the constant section one,
which produces a retraction.
-/

public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory MonoidalClosed TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

universe u

variable {X : Scheme.{u}}

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

local notation "𝟙ₘ" => 𝟙_ X.Modules

local instance evaluationModuleIsQuasicoherent (E : FiniteLocallyFreeSheaf X) :
    ((ihom E.obj).obj 𝟙ₘ).IsQuasicoherent := by
  rw [← dual_obj E]
  exact ((toQuasicoherent X).obj (dual E)).property

/-- On an affine scheme, a section whose evaluation ideal is the unit ideal
admits a global linear retraction. -/
theorem exists_retraction_of_imageIdealSheaf_evaluation_eq_top [IsAffine X]
    (E : FiniteLocallyFreeSheaf X) (s : 𝟙ₘ ⟶ E.obj)
    (h : ((dualHomUnitEquiv E.obj).symm s).imageIdealSheaf = ⊤) :
    ∃ r : E.obj ⟶ 𝟙ₘ, s ≫ r = 𝟙 _ := by
  let T : X.Modules := (ihom E.obj).obj 𝟙ₘ
  let φ : T ⟶ 𝟙ₘ := (dualHomUnitEquiv E.obj).symm s
  have : T.IsQuasicoherent := evaluationModuleIsQuasicoherent E
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  have hone : (1 : Γ(X, (⊤ : X.Opens))) ∈ φ.imageIdeal U := by
    rw [← Scheme.Modules.Hom.imageIdealSheaf_ideal φ U, h]
    exact Submodule.mem_top
  obtain ⟨t, ht⟩ := (φ.mem_imageIdeal).mp hone
  let a : 𝟙ₘ ⟶ T := T.unitHomEquivTop.symm t
  have ha : a ≫ φ = 𝟙 𝟙ₘ := by
    apply (unitHomEquivTop 𝟙ₘ).injective
    exact (unitHomEquivTop_comp T a φ).trans (by
      dsimp only [a]
      rw [Equiv.apply_symm_apply]
      have hunit : (unitHomEquivTop 𝟙ₘ) (𝟙 𝟙ₘ) = (1 : Γ(X, (⊤ : X.Opens))) :=
        (unitHomEquivTop_apply 𝟙ₘ (𝟙 𝟙ₘ)).trans rfl
      exact ht.trans hunit.symm)
  refine ⟨uncurry' a, ?_⟩
  have hφ : a ≫ φ = s ≫ uncurry' a := by
    dsimp only [φ]
    rw [dualHomUnitEquiv_symm_apply, ← Category.assoc a,
      leftUnitor_inv_naturality, Category.assoc, whisker_exchange_assoc,
      ← uncurry_eq, uncurry', unitors_inv_equal, rightUnitor_inv_naturality_assoc]
  exact hφ.symm.trans ha

private theorem pullback_tensorDual_section {Y : Scheme.{u}} (f : Y ⟶ X)
    {M : X.Modules} (L : InvertibleSheaf X) (i : L.obj ⟶ M) :
    let P := Scheme.Modules.pullback f
    let D := P.obj L.dual.obj
    ∃ (a : (𝟙_ Y.Modules) ≅ P.obj L.obj ⊗ D)
      (b : P.obj (M ⊗ L.dual.obj) ≅ P.obj M ⊗ D),
      (pullbackObjUnitIso f).inv ≫ P.map (L.evaluationDualIso.inv ≫ i ▷ L.dual.obj) ≫ b.hom =
        a.hom ≫ P.map i ▷ D := by
  dsimp only
  let P := Scheme.Modules.pullback f
  let D := L.dual
  let δL := asIso (Functor.OplaxMonoidal.δ P L.obj D.obj)
  let δM := asIso (Functor.OplaxMonoidal.δ P M D.obj)
  let a := (pullbackObjUnitIso f).symm ≪≫ P.mapIso L.evaluationDualIso.symm ≪≫ δL
  refine ⟨a, δM, ?_⟩
  have hδ := Functor.OplaxMonoidal.δ_natural_left P i D.obj
  simp only [a, δL, δM, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.map_comp, asIso_hom, Category.assoc]
  exact congrArg (fun ψ ↦ (pullbackObjUnitIso f).inv ≫ P.map L.evaluationDualIso.inv ≫ ψ)
    hδ.symm

private theorem twistedSection_imageIdealSheaf_eq_top
    (E : FiniteLocallyFreeSheaf X) (L : InvertibleSheaf X) (i : L.obj ⟶ E.obj)
    (hi : ∀ x : X, (Scheme.Modules.pullback (X.fromSpecResidueField x)).map i ≠ 0) :
    let T : FiniteLocallyFreeSheaf X := E ⊗ (InvertibleSheaf.toFiniteLocallyFree X).obj L.dual
    let s : 𝟙ₘ ⟶ T.obj := L.evaluationDualIso.inv ≫ i ▷ L.dual.obj
    ((dualHomUnitEquiv T.obj).symm s).imageIdealSheaf = ⊤ := by
  intro T s
  rw [← Scheme.IdealSheafData.support_eq_bot_iff]
  apply SetLike.coe_injective
  rw [Closeds.coe_bot]
  refine Set.eq_empty_iff_forall_notMem.mpr fun x hx ↦ ?_
  let j := X.fromSpecResidueField x
  let J := Scheme.Modules.pullback j
  let W := (InvertibleSheaf.pullback j).obj L.dual
  obtain ⟨a, b, h⟩ := pullback_tensorDual_section j L i
  have hs := (T.mem_support_imageIdealSheaf_evaluation_iff s x).mp hx
  have he : a.hom ≫ J.map i ▷ W.obj = 0 := h.symm.trans
    (congrArg (· ≫ b.hom) hs |>.trans (zero_comp : _))
  have hF : (tensorRight W.obj).IsEquivalence := by
    rw [← W.tensorRightDualEquivalence_inverse]
    infer_instance
  have hW := zero_of_epi_comp _ he
  let : MonoidalPreadditive (Spec (X.residueField x)).Modules :=
    TauCeti.SheafOfModules.monoidalPreadditive (Spec (X.residueField x)).sheaf
  exact hi x ((tensorRight W.obj).map_injective
    (hW.trans MonoidalPreadditive.zero_whiskerRight.symm))

/-- A map from a line bundle to a vector bundle that is nonzero in every
residue-field fiber has a linear retraction after pullback to any affine scheme. -/
theorem exists_retraction_pullback_of_fiberwise_ne_zero
    (E : FiniteLocallyFreeSheaf X) (L : InvertibleSheaf X) (i : L.obj ⟶ E.obj)
    (hi : ∀ x : X, (Scheme.Modules.pullback (X.fromSpecResidueField x)).map i ≠ 0)
    {Y : Scheme.{u}} [IsAffine Y] (f : Y ⟶ X) :
    ∃ r : (Scheme.Modules.pullback f).obj E.obj ⟶ (Scheme.Modules.pullback f).obj L.obj,
      (Scheme.Modules.pullback f).map i ≫ r = 𝟙 _ := by
  let T : FiniteLocallyFreeSheaf X := E ⊗ (InvertibleSheaf.toFiniteLocallyFree X).obj L.dual
  let s : 𝟙ₘ ⟶ T.obj := L.evaluationDualIso.inv ≫ i ▷ L.dual.obj
  let P := Scheme.Modules.pullback f
  let D := (InvertibleSheaf.pullback f).obj L.dual
  let F := tensorRight D.obj
  have : F.IsEquivalence := by
    dsimp only [F]
    rw [← D.tensorRightDualEquivalence_inverse]
    infer_instance
  have htop := twistedSection_imageIdealSheaf_eq_top E L i hi
  let T' : FiniteLocallyFreeSheaf Y :=
    ⟨P.obj T.obj, Scheme.Modules.isLocallyFree_pullback f T.obj,
      Scheme.Modules.isFinitePresentation_pullback f T.obj⟩
  let s' : 𝟙_ Y.Modules ⟶ T'.obj := (pullbackObjUnitIso f).inv ≫ P.map s
  let := evaluationModuleIsQuasicoherent T'
  have htop' : ((dualHomUnitEquiv T'.obj).symm s').imageIdealSheaf = ⊤ :=
    (T.imageIdealSheaf_evaluation_pullback s f).trans
      (by rw [htop, Scheme.IdealSheafData.comap_top])
  obtain ⟨r, hr⟩ := T'.exists_retraction_of_imageIdealSheaf_evaluation_eq_top s' htop'
  obtain ⟨a, b, h⟩ := pullback_tensorDual_section f L i
  let r' := F.preimage (b.inv ≫ r ≫ a.hom)
  refine ⟨r', F.map_injective ((F.map_comp _ _).trans ?_)⟩
  have h' : s' ≫ b.hom = a.hom ≫ F.map (P.map i) := h
  have hmap : F.map r' = b.inv ≫ r ≫ a.hom := F.map_preimage _
  refine (congrArg (F.map (P.map i) ≫ ·) hmap).trans (?_ : _ = 𝟙 _)
    |>.trans (F.map_id _).symm
  apply (cancel_epi a.hom).mp
  calc
    _ = (a.hom ≫ F.map (P.map i)) ≫ b.inv ≫ r ≫ a.hom := (Category.assoc _ _ _).symm
    _ = (s' ≫ b.hom) ≫ b.inv ≫ r ≫ a.hom := congrArg (· ≫ b.inv ≫ r ≫ a.hom) h'.symm
    _ = s' ≫ r ≫ a.hom := (Category.assoc _ _ _).trans (congrArg (s' ≫ ·) (b.hom_inv_id_assoc _))
    _ = _ := by
      rw [← Category.assoc, hr, Category.id_comp]
      exact (Category.comp_id a.hom).symm

namespace FixedRank

/-- The cokernel of a split inclusion of a line bundle into a rank-two bundle
is a line bundle. -/
theorem isInvertible_cokernel_of_retraction
    (E : FixedRank X 2) (L : InvertibleSheaf X) (i : L.obj ⟶ E.obj.obj)
    {r : E.obj.obj ⟶ L.obj} (hr : i ≫ r = 𝟙 _) :
    SheafOfModules.isInvertible X (cokernel i) := by
  have : Mono i := mono_of_mono_fac hr
  let S := ShortComplex.cokernelSequence i
  have hS : S.ShortExact := TauCeti.cokernelSequence_shortExact i
  let split := ShortComplex.Splitting.ofExactOfRetraction S hS.exact r hr hS.epi_g
  have : (cokernel i).IsQuasicoherent := Scheme.Modules.isQuasicoherent_cokernel i
  have hQ : isFiniteLocallyFree X (cokernel i) := by
    apply (isFiniteLocallyFree_iff_forall_isAffineOpen _).mpr
    intro U hU
    obtain ⟨hFin, hProj⟩ := (isFiniteLocallyFree_iff_forall_isAffineOpen _).mp E.obj.property U hU
    let : Module.Finite Γ(X, U) Γ(E.obj.obj, U) := hFin
    let : Module.Projective Γ(X, U) Γ(E.obj.obj, U) := hProj
    let G := sectionsFunctor U
    let a : Γ(cokernel i, U) →ₗ[Γ(X, U)] Γ(E.obj.obj, U) := (G.map split.s).hom
    let b : Γ(E.obj.obj, U) →ₗ[Γ(X, U)] Γ(cokernel i, U) := (G.map S.g).hom
    have hG : G.map split.s ≫ G.map S.g = 𝟙 (G.obj S.X₃) :=
      (G.map_comp _ _).symm.trans ((congrArg G.map split.s_g).trans (G.map_id _))
    have hcomp : b.comp a = LinearMap.id := congrArg ModuleCat.Hom.hom hG
    exact ⟨Module.Finite.of_surjective b (Function.RightInverse.surjective
      (fun x ↦ DFunLike.congr_fun hcomp x)), Module.Projective.of_split a b hcomp⟩
  let Q : FiniteLocallyFreeSheaf X := ⟨cokernel i, hQ⟩
  let A := (InvertibleSheaf.toFiniteLocallyFree X).obj L
  let e : E.obj.obj ≅ (A ⊞ Q).obj :=
    split.isoBinaryBiproduct ≪≫ ((isFiniteLocallyFree X).ι.mapBiprod A Q).symm
  apply Q.isInvertible_iff_forall_rank_eq_one.mpr
  intro x
  have h := DFunLike.congr_fun (rank_eq_of_iso e) x
  rw [rank_biprod_apply, InvertibleSheaf.rank_toFiniteLocallyFree_apply, FixedRank.rank_apply] at h
  omega

/-- A line bundle map into a rank-two vector bundle that is nonzero in every
residue-field fiber is injective and has invertible cokernel. -/
theorem mono_and_isInvertible_cokernel_of_fiberwise_ne_zero
    (E : FixedRank X 2) (L : InvertibleSheaf X) (i : L.obj ⟶ E.obj.obj)
    (hi : ∀ x : X, (Scheme.Modules.pullback (X.fromSpecResidueField x)).map i ≠ 0) :
    Mono i ∧ SheafOfModules.isInvertible X (cokernel i) := by
  have h (U : X.affineOpens) :
      ∃ r : (Scheme.Modules.pullback U.val.ι).obj E.obj.obj ⟶
        (Scheme.Modules.pullback U.val.ι).obj L.obj,
        (Scheme.Modules.pullback U.val.ι).map i ≫ r = 𝟙 _ := by
    let : IsAffine (U.val : Scheme) := U.property
    exact E.obj.exists_retraction_pullback_of_fiberwise_ne_zero L i hi U.val.ι
  refine ⟨(mono_iff_of_isOpenCover X.isBasis_affineOpens.isOpenCover i).mpr fun U ↦ ?_, ?_⟩
  · obtain ⟨r, hr⟩ := h U
    exact mono_of_mono_fac hr
  · let 𝒰 := X.openCoverOfIsOpenCover (fun U : X.affineOpens ↦ U.val)
        X.isBasis_affineOpens.isOpenCover
    refine (SheafOfModules.isInvertible_iff_forall_restrict 𝒰 _).mpr ?_
    suffices hloc : ∀ U : X.affineOpens, SheafOfModules.isInvertible (U.val : Scheme)
        ((cokernel i).restrict U.val.ι) from hloc
    intro U
    let f := U.val.ι
    let P := Scheme.Modules.pullback f
    obtain ⟨r, hr⟩ := h U
    let A := (InvertibleSheaf.pullback f).obj L
    let B : FiniteLocallyFreeSheaf (U.val : Scheme) :=
      ⟨P.obj E.obj.obj, Scheme.Modules.isLocallyFree_pullback f E.obj.obj,
        Scheme.Modules.isFinitePresentation_pullback f E.obj.obj⟩
    have hB (x : U.val) : B.rank x = 2 := by
      let e : B.obj ≅ ((FiniteLocallyFreeSheaf.pullback f).obj E.obj).obj :=
        eqToIso (FiniteLocallyFreeSheaf.pullback_obj_obj f E.obj).symm
      exact (DFunLike.congr_fun (rank_eq_of_iso e) x).trans
        ((rank_pullback_apply f E.obj x).trans (E.rank_apply (f x)))
    let V : FixedRank (U.val : Scheme) 2 := ⟨B, (isConstantRank_iff B 2).mpr hB⟩
    have hQ := isInvertible_cokernel_of_retraction V A (P.map i) hr
    let e := (PreservesCokernel.iso P i).symm ≪≫
      ((restrictFunctorIsoPullback f).app (cokernel i)).symm
    exact (SheafOfModules.isInvertible _).prop_of_iso e hQ

end FixedRank

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf
