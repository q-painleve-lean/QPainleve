/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.VectorBundle.FixedRank
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
public import TauCeti.AlgebraicGeometry.Cohomology.Fiber.BaseChange
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.AffineCover.Fiber
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Relative
import TauCeti.AlgebraicGeometry.Cohomology.CohomologyAndBaseChange
import TauCeti.AlgebraicGeometry.Cohomology.Semicontinuity
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Finite
import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Basic
import TauCeti.AlgebraicGeometry.VectorBundle.OpenCover
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.BaseChange
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.QuasiSeparated

/-!
# Pushforward of vector bundles with vanishing fiber cohomology

For a flat projective family of curves, vanishing first cohomology on the closed fibers
allows degree-zero base change. When the fiber spaces of sections have constant dimension,
the pushforward is a vector bundle of that rank. This applies to line bundles of degree one
on projective-line rulings.

The affine calculation uses Tau Ceti's two-open cohomology and base change theorem,
the degree-zero case of Hartshorne, *Algebraic Geometry*, Theorem III.12.11.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace
open TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry

namespace Scheme

variable {R : Type u} [CommRing R] {X : Scheme.{u}} [X.Over (Spec (.of R))]

/-- Sections of a vector bundle over an affine open of a flat scheme over an affine base
are flat over the base ring. -/
theorem flat_sectionsBase_of_flat (E : FiniteLocallyFreeSheaf X)
    [Flat (X ↘ Spec (.of R))] {U : X.Opens} (hU : IsAffineOpen U) :
    Module.Flat R (((sectionsBasePresheafFunctor R).obj E.obj).obj (op U)) := by
  let A := Γ(X, U)
  let φ := (X.baseRingToStructurePresheaf R).app (op U)
  let : Algebra R A := φ.hom.toAlgebra
  have hflat : φ.hom.Flat := by
    dsimp only [φ]
    rw [baseRingToStructurePresheaf_app_eq_appLE]
    exact (RingHom.Flat.of_bijective
      ((Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.bijective)).comp
      ((X ↘ Spec (.of R)).flat_appLE (isAffineOpen_top _) hU le_top)
  let : Module.Flat R A := hflat
  obtain ⟨_, hproj⟩ :=
    (E.obj.isFiniteLocallyFree_iff_forall_isAffineOpen.mp E.property) U hU
  let : Module.Projective A Γ(E.obj, U) := hproj
  let : Module R Γ(E.obj, U) := sectionsBaseModule R E.obj U
  let : IsScalarTower R A Γ(E.obj, U) := .of_algebraMap_smul fun _ _ ↦ rfl
  exact Module.Flat.trans R A Γ(E.obj, U)

end Scheme

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

private theorem isPullback_affineOpen_spec (W : Y.Opens) (hW : IsAffineOpen W) :
    IsPullback (f ⁻¹ᵁ W).ι ((f ∣_ W) ≫ hW.isoSpec.hom) f hW.fromSpec :=
  (isPullback_morphismRestrict f W).flip.of_iso (.refl _) (.refl _) hW.isoSpec (.refl _)
    (by simp) (by simp) (by simp) (by simp)

private theorem affine_fiber_cohomology (W : Y.Opens) (hW : IsAffineOpen W) (M : X.Modules)
    [M.IsQuasicoherent] [IsProper f] (p : Spec Γ(Y, W)) :
    letI := p.isPrime
    let R := Γ(Y, W)
    let g := (f ∣_ W) ≫ hW.isoSpec.hom
    let a := Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))
    let P := pullback g a
    let N := (Scheme.Modules.pullback ((f ⁻¹ᵁ W).ι)).obj M
    letI : P.Over (Spec (.of p.asIdeal.ResidueField)) := ⟨pullback.snd g a⟩
    ∀ j : ℕ,
    (Subsingleton (Cohomology ((Scheme.Modules.pullback (pullback.fst g a)).obj N) j) ↔
      Subsingleton (Cohomology ((Scheme.Modules.pullback (f.fiberι (hW.fromSpec p))).obj M) j)) ∧
    Module.finrank p.asIdeal.ResidueField
      (Cohomology ((Scheme.Modules.pullback (pullback.fst g a)).obj N) j) =
      fiberCohomologyFinrank M f j (hW.fromSpec p) := by
  intro R g a P N j
  let := p.isPrime
  let y := hW.fromSpec p
  let r := hW.fromSpec.residueFieldMap p ≫ (Scheme.Spec.residueFieldIso R p).hom
  let : Algebra (Y.residueField y) p.asIdeal.ResidueField := r.hom.toAlgebra
  let b := Y.fromSpecResidueField y
  have hr : a ≫ hW.fromSpec = Spec.map r ≫ b := by
    dsimp only [r, b, y]
    rw [Spec.map_comp, Category.assoc, hW.fromSpec.SpecMap_residueFieldMap_fromSpecResidueField]
    rw [← cancel_epi (Spec.map (Scheme.Spec.residueFieldIso R p).inv)]
    simp only [← Spec.map_comp_assoc, Iso.hom_inv_id, Spec.map_id]
    exact Category.assoc _ _ _ |>.symm.trans
      (congrArg (fun m ↦ m ≫ hW.fromSpec)
        (Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField R p))
  let c := pullback.fst g a ≫ (f ⁻¹ᵁ W).ι
  have H : IsPullback c (pullback.snd g a) f (Spec.map r ≫ b) :=
    hr ▸ (IsPullback.of_hasPullback g a).paste_horiz (f.isPullback_affineOpen_spec W hW)
  -- Compare the two descriptions of the fiber over the isomorphic residue fields.
  let i := pullback.lift c (pullback.snd g a ≫ Spec.map r) (by rw [H.w, Category.assoc])
  have hi : i ≫ f.fiberι y = c := pullback.lift_fst _ _ _
  have H' : IsPullback i (pullback.snd g a) (f.fiberToSpecResidueField y) (Spec.map r) :=
    IsPullback.of_right (hi.symm ▸ H) (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback f b)
  let := f.fiberOverSpecResidueField y
  let : P.Over (Spec (.of p.asIdeal.ResidueField)) := ⟨pullback.snd g a⟩
  let e := cohomologyBaseChangeLinearEquiv (R := Y.residueField y)
    (R' := p.asIdeal.ResidueField) (Y := P) H'
    ((Scheme.Modules.pullback (f.fiberι y)).obj M) j
  let eM := (pullbackComp i (f.fiberι y)).app M ≪≫ (pullbackCongr hi).app M ≪≫
    ((pullbackComp (pullback.fst g a) (f ⁻¹ᵁ W).ι).app M).symm
  let e' := e.trans (cohomologyBaseLinearEquivOfIso p.asIdeal.ResidueField eM j)
  refine ⟨e'.symm.toEquiv.subsingleton_congr.trans
    (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right _ _), ?_⟩
  rw [fiberCohomologyFinrank_def]
  exact e'.symm.finrank_eq.trans Module.finrank_baseChange

private theorem affine_chart_pushforward (W : Y.Opens) (hW : IsAffineOpen W)
    [IsProper f] (E : FiniteLocallyFreeSheaf X) :
    let Z := (f ⁻¹ᵁ W).toScheme
    let g := (f ∣_ W) ≫ hW.isoSpec.hom
    let N := (Scheme.Modules.pullback (f ⁻¹ᵁ W).ι).obj E.obj
    letI : Z.Over (Spec Γ(Y, W)) := ⟨g⟩
    Nonempty (Cohomology N 0 ≃ₗ[Γ(Y, W)]
      moduleSpecΓFunctor.obj ((Scheme.Modules.pullback hW.fromSpec).obj
        ((pushforward f).obj E.obj))) := by
  intro Z g N
  let R := Γ(Y, W)
  let : Z.Over (Spec R) := ⟨g⟩
  let : IsOpenImmersion hW.fromSpec := hW.isOpenImmersion_fromSpec
  let H := f.isPullback_affineOpen_spec W hW
  have := isIso_pushforwardBaseChange_app H E.obj
  let e := (moduleSpecΓFunctor (R := R)).mapIso
    (asIso ((pushforwardBaseChange H.toCommSq).app E.obj))
  let : Module R Γ(N, ⊤) := sectionsBaseModule R N ⊤
  let : Algebra R Γ(Z, ⊤) := ((Z.baseRingToStructurePresheaf R).app (op ⊤)).hom.toAlgebra
  let : IsScalarTower R Γ(Z, ⊤) Γ(N, ⊤) := .of_algebraMap_smul fun _ _ ↦ rfl
  have := isScalarTower_cohomology R Z N 0
  let e₀ := (cohomologyZeroLinearEquiv N).restrictScalars R
  let e₁ : Γ(N, ⊤) ≃ₗ[R] moduleSpecΓFunctor.obj ((pushforward g).obj N) :=
    { toEquiv := Equiv.refl _
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro r v
        -- Both actions come from the structure map of the affine base.
        simp only [RingHom.id_apply]
        refine Eq.trans ?_ (smul_Spec_def (M := (pushforward g).obj N)
          (U := ⊤) r v).symm
        have ht : (⊤ : (Spec R).Opens).leTop.op = 𝟙 _ := Subsingleton.elim _ _
        have hm : (Spec R).presheaf.map (⊤ : (Spec R).Opens).leTop.op
            ((Scheme.ΓSpecIso R).inv r) = (Scheme.ΓSpecIso R).inv r := by
          rw [ht]
          exact ConcreteCategory.congr_hom ((Spec R).presheaf.map_id _) _
        rw [hm]
        have hbase : ((Z.baseRingToStructurePresheaf R).app (op ⊤)) r =
            g.appLE ⊤ ⊤ le_top ((Scheme.ΓSpecIso R).inv r) := by
          rw [Scheme.baseRingToStructurePresheaf_app_eq_appLE]
          rfl
        have happ : g.appLE ⊤ ⊤ le_top ((Scheme.ΓSpecIso R).inv r) =
            (g.toRingCatSheafHom.hom.app (op ⊤)) ((Scheme.ΓSpecIso R).inv r) := by
          exact congrArg (fun q : Γ(Spec R, ⊤) ⟶ Γ(Z, g ⁻¹ᵁ ⊤) ↦
            q ((Scheme.ΓSpecIso R).inv r)) (g.appLE_eq_app (U := ⊤))
        exact congrArg (fun a : Γ(Z, ⊤) ↦ a • v) (hbase.trans happ) }
  exact ⟨e₀.trans (e₁.trans e.symm.toLinearEquiv)⟩

variable {k : Type u} [Field k] [Infinite k]
  [hX : X.Over (Spec (.of k))] [hY : Y.Over (Spec (.of k))] [hf : f.IsOver (Spec (.of k))]
  [hsep : IsSeparated (Y ↘ Spec (.of k))] [hft : LocallyOfFiniteType (Y ↘ Spec (.of k))]
  [hproj : X.IsProjectiveOver k] [Flat f]

include hX hY hf hsep hft hproj in
omit [Infinite k] in
private theorem finite_projective_on_two_affines
    [IsProper f] (W : Y.Opens) (hW : IsAffineOpen W) (E : FiniteLocallyFreeSheaf X)
    (U V : (f ⁻¹ᵁ W).toScheme.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : U ⊔ V = ⊤)
    (hvan : ∀ y : Y, IsClosed ({y} : Set Y) →
      Subsingleton (Cohomology ((Scheme.Modules.pullback (f.fiberι y)).obj E.obj) 1)) :
    let R := Γ(Y, W)
    let M := ((Scheme.Modules.pullback hW.fromSpec).obj ((pushforward f).obj E.obj))
    (Module.Finite R (moduleSpecΓFunctor.obj M) ∧
      Module.Projective R (moduleSpecΓFunctor.obj M)) ∧
    ∀ p : Spec R, Module.rankAtStalk (moduleSpecΓFunctor.obj M) p =
      fiberCohomologyFinrank E.obj f 0 (hW.fromSpec p) := by
  intro R M
  let Z := (f ⁻¹ᵁ W).toScheme
  let g := (f ∣_ W) ≫ hW.isoSpec.hom
  let : Z.Over (Spec R) := ⟨g⟩
  let N := (Scheme.Modules.pullback (f ⁻¹ᵁ W).ι).obj E.obj
  let E' : FiniteLocallyFreeSheaf Z := ⟨N, by
    dsimp only [N]
    rw [← FiniteLocallyFreeSheaf.pullback_obj_obj]
    exact ((FiniteLocallyFreeSheaf.pullback (f ⁻¹ᵁ W).ι).obj E).property⟩
  let : IsProper g :=
    MorphismProperty.of_isPullback (f.isPullback_affineOpen_spec W hW) inferInstance
  let : Flat (Z ↘ Spec R) := inferInstanceAs (Flat ((f ∣_ W) ≫ hW.isoSpec.hom))
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  let : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  let : Z.IsProjectiveOver R := f.isProjectiveOver_morphismRestrict (R := k) hW
  let : IsSeparated (Limits.terminal.from Z) := by
    rw [← Limits.terminal.comp_from g]
    infer_instance
  have hI : IsAffineOpen (U ⊓ V) := hU.inf hV
  have := Z.flat_sectionsBase_of_flat (R := R) E' hU
  have := Z.flat_sectionsBase_of_flat (R := R) E' hV
  have := Z.flat_sectionsBase_of_flat (R := R) E' hI
  let : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace (Y ↘ Spec (.of k))
  let : IsOpenImmersion hW.fromSpec := hW.isOpenImmersion_fromSpec
  have hzero : Subsingleton (Cohomology E'.obj 1) :=
    (subsingleton_cohomology_one_iff_forall_isMaximal E'.obj hU hV hI hUV).mpr fun p hp ↦ by
      apply (f.affine_fiber_cohomology W hW E.obj p 1).1.mpr
      apply hvan
      have hc : (p : Spec R) ∈ closedPoints (Spec R) :=
        (p.isClosed_singleton_iff_isMaximal).mpr hp
      have hp' : p ∈ hW.fromSpec ⁻¹' closedPoints Y := by
        rw [hW.fromSpec.isOpenEmbedding.preimage_closedPoints]
        exact hc
      exact mem_closedPoints_iff.mp (Set.mem_preimage.mp hp')
  have := flat_cohomology_zero_of_subsingleton_cohomology_one (R := R) E'.obj U V hUV
  let : Module.FinitePresentation R (Cohomology E'.obj 0) :=
    Module.finitePresentation_of_finite R _
  let : Module.Projective R (Cohomology E'.obj 0) := Module.Flat.projective_of_finitePresentation
  obtain ⟨e⟩ := f.affine_chart_pushforward W hW E
  refine ⟨⟨Module.Finite.equiv e, Module.Projective.of_equiv e⟩, fun p ↦ ?_⟩
  let := p.isPrime
  let a := Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))
  let P := pullback g a
  let : P.Over (Spec (.of p.asIdeal.ResidueField)) := ⟨pullback.snd g a⟩
  have h := finrank_cohomology_zero_pullback_eq_finrank_fiber (Y := P) p
    (IsPullback.of_hasPullback g a) E'.obj hU hV hI hUV
  exact (congrFun (Module.rankAtStalk_eq_of_equiv e) p).symm.trans
    ((Module.rankAtStalk_eq (M := Cohomology N 0) (p : PrimeSpectrum R)).trans
      (h.symm.trans (f.affine_fiber_cohomology W hW E.obj p 0).2))

include hX hY hf hsep hft hproj in
omit [Flat f] in
private theorem iSup_affine_opens_with_two_affine_preimages
    (hdim : ∀ y : Y, IsClosed ({y} : Set Y) → topologicalKrullDim (f.fiber y) ≤ 1) :
    (⨆ i : {W : Y.Opens // IsAffineOpen W ∧
      ∃ U V : (f ⁻¹ᵁ W).toScheme.Opens, IsAffineOpen U ∧ IsAffineOpen V ∧ U ⊔ V = ⊤},
      i.val) = ⊤ := by
  let : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace (Y ↘ Spec (.of k))
  let I := {W : Y.Opens // IsAffineOpen W ∧
    ∃ U V : (f ⁻¹ᵁ W).toScheme.Opens, IsAffineOpen U ∧ IsAffineOpen V ∧ U ⊔ V = ⊤}
  let W : I → Y.Opens := Subtype.val
  have hclosed (y : Y) (hy : IsClosed ({y} : Set Y)) : ∃ i : I, y ∈ W i := by
    obtain ⟨V, hyV, _, hV, U, hU, hcover⟩ :=
      f.exists_affineCover_of_fiber_dim_lt (k := k) (n := 2) (Opens.mem_top y)
        ((hdim y hy).trans_lt (by decide))
    refine ⟨⟨V, hV, U 0, U 1, hU 0, hU 1, ?_⟩, hyV⟩
    rw [← hcover]
    refine le_antisymm (sup_le (le_iSup _ _) (le_iSup _ _)) (iSup_le fun j ↦ ?_)
    fin_cases j
    · exact le_sup_left
    · exact le_sup_right
  refine top_unique fun y _ ↦ ?_
  by_contra hy
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints (X := Y)
    (Z := (↑(⨆ i, W i) : Set Y)ᶜ) ⟨y, hy⟩ ((⨆ i, W i).isOpen.isClosed_compl.isLocallyClosed)
  obtain ⟨i, hi⟩ := hclosed z hzc
  exact hz ((le_iSup W i) hi)

include hX hY hf hsep hft hproj in
/-- For a flat morphism from a projective scheme to a separated scheme of locally finite
type over an infinite field, assume that the closed fibers have dimension at most one.
If a vector bundle has vanishing first cohomology and an `r`-dimensional space of global
sections on each closed fiber, its direct image is a vector bundle of rank `r`. -/
theorem exists_fixedRank_pushforward (E : FiniteLocallyFreeSheaf X) (r : ℕ)
    (hdim : ∀ y : Y, IsClosed ({y} : Set Y) → topologicalKrullDim (f.fiber y) ≤ 1)
    (hvan : ∀ y : Y, IsClosed ({y} : Set Y) →
      Subsingleton (Cohomology ((Scheme.Modules.pullback (f.fiberι y)).obj E.obj) 1))
    (hr : ∀ y : Y, IsClosed ({y} : Set Y) → fiberCohomologyFinrank E.obj f 0 y = r) :
    ∃ V : FiniteLocallyFreeSheaf.FixedRank Y r, V.obj.obj = (pushforward f).obj E.obj := by
  classical
  let : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace (Y ↘ Spec (.of k))
  let I := {W : Y.Opens // IsAffineOpen W ∧
    ∃ U V : (f ⁻¹ᵁ W).toScheme.Opens, IsAffineOpen U ∧ IsAffineOpen V ∧ U ⊔ V = ⊤}
  let W : I → Y.Opens := Subtype.val
  have hcover : ⨆ i, W i = ⊤ := f.iSup_affine_opens_with_two_affine_preimages (k := k) hdim
  let A := Scheme.AffineOpenCover.ofIsOpenCover W hcover fun i ↦ i.property.1
  let M := (pushforward f).obj E.obj
  let : IsProper f := by
    have : IsProper (f ≫ Y ↘ Spec (.of k)) := by rw [comp_over]; infer_instance
    exact IsProper.of_comp f (Y ↘ Spec (.of k))
  let : M.IsQuasicoherent := isQuasicoherent_pushforward E.obj f
  have hlocal (i : I) :=
    f.finite_projective_on_two_affines (k := k) (W i) i.property.1 E
  have hM : isFiniteLocallyFree Y M := by
    apply (isFiniteLocallyFree_iff_forall_pullback A.openCover M).mpr
    intro i
    obtain ⟨U, V, hU, hV, hUV⟩ := i.property.2
    let e := M.fromSpecSectionsEquiv i.property.1
    obtain ⟨⟨hfin, hproj⟩, _⟩ := hlocal i U V hU hV hUV hvan
    let : IsOpenImmersion i.property.1.fromSpec := i.property.1.isOpenImmersion_fromSpec
    let e' := (moduleSpecΓFunctor (R := Γ(Y, W i))).mapIso
      ((restrictFunctorIsoPullback i.property.1.fromSpec).app M)
    exact (M.isFiniteLocallyFree_pullback_fromSpec_iff i.property.1).mpr
      ⟨Module.Finite.equiv (e.trans e'.toLinearEquiv).symm,
        Module.Projective.of_equiv (e.trans e'.toLinearEquiv).symm⟩
  let V : FiniteLocallyFreeSheaf Y := ⟨M, hM⟩
  refine ⟨⟨V, ?_⟩, rfl⟩
  have hRank (y : Y) : V.rank y = fiberCohomologyFinrank E.obj f 0 y := by
    obtain ⟨i, hy⟩ : ∃ i, y ∈ W i := by
      simpa only [← Opens.mem_iSup, hcover] using Opens.mem_top y
    obtain ⟨U, U', hU, hU', hUU'⟩ := i.property.2
    let p := i.property.1.primeIdealOf ⟨y, hy⟩
    have hp : i.property.1.fromSpec p = y := i.property.1.fromSpec_primeIdealOf ⟨y, hy⟩
    have hv := FiniteLocallyFreeSheaf.rank_pullback_apply i.property.1.fromSpec V p
    let Q := (FiniteLocallyFreeSheaf.pullback i.property.1.fromSpec).obj V
    have hs := Q.rank_apply_eq_rankAtStalk p
    rw [FiniteLocallyFreeSheaf.pullback_obj_obj] at hs
    have ht := hs.trans ((hlocal i U U' hU hU' hUU' hvan).2 p)
    rw [hp] at hv ht
    exact hv.symm.trans ht
  have hZ := V.rank.isLocallyConstant.isClosed_fiber r
  have hAll : (closedPoints Y) ⊆ {y | V.rank y = r} := fun y hy ↦ (hRank y).trans (hr y hy)
  have hsub := closure_minimal hAll hZ
  rw [closure_closedPoints] at hsub
  exact (FiniteLocallyFreeSheaf.isConstantRank_iff _ _).mpr fun y ↦ hsub (Set.mem_univ y)

end Scheme.Hom

end AlgebraicGeometry
