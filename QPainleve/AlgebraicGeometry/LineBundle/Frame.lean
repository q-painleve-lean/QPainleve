/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.LineBundle.Ratio
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Comparing line bundles by section ratios

Two families of global sections determine an isomorphism of their line bundles when they
give frames on the same open cover and have the same ratios in those frames.
-/

public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

section

variable {X : Scheme.{u}} {M N : X.Modules}
  [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M]
  {ι : Type*} {U : ι → X.Opens} {s : ι → Γ(M, ⊤)} {t : ι → Γ(N, ⊤)}

private theorem le_nonvanishingLocus_res {M : X.Modules}
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M]
    {W : X.Opens} {s : Γ(M, ⊤)} (h : W ≤ M.nonvanishingLocus s) :
    W ≤ M.nonvanishingLocus (M.presheaf.map W.leTop.op s) :=
  M.le_nonvanishingLocus_map W.leTop s h

variable (M) in
/-- A nowhere vanishing section gives a basis for the module of sections over its open. -/
def sectionFrame {W : X.Opens} (s : Γ(M, W))
    (hs : W ≤ M.nonvanishingLocus s) : Γ(X, W) ≃ₗ[Γ(X, W)] Γ(M, W) :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton (Γ(X, W)) _ s)
    ⟨M.injective_smul_of_le_nonvanishingLocus hs,
      M.surjective_smul_of_le_nonvanishingLocus hs⟩

variable (M) in
/-- The frame sends a regular function to its multiple of the chosen section. -/
@[simp]
theorem sectionFrame_apply {W : X.Opens} (s : Γ(M, W))
    (hs : W ≤ M.nonvanishingLocus s) (r : Γ(X, W)) : M.sectionFrame s hs r = r • s :=
  LinearMap.toSpanSingleton_apply _ _ s r

variable (M) in
/-- The inverse frame reads the coefficient of a section in the given basis. -/
@[simp]
theorem sectionFrame_symm_apply {W : X.Opens} (s : Γ(M, W))
    (hs : W ≤ M.nonvanishingLocus s) (m : Γ(M, W)) :
    (M.sectionFrame s hs).symm m = M.sectionRatio m s hs := by
  symm
  apply (M.sectionRatio_eq_iff hs).mpr
  rw [← M.sectionFrame_apply s hs, LinearEquiv.apply_symm_apply]

private def frameMap {W : X.Opens} {i : ι} (h : W ≤ U i)
    (hs : ∀ i, U i ≤ M.nonvanishingLocus (s i)) : Γ(M, W) →ₗ[Γ(X, W)] Γ(N, W) :=
  let e := M.sectionFrame (M.presheaf.map W.leTop.op (s i))
    (le_nonvanishingLocus_res (h.trans (hs i)))
  (LinearMap.toSpanSingleton (Γ(X, W)) _ (N.presheaf.map W.leTop.op (t i))).comp e.symm.toLinearMap

private theorem frameMap_smul_basis {W : X.Opens} {i : ι} (h : W ≤ U i)
    (hs : ∀ i, U i ≤ M.nonvanishingLocus (s i)) (r : Γ(X, W)) :
    frameMap (t := t) h hs (r • M.presheaf.map W.leTop.op (s i)) =
      r • N.presheaf.map W.leTop.op (t i) := by
  rw [frameMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    ← M.sectionFrame_apply _ (le_nonvanishingLocus_res (h.trans (hs i))) r,
    LinearEquiv.symm_apply_apply, LinearMap.toSpanSingleton_apply]

private theorem frameMap_eq_ratio {W : X.Opens} {i : ι} (h : W ≤ U i)
    (hs : ∀ i, U i ≤ M.nonvanishingLocus (s i)) (m : Γ(M, W)) :
    frameMap (t := t) h hs m = M.sectionRatio m (M.presheaf.map W.leTop.op (s i))
      (le_nonvanishingLocus_res (h.trans (hs i))) • N.presheaf.map W.leTop.op (t i) := by
  simp only [frameMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    sectionFrame_symm_apply, LinearMap.toSpanSingleton_apply]

private theorem frameMap_restrict {V W : X.Opens} {i : ι} (j : V ⟶ W) (h : W ≤ U i)
    (hs : ∀ i, U i ≤ M.nonvanishingLocus (s i)) (m : Γ(M, W)) :
    N.presheaf.map j.op (frameMap (t := t) h hs m) =
      frameMap (t := t) (j.le.trans h) hs (M.presheaf.map j.op m) := by
  rw [frameMap_eq_ratio, frameMap_eq_ratio, N.map_smul, M.map_sectionRatio]
  simp only [← Functor.map_comp_apply, ← op_comp]
  rfl

variable (hs : ∀ i, U i ≤ M.nonvanishingLocus (s i))
  (hr : ∀ i j,
    M.sectionRatio (M.presheaf.map (U i).leTop.op (s j))
      (M.presheaf.map (U i).leTop.op (s i)) (by
        rw [M.nonvanishingLocus_map]; exact le_inf le_rfl (hs i)) •
      N.presheaf.map (U i).leTop.op (t i) = N.presheaf.map (U i).leTop.op (t j))

include hr in
private theorem frameMap_section (i j : ι) :
    frameMap (U := U) (s := s) (t := t) (i := i) (le_refl (U i)) hs
      (M.presheaf.map (U i).leTop.op (s j)) = N.presheaf.map (U i).leTop.op (t j) := by
  rw [frameMap_eq_ratio]
  exact hr i j

include hr in
private theorem frameMap_eq {W : X.Opens} {i j : ι} (hi : W ≤ U i) (hj : W ≤ U j)
    (m : Γ(M, W)) :
    frameMap (t := t) hi hs m = frameMap (t := t) hj hs m := by
  obtain ⟨a, rfl⟩ := M.surjective_smul_of_le_nonvanishingLocus
    (le_nonvanishingLocus_res (hj.trans (hs j))) m
  have he := congrArg (N.presheaf.map (homOfLE hi).op) (frameMap_section hs hr i j)
  rw [frameMap_restrict] at he
  simp only [← Functor.map_comp_apply, ← op_comp] at he
  rw [Subsingleton.elim (homOfLE hi ≫ (U i).leTop) W.leTop] at he
  rw [frameMap_smul_basis (i := j), LinearMap.map_smul]
  exact congrArg (a • ·) he

include hr in
private theorem exists_frameMap_gluing (hU : ⨆ i, U i = ⊤) (W : X.Opens) (m : Γ(M, W)) :
    ∃! n : Γ(N, W), ∀ i, N.presheaf.map (homOfLE (inf_le_left (b := U i))).op n =
      frameMap (t := t) (i := i) (inf_le_right (a := W) (b := U i)) hs
        (M.presheaf.map (homOfLE inf_le_left).op m) := by
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨N.presheaf, N.isSheaf⟩
  refine F.existsUnique_gluing' (fun i ↦ W ⊓ U i) W (fun _ ↦ homOfLE inf_le_left)
    (by rw [← inf_iSup_eq, hU, inf_top_eq]) _ ?_
  intro i j
  rw [frameMap_restrict, frameMap_restrict]
  simp only [← Functor.map_comp_apply, ← op_comp]
  exact frameMap_eq hs hr (i := i) (j := j) _ _ _

private def framesMap (hU : ⨆ i, U i = ⊤) (W : X.Opens) (m : Γ(M, W)) :
    Γ(N, W) :=
  (exists_frameMap_gluing hs hr hU W m).exists.choose

include hr in
private theorem framesMap_restrict (hU : ⨆ i, U i = ⊤) {V W : X.Opens}
    {i : ι} (j : V ⟶ W) (hi : V ≤ U i) (m : Γ(M, W)) :
    N.presheaf.map j.op (framesMap hs hr hU W m) =
      frameMap (t := t) hi hs (M.presheaf.map j.op m) := by
  let k : V ⟶ W ⊓ U i := homOfLE (le_inf j.le hi)
  have h := congrArg (N.presheaf.map k.op)
    ((exists_frameMap_gluing hs hr hU W m).exists.choose_spec i)
  rw [frameMap_restrict] at h
  simp only [← Functor.map_comp_apply, ← op_comp] at h
  rw [Subsingleton.elim (k ≫ (homOfLE inf_le_left : W ⊓ U i ⟶ W)) j] at h
  exact h

private theorem hom_ext_cover (hU : ⨆ i, U i = ⊤) {W : X.Opens} (n n' : Γ(N, W))
    (h : ∀ i, N.presheaf.map (homOfLE (inf_le_left (b := U i))).op n =
      N.presheaf.map (homOfLE inf_le_left).op n') : n = n' :=
  TopCat.Sheaf.eq_of_locally_eq' (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    (fun i ↦ W ⊓ U i) W (fun _ ↦ homOfLE inf_le_left)
    (by rw [← inf_iSup_eq, hU, inf_top_eq]) n n' h

private def framesLinear (hU : ⨆ i, U i = ⊤) (W : X.Opens) :
    Γ(M, W) →ₗ[Γ(X, W)] Γ(N, W) where
  toFun := framesMap hs hr hU W
  map_add' x y := hom_ext_cover hU _ _ fun i ↦ by
    rw [map_add, framesMap_restrict hs hr hU _ (i := i) inf_le_right,
      framesMap_restrict hs hr hU _ (i := i) inf_le_right,
      framesMap_restrict hs hr hU _ (i := i) inf_le_right, map_add, map_add]
  map_smul' r m := hom_ext_cover hU _ _ fun i ↦ by
    rw [RingHom.id_apply, N.map_smul, framesMap_restrict hs hr hU _ (i := i) inf_le_right,
      framesMap_restrict hs hr hU _ (i := i) inf_le_right]
    rw [M.map_smul]
    exact (frameMap (t := t) (i := i) (W := W ⊓ U i) inf_le_right hs).map_smul _ _

private def framesHom (hU : ⨆ i, U i = ⊤) : M ⟶ N where
  val :=
    { app := fun W ↦ ModuleCat.ofHom (framesLinear hs hr hU W.unop)
      naturality := by
        intro W V f
        ext m
        -- Both composites restrict to the same framed map on each member of the cover.
        apply hom_ext_cover hU
        intro i
        -- The presheaf map composes the two restrictions as maps of underlying sections.
        change N.presheaf.map (homOfLE inf_le_left : V.unop ⊓ U i ⟶ V.unop).op
            (framesMap hs hr hU V.unop (M.presheaf.map f m)) =
          N.presheaf.map (homOfLE inf_le_left : V.unop ⊓ U i ⟶ V.unop).op
            (N.presheaf.map f (framesMap hs hr hU W.unop m))
        let j : V.unop ⊓ U i ⟶ V.unop := homOfLE inf_le_left
        let k : V.unop ⊓ U i ⟶ W.unop := j ≫ f.unop
        have hk : k.op = f ≫ j.op := by simp [k]
        let x : Γ(M, W.unop) := m
        have hx := (Functor.map_comp_apply M.presheaf f j.op x).symm
        rw [← hk] at hx
        have hy := Functor.map_comp_apply N.presheaf f j.op (framesMap hs hr hU W.unop x)
        rw [← hk] at hy
        exact (framesMap_restrict hs hr hU j (i := i) inf_le_right _).trans
          ((congrArg (frameMap (t := t) (i := i) inf_le_right hs) hx).trans
            ((framesMap_restrict hs hr hU k (i := i) inf_le_right x).symm.trans hy)) }

include hr in
private theorem framesHom_app (hU : ⨆ i, U i = ⊤) {V W : X.Opens} {i : ι}
    (j : V ⟶ W) (hi : V ≤ U i) (m : Γ(M, W)) :
    N.presheaf.map j.op ((framesHom hs hr hU).app W m) =
      frameMap (t := t) hi hs (M.presheaf.map j.op m) :=
  framesMap_restrict hs hr hU j hi m

/-- A morphism out of a line bundle is determined by its values on sections
that give frames on an open cover. -/
theorem hom_ext_of_covering_sections (hU : ⨆ i, U i = ⊤)
    (hs : ∀ i, U i ≤ M.nonvanishingLocus (s i)) {φ ψ : M ⟶ N}
    (h : ∀ i, φ.app ⊤ (s i) = ψ.app ⊤ (s i)) : φ = ψ := by
  refine hom_ext _ _ fun W ↦ ?_
  ext m
  apply hom_ext_cover hU
  intro i
  let V := W ⊓ U i
  let j : V ⟶ W := homOfLE inf_le_left
  change N.presheaf.map j.op (φ.app W m) = N.presheaf.map j.op (ψ.app W m)
  have hφ := φ.mapPresheaf.naturality_apply j.op m
  have hψ := ψ.mapPresheaf.naturality_apply j.op m
  simp only [mapPresheaf_app] at hφ hψ
  rw [← hφ, ← hψ]
  obtain ⟨r, hr⟩ := M.surjective_smul_of_le_nonvanishingLocus
    (le_nonvanishingLocus_res ((inf_le_right (a := W)).trans (hs i)))
    (M.presheaf.map j.op m)
  have hφs := φ.mapPresheaf.naturality_apply V.leTop.op (s i)
  have hψs := ψ.mapPresheaf.naturality_apply V.leTop.op (s i)
  simp only [mapPresheaf_app] at hφs hψs
  rw [← hr, φ.app_smul, ψ.app_smul, hφs, hψs, h i]

variable [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X N]

variable (M N) in
/-- Line bundles with the same ratios in covering families of frame sections are isomorphic
by an isomorphism taking each section in the first family to its counterpart. -/
theorem exists_iso_of_sectionRatios (hU : ⨆ i, U i = ⊤)
    (hs : ∀ i, U i ≤ M.nonvanishingLocus (s i))
    (ht : ∀ i, U i ≤ N.nonvanishingLocus (t i))
    (hRatio : ∀ (i j : ι) (r : Γ(X, U i)),
      r • M.presheaf.map (U i).leTop.op (s i) = M.presheaf.map (U i).leTop.op (s j) →
        r • N.presheaf.map (U i).leTop.op (t i) = N.presheaf.map (U i).leTop.op (t j)) :
    ∃ e : M ≅ N, ∀ i, e.hom.app ⊤ (s i) = t i := by
  have hr (i j : ι) :=
    hRatio i j _ (M.sectionRatio_smul _ _ (le_nonvanishingLocus_res (hs i)))
  let φ : M ⟶ N := framesHom hs hr hU
  have hφ (i : ι) : φ.app ⊤ (s i) = t i := by
    apply hom_ext_cover hU
    intro j
    dsimp only [φ]
    rw [framesHom_app hs hr hU (t := t) (i := j) _ inf_le_right]
    have he := congrArg (N.presheaf.map (homOfLE (inf_le_right (a := ⊤) (b := U j))).op)
      (frameMap_section hs hr j i)
    rw [frameMap_restrict] at he
    simp only [← Functor.map_comp_apply, ← op_comp] at he
    exact he
  have hψ (i j : ι) :
      N.sectionRatio (N.presheaf.map (U i).leTop.op (t j))
        (N.presheaf.map (U i).leTop.op (t i)) (le_nonvanishingLocus_res (ht i)) •
        M.presheaf.map (U i).leTop.op (s i) = M.presheaf.map (U i).leTop.op (s j) := by
    rw [(N.sectionRatio_eq_iff _).mpr (hr i j), M.sectionRatio_smul]
  let ψ : N ⟶ M := framesHom ht hψ hU
  have hcomp {P Q : X.Modules}
      [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X P]
      [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X Q]
      {a : ι → Γ(P, ⊤)} {b : ι → Γ(Q, ⊤)}
      (ha : ∀ i, U i ≤ P.nonvanishingLocus (a i))
      (hb : ∀ i, U i ≤ Q.nonvanishingLocus (b i))
      (hab : ∀ i j, P.sectionRatio (P.presheaf.map (U i).leTop.op (a j))
        (P.presheaf.map (U i).leTop.op (a i)) (le_nonvanishingLocus_res (ha i)) •
        Q.presheaf.map (U i).leTop.op (b i) = Q.presheaf.map (U i).leTop.op (b j))
      (hba : ∀ i j, Q.sectionRatio (Q.presheaf.map (U i).leTop.op (b j))
        (Q.presheaf.map (U i).leTop.op (b i)) (le_nonvanishingLocus_res (hb i)) •
        P.presheaf.map (U i).leTop.op (a i) = P.presheaf.map (U i).leTop.op (a j)) :
      framesHom ha hab hU ≫ framesHom hb hba hU = 𝟙 P := by
    apply Scheme.Modules.hom_ext
    intro W
    ext m
    apply hom_ext_cover hU
    intro i
    simp only [Hom.comp_app, Hom.id_app, ConcreteCategory.comp_apply, ConcreteCategory.id_apply]
    rw [framesHom_app hb hba hU _ (inf_le_right (b := U i)),
      framesHom_app ha hab hU _ (inf_le_right (b := U i))]
    obtain ⟨r, hr⟩ := P.surjective_smul_of_le_nonvanishingLocus
      (le_nonvanishingLocus_res ((inf_le_right (a := W)).trans (ha i)))
      (P.presheaf.map (homOfLE inf_le_left).op m)
    rw [← hr, frameMap_smul_basis, frameMap_smul_basis]
  exact ⟨⟨φ, ψ, hcomp hs ht hr hψ, hcomp ht hs hψ hr⟩, hφ⟩

end

section

variable {X : Scheme.{u}} {ι : Type*} (M N : X.Modules)
  [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M]
  [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X N]
  (s : ι → Γ(M, ⊤)) (t : ι → Γ(N, ⊤)) (U : ι → X.Opens)
  (hs : ∀ i, U i ≤ M.nonvanishingLocus (s i))
  (ht : ∀ i, U i ≤ N.nonvanishingLocus (t i))
  (hr : ∀ i j,
    M.sectionRatio (M.presheaf.map (U i).leTop.op (s j)) (M.presheaf.map (U i).leTop.op (s i))
        (M.le_nonvanishingLocus_map (U i).leTop (s i) (hs i)) =
      N.sectionRatio (N.presheaf.map (U i).leTop.op (t j)) (N.presheaf.map (U i).leTop.op (t i))
        (N.le_nonvanishingLocus_map (U i).leTop (t i) (ht i)))
  (hU : ⨆ i, U i = ⊤)

include hr hU in
private theorem exists_isoOfSectionRatios : ∃ e : M ≅ N, ∀ i, e.hom.app ⊤ (s i) = t i := by
  apply M.exists_iso_of_sectionRatios N hU hs ht
  intro i j r h
  rw [← (M.sectionRatio_eq_iff (le_nonvanishingLocus_res (hs i))).2 h,
    hr i j, N.sectionRatio_smul]

/-- The isomorphism between two invertible sheaves with matching section ratios on a cover. -/
def isoOfSectionRatios : M ≅ N :=
  (exists_isoOfSectionRatios M N s t U hs ht hr hU).choose

/-- The isomorphism constructed from ratios sends each specified section to its counterpart. -/
@[simp]
theorem isoOfSectionRatios_hom_app (j : ι) :
    (isoOfSectionRatios M N s t U hs ht hr hU).hom.app ⊤ (s j) = t j :=
  (exists_isoOfSectionRatios M N s t U hs ht hr hU).choose_spec j

/-- A morphism sending every specified section to its counterpart is the comparison morphism. -/
theorem eq_isoOfSectionRatios_hom (φ : M ⟶ N) (hφ : ∀ i, φ.app ⊤ (s i) = t i) :
    φ = (isoOfSectionRatios M N s t U hs ht hr hU).hom :=
  hom_ext_of_covering_sections hU hs fun i ↦
    (hφ i).trans (isoOfSectionRatios_hom_app M N s t U hs ht hr hU i).symm

end

end AlgebraicGeometry.Scheme.Modules
