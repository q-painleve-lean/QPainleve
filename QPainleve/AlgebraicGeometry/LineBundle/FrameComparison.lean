/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.LineBundle.Ratio
import TauCeti.Algebra.Category.ModuleCat.Sheaf.Hom
import TauCeti.AlgebraicGeometry.Modules.AffineRestriction

/-!
# Comparing line bundles by their section ratios

Families of sections of two line bundles with the same ratios on a common
nonvanishing cover determine a unique section-preserving isomorphism.
The local maps are glued using SheafOfModules.glueOfOpenCover.
-/

public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u v

variable {X : Scheme.{u}} (M N : X.Modules)
  [SheafOfModules.isInvertible X M] [SheafOfModules.isInvertible X N]

variable {ι : Type v} (s : ι → Γ(M, ⊤)) (t : ι → Γ(N, ⊤))
  (U : ι → X.Opens) (hs : ∀ i, U i ≤ M.nonvanishingLocus (s i))
  (ht : ∀ i, U i ≤ N.nonvanishingLocus (t i))

private def frameComparison (i : ι) {V : X.Opens} (hV : V ≤ U i) :
    Γ(M, V) ≃ₗ[Γ(X, V)] Γ(N, V) :=
  (M.sectionFrame (M.presheaf.map V.leTop.op (s i))
    (M.le_nonvanishingLocus_map V.leTop (s i) (hV.trans (hs i)))).symm ≪≫ₗ
      N.sectionFrame (N.presheaf.map V.leTop.op (t i))
        (N.le_nonvanishingLocus_map V.leTop (t i) (hV.trans (ht i)))

private theorem frameComparison_apply (i : ι) {V : X.Opens} (hV : V ≤ U i) (m : Γ(M, V)) :
    frameComparison M N s t U hs ht i hV m =
      M.sectionRatio m (M.presheaf.map V.leTop.op (s i))
        (M.le_nonvanishingLocus_map V.leTop (s i) (hV.trans (hs i))) •
          N.presheaf.map V.leTop.op (t i) := by
  simp [frameComparison]

private theorem frameComparison_naturality (i : ι) {V W : X.Opens} (j : W ⟶ V)
    (hV : V ≤ U i) (m : Γ(M, V)) :
    N.presheaf.map j.op (frameComparison M N s t U hs ht i hV m) =
      frameComparison M N s t U hs ht i (j.le.trans hV) (M.presheaf.map j.op m) := by
  rw [frameComparison_apply, frameComparison_apply, N.map_smul, M.map_sectionRatio]
  have hj : V.leTop.op ≫ j.op = W.leTop.op := Subsingleton.elim _ _
  simp only [← Functor.map_comp_apply, hj]

private def frameComparisonOn (i : ι) : M.over (U i) ⟶ N.over (U i) where
  val.app V := ModuleCat.ofHom (R := Γ(X, V.unop.left))
    (frameComparison M N s t U hs ht i V.unop.hom.le).toLinearMap
  val.naturality := by
    intro V W φ
    ext m
    exact (frameComparison_naturality M N s t U hs ht i φ.unop.left V.unop.hom.le m).symm

variable (hr : ∀ i j,
  M.sectionRatio (M.presheaf.map (U i).leTop.op (s j)) (M.presheaf.map (U i).leTop.op (s i))
      (M.le_nonvanishingLocus_map (U i).leTop (s i) (hs i)) =
    N.sectionRatio (N.presheaf.map (U i).leTop.op (t j)) (N.presheaf.map (U i).leTop.op (t i))
        (N.le_nonvanishingLocus_map (U i).leTop (t i) (ht i)))

include hr in
private theorem frameComparison_sections (i j : ι) {V : X.Opens} (hV : V ≤ U i) :
    frameComparison M N s t U hs ht i hV (M.presheaf.map V.leTop.op (s j)) =
      N.presheaf.map V.leTop.op (t j) := by
  have h := congrArg (X.presheaf.map (homOfLE hV).op) (hr i j)
  have hi : (U i).leTop.op ≫ (homOfLE hV).op = V.leTop.op := Subsingleton.elim _ _
  simp only [M.map_sectionRatio, N.map_sectionRatio, ← Functor.map_comp_apply, hi] at h
  rw [frameComparison_apply, h, N.sectionRatio_smul]

include hr in
private theorem frameComparison_compatible (i j : ι) (V : X.Opens)
    (hi : V ≤ U i) (hj : V ≤ U j) (m : Γ(M, V)) :
    (frameComparisonOn M N s t U hs ht i).val.app (op (Over.mk (homOfLE hi))) m =
      (frameComparisonOn M N s t U hs ht j).val.app (op (Over.mk (homOfLE hj))) m := by
  obtain ⟨a, rfl⟩ := (M.sectionFrame (M.presheaf.map (V).leTop.op (s j))
    (M.le_nonvanishingLocus_map V.leTop (s j) (hj.trans (hs j)))).surjective m
  -- The slice component is the linear equivalence on the underlying open.
  change frameComparison M N s t U hs ht i hi (M.sectionFrame _ _ a) =
    frameComparison M N s t U hs ht j hj (M.sectionFrame _ _ a)
  rw [sectionFrame_apply, (frameComparison M N s t U hs ht i hi).map_smul,
    (frameComparison M N s t U hs ht j hj).map_smul,
    frameComparison_sections M N s t U hs ht hr i j hi,
    frameComparison_sections M N s t U hs ht hr j j hj]

variable (hU : ⨆ i, U i = ⊤)

private def sectionRatiosHom : M ⟶ N :=
  SheafOfModules.glueOfOpenCover (X := X.toTopCat) M N U hU
    (frameComparisonOn M N s t U hs ht) (frameComparison_compatible M N s t U hs ht hr)

private theorem sectionRatiosHom_app_of_le (i : ι) (V : X.Opens) (hV : V ≤ U i)
    (m : Γ(M, V)) :
    (sectionRatiosHom M N s t U hs ht hr hU).app V m =
      frameComparison M N s t U hs ht i hV m :=
  SheafOfModules.glueOfOpenCover_app (X := X.toTopCat) M N U hU
    (frameComparisonOn M N s t U hs ht) (frameComparison_compatible M N s t U hs ht hr) i V hV m

include hU in
private theorem isIso_sectionRatiosHom : IsIso (sectionRatiosHom M N s t U hs ht hr hU) := by
  let A := {V : X.affineOpens // ∃ i, V.val ≤ U i}
  have hA : ⨆ V : A, V.val.val = ⊤ := top_unique <| fun x _ ↦ by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hU.ge (Set.mem_univ x))
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, hle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hi (U i).is_open'
    exact Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, i, hle⟩, hx⟩
  refine Hom.isIso_of_bijective_app _ (fun V : A ↦ V.val.property) hA fun V ↦ ?_
  obtain ⟨i, hi⟩ := V.property
  rw [show ((sectionRatiosHom M N s t U hs ht hr hU).app V.val.val : _ → _) =
      frameComparison M N s t U hs ht i hi from
    funext (sectionRatiosHom_app_of_le M N s t U hs ht hr hU i _ hi)]
  exact (frameComparison M N s t U hs ht i hi).bijective

/-- The isomorphism between two invertible sheaves with matching section ratios on a cover. -/
def isoOfSectionRatios : M ≅ N :=
  have := isIso_sectionRatiosHom M N s t U hs ht hr hU
  asIso (sectionRatiosHom M N s t U hs ht hr hU)

/-- The isomorphism constructed from ratios sends each specified section to its counterpart. -/
@[simp]
theorem isoOfSectionRatios_hom_app (j : ι) :
    (isoOfSectionRatios M N s t U hs ht hr hU).hom.app ⊤ (s j) = t j := by
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩ U ⊤ (fun i ↦ (U i).leTop)
    (by rw [hU]) _ _ fun i ↦ ?_
  let φ := sectionRatiosHom M N s t U hs ht hr hU
  have h := φ.mapPresheaf.naturality_apply (U i).leTop.op (s j)
  simp only [mapPresheaf_app] at h
  -- The hom of asIso is the glued morphism.
  change N.presheaf.map (U i).leTop.op (φ.app ⊤ (s j)) = N.presheaf.map (U i).leTop.op (t j)
  rw [← h, sectionRatiosHom_app_of_le M N s t U hs ht hr hU i _ le_rfl]
  exact frameComparison_sections M N s t U hs ht hr i j le_rfl

/-- A morphism sending every specified section to its counterpart is the glued isomorphism. -/
theorem eq_isoOfSectionRatios_hom (φ : M ⟶ N)
    (hφ : ∀ i, φ.app ⊤ (s i) = t i) :
    φ = (isoOfSectionRatios M N s t U hs ht hr hU).hom := by
  refine SheafOfModules.glueOfOpenCover_unique (X := X.toTopCat) M N U hU
    (frameComparisonOn M N s t U hs ht) (frameComparison_compatible M N s t U hs ht hr)
    φ fun i V hi m ↦ ?_
  let e := M.sectionFrame (M.presheaf.map V.leTop.op (s i))
    (M.le_nonvanishingLocus_map V.leTop (s i) (hi.trans (hs i)))
  let m' : Γ(M, V) := m
  obtain ⟨a, ha⟩ := e.surjective m'
  have hnat : φ.app V (M.presheaf.map V.leTop.op (s i)) =
      N.presheaf.map V.leTop.op (t i) := by
    rw [← hφ i]
    exact φ.mapPresheaf.naturality_apply V.leTop.op (s i)
  -- The local morphism is evaluated on the underlying open of the slice.
  change φ.app V m' = frameComparison M N s t U hs ht i hi m'
  rw [← ha]
  simp only [e, sectionFrame_apply]
  rw [φ.app_smul, hnat, (frameComparison M N s t U hs ht i hi).map_smul,
    frameComparison_sections M N s t U hs ht hr i i hi]

end AlgebraicGeometry.Scheme.Modules
