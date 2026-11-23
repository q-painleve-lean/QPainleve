/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections.RationalMap
public import Mathlib.AlgebraicGeometry.Birational.Composition

/-!
# Pullback of projective section presentations

A dominant morphism pulls back the nonvanishing open of a chosen section to
a dense open. The pulled-back sections present the composite rational map.
This comparison tracks a specified rational map when its presenting linear
system is pulled back along a blowup.
-/

public noncomputable section

open CategoryTheory MvPolynomial TopologicalSpace
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X Y : Scheme.{u}} {R ι : Type u} [CommRing R]
  (M : Y.Modules) [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible Y M]
  (f : Y ⟶ Spec (.of R)) (s : ι → Γ(M, ⊤)) (g : X ⟶ Y)

local notation "N" => Functor.obj (Scheme.Modules.pullback g) M
local notation "t" =>
  (fun j : ι ↦ Scheme.Hom.pullbackSectionsLE g M ⊤ ⊤
    (Eq.ge (Scheme.Hom.preimage_top g)) (s j) : ι → Γ(N, ⊤))
local notation "D[" i "]" => Scheme.Modules.nonvanishingLocus M (s i)
local notation "E[" i "]" => Scheme.Modules.nonvanishingLocus N (t i)
local notation "𝒜" => MvPolynomial.homogeneousSubmodule ι R
local notation "j[" i "]" =>
  Proj.awayι 𝒜 (MvPolynomial.X i)
    (Iff.mpr (mem_homogeneousSubmodule _ _) (isHomogeneous_X R i)) one_pos

/-- A covering family of sections remains covering after pullback, and its
projective morphism is the composite with the original projective morphism. -/
theorem toProjectiveSpace_pullback (h : ⨆ i, D[i] = ⊤) :
    (N).toProjectiveSpace (g ≫ f) t
        (by simpa only [nonvanishingLocus_pullbackSectionsLE, top_inf_eq] using
          g.iSup_preimage_eq_top h) =
      g ≫ M.toProjectiveSpace f s h := by
  have hE : ⨆ i, E[i] = ⊤ := by
    simpa only [nonvanishingLocus_pullbackSectionsLE, top_inf_eq] using g.iSup_preimage_eq_top h
  refine (X.openCoverOfIsOpenCover (fun i ↦ E[i]) (IsOpenCover.mk hE)).hom_ext _ _ ?_
  intro k
  let i : ι := k
  change (E[i]).ι ≫ (N).toProjectiveSpace (g ≫ f) t hE =
    (E[i]).ι ≫ g ≫ M.toProjectiveSpace f s h
  rw [← toProjectiveSpaceChart_awayι (N) (g ≫ f) t hE i, toProjectiveSpaceChart_pullback_assoc,
    toProjectiveSpaceChart_awayι, Scheme.Hom.resLE_comp_ι_assoc]

variable [PreirreducibleSpace X] [Nonempty Y] [IsDominant g]

/-- Pulling back the line bundle and its sections gives a presentation of the
precomposition of the original rational map by the dominant morphism. -/
theorem toRationalMap_partialMapToProjectiveSpace_pullback
    (i : ι) (hi : Dense (D[i] : Set Y)) :
    ((N).partialMapToProjectiveSpace (g ≫ f) t i
      (M.dense_nonvanishingLocus_pullbackSectionsLE_top g hi)).toRationalMap =
      g.toRationalMap.comp (M.partialMapToProjectiveSpace f s i hi).toRationalMap := by
  let p := M.partialMapToProjectiveSpace f s i hi
  let hd := M.dense_nonvanishingLocus_pullbackSectionsLE_top g hi
  let q := (N).partialMapToProjectiveSpace (g ≫ f) t i hd
  have hp : p.domain = D[i] := M.partialMapToProjectiveSpace_domain f s i hi
  have hq : q.domain = E[i] := (N).partialMapToProjectiveSpace_domain (g ≫ f) t i hd
  change q.toRationalMap = g.toPartialMap.toRationalMap.comp p.toRationalMap
  rw [RationalMap.toRationalMap_comp, PartialMap.toRationalMap_eq_iff]
  have hdom : (g.toPartialMap.comp p).domain = E[i] := by
    rw [PartialMap.comp_domain, hp]
    change (⊤ : X.Opens).ι ''ᵁ (X.topIso.hom ≫ g) ⁻¹ᵁ D[i] = E[i]
    rw [Hom.comp_preimage, topIso_hom, Hom.image_preimage_eq_opensRange_inf,
      Opens.opensRange_ι, top_inf_eq, nonvanishingLocus_pullbackSectionsLE, top_inf_eq]
  refine ⟨E[i], hd, hq.ge, hdom.ge, ?_⟩
  let e := g.resLE D[i] E[i] (by rw [nonvanishingLocus_pullbackSectionsLE, top_inf_eq])
  let U := g.toPartialMap.hom ⁻¹ᵁ p.domain
  let V := g.toPartialMap.domain.ι ''ᵁ U
  have hle : E[i] ≤ V := ((PartialMap.comp_domain g.toPartialMap p).symm.trans hdom).ge
  let b := (g.toPartialMap.domain.ι.isoImage U).inv ≫ g.toPartialMap.hom ∣_ p.domain
  have hb : b ≫ p.domain.ι = V.ι ≫ g := by
    dsimp only [b]
    rw [Category.assoc, morphismRestrict_ι]
    change (g.toPartialMap.domain.ι.isoImage U).inv ≫ U.ι ≫ g.toPartialMap.domain.ι ≫ g = _
    rw [Opens.isoImage_ι_inv_ι_assoc, homOfLE_ι_assoc]
  have hres : X.homOfLE hle ≫ b ≫ Y.homOfLE hp.le = e := by
    rw [← cancel_mono (D[i]).ι]
    simp only [Category.assoc, homOfLE_ι, hb, homOfLE_ι_assoc, Hom.resLE_comp_ι, e]
  have hqhom : X.homOfLE hq.ge ≫ q.hom = (N).toProjectiveSpaceChart (g ≫ f) t i ≫ j[i] := by
    rw [partialMapToProjectiveSpace_hom (N) (g ≫ f) t i hd, ← Category.assoc,
      homOfLE_homOfLE, homOfLE_rfl, Category.id_comp]
  change X.homOfLE hq.ge ≫ q.hom = X.homOfLE hdom.ge ≫ (g.toPartialMap.comp p).hom
  rw [hqhom, PartialMap.comp_hom, partialMapToProjectiveSpace_hom M f s i hi,
    toProjectiveSpaceChart_pullback_assoc]
  change e ≫ M.toProjectiveSpaceChart f s i ≫ j[i] =
    X.homOfLE hle ≫ (g.toPartialMap.domain.ι.isoImage U).inv ≫
      g.toPartialMap.hom ∣_ p.domain ≫ Y.homOfLE hp.le ≫ M.toProjectiveSpaceChart f s i ≫ j[i]
  simpa only [b, Category.assoc] using
    (congrArg (· ≫ M.toProjectiveSpaceChart f s i ≫ j[i]) hres).symm

end AlgebraicGeometry.Scheme.Modules
