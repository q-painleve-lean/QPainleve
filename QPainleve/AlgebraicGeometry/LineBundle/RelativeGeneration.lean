/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Topology.JacobsonSpace
public import QPainleve.AlgebraicGeometry.LineBundle.Pullback
public import QPainleve.AlgebraicGeometry.Modules.Pullback.Sections

import TauCeti.AlgebraicGeometry.LineBundle.Functoriality
import TauCeti.AlgebraicGeometry.Modules.Sheaf

/-!
# Relative generation of line bundles

The evaluation map of a line bundle is an epimorphism if sections over inverse
images of base opens generate the bundle locally. Sections of a twist by the
pullback of a line bundle on the base can be used to check this condition, since
the twist can be trivialized near the image of the point.
-/

public section

open CategoryTheory MonoidalCategory TopologicalSpace
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Hom

open Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M : X.Modules} {L : InvertibleSheaf X}

/-- A morphism to a line bundle is an epimorphism if its local image contains a section
generating the line bundle at each point. -/
theorem epi_of_exists_mem_nonvanishingLocus (φ : M ⟶ L.obj)
    (h : ∀ x : X, ∃ (V : X.Opens) (s : Γ(M, V)), x ∈ L.obj.nonvanishingLocus (φ.app V s)) :
    Epi φ := by
  have : Sheaf.IsLocallySurjective ((toSheaf X).map φ) := by
    constructor
    intro U t x hx
    obtain ⟨V, s, hs⟩ := h x
    let W := U ⊓ L.obj.nonvanishingLocus (φ.app V s)
    let i : W ⟶ U := homOfLE inf_le_left
    let j : W ⟶ V := homOfLE (inf_le_right.trans (L.obj.nonvanishingLocus_le _))
    let s' := M.presheaf.map j.op s
    have hs' : φ.app W s' = L.obj.presheaf.map j.op (φ.app V s) :=
      φ.mapPresheaf.naturality_apply j.op s
    have hW : W ≤ L.obj.nonvanishingLocus (φ.app W s') := by
      rw [hs', L.obj.nonvanishingLocus_map]
      exact le_inf le_rfl inf_le_right
    obtain ⟨r, hr⟩ := L.obj.surjective_smul_of_le_nonvanishingLocus hW
      (L.obj.presheaf.map i.op t)
    exact ⟨W, i, ⟨r • s', (φ.app_smul r s').trans hr⟩, ⟨hx, hs⟩⟩
  exact (toSheaf X).epi_of_epi_map (Sheaf.epi_of_isLocallySurjective _)

end AlgebraicGeometry.Scheme.Modules.Hom

namespace AlgebraicGeometry.Scheme.Hom

open Scheme.Modules

variable {X Y : Scheme.{u}}

/-- On a Jacobson source, sections over inverse images of base opens that generate at all
closed points suffice for surjectivity of the evaluation map. -/
theorem epi_counit_of_exists_mem_nonvanishingLocus [JacobsonSpace X] (f : X ⟶ Y)
    (L : InvertibleSheaf X)
    (h : ∀ x : X, IsClosed ({x} : Set X) →
      ∃ (U : Y.Opens) (s : Γ(L.obj, f ⁻¹ᵁ U)), x ∈ L.obj.nonvanishingLocus s) :
    Epi ((pullbackPushforwardAdjunction f).counit.app L.obj) := by
  let ι := Σ U : Y.Opens, Γ(L.obj, f ⁻¹ᵁ U)
  let W : X.Opens := ⨆ a : ι, L.obj.nonvanishingLocus a.2
  have htop : W = ⊤ := by
    apply top_unique
    intro x _
    by_contra hx
    obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints (Z := (W : Set X)ᶜ)
      ⟨x, hx⟩ W.isOpen.isClosed_compl.isLocallyClosed
    obtain ⟨U, s, hs⟩ := h y hyc
    exact hy (Opens.mem_iSup.mpr ⟨⟨U, s⟩, hs⟩)
  apply Scheme.Modules.Hom.epi_of_exists_mem_nonvanishingLocus
  intro x
  obtain ⟨⟨U, s⟩, hs⟩ := Opens.mem_iSup.mp (htop.symm ▸ Opens.mem_top x)
  exact ⟨f ⁻¹ᵁ U, f.pullbackSections ((pushforward f).obj L.obj) U s,
    (f.counit_app_pullbackSections L.obj U s).symm ▸ hs⟩

private theorem exists_mem_nonvanishingLocus_of_twist (f : X ⟶ Y) (L : InvertibleSheaf X)
    (N : InvertibleSheaf Y) (x : X)
    (s : Γ((L.tensorProduct ((InvertibleSheaf.pullback f).obj N)).obj, ⊤))
    (hs : x ∈ (L.tensorProduct ((InvertibleSheaf.pullback f).obj N)).obj.nonvanishingLocus s) :
    ∃ (U : Y.Opens) (t : Γ(L.obj, f ⁻¹ᵁ U)), x ∈ L.obj.nonvanishingLocus t := by
  obtain ⟨U, -, hx, -, ⟨e⟩⟩ :=
    exists_isAffineOpen_mem_trivialization_le N.obj (Opens.mem_top (f x))
  let W := f ⁻¹ᵁ U
  let j := W.ι
  let P := (InvertibleSheaf.pullback f).obj N
  let B := L.tensorProduct P
  let eP : 𝟙_ W.toScheme.Modules ≅ (pullback j).obj P.obj :=
    unitIsoRestrictPullback f (W := W) le_rfl e ≪≫
      (restrictFunctorIsoPullback j).app _ ≪≫
      (pullback j).mapIso (eqToIso (InvertibleSheaf.pullback_obj_obj f N).symm)
  let eB : (pullback j).obj B.obj ≅ (pullback j).obj L.obj :=
    (pullback j).mapIso (L.tensorProductObjIso P) ≪≫
      asIso (Functor.OplaxMonoidal.δ (pullback j) L.obj P.obj) ≪≫
      whiskerLeftIso _ eP.symm ≪≫ ρ_ _
  let t := j.pullbackSectionsLE B.obj ⊤ ⊤ (by simp) s
  obtain ⟨z, hz⟩ := (bijective_pullbackSectionsLE_ι L.obj W ⊤ rfl).surjective (eB.hom.app ⊤ t)
  refine ⟨U, z, ?_⟩
  have hxt : (⟨x, hx⟩ : W.toScheme) ∈ ((pullback j).obj B.obj).nonvanishingLocus t := by
    have ht := nonvanishingLocus_pullbackSectionsLE B.obj j (U := ⊤) (V := ⊤) (by simp) s
    exact ht.symm ▸ ⟨Opens.mem_top _, hs⟩
  have he := (nonvanishingLocus_hom_app eB t).symm.trans
    (congrArg ((pullback j).obj L.obj).nonvanishingLocus hz.symm)
  rw [nonvanishingLocus_pullbackSectionsLE] at he
  exact (he ▸ hxt).2

/-- On a Jacobson source the evaluation map is surjective if at each closed point some
twist of the line bundle by a pullback from the base has a nonvanishing global section there. -/
theorem epi_counit_of_exists_twist_section [JacobsonSpace X] (f : X ⟶ Y)
    (L : InvertibleSheaf X)
    (h : ∀ x : X, IsClosed ({x} : Set X) → ∃ (N : InvertibleSheaf Y)
      (s : Γ((L.tensorProduct ((InvertibleSheaf.pullback f).obj N)).obj, ⊤)),
      x ∈ (L.tensorProduct ((InvertibleSheaf.pullback f).obj N)).obj.nonvanishingLocus s) :
    Epi ((pullbackPushforwardAdjunction f).counit.app L.obj) := by
  apply f.epi_counit_of_exists_mem_nonvanishingLocus L
  intro x hx
  obtain ⟨N, s, hs⟩ := h x hx
  exact exists_mem_nonvanishingLocus_of_twist f L N x s hs

end AlgebraicGeometry.Scheme.Hom
