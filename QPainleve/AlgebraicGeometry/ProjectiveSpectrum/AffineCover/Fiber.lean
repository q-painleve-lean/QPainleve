/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.AffineCover.Basic

/-!
# Affine covers near fibers of projective schemes

For a morphism from a projective scheme to a separated scheme over an infinite field, a bound
on the dimension of a scheme-theoretic fiber gives an affine cover of the same size over an
affine neighborhood of that fiber. In relative dimension one, the two opens and their affine
intersection give the cover used in cohomology and base change.
-/

public section

open CategoryTheory TopologicalSpace
open TauCeti.SymmetricAlgebra (homogeneousSubmodule)

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]

/-- A fiber of dimension strictly less than `n` has an affine neighborhood in the base
whose inverse image is covered by `n` affine opens. The neighborhood can be chosen
inside any prescribed open containing the base point. -/
theorem exists_affineCover_of_fiber_dim_lt [Infinite k] [X.IsProjectiveOver k]
    {y : Y} {V : Y.Opens} (hyV : y ∈ V) {n : ℕ} (hdim : topologicalKrullDim (f.fiber y) < n) :
    ∃ (W : Y.Opens), y ∈ W ∧ W ≤ V ∧ IsAffineOpen W ∧
      ∃ U : Fin n → (f ⁻¹ᵁ W).toScheme.Opens, (∀ j, IsAffineOpen (U j)) ∧ (⨆ j, U j) = ⊤ := by
  obtain ⟨M, _, _, _, j, hj, _⟩ :=
    IsProjectiveOver.exists_isClosedImmersion (R := k) (X := X)
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup k
  let : NoetherianSpace (f.fiber y) :=
    ((f.fiberι y ≫ j).isEmbedding.isInducing).noetherianSpace
  obtain ⟨v, hv⟩ := (f.fiberι y ≫ j).exists_basicOpen_ι_cover_of_dim_lt hdim
  let U (a : Fin n) := j ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule k M)
    (SymmetricAlgebra.ι k M (v a))
  have hU (a : Fin n) : IsAffineOpen (U a) :=
    (Proj.isAffineOpen_basicOpen _ _
      (TauCeti.SymmetricAlgebra.ι_mem_homogeneousSubmodule k M (v a)) Nat.one_pos).preimage j
  have hproper : IsProper f := by
    have : IsProper (f ≫ Y ↘ Spec (.of k)) := by rw [comp_over f (Spec (.of k))]; infer_instance
    exact IsProper.of_comp f (Y ↘ Spec (.of k))
  let A : X.Opens := ⨆ a, U a
  have hfiber : Set.range (f.fiberι y) ⊆ A := by
    rw [Set.range_subset_iff]
    have : (f.fiberι y) ⁻¹ᵁ A = ⊤ := by
      simpa only [A, U, preimage_iSup, comp_preimage] using hv
    intro z
    have hz : z ∈ (f.fiberι y) ⁻¹ᵁ A := this.symm ▸ Opens.mem_top z
    exact hz
  have hnear := f.isClosedMap.comap_nhds_le (A.isOpen.mem_nhdsSet.mpr
    (by simpa only [f.range_fiberι] using hfiber))
  obtain ⟨S, hyS, hS⟩ := Filter.mem_comap.mp hnear
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWVS⟩ :=
    Y.isBasis_affineOpens.mem_nhds_iff.mp
      (Filter.inter_mem (V.isOpen.mem_nhds hyV) hyS)
  have hWA : f ⁻¹ᵁ W ≤ A := fun _ hx ↦ hS (hWVS hx).2
  let iW := (f ⁻¹ᵁ W).ι
  refine ⟨W, hyW, fun _ hx ↦ (hWVS hx).1, hW, fun a ↦ iW ⁻¹ᵁ U a, fun a ↦ ?_, ?_⟩
  · have : IsAffine (U a) := hU a
    have : IsAffineHom ((U a).ι ≫ f) := by
      have : IsAffineHom (((U a).ι ≫ f) ≫ Y ↘ Spec (.of k)) := inferInstance
      exact IsAffineHom.of_comp _ (Y ↘ Spec (.of k))
    have ha := (hW.preimage ((U a).ι ≫ f)).image_of_isOpenImmersion (U a).ι
    apply iW.isAffineOpen_iff_of_isOpenImmersion.mp
    simpa only [iW, image_preimage_eq_opensRange_inf, Opens.opensRange_ι, comp_preimage,
      inf_comm (f ⁻¹ᵁ W) (U a)] using ha
  · rw [← preimage_iSup]
    exact top_unique (fun x _ ↦ hWA x.property)

end AlgebraicGeometry.Scheme.Hom
