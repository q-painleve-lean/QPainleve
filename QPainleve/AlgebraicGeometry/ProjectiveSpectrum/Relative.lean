/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricBaseChange
import TauCeti.AlgebraicGeometry.Scheme.SpecOver

/-!
# Projective presentations over affine target opens

A map from a projective scheme to a separated scheme over the same coefficient ring
has a projective presentation over each affine open of its target. The closed graph
of the projective embedding and the map base changes to the required embedding.
-/

public section

open CategoryTheory Limits TopologicalSpace
open TauCeti.SymmetricAlgebra (homogeneousSubmodule projToSpec)
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
  [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of R))] [IsSeparated (Y ↘ Spec (.of R))]

/-- The preimage of an affine open of the separated target of a map from a projective
scheme is projective over the coordinate ring of that open. -/
theorem isProjectiveOver_morphismRestrict [X.IsProjectiveOver R]
    {W : Y.Opens} (hW : IsAffineOpen W) :
    letI : (f ⁻¹ᵁ W).toScheme.Over (Spec Γ(Y, W)) := ⟨(f ∣_ W) ≫ hW.isoSpec.hom⟩
    (f ⁻¹ᵁ W).toScheme.IsProjectiveOver Γ(Y, W) := by
  let A := Γ(Y, W)
  let S := Spec (CommRingCat.of R)
  let t := Y ↘ S
  let Z := f ⁻¹ᵁ W
  let g := (f ∣_ W) ≫ hW.isoSpec.hom
  let : Z.toScheme.Over (Spec A) := ⟨g⟩
  let : Algebra R A := t.sectionsAlgebra W
  have hA : Spec.map (CommRingCat.ofHom (algebraMap R A)) = hW.fromSpec ≫ t :=
    (t.fromSpec_toSpec hW).symm
  obtain ⟨M, _, _, _, j, _, hj⟩ := IsProjectiveOver.exists_isClosedImmersion (R := R) (X := X)
  let p := projToSpec R M
  let q := projToSpec A (A ⊗[R] M)
  let H := IsPullback.of_hasPullback p t
  have hjf : j ≫ p = f ≫ t := (comp_over j S).trans (comp_over f S).symm
  let graph : X ⟶ pullback p t := pullback.lift j f hjf
  have hfst : graph ≫ pullback.fst p t = j := pullback.lift_fst _ _ _
  have hsnd : graph ≫ pullback.snd p t = f := pullback.lift_snd _ _ _
  have hgraph : IsClosedImmersion graph := by
    let : IsSeparated t := ‹IsSeparated (Y ↘ Spec (.of R))›
    have : IsClosedImmersion (graph ≫ pullback.fst p t) := by
      rw [hfst]
      infer_instance
    exact .of_comp _ (pullback.fst p t)
  have hp := hA ▸ Proj.isPullback_symmetricAlgebra_baseChange R A M
  let b := H.lift _ (q ≫ hW.fromSpec) (by rw [hp.w, Category.assoc])
  have hb : IsPullback b q (pullback.snd p t) hW.fromSpec := hp.of_right' H
  have hg : g ≫ hW.fromSpec = Z.ι ≫ f := by
    rw [Category.assoc, hW.isoSpec_hom_fromSpec, morphismRestrict_ι]
  have HZ : IsPullback g Z.ι hW.fromSpec f :=
    (isPullback_morphismRestrict f W).of_iso (.refl _) hW.isoSpec (.refl _) (.refl _)
      (by simp [g]) (by simp [Z]) (by simp [hW.isoSpec_hom_fromSpec]) (by simp)
  have hcomm : (Z.ι ≫ j) ≫ p = g ≫ hW.fromSpec ≫ t := by
    rw [← Category.assoc g, hg, Category.assoc, Category.assoc, hjf]
  let jW := hp.lift (Z.ι ≫ j) g hcomm
  have hcorner : jW ≫ b = Z.ι ≫ graph := by
    apply pullback.hom_ext
    · rw [Category.assoc, H.lift_fst, hp.lift_fst, Category.assoc, hfst]
    · rw [Category.assoc, hb.w, hp.lift_snd_assoc, hg, Category.assoc, hsnd]
  have hpb : IsPullback jW Z.ι b graph := by
    refine IsPullback.of_right ?_ hcorner hb.flip
    have hjq : jW ≫ q = g := hp.lift_snd _ _ _
    rwa [hjq, hsnd]
  exact ⟨⟨A ⊗[R] M, inferInstance, inferInstance, inferInstance, jW,
    MorphismProperty.of_isPullback hpb.flip hgraph, ⟨hp.lift_snd _ _ _⟩⟩⟩

end AlgebraicGeometry.Scheme.Hom
