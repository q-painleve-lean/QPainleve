/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.Affine
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange

/-!
# Kernel ideals on affine schemes

If a morphism from an affine scheme factors through an affine open, its kernel ideal
is computed by the ring map on that open. In an affine pullback of a closed immersion,
the kernel is the extension of the original kernel. These compare the ring ideals with
Tau Ceti's ideal-sheaf base change theorems.
-/

public section

open CategoryTheory Limits
open AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.IsAffineOpen

/-- If `p` factors through an affine open `U` by `Spec.map ψ`, the kernel ideal of `p`
on `U` is the kernel of `ψ`. -/
theorem ideal_ker_eq_of_SpecMap_comp_fromSpec_eq {Y : Scheme} {U : Y.Opens} (hU : IsAffineOpen U)
    {R : CommRingCat} {ψ : Γ(Y, U) ⟶ R} {p : Spec R ⟶ Y} [QuasiCompact p]
    (hψ : Spec.map ψ ≫ hU.fromSpec = p) : p.ker.ideal ⟨U, hU⟩ = RingHom.ker ψ.hom := by
  have h := ker_eq_comap_of_isPullback_of_isOpenImmersion hU.fromSpec
    (IsPullback.of_vert_isIso_mono (snd := 𝟙 (Spec R)) ⟨by simpa using hψ⟩)
  rw [Scheme.Hom.ker_Spec_map, comap_fromSpec_eq_ofIdealTop] at h
  have h' := equivOfIsAffine.symm.injective h
  have hf := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso Γ(Y, U)).inv
  have h'' := congrArg (Ideal.comap (Scheme.ΓSpecIso Γ(Y, U)).inv.hom) h'
  simpa only [Ideal.comap_map_of_bijective _ hf] using h''.symm

end AlgebraicGeometry.IsAffineOpen

namespace CategoryTheory.IsPullback

open AlgebraicGeometry

/-- In a cartesian square of affine schemes, the ring ideal of the pulled-back closed
immersion is the extension of the ring ideal of the original closed immersion. -/
theorem ker_eq_map_of_SpecMap {R R' B B' : CommRingCat}
    {f : R ⟶ R'} {i : R ⟶ B} {f' : B ⟶ B'} {i' : R' ⟶ B'}
    [IsClosedImmersion (Spec.map i)]
    (H : IsPullback (Spec.map i') (Spec.map f') (Spec.map f) (Spec.map i)) :
    RingHom.ker i'.hom = (RingHom.ker i.hom).map f.hom := by
  have h := ker_eq_comap_of_isPullback (Spec.map i) H
  rw [Scheme.Hom.ker_Spec_map, Scheme.Hom.ker_Spec_map, comap_ofIdealTop_map_ΓSpecIso_inv] at h
  have hf := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R').inv
  have h' := congrArg (Ideal.comap (Scheme.ΓSpecIso R').inv.hom) (equivOfIsAffine.symm.injective h)
  simpa only [Ideal.comap_map_of_bijective _ hf] using h'

end CategoryTheory.IsPullback
