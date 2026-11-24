/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.BaseChange
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.LocalTriviality
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Pullback
import TauCeti.LinearAlgebra.SymmetricAlgebra.BasisComparison

/-!
# Polynomial and symmetric-algebra presentations of projective space

A basis identifies the two projective spectra over the coefficient ring and identifies their
twisting sheaves. The comparison uses Tau Ceti's degreewise comparison for
`SymmetricAlgebra.equivMvPolynomial`.
-/

public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Proj CategoryTheory TauCeti.AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Proj

/-- The invertible sheaf `𝒪(m)` on the projective spectrum of a symmetric algebra. -/
@[expose]
def symmetricAlgebraTwistingBundle (k M : Type u) [CommRing k] [AddCommMonoid M] [Module k M]
    (m : ℤ) : InvertibleSheaf (Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule k M)) :=
  ⟨twistingSheaf _ m, inferInstance⟩

/-- The underlying module sheaf of the bundled twist is the native twisting sheaf. -/
@[simp]
theorem symmetricAlgebraTwistingBundle_obj (R M : Type u) [CommRing R] [AddCommMonoid M]
    [Module R M] (m : ℤ) :
    (symmetricAlgebraTwistingBundle R M m).obj =
      twistingSheaf (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M) m :=
  (rfl)

end AlgebraicGeometry.Proj

namespace Module.Basis

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R M : Type (max u v)} [CommRing R] [AddCommMonoid M] [Module R M] {ι : Type v}

local notation "𝒮" => TauCeti.SymmetricAlgebra.homogeneousSubmodule R M
local notation "𝒫" => MvPolynomial.homogeneousSubmodule ι R

/-- A basis identifies the symmetric algebra with polynomials in the same grading. -/
def toPolynomialGradedHom (b : Basis ι R M) : 𝒮 →+*ᵍ 𝒫 where
  toRingHom := (SymmetricAlgebra.equivMvPolynomial b).toRingHom
  map_mem {i x} hx := (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
    ((SymmetricAlgebra.equivMvPolynomial_isHomogeneous_iff R M b i x).mpr hx)

/-- The graded polynomial map sending each variable to its basis vector in the symmetric algebra. -/
def fromPolynomialGradedHom (b : Basis ι R M) : 𝒫 →+*ᵍ 𝒮 where
  toRingHom := (SymmetricAlgebra.equivMvPolynomial b).symm.toRingHom
  map_mem {i x} hx := (SymmetricAlgebra.equivMvPolynomial_isHomogeneous_iff R M b i _).mp
    (by
      have h : SymmetricAlgebra.equivMvPolynomial b
          ((SymmetricAlgebra.equivMvPolynomial b).symm.toRingHom x) = x :=
        (SymmetricAlgebra.equivMvPolynomial b).apply_symm_apply x
      rw [h]
      exact (MvPolynomial.mem_homogeneousSubmodule _ _).mp hx)

/-- The forward graded map is the basis-induced algebra equivalence on elements. -/
@[simp]
theorem toPolynomialGradedHom_apply (b : Basis ι R M) (x : SymmetricAlgebra R M) :
    b.toPolynomialGradedHom x = SymmetricAlgebra.equivMvPolynomial b x := (rfl)

/-- The reverse graded map acts by the inverse basis-induced algebra equivalence. -/
@[simp]
theorem fromPolynomialGradedHom_apply (b : Basis ι R M) (x : MvPolynomial ι R) :
    b.fromPolynomialGradedHom x = (SymmetricAlgebra.equivMvPolynomial b).symm x := (rfl)

/-- The graded comparison onto the polynomial algebra is surjective. -/
theorem toPolynomialGradedHom_surjective (b : Basis ι R M) :
    Function.Surjective (toPolynomialGradedHom b) :=
  (SymmetricAlgebra.equivMvPolynomial b).surjective

/-- The graded comparison onto the symmetric algebra is surjective. -/
theorem fromPolynomialGradedHom_surjective (b : Basis ι R M) :
    Function.Surjective (fromPolynomialGradedHom b) :=
  (SymmetricAlgebra.equivMvPolynomial b).symm.surjective

/-- The isomorphism from polynomial projective space to the projective spectrum of the
symmetric algebra obtained by choosing a basis of the module. -/
def polynomialProjIso (b : Basis ι R M) : Proj 𝒫 ≅ Proj 𝒮 :=
  mapIso (toPolynomialGradedHom b) (fromPolynomialGradedHom b)
    (SymmetricAlgebra.equivMvPolynomial b).apply_symm_apply
    (SymmetricAlgebra.equivMvPolynomial b).symm_apply_apply

/-- The forward projective comparison pulls back by the graded map to polynomials. -/
theorem polynomialProjIso_hom (b : Basis ι R M) :
    b.polynomialProjIso.hom = map (toPolynomialGradedHom b)
      (HomogeneousIdeal.irrelevant_le_map_of_surjective _ (toPolynomialGradedHom_surjective b)) :=
  mapIso_hom _ _ _ _

/-- The inverse projective comparison pulls variables back to the corresponding basis vectors. -/
theorem polynomialProjIso_inv (b : Basis ι R M) :
    b.polynomialProjIso.inv = map (fromPolynomialGradedHom b)
      (HomogeneousIdeal.irrelevant_le_map_of_surjective _ b.fromPolynomialGradedHom_surjective) :=
  mapIso_inv _ _ _ _

/-- The basis comparison preserves the projective structure morphisms. -/
@[reassoc (attr := simp)]
theorem polynomialProjIso_hom_over (b : Basis ι R M) :
    b.polynomialProjIso.hom ≫ TauCeti.SymmetricAlgebra.projToSpec R M = toSpecCoeff 𝒫 := by
  rw [polynomialProjIso_hom, TauCeti.SymmetricAlgebra.projToSpec_def, ← toSpecCoeff_def]
  apply map_toSpecCoeff
  intro r
  apply Subtype.ext
  rw [GradedRingHom.gradedZeroRingHom_apply_coe, SetLike.GradeZero.coe_algebraMap,
    SetLike.GradeZero.coe_algebraMap]
  exact (SymmetricAlgebra.equivMvPolynomial b).commutes r

/-- The projective comparison identifies the basic open of a basis vector with the
basic open of the corresponding polynomial variable. -/
@[simp]
theorem polynomialProjIso_hom_preimage_basicOpen_ι (b : Basis ι R M) (j : ι) :
    b.polynomialProjIso.hom ⁻¹ᵁ basicOpen 𝒮 (SymmetricAlgebra.ι R M (b j)) =
      basicOpen 𝒫 (MvPolynomial.X j) := by
  rw [polynomialProjIso_hom, map_preimage_basicOpen]
  simp [toPolynomialGradedHom]

/-- The basis comparison pulls the symmetric-algebra twist back to the same polynomial twist. -/
def polynomialProjIsoPullbackTwistingSheafIso (b : Basis ι R M) (m : ℤ) :
    (Scheme.Modules.pullback b.polynomialProjIso.hom).obj (twistingSheaf 𝒮 m) ≅
      twistingSheaf 𝒫 m := by
  rw [polynomialProjIso_hom]
  exact asIso (pullbackTwistingSheafMap (toPolynomialGradedHom b)
    (HomogeneousIdeal.irrelevant_le_map_of_surjective _ (toPolynomialGradedHom_surjective b)) m)

open LineBundleClass in
/-- A basis identifies the class of the symmetric-algebra twist with the same twist
on the polynomial projective spectrum. -/
theorem pullback_mk_symmetricAlgebraTwistingBundle {R V : Type (max v w)} {ι : Type w}
    [CommRing R] [AddCommMonoid V] [Module R V] (b : Basis ι R V) (m : ℤ)
    (L : InvertibleSheaf (Proj (MvPolynomial.homogeneousSubmodule ι R)))
    (hL : L.obj = twistingSheaf _ m) :
    pullback b.polynomialProjIso.hom (LineBundleClass.mk (symmetricAlgebraTwistingBundle R V m)) =
      LineBundleClass.mk L := by
  rw [pullback_mk, mk_eq_mk_iff]
  refine ⟨?_⟩
  rw [InvertibleSheaf.pullback_obj_obj, symmetricAlgebraTwistingBundle_obj, hL]
  exact b.polynomialProjIsoPullbackTwistingSheafIso m

end Module.Basis

namespace QPainleve

attribute [local instance] MvPolynomial.gradedAlgebra

/-- An equivalence of coordinate indices with `Fin 3` identifies the corresponding
polynomial projective spectrum with the standard projective plane. -/
@[expose]
def polynomialPlaneIso {k ι : Type u} [Field k] (ε : ι ≃ Fin 3) :
    Proj (MvPolynomial.homogeneousSubmodule ι k) ≅
      Proj (MvPolynomial.homogeneousSubmodule (Fin 3) k) :=
  let b := Pi.basisFun k (Fin 3)
  (b.reindex ε.symm).polynomialProjIso ≪≫ b.polynomialProjIso.symm

end QPainleve
