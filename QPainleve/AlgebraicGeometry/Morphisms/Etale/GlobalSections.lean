/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale

import Mathlib.Algebra.Group.Pi.Units
import Mathlib.RingTheory.Etale.Field
import Mathlib.AlgebraicGeometry.Group.Affine
import TauCeti.AlgebraicGeometry.Morphisms.Etale.Basic
import TauCeti.AlgebraicGeometry.ResidueField

/-!
# Global sections of split finite étale schemes

Over a separably closed field, the global sections of a finite étale scheme are
functions on its actual points. Pullback along a morphism over the field is
precomposition, also on units.

The construction transports Mathlib's
`Algebra.FormallyEtale.equivPiOfIsSepClosed` from the coordinate prime spectrum
to the scheme.
-/

public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

local notation "S" => Spec (CommRingCat.of k)
private abbrev globalSectionsAlgebra (f : X ⟶ S) : CommAlgCat k :=
  ((algΓ (CommRingCat.of k)).obj (Over.mk f)).unop

local notation "A" f:arg => globalSectionsAlgebra f

private theorem algebraEtale_globalSections (f : X ⟶ S) [IsFinite f] [Etale f] :
    Algebra.Etale k (A f) := by
  have : IsAffine X := isAffine_of_isAffineHom f
  let : Algebra k Γ(X, ⊤) := inferInstanceAs (Algebra k (A f))
  exact (f.etale_iff_algebraEtale (R := k) rfl).mp inferInstance

variable [IsSepClosed k]

/-- Global sections of a finite étale scheme over a separably closed field
are functions on its points. -/
def finiteEtaleGlobalSectionsEquiv (f : X ⟶ S) [IsFinite f] [Etale f] :
    Γ(X, ⊤) ≃+* (X → k) := by
  have : IsAffine X := isAffine_of_isAffineHom f
  have : Algebra.Etale k (A f) := algebraEtale_globalSections f
  exact ((Algebra.FormallyEtale.equivPiOfIsSepClosed k (A f)).trans
    (AlgEquiv.piCongrLeft' k (fun _ ↦ k) X.isoSpec.hom.homeomorph.toEquiv.symm)).toRingEquiv

/-- Under the split coordinates, pullback of sections is precomposition on points. -/
theorem finiteEtaleGlobalSectionsEquiv_appTop (f : X ⟶ S) (g : Y ⟶ S)
    [IsFinite f] [Etale f] [IsFinite g] [Etale g] (h : X ⟶ Y) (hh : h ≫ g = f)
    (a : Γ(Y, ⊤)) (x : X) :
    f.finiteEtaleGlobalSectionsEquiv (h.appTop a) x =
      g.finiteEtaleGlobalSectionsEquiv a (h x) := by
  have : IsAffine X := isAffine_of_isAffineHom f
  have : IsAffine Y := isAffine_of_isAffineHom g
  have : Algebra.Etale k (A f) := algebraEtale_globalSections f
  have : Algebra.Etale k (A g) := algebraEtale_globalSections g
  let hOver : Over.mk f ⟶ Over.mk g := Over.homMk h hh
  let hΓ := ((algΓ (CommRingCat.of k)).map hOver).unop
  have hmap : hΓ.hom.toRingHom = h.appTop.hom := by
    rfl
  have hn : PrimeSpectrum.comap hΓ.hom.toRingHom (X.toSpecΓ x) = Y.toSpecΓ (h x) := by
    rw [hmap]
    have he := congrArg (fun p : X ⟶ Spec Γ(Y, ⊤) ↦ p x)
      (Scheme.toSpecΓ_naturality h).symm
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, AlgebraicGeometry.Spec.map_apply] at he
    exact he
  have heaval (a : Γ(Y, ⊤)) : hΓ.hom a = h.appTop a :=
    DFunLike.congr_fun hmap a
  rw [← heaval]
  rw [finiteEtaleGlobalSectionsEquiv, finiteEtaleGlobalSectionsEquiv]
  -- The reindexing evaluates the affine-algebra coordinates at the two image primes.
  change Algebra.FormallyEtale.equivPiOfIsSepClosed k (A f) (hΓ.hom a) (X.toSpecΓ x) =
    Algebra.FormallyEtale.equivPiOfIsSepClosed k (A g) a (Y.toSpecΓ (h x))
  exact (Algebra.FormallyEtale.equivPiOfIsSepClosed_comap hΓ.hom a (X.toSpecΓ x)).symm.trans
    (congrArg (Algebra.FormallyEtale.equivPiOfIsSepClosed k (A g) a) hn)

/-- A scalar pulled back from the field has that value at each point. -/
@[simp]
theorem finiteEtaleGlobalSectionsEquiv_algebraMap (f : X ⟶ S) [IsFinite f] [Etale f]
    (a : k) (x : X) :
    f.finiteEtaleGlobalSectionsEquiv (f.appTop ((ΓSpecIso (CommRingCat.of k)).inv a)) x = a := by
  have : IsAffine X := isAffine_of_isAffineHom f
  have : Algebra.Etale k (A f) := algebraEtale_globalSections f
  rw [finiteEtaleGlobalSectionsEquiv]
  -- The pullback from the field is the structure map of the global-sections algebra.
  change Algebra.FormallyEtale.equivPiOfIsSepClosed k (A f) (algebraMap k (A f) a)
    (X.toSpecΓ x) = a
  exact congrFun ((Algebra.FormallyEtale.equivPiOfIsSepClosed k (A f)).commutes a) _

/-- The split coordinate at a point vanishes exactly when the residue of the section
at that point vanishes. -/
theorem finiteEtaleGlobalSectionsEquiv_apply_eq_zero_iff (f : X ⟶ S) [IsFinite f] [Etale f]
    (a : Γ(X, ⊤)) (x : X) :
    f.finiteEtaleGlobalSectionsEquiv a x = 0 ↔ X.Γevaluation x a = 0 := by
  let h := X.fromSpecResidueField x
  let g := h ≫ f
  have : IsIso g := by
    let : Algebra ((S).residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    have hsep : Algebra.IsSeparable ((S).residueField (f x)) (X.residueField x) := inferInstance
    have hbij : Function.Bijective (algebraMap ((S).residueField (f x)) (X.residueField x)) :=
      IsSepClosed.algebraMap_bijective _ _
    have : IsIso (f.residueFieldMap x) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr hbij
    have := (f x).isPrime
    have : IsIso (CommRingCat.ofHom (algebraMap k (f x).asIdeal.ResidueField)) :=
      (Ideal.algEquivResidueFieldOfField (f x).asIdeal).toRingEquiv.toCommRingCatIso.isIso_hom
    rw [show g = h ≫ f from rfl, ← f.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
    infer_instance
  have : IsFinite g := inferInstance
  have : Etale g := inferInstance
  let p : Spec (X.residueField x) := IsLocalRing.closedPoint _
  have hp : h p = x := X.fromSpecResidueField_apply x p
  have hsplit := finiteEtaleGlobalSectionsEquiv_appTop g f h rfl a p
  rw [hp] at hsplit
  have hg₀ : g.finiteEtaleGlobalSectionsEquiv (h.appTop a) p = 0 ↔ h.appTop a = 0 := by
    refine ⟨fun hh ↦ g.finiteEtaleGlobalSectionsEquiv.injective ?_, fun hh ↦ by rw [hh]; simp⟩
    rw [map_zero]
    funext q
    -- A section of the spectrum of a field has a single coordinate.
    change g.finiteEtaleGlobalSectionsEquiv (h.appTop a) q = 0
    exact (congrArg _ (Subsingleton.elim q p)).trans hh
  have hres := Scheme.Γevaluation_naturality_apply h p a
  rw [← hsplit, hg₀]
  calc
    h.appTop a = 0 ↔ X.Γevaluation (h p) a = 0 := by
      let ev := (Spec (X.residueField x)).Γevaluation p
      have : IsIso ev := Scheme.Spec.isIso_Γevaluation p
      have hev := (ConcreteCategory.bijective_of_isIso ev).1
      have hm := (h.residueFieldMap p).hom.injective
      rw [← hev.eq_iff, ← hres, map_zero, ← (h.residueFieldMap p).hom.map_zero, hm.eq_iff]
    _ ↔ X.Γevaluation x a = 0 := by rw [hp]

/-- Units in the global sections are pointwise nonzero scalars. -/
def finiteEtaleGlobalUnitsEquiv (f : X ⟶ S) [IsFinite f] [Etale f] :
    Γ(X, ⊤)ˣ ≃* (X → kˣ) :=
  (Units.mapEquiv f.finiteEtaleGlobalSectionsEquiv.toMulEquiv).trans MulEquiv.piUnits

/-- Taking the value of a split unit commutes with forgetting invertibility. -/
@[simp]
theorem val_finiteEtaleGlobalUnitsEquiv_apply (f : X ⟶ S) [IsFinite f] [Etale f]
    (a : Γ(X, ⊤)ˣ) (x : X) :
    ↑(f.finiteEtaleGlobalUnitsEquiv a x) = f.finiteEtaleGlobalSectionsEquiv a.val x := by
  rfl

/-- Pullback of a global unit in split coordinates is precomposition on points. -/
theorem finiteEtaleGlobalUnitsEquiv_appTop (f : X ⟶ S) (g : Y ⟶ S)
    [IsFinite f] [Etale f] [IsFinite g] [Etale g] (h : X ⟶ Y) (hh : h ≫ g = f)
    (a : Γ(Y, ⊤)ˣ) (x : X) :
    f.finiteEtaleGlobalUnitsEquiv (Units.map h.appTop.hom a) x =
      g.finiteEtaleGlobalUnitsEquiv a (h x) := by
  apply Units.ext
  simp only [val_finiteEtaleGlobalUnitsEquiv_apply, Units.coe_map]
  exact finiteEtaleGlobalSectionsEquiv_appTop f g h hh a.val x

end AlgebraicGeometry.Scheme.Hom
