/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality
public import TauCeti.AlgebraicGeometry.LineBundle.GlobalGeneration.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.LocalTriviality

import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.LineBundle.GlobalGeneration
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.SymmetricAlgebra
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections.TwistingSheaf
import TauCeti.AlgebraicGeometry.Curves.ProjectiveLine
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import TauCeti.AlgebraicGeometry.LineBundle.LocalRing
import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import TauCeti.AlgebraicGeometry.Scheme.GenericPoint.Basic

/-!
# Morphisms to the projective line

Two basis sections of a globally generated line bundle define a morphism to the
projective line. A nontrivial pullback of `𝒪(1)` implies dominance for morphisms from
integral schemes.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry LineBundleClass

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}}

local notation "S" => Spec (CommRingCat.of k)
local notation "𝒜" => TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Fin 2 → k)
local notation "T" => (ObjectProperty.FullSubcategory.mk (Proj.twistingSheaf 𝒜 1) inferInstance :
  InvertibleSheaf (projectiveLine k))

namespace AlgebraicGeometry.Scheme.Hom

/-- A morphism from an integral scheme to the projective line is dominant if the class
of its pullback of `𝒪(1)` is nontrivial. -/
theorem isDominant_of_pullback_twistingSheaf_ne_one [IsIntegral X]
    (f : X ⟶ projectiveLine k) (h : pullback f (LineBundleClass.mk T) ≠ 1) : IsDominant f := by
  rw [isDominant_iff_genericPoint_eq]
  by_contra hn
  let p := f (genericPoint X)
  have hdim := Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := projectiveLine k) k
  have hp : IsClosed ({p} : Set (projectiveLine k)) :=
    TauCeti.AlgebraicGeometry.Scheme.isClosed_singleton_of_ne_genericPoint hdim.le hn
  let j := (projectiveLine k).fromSpecResidueField p
  have : IsClosedImmersion j := isClosed_singleton_iff_isClosedImmersion.mp hp
  have hrange : Set.range f ⊆ {p} := by
    rintro _ ⟨x, rfl⟩
    exact ((genericPoint_specializes x).map f.continuous).mem_closed hp (Set.mem_singleton p)
  have hker : j.ker ≤ f.ker := by
    rw [Scheme.ker_fromSpecResidueField_eq_vanishingIdeal]
    apply IdealSheafData.vanishingIdeal_le_ker_of_range_subset f
    rw [Closeds.coe_mk, hp.closure_eq]
    exact hrange
  let g := IsClosedImmersion.lift j f hker
  have hg : g ≫ j = f := IsClosedImmersion.lift_fac _ _ _
  exact h (by rw [← hg, ← pullback_comp,
    Subsingleton.elim (pullback j (LineBundleClass.mk T)) 1, pullback_one])

end AlgebraicGeometry.Scheme.Hom

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

open _root_.AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A basis of two global sections of a globally generated line bundle gives a morphism
to the projective line over the base field whose pullback of `𝒪(1)` has the given class. -/
theorem exists_to_projectiveLine_of_basis [X.Over S] (L : InvertibleSheaf X)
    (v : Module.Basis (ULift.{u} (Fin 2)) k Γ(L.obj, ⊤)) (hglob : L.IsGloballyGenerated) :
    ∃ f : X ⟶ projectiveLine k, f.IsOver S ∧
      LineBundleClass.pullback f (LineBundleClass.mk T) = LineBundleClass.mk L := by
  let b := (Pi.basisFun k (Fin 2)).reindex Equiv.ulift.symm
  let hcover := hglob.iSup_nonvanishingLocus_basis_eq_top v
  let g := L.obj.toProjectiveSpace (X ↘ S) v hcover
  let f := g ≫ b.polynomialProjIso.hom
  have hbase : b.polynomialProjIso.hom ≫ (projectiveLine k ↘ S) =
      Proj.toSpecCoeff (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) k) :=
    b.polynomialProjIso_hom_over
  have hf : f ≫ (projectiveLine k ↘ S) = X ↘ S := by
    rw [Category.assoc, hbase,
      L.obj.toProjectiveSpace_toSpecCoeff (X ↘ S) v hcover]
  obtain ⟨a, -⟩ := L.obj.exists_iso_pullbackTwistingSheaf_toProjectiveSpace (X ↘ S) v hcover
  refine ⟨f, ⟨hf⟩, ?_⟩
  dsimp only [f]
  rw [← pullback_comp, pullback_mk, pullback_mk]
  exact mk_eq_mk_iff.mpr ⟨
    (Scheme.Modules.pullback g).mapIso (b.polynomialProjIsoPullbackTwistingSheafIso 1) ≪≫ a⟩

end TauCeti.AlgebraicGeometry.InvertibleSheaf
