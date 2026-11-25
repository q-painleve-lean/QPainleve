/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Morphisms.Smooth.Factorial
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Picard
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Smooth
public import TauCeti.AlgebraicGeometry.CartierDivisor.Excision

import QPainleve.AlgebraicGeometry.CartierDivisor.ZeroDivisor
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Ample
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.GlobalSections

/-!
# Degree-one prime divisors on the projective plane

A prime divisor whose class is `𝒪(1)` is the vanishing locus of a linear form. This follows
from the description of global sections of `𝒪(1)` as degree-one forms.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Scheme.IdealSheafData TauCeti.AlgebraicGeometry.LineBundleClass

namespace TauCeti.AlgebraicGeometry.CodimensionOnePoint

universe u

variable {k : Type u} [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "V₃" => (Fin 3 → k)
local notation "𝒜" => TauCeti.SymmetricAlgebra.homogeneousSubmodule k V₃
local notation "P" => Proj 𝒜
local notation "std" => Pi.basisFun k (Fin 3)
local notation "degree" => Module.Basis.picardTwistEquiv std
local notation "L" => Proj.symmetricAlgebraTwistingBundle k V₃ 1
local notation "linearForm" => _root_.SymmetricAlgebra.ι k V₃

/-- The complement of a degree-one prime divisor on the projective plane is the
basic open of a linear form. The degree is the Picard coordinate in which `𝒪(1)` has degree
one. -/
theorem exists_linearForm_of_projectivePlane_degree_eq_one (p : CodimensionOnePoint P) :
    letI := (P ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    degree (Additive.ofMul (primeDivisorClass p)) = 1 →
      ∃ v : V₃, ∀ x : P, x ∈ Proj.basicOpen 𝒜 (linearForm v) ↔
        x ∉ closure {(p : P)} := by
  intro hp
  let := (P ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let I : (P).IdealSheafData := vanishingIdeal ⟨closure {(p : P)}, isClosed_closure⟩
  let hI : I.IsEffectiveCartier := isEffectiveCartier_vanishingIdeal_closure_singleton p.property
  have hclass : LineBundleClass.mk hI.toInvertibleSheaf.dual = LineBundleClass.mk L := by
    rw [← inv_mk, ← primeDivisorClass_def]
    apply Additive.ofMul.injective
    apply (degree).injective
    rwa [(std).picardTwistEquiv_apply_twist]
  obtain ⟨u, hu⟩ := hI.exists_zeroIdeal_eq_dual
  obtain ⟨f⟩ := mk_eq_mk_iff.mp hclass
  let s := f.hom.app ⊤ u
  have hI' : (L).zeroIdeal s = I :=
    (hI.toInvertibleSheaf.dual.zeroIdeal_hom_app f u).trans hu
  let e := TauCeti.SymmetricAlgebra.homogeneousSubmoduleLinearEquivTwistingSheafTop 1 std
  let v := TauCeti.SymmetricAlgebra.homogeneousSubmoduleOneEquiv k V₃ (e.symm s)
  refine ⟨v, fun x ↦ ?_⟩
  have hopen : (L).obj.nonvanishingLocus s = Proj.basicOpen 𝒜 (linearForm v) := by
    let w := e.symm s
    have hw : Proj.toTwistingSheaf 𝒜 rfl ⊤ w = s := by
      simpa only [e, TauCeti.SymmetricAlgebra.homogeneousSubmoduleLinearEquivTwistingSheafTop_apply]
        using e.apply_symm_apply s
    rw [← hw]
    have h := Proj.twistingSheaf.nonvanishingLocus_toTwistingSheaf
      (fun (i : ULift.{u} (Fin 3)) ↦ linearForm (std i.down))
      (fun i ↦ TauCeti.SymmetricAlgebra.ι_mem_homogeneousSubmodule k V₃ _)
      (by simpa only [iSup_ulift] using
        TauCeti.SymmetricAlgebra.iSup_basicOpen_ι_eq_top k V₃ std (std).span_eq) 1 w
    -- The section formula is stated for the underlying twisting sheaf.
    change (Proj.twistingSheaf 𝒜 ((1 : ℕ) : ℤ)).nonvanishingLocus
      (Proj.toTwistingSheaf 𝒜 rfl ⊤ w) = _
    simpa only [v, w, TauCeti.SymmetricAlgebra.ι_homogeneousSubmoduleOneEquiv_apply] using! h
  rw [← hopen, (L).mem_nonvanishingLocus_iff_notMem_support_zeroIdeal, hI']
  simp only [I, ← SetLike.mem_coe, coe_support_vanishingIdeal, Closeds.coe_mk]

end TauCeti.AlgebraicGeometry.CodimensionOnePoint
