/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Factorization
public import QPainleve.Geometry.Toric.Fan.ProjectiveSpace.Plane
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Plane.Isomorphism

import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.AlgebraicGeometry.IdealSheaf.Restriction
import QPainleve.Geometry.Toric.BaseChange.Fan
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced

/-!
# The terminal toric map of a degree-one plane resolution

A common logarithmic pole ideal on a degree-one resolution gives a regular map
between the prescribed toric planes. The factorization into a fan equivalence
and a translation recovers the resolving morphism on the entire point tower.
This supplies the terminal toric isomorphism in the factorization of
[Lutz, Theorem 8.4](https://arxiv.org/abs/2005.05010v3).
-/

public section

open AlgebraicGeometry CategoryTheory Module Multiplicative TauCeti.Toric
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra
open Scheme.IdealSheafData

namespace QPainleve.BlowupTower.IsClosedPointTower

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable (k : Type u) [Field k] [IsAlgClosed k]

local notation "S" => Spec (CommRingCat.of k)
local notation "P" => Proj (homogeneousSubmodule k (Fin 3 → k))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle k (Fin 3 → k) 1)
local notation "s" => (P ↘ S)
local notation "coords" => Pi.basisFun k (Fin 3)
local notation "degree" => Module.Basis.picardTwistEquiv coords
local notation "planeIso(" b "," h ")" =>
  Fan.projectivePlaneIso k b h ≪≫ Module.Basis.polynomialProjIso coords

variable {N N' : Type u} {V V' : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup N'] [AddCommGroup V'] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'}

local notation "D(" b "," h ")" =>
  Fan.toricBoundaryIdeal k (Fan.projectiveSpace b h)
    (Fan.IsComplete.nonempty_cones (Fan.isComplete_projectiveSpace b h))

/-- The terminal map of a specified degree-one resolution with a common pole ideal
is a unique fan equivalence followed by a unique torus translation. The two plane
fans may use different lattices. The factorization commutes with the given morphisms
on the whole resolution, including all exceptional curves. -/
theorem existsUnique_toric_factorization_of_plane_degree_one
    {Y : Scheme} {n : ℕ} {T : BlowupTower P n Y} (hT : IsClosedPointTower P T)
    (b : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)
    (b' : Basis (Fin 2) ℤ N') (hi' : IsIntegralLattice i')
    (g : Y ⟶ P) (hg : g ≫ s = T.toBase ≫ s) (hbir : Scheme.BirationalOver g (𝟙 P))
    (J : Y.IdealSheafData) :
    let : IsNoetherian P := isNoetherian_of_finiteType s
    let : Y.Over S := ⟨T.toBase ≫ s⟩
    letI : g.IsOver S := ⟨hg⟩
    letI : Smooth (Y ↘ S) := (hT.smoothOfRelativeDimension s).smooth
    let v := (T.picardMarking hT s).symm (Additive.ofMul (pullback g H))
    degree v.1 = 1 →
    (D(b,hi).comap (planeIso(b,hi)).inv).comap T.toBase =
      J * hT.ramificationIdealSheafToBase k →
    (D(b',hi').comap (planeIso(b',hi')).inv).comap g =
      J * ramificationIdealSheaf k g →
    let Ψ := Fan.projectiveSpace b' hi'
    letI : Nonempty Ψ.cones := (Fan.isComplete_projectiveSpace b' hi').nonempty_cones
    ∃! q : FanEquiv (Fan.projectiveSpace b hi) Ψ × (Multiplicative (N' →+ ℤ) →* kˣ),
      T.toBase ≫ (planeIso(b,hi)).inv ≫ q.1.toFanHom.finiteFanSchemeHom k ≫
        (Ψ.torusTranslationIso k q.2).hom ≫ (planeIso(b',hi')).hom = g := by
  intro _ _ _ hd hD hE Ψ
  let := (Fan.isComplete_projectiveSpace b hi).nonempty_cones
  let := (Fan.isComplete_projectiveSpace b' hi').nonempty_cones
  let e₀ := planeIso(b,hi)
  let e₁ := planeIso(b',hi')
  obtain ⟨f, ⟨hf, hfs, hboundary⟩, -⟩ :=
    hT.existsUnique_iso_of_plane_degree_one_of_eq_poleIdeal g hg hbir
      (D(b,hi).comap e₀.inv) (D(b',hi').comap e₁.inv) J hd hD hE
  let e := e₀ ≪≫ f ≪≫ e₁.symm
  let : e₀.hom.IsOver S := Fan.projectivePlaneIso_trans_polynomialProjIso_hom_isOver k b hi coords
  let : e₁.hom.IsOver S := Fan.projectivePlaneIso_trans_polynomialProjIso_hom_isOver k b' hi' coords
  have : f.hom.IsOver S := ⟨hfs⟩
  have : e.hom.IsOver S := by
    simpa only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc] using
      (inferInstanceAs ((e₀.hom ≫ f.hom ≫ e₁.inv).IsOver S))
  have ⟨hrad₀, hrad₁⟩ : D(b,hi).radical = D(b,hi) ∧ D(b',hi').radical = D(b',hi') := by
    constructor <;> apply (isReduced_subscheme_iff_radical_eq _).mp <;>
      rw [Fan.toricBoundaryIdeal_def k] <;> infer_instance
  have he : D(b',hi').comap e.hom = D(b,hi) := by
    have h := congrArg (fun I : (P).IdealSheafData ↦ I.comap e₀.hom) hboundary
    simpa only [e, Iso.trans_hom, Iso.symm_hom, radical_comap_of_isOpenImmersion,
      ← comap_comp, ← Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, comap_id,
      hrad₀, hrad₁] using h
  obtain ⟨q, hq, huniq⟩ := Fan.existsUnique_toric_factorization_of_boundary_iso k
    (Fan.isRegular_projectiveSpace b hi) (Fan.isRegular_projectiveSpace b' hi')
    (Fan.isComplete_projectiveSpace b hi) (Fan.isComplete_projectiveSpace b' hi')
    ((Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2))
    ((Module.finrank_eq_card_basis b').trans (Fintype.card_fin 2)) e he
  have hproj : T.toBase ≫ e₀.inv ≫ e.hom ≫ e₁.hom = g := by
    simpa only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id] using hf
  refine ⟨q, ?_, fun r hr ↦ huniq r ?_⟩
  · simpa only [Ψ, Category.assoc, reassoc_of% hq] using hproj
  · have := hT.isModification_of_smoothOfRelativeDimension_two s
    have : IsDominant (T.toBase ≫ e₀.inv) := inferInstance
    have := Ψ.isSeparated_finiteFanScheme k
    apply ext_of_isDominant (T.toBase ≫ e₀.inv)
    apply (cancel_mono e₁.hom).mp
    simpa only [Category.assoc] using hr.trans hproj.symm

end QPainleve.BlowupTower.IsClosedPointTower
