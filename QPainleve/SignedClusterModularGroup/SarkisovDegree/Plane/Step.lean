/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Plane.Logarithmic
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Plane.PolePropagation
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Plane.Terminal

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.Blowup.Tower.Centres
import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.PoleIdeal
import QPainleve.AlgebraicGeometry.Modules.Differentials.PoleIdeal
import QPainleve.Geometry.Toric.Fan.Mutation.Projective
import QPainleve.SignedClusterModularGroup.SarkisovDegree.Plane.Centres
import QPainleve.SignedClusterModularGroup.SarkisovDegree.Plane.Multiplicity
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced

/-!
# The plane step of logarithmic Sarkisov factorization

A specified logarithmic plane resolution is terminal in degree one.
Otherwise a proper high-order center selects either a vertex blowup or
the opposite-vertex blowup followed by a mutation and ruling exchange.

See [Lutz, Proposition 8.11 and Theorem 8.4][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=71
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module PointedCone
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra TauCeti.Toric
open Scheme.IdealSheafData

namespace QPainleve.BlowupTower.IsClosedPointTower

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "s" => (P ↘ S)
local notation "coords" => Pi.basisFun ℂ (Fin 3)
local notation "degree" => Module.Basis.picardTwistEquiv coords
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "X[" Φ "]" => Fan.algebraicRealization Φ
local notation "f[" Φ "]" => (X[Φ] ↘ S)
local notation "B[" Φ "," hc "]" => Fan.boundaryIdeal Φ (Fan.IsComplete.nonempty_cones hc)
local notation "Π[" b "," hi "]" => Fan.projectiveSpace b hi
local notation "eP[" b "," hi "]" =>
  Fan.projectivePlaneIso b hi ≪≫ Module.Basis.polynomialProjIso coords
local notation "E[" b "," hi "]" =>
  Scheme.IdealSheafData.comap (B[Π[b,hi],Fan.isComplete_projectiveSpace b hi]) (Iso.inv (eP[b,hi]))
local notation "mark[" T "," h "," f "," g "]" =>
  LinearEquiv.symm (BlowupTower.picardMarking T h f) (Additive.ofMul (pullback g H))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (d : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)

local notation "Π" => Π[d,hi]
local notation "eP" => eP[d,hi]
local notation "reg" => Fan.isRegular_projectiveSpace d hi
local notation "hc" => Fan.isComplete_projectiveSpace d hi
local notation "σ(" v ")" => Fan.projectiveSpaceMaximalCone d hi v
local notation "Φ(" v ")" => Fan.starSubdivisionAlong Π reg (Subtype.property (σ(v)))
local notation "subdiv(" v "," h ")" =>
  Fan.starSubdivisionAlong_isSubdivision Π reg (Subtype.property (σ(v))) h
local notation "π(" v "," h ")" => FanHom.algebraicMap (Fan.IsSubdivision.toFanHom (subdiv(v,h)))
local notation "rankTwo" => Eq.trans (Module.finrank_eq_card_basis d) (Fintype.card_fin 2)
local notation "pt" => IsLocalRing.closedPoint ℂ
local notation "vertex(" v ")" => (Fan.distinguishedPointHom Π (σ(v)) ≫ Iso.hom (eP)) pt

variable {Y : Scheme} {n : ℕ} {T : BlowupTower P n Y} (hT : IsClosedPointTower P T)

private theorem plane_baseCenter_cases
    (hle : (E[d,hi]).comap T.toBase ≤ hT.ramificationIdealSheafToBase ℂ) (j : Fin n) :
    (∃ v, vertex(v) = hT.baseCenter j) ∨
    (∃ (v : Option (Fin 2)) (hσ : (σ(v)).val ≠ ⊥) (b : Basis (Fin 2) ℤ N)
        (r : Fin 4 ≃ (Φ(v)).Ray) (c : ℂˣ),
      let ρ := r 2
      let u := ρ.binomialCenter rankTwo (b.detDualEquiv_self ρ.primitiveGenerator)
        (ρ.surjective_detCharacter b) c
      (fun l ↦ (r l).primitiveGenerator) = ![b 0, b 1, -b 0, (1 : ℤ) • b 0 - b 1] ∧
      (Π).starSubdivisionAlongRay reg (Subtype.property (σ(v))) hσ = r 0 ∧
      (eP).hom (π(v,hσ) (u pt)) = hT.baseCenter j) := by
  let : Nonempty (Π).cones := Fan.IsComplete.nonempty_cones hc
  let : SmoothOfRelativeDimension 2 f[Π] :=
    by simpa only [rankTwo, Fan.algebraicRealization_over] using
      (Π).smoothOfRelativeDimension_algebraicRealizationStructureMap reg
  let : Smooth f[Π] := SmoothOfRelativeDimension.smooth 2 _
  let := Fan.projectivePlaneIso_trans_polynomialProjIso_hom_isOver d hi coords
  let L := T.transport (eP).symm
  let hL := L.isLift.isClosedPointTower hT
  have he : L.iso.inv ≫ T.toBase = L.tower.toBase ≫ (eP).hom := by
    simpa only [Iso.symm_hom, Iso.symm_inv] using L.isLift.symm.hom_toBase
  have hram' : (hT.ramificationIdealSheafToBase ℂ).comap L.iso.inv =
      hL.ramificationIdealSheafToBase ℂ := by
    -- Composing the transported projection with the plane isomorphism adds no ramification.
    let : L.top.Over S := ⟨L.tower.toBase ≫ f[Π]⟩
    let : SmoothOfRelativeDimension 2 (L.top ↘ S) := hL.smoothOfRelativeDimension f[Π]
    let : Smooth (L.top ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    let : L.tower.toBase.IsOver S := ⟨rfl⟩
    let : (L.tower.toBase ≫ (eP).hom).IsOver S := inferInstance
    have hram := hT.comap_ramificationIdealSheafToBase ℂ L.iso.symm he
    simp only [Iso.symm_hom] at hram
    rw [hram,
      ramificationIdealSheaf_comp ℂ L.tower.toBase (eP).hom 2,
      ramificationIdealSheaf_eq_top_of_isOpenImmersion ℂ (eP).hom, comap_top, mul_top,
      ramificationIdealSheafToBase_def]
  have hle' : (B[Π,hc]).comap L.tower.toBase ≤ hL.ramificationIdealSheafToBase ℂ := by
    have h := comap_mono (f := L.iso.inv) hle
    dsimp only at h
    rwa [hram', ← comap_comp, ← comap_comp, he, Category.assoc,
      Iso.hom_inv_id, Category.comp_id] at h
  have hcenter := L.isLift.symm.hom_baseCenter hL hT j
  rcases Fan.projectivePlane_baseCenter_cases_of_totalTransform_le_ramification d hi hL hle' j with
    ⟨v, hv⟩ | ⟨v, hσ, b, r, c, hr, hnew, hp, -, -⟩
  · have h := Scheme.Hom.comp_apply (Fan.distinguishedPointHom Π (σ(v))) (eP).hom (pt : S)
    exact Or.inl ⟨v, h.trans ((congrArg (eP).hom hv).trans hcenter)⟩
  · exact Or.inr ⟨v, hσ, b, r, c, hr, hnew, (congrArg (eP).hom hp).trans hcenter⟩

section Link

variable {A : Scheme} [IsIntegral A] [A.Over S] [Smooth (A ↘ S)]
  {Φ : Fan i} (a : A ⟶ X[Φ]) [IsDominant a] (J : A.IdealSheafData)

local notation "mut[" b "," ρ "," h "]" =>
  Fan.mutationFan Φ b (Fan.Ray.primitiveGenerator_ne_zero ρ)
    (Fan.Ray.hull_primitiveGenerator_mem ρ) h

/-- The continuation of a resolved plane vertex subdivision. At a vertex the
subdivision already gives the next model. At a smooth edge center it is followed
by the binomial mutation and the exchange of the quadric rulings. The incoming
and outgoing projections are defined on the same resolving surface. -/
inductive ResolvesPlaneSarkisovLink : ℕ → (Ψ : Fan i) → (A ⟶ X[Ψ]) → Prop
  | vertex : ResolvesPlaneSarkisovLink 1 Φ a
  | edge (b : Basis (Fin 2) ℤ N) (ρ : Φ.Ray) (c : ℂˣ)
      (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones)
      (hΨ : (mut[b,ρ,hOpp]).IsRegular) (hcΨ : (mut[b,ρ,hOpp]).IsComplete)
      (b' : Basis (Fin 2) ℤ N) (r : Fin 4 ≃ (mut[b,ρ,hOpp]).Ray)
      (hr : (fun l ↦ (r l).primitiveGenerator) = ![b' 0, b' 1, -b' 0, (0 : ℤ) • b' 0 - b' 1])
      (p : A ⟶ X[mut[b,ρ,hOpp]]) (pOver : p.IsOver S)
      (hmap : letI : Nonempty Φ.cones := ⟨ρ.toCone⟩
        let μ := Φ.mutationPartialMap b (c : ℂ) ρ.primitiveGenerator_ne_zero
          ρ.hull_primitiveGenerator_mem hOpp
        a.toRationalMap.comp μ.toRationalMap = p.toRationalMap)
      (hpole : letI := pOver
        (B[mut[b,ρ,hOpp],hcΨ]).comap p = J * ramificationIdealSheaf ℂ p) :
      ResolvesPlaneSarkisovLink 0 (mut[b,ρ,hOpp])
        (p ≫ (Fan.quadricRulingExchange b' hΨ hcΨ r hr).toFanHom.algebraicMap)

end Link

variable (g : Y ⟶ P) (D : Y.IdealSheafData)
local notation "regΦ(" v ")" => Fan.isRegular_starSubdivisionAlong Π reg (Subtype.property (σ(v)))
local notation "hcΦ(" v "," h ")" => Iff.mpr (Fan.IsSubdivision.isComplete_iff (subdiv(v,h))) hc

/-- A decreasing block of the plane factorization with its regular projections.
The first projection lifts the prescribed plane projection through one vertex
subdivision. The final projection is marked by a closed-point tower over the
new Hirzebruch surface. Both plane maps and the pole divisor are retained on
the common nodal refinement. -/
structure PlaneSarkisovDecrease where
  /-- Vertex of the initial star subdivision. -/
  vertexIndex : Option (Fin 2)
  /-- The vertex cone is nonzero. -/
  vertexCone_ne_bot : (σ(vertexIndex)).val ≠ ⊥
  /-- Surface resolving the chosen block. -/
  resolving : Scheme
  /-- Map back to the original resolving surface. -/
  refinement : resolving ⟶ Y
  /-- Number of added nodal blowups. -/
  length : ℕ
  /-- At most one additional nodal blowup is needed. -/
  length_le_one : length ≤ 1
  /-- Final surface of the nodal refinement tower. -/
  top : Scheme
  /-- Nodal refinement tower of the original resolving surface. -/
  tower : BlowupTower Y length top
  /-- Every center of the refinement is nodal for the reduced total boundary. -/
  nodal : IsNodalBoundaryTower D (T.toBase ≫ s) (𝟙 Y) tower
  /-- Comparison of the common resolution with the nodal tower. -/
  refinementIso : resolving ≅ top
  /-- The comparison identifies the refinement map. -/
  refinementIso_comp : refinementIso.hom ≫ tower.toBase = refinement
  /-- The projection after the first vertex blowup. -/
  first : resolving ⟶ X[Φ(vertexIndex)]
  /-- The first projection lifts the specified plane projection. -/
  first_comp : first ≫ π(vertexIndex,vertexCone_ne_bot) ≫ (eP).hom = refinement ≫ T.toBase
  /-- The first projection is dominant. -/
  first_dominant : IsDominant first
  /-- The common resolution is integral. -/
  integral : IsIntegral resolving
  /-- Smoothness of the common resolution over the base field. -/
  smooth : let : resolving.Over S := ⟨first ≫ f[Φ(vertexIndex)]⟩
    SmoothOfRelativeDimension 2 (resolving ↘ S)
  /-- The first projection has the pole divisor of the refined resolution. -/
  first_pole : let : resolving.Over S := ⟨first ≫ f[Φ(vertexIndex)]⟩
    let : Smooth (resolving ↘ S) := smooth.smooth
    let : first.IsOver S := ⟨rfl⟩
    (B[Φ(vertexIndex),hcΦ(vertexIndex,vertexCone_ne_bot)]).comap first =
      (D.comap refinement).radical * ramificationIdealSheaf ℂ first
  /-- The returned fan. -/
  fan : Fan i
  /-- The returned fan is regular. -/
  regular : fan.IsRegular
  /-- The returned fan is complete. -/
  complete : fan.IsComplete
  /-- The returned toric surface is projective. -/
  projective : (X[fan]).IsProjectiveOver ℂ
  /-- Index of the returned Hirzebruch surface. -/
  index : ℕ
  /-- Frame of the returned Hirzebruch fan. -/
  basis : Basis (Fin 2) ℤ N
  /-- Ray numbering in the returned Hirzebruch frame. -/
  rays : Fin 4 ≃ fan.Ray
  /-- Primitive generators of the rays in the returned frame. -/
  rayGenerators : (fun l ↦ (rays l).primitiveGenerator) =
    ![basis 0, basis 1, -basis 0, (index : ℤ) • basis 0 - basis 1]
  /-- Number of centers of the returned point tower. -/
  centers : ℕ
  /-- Final surface of the returned point tower. -/
  model : Scheme
  /-- The returned point tower. -/
  modelTower : BlowupTower X[fan] centers model
  /-- The returned tower consists of closed-point blowups. -/
  closedPoint : IsClosedPointTower X[fan] modelTower
  /-- Identification of the common resolution with the returned tower. -/
  modelIso : resolving ≅ model
  /-- The continuation after the vertex subdivision realizes the specified links. -/
  link : let : resolving.Over S := ⟨first ≫ f[Φ(vertexIndex)]⟩
    let : IsIntegral resolving := integral
    let : IsDominant first := first_dominant
    let : Smooth (resolving ↘ S) := smooth.smooth
    ResolvesPlaneSarkisovLink first (D.comap refinement).radical index fan
      (modelIso.hom ≫ modelTower.toBase)
  /-- Pole factorization for the new point tower in its own coordinates. -/
  model_pole : let : Nonempty fan.cones := complete.nonempty_cones
    let : SmoothOfRelativeDimension 2 f[fan] :=
      Eq.mp (congrArg (fun n ↦ SmoothOfRelativeDimension n f[fan]) rankTwo)
        (fan.smoothOfRelativeDimension_algebraicRealizationStructureMap regular)
    (B[fan,complete]).comap modelTower.toBase =
      ((D.comap refinement).radical.comap modelIso.inv) * closedPoint.ramificationIdealSheafToBase ℂ
  /-- The transported morphism to the target plane is over the base field. -/
  target_over : (modelIso.inv ≫ refinement ≫ g) ≫ s = modelTower.toBase ≫ f[fan]
  /-- The transported morphism still resolves a birational map to the target plane. -/
  target_birational : Scheme.BirationalOver (modelIso.inv ≫ refinement ≫ g) (𝟙 P)
  /-- The returned fiber degree is positive and the bidegree strictly decreases. -/
  decreases : let : Nonempty fan.cones := complete.nonempty_cones
    let : SmoothOfRelativeDimension 2 f[fan] :=
      Eq.mp (congrArg (fun n ↦ SmoothOfRelativeDimension n f[fan]) rankTwo)
        (fan.smoothOfRelativeDimension_algebraicRealizationStructureMap regular)
    let w := mark[T,hT,s,g]
    let u := mark[modelTower,closedPoint,f[fan],(modelIso.inv ≫ refinement ≫ g)]
    let b := (fan.hirzebruchPicardBasis basis index regular rays rayGenerators).repr u.1 1
    0 < b ∧
      hirzebruchSarkisovBidegree b.toNat (∑ l, (-u.2 l).toNat) <
        planeSarkisovBidegree (degree w.1).toNat (∑ l, (-w.2 l).toNat)

section Decrease

variable {T : BlowupTower P (n + 1) Y} (hT : IsClosedPointTower P T)
  (g : Y ⟶ P) (hg : g ≫ s = T.toBase ≫ s) (hbir : Scheme.BirationalOver g (𝟙 P))
  (D : Y.IdealSheafData) (hD : D.IsEffectiveCartier)
  (hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ T.toBase ≫ s))
  (hpole : (E[d,hi]).comap T.toBase = D * hT.ramificationIdealSheafToBase ℂ)
  (j : Fin (n + 1)) (hfirst : ∀ l < j, hT.baseCenter l ≠ hT.baseCenter j)
  (hhigh : let w := mark[T,hT,s,g]; degree w.1 < 3 * (-w.2 j))

include hg hbir hN hpole hfirst hhigh in
private theorem plane_vertex_decrease (v : Option (Fin 2)) (hj : hT.baseCenter j = vertex(v)) :
    Nonempty (PlaneSarkisovDecrease d hi hT g D) := by
  let : Y.Over S := ⟨T.toBase ≫ s⟩
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension s
  let : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : T.toBase.IsOver S := ⟨rfl⟩
  -- This vertex link already resolves on the original surface, so use the empty nodal tower.
  obtain ⟨hσ, b, r, hr, Z, U, hU, e, ha, hP, hcomp, -, hPa, hPU, hs, hb, -, _, _, hpos, hlt⟩ :=
    hT.exists_sarkisov_decrease_of_logarithmic_plane_vertex
      d hi v j hj (fun l hl ↦ hj ▸ hfirst l hl)
      g hg hbir D (hT.ramificationIdealSheafToBase_def ℂ ▸ hpole) hhigh
  let a := e.hom ≫ U.toBase
  let : Nonempty (Φ(v)).cones := (hcΦ(v,hσ)).nonempty_cones
  let : SmoothOfRelativeDimension 2 f[Φ(v)] :=
    Eq.mp (congrArg (fun n ↦ SmoothOfRelativeDimension n f[Φ(v)]) rankTwo)
      ((Φ(v)).smoothOfRelativeDimension_algebraicRealizationStructureMap (regΦ(v)))
  let : IsIntegral Y := hT.isIntegral s
  let : IsModification U.toBase :=
    hU.isModification_of_smoothOfRelativeDimension_two f[Φ(v)]
  let : IsDominant a := inferInstanceAs (IsDominant (e.hom ≫ U.toBase))
  have hsmooth : SmoothOfRelativeDimension 2 (a ≫ f[Φ(v)]) :=
    ha.comp_over.symm ▸ hT.smoothOfRelativeDimension s
  have hrad : D.radical = D := (isReduced_subscheme_iff_radical_eq _).mp hN.isReduced
  refine ⟨{
    vertexIndex := v
    vertexCone_ne_bot := hσ
    resolving := Y
    refinement := 𝟙 Y
    length := 0
    length_le_one := by omega
    top := Y
    tower := .nil
    nodal := .nil
    refinementIso := Iso.refl Y
    refinementIso_comp := by simp
    first := a
    first_comp := by simpa only [Category.id_comp] using hcomp
    first_dominant := inferInstance
    integral := inferInstance
    smooth := hsmooth
    first_pole := ?_
    fan := Φ(v)
    regular := regΦ(v)
    complete := hcΦ(v,hσ)
    projective := hP
    index := 1
    basis := b
    rays := r
    rayGenerators := hr
    centers := n
    model := Z
    modelTower := U
    closedPoint := hU
    modelIso := e
    link := ?_
    model_pole := ?_
    target_over := by simpa only [Category.id_comp] using hs
    target_birational := by simpa only [Category.id_comp] using hb
    decreases := by simpa only [Category.id_comp, Nat.cast_one] using And.intro hpos hlt
  }⟩
  · simpa only [Scheme.IdealSheafData.comap_id, hrad] using hPa.trans
      (congrArg (D * ·) (ramificationIdealSheaf_congr ℂ (rfl : a = a)))
  · let : Y.Over S := ⟨a ≫ f[Φ(v)]⟩
    let : Smooth (Y ↘ S) := hsmooth.smooth
    exact .vertex
  · rw [Scheme.IdealSheafData.comap_id, hrad]
    simpa only [hU.ramificationIdealSheafToBase_def ℂ] using hPU

include hg hbir hD hN hpole hfirst hhigh in
private theorem plane_edge_decrease (v : Option (Fin 2)) (hσ : (σ(v)).val ≠ ⊥)
    (b : Basis (Fin 2) ℤ N) (r : Fin 4 ≃ (Φ(v)).Ray) (c : ℂˣ)
    (hr : (fun l ↦ (r l).primitiveGenerator) = ![b 0, b 1, -b 0, (1 : ℤ) • b 0 - b 1])
    (hnew : (Π).starSubdivisionAlongRay reg (Subtype.property (σ(v))) hσ = r 0)
    (hj : let ρ := r 2
      let u := ρ.binomialCenter rankTwo (b.detDualEquiv_self ρ.primitiveGenerator)
        (ρ.surjective_detCharacter b) c
      (eP).hom (π(v,hσ) (u pt)) = hT.baseCenter j) :
    Nonempty (PlaneSarkisovDecrease d hi hT g D) := by
  let : (eP).hom.IsOver S := Fan.projectivePlaneIso_trans_polynomialProjIso_hom_isOver d hi coords
  obtain ⟨_, b₀, r₀, e₀, -, hπ, -, hE, hnew'⟩ := exists_vertex_blowup_comparison d hi v
  rw [← hnew', hnew] at hE
  have hj' := hj.symm
  simp only [← Scheme.Hom.comp_apply, ← hπ] at hj'
  obtain ⟨A, q, a, d', hd', m, Z, U, hU, e, p, hI, hdom, l, W, R, e₁, hR,
    hA, ha, hp, hl, he₁, habase, hmut, hτ, haPole, hpPole, -, hUPole, hg', hb', -, hpos, hlt⟩ :=
    hT.exists_sarkisov_decrease_of_logarithmic_plane_edge
      (regΦ(v)) (hcΦ(v,hσ)) b r hr c e₀ j g hg hbir reg hc (subdiv(v,hσ)) eP
      hπ hE (σ(v)) (Fan.card_toricRay_projectiveSpaceMaximalCone d hi v)
      (Scheme.Hom.comp_apply _ _ _).symm
      hj' hfirst hhigh D hD hN hpole
  let ρ := r 2
  have hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ (Φ(v)).cones := by
    have he : -ρ.primitiveGenerator = (r 0).primitiveGenerator := by
      exact (congrArg Neg.neg (congrFun hr 2)).trans
        ((neg_neg (b 0)).trans (congrFun hr 0).symm)
    rw [he]
    exact (r 0).hull_primitiveGenerator_mem
  let Ψ := (Φ(v)).mutationFan b ρ.primitiveGenerator_ne_zero ρ.hull_primitiveGenerator_mem hOpp
  let regΨ := ((Φ(v)).isRegular_mutationFan_iff b ρ.primitiveGenerator_ne_zero
    ρ.hull_primitiveGenerator_mem hOpp).mpr (regΦ(v))
  let hcΨ := ((Φ(v)).isComplete_mutationFan_iff b ρ.primitiveGenerator_ne_zero
    ρ.hull_primitiveGenerator_mem hOpp).mpr (hcΦ(v,hσ))
  -- Keep the exact mutated fan and ruling used by the edge comparison.
  let s' := r.trans ((Φ(v)).mutationFanRayEquiv b ρ.primitiveGenerator_ne_zero
    ρ.hull_primitiveGenerator_mem hOpp)
  let : (X[Φ(v)]).IsProjectiveOver ℂ :=
    Fan.isProjectiveOver_projectivePlane_vertex_starSubdivision d hi v
  let : A.Over S := ⟨a ≫ f[Φ(v)]⟩
  let : Smooth (A ↘ S) := hA.smooth
  let : IsIntegral A := hI
  let : IsDominant a := hdom
  refine ⟨{
    vertexIndex := v
    vertexCone_ne_bot := hσ
    resolving := A
    refinement := q
    length := l
    length_le_one := hl
    top := W
    tower := R
    nodal := hR
    refinementIso := e₁
    refinementIso_comp := he₁
    first := a
    first_comp := habase
    first_dominant := hdom
    integral := hI
    smooth := hA
    first_pole := haPole
    fan := Ψ
    regular := regΨ
    complete := hcΨ
    projective := ρ.isProjectiveOver_mutationFan b hOpp (regΦ(v))
    index := 0
    basis := d'
    rays := s'
    rayGenerators := hd'
    centers := m
    model := Z
    modelTower := U
    closedPoint := hU
    modelIso := e
    link := ?_
    model_pole := hUPole
    target_over := hg'
    target_birational := hb'
    decreases := ⟨hpos, hlt⟩
  }⟩
  rw [hτ]
  exact .edge b ρ c hOpp regΨ hcΨ d' s' hd' p hp hmut hpPole

end Decrease

/-- A specified logarithmic nonterminal plane resolution admits a decreasing
Sarkisov block. A proper high-order center selects the vertex or edge link, and
all partial composites are regular on one nodal refinement of the given
resolution. The next step uses the returned closed-point tower and its
strictly smaller bidegree. -/
theorem nonempty_planeSarkisovDecrease
    (hg : g ≫ s = T.toBase ≫ s) (hbir : Scheme.BirationalOver g (𝟙 P))
    (hD : D.IsEffectiveCartier)
    (hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ T.toBase ≫ s))
    (hpole : (E[d,hi]).comap T.toBase = D * hT.ramificationIdealSheafToBase ℂ)
    (hdegree : degree (mark[T,hT,s,g]).1 ≠ 1) :
    Nonempty (PlaneSarkisovDecrease d hi hT g D) := by
  obtain ⟨-, -, h⟩ := hT.plane_degree_eq_one_or_exists_high_baseCenter g hg hbir
  obtain ⟨j, hhigh, hfirst⟩ := h.resolve_left hdegree
  cases n with
  | zero => exact j.elim0
  | succ n =>
    have hle : (E[d,hi]).comap T.toBase ≤ hT.ramificationIdealSheafToBase ℂ :=
      hpole.le.trans (mul_le_of_le_one_left' le_top)
    rcases plane_baseCenter_cases d hi hT hle j with
      ⟨v, hv⟩ | ⟨v, hσ, b, r, c, hr, hnew, hj⟩
    · exact plane_vertex_decrease d hi hT g hg hbir D hN hpole j hfirst hhigh v hv.symm
    · exact plane_edge_decrease d hi hT g hg hbir D hD hN hpole j hfirst hhigh v hσ b r c hr hnew hj

variable {d hi hT g D} in
/-- The transported morphism to the original target has the same pole factorization
on the returned tower. This applies to any ideal on the target plane having the
given pole divisor on the original resolving surface. -/
theorem PlaneSarkisovDecrease.target_pole (R : PlaneSarkisovDecrease d hi hT g D)
    (hg : g ≫ s = T.toBase ≫ s)
    (hD : D.IsEffectiveCartier)
    (hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ T.toBase ≫ s))
    (E : (P).IdealSheafData) :
    let : Y.Over S := ⟨T.toBase ≫ s⟩
    let : g.IsOver S := ⟨hg⟩
    let : Smooth (Y ↘ S) := (hT.smoothOfRelativeDimension s).smooth
    E.comap g = D * ramificationIdealSheaf ℂ g →
    let : Nonempty R.fan.cones := R.complete.nonempty_cones
    let : SmoothOfRelativeDimension 2 f[R.fan] :=
      Eq.mp (congrArg (fun n ↦ SmoothOfRelativeDimension n f[R.fan]) rankTwo)
        (R.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap R.regular)
    let : R.model.Over S := ⟨R.modelTower.toBase ≫ f[R.fan]⟩
    let : Smooth (R.model ↘ S) := (R.closedPoint.smoothOfRelativeDimension f[R.fan]).smooth
    let : (R.modelIso.inv ≫ R.refinement ≫ g).IsOver S := ⟨R.target_over⟩
    E.comap (R.modelIso.inv ≫ R.refinement ≫ g) =
      (D.comap R.refinement).radical.comap R.modelIso.inv *
        ramificationIdealSheaf ℂ (R.modelIso.inv ≫ R.refinement ≫ g) := by
  dsimp only
  intro hE
  let : Y.Over S := ⟨T.toBase ≫ s⟩
  let : g.IsOver S := ⟨hg⟩
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension s
  let : R.resolving.Over S := ⟨R.first ≫ f[Φ(R.vertexIndex)]⟩
  let : Nonempty (Φ(R.vertexIndex)).cones := (hcΦ(R.vertexIndex,R.vertexCone_ne_bot)).nonempty_cones
  let : SmoothOfRelativeDimension 2 (R.resolving ↘ S) := R.smooth
  let : (eP).hom.IsOver S := Fan.projectivePlaneIso_trans_polynomialProjIso_hom_isOver d hi coords
  have hq : R.refinement ≫ (Y ↘ S) = R.resolving ↘ S := by
    have h := (reassoc_of% R.first_comp) s
    rw [comp_over (eP).hom S, comp_over (π(R.vertexIndex,R.vertexCone_ne_bot)) S] at h
    exact h.symm
  let : R.refinement.IsOver S := ⟨hq⟩
  let : IsIntegral Y := hT.isIntegral s
  let : IsNoetherian Y := T.isNoetherian
  have hqPole :=
    R.nodal.comap_eq_radical_mul_ramificationIdealSheaf_of_iso hD hN
      R.refinementIso R.refinement R.refinementIso_comp
  have hAg := comap_eq_mul_ramificationIdealSheaf_comp ℂ R.refinement g 2 hE hqPole
  let : Nonempty R.fan.cones := R.complete.nonempty_cones
  let : SmoothOfRelativeDimension 2 f[R.fan] :=
    Eq.mp (congrArg (fun n ↦ SmoothOfRelativeDimension n f[R.fan]) rankTwo)
      (R.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap R.regular)
  let : R.model.Over S := ⟨R.modelTower.toBase ≫ f[R.fan]⟩
  let : SmoothOfRelativeDimension 2 (R.model ↘ S) :=
    R.closedPoint.smoothOfRelativeDimension f[R.fan]
  let : R.modelIso.inv.IsOver S := ⟨by
    have h := R.target_over
    rw [Category.assoc, Category.assoc, comp_over g S, comp_over R.refinement S] at h
    exact h⟩
  exact comap_eq_mul_ramificationIdealSheaf_comp ℂ R.modelIso.inv (R.refinement ≫ g) 2
    hAg (by simp only [ramificationIdealSheaf_eq_top_of_isOpenImmersion, mul_top])

variable {N' V' : Type} [AddCommGroup N'] [AddCommGroup V'] [Module ℝ V']
  {i' : N' →+ V'} (d' : Basis (Fin 2) ℤ N') (hi' : IsIntegralLattice i')

/-- The plane case of logarithmic Sarkisov factorization. Either the specified
map is the terminal toric isomorphism followed by a translation, or it admits
a strictly decreasing resolved block. In the latter case the returned point
tower is again a logarithmic resolution of a map to the same target plane. -/
theorem exists_toric_factorization_or_sarkisov_decrease_of_logarithmic_plane
    (hg : g ≫ s = T.toBase ≫ s) (hbir : Scheme.BirationalOver g (𝟙 P))
    (hD : D.IsEffectiveCartier)
    (hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ T.toBase ≫ s))
    (hpole : (E[d,hi]).comap T.toBase = D * hT.ramificationIdealSheafToBase ℂ) :
    let : Y.Over S := ⟨T.toBase ≫ s⟩
    let : g.IsOver S := ⟨hg⟩
    let : Smooth (Y ↘ S) := (hT.smoothOfRelativeDimension s).smooth
    (E[d',hi']).comap g = D * ramificationIdealSheaf ℂ g →
    (let Ψ := Π[d',hi']
     let : Nonempty Ψ.cones := (Fan.isComplete_projectiveSpace d' hi').nonempty_cones
     ∃! a : FanEquiv Π Ψ × (Multiplicative (N' →+ ℤ) →* ℂˣ),
       T.toBase ≫ (eP).inv ≫ a.1.toFanHom.algebraicMap ≫
         (Ψ.torusTranslation a.2).hom ≫ (eP[d',hi']).hom = g) ∨
    (∃ R : PlaneSarkisovDecrease d hi hT g D,
      let : Nonempty R.fan.cones := R.complete.nonempty_cones
      let : SmoothOfRelativeDimension 2 f[R.fan] :=
        Eq.mp (congrArg (fun n ↦ SmoothOfRelativeDimension n f[R.fan]) rankTwo)
          (R.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap R.regular)
      let : R.model.Over S := ⟨R.modelTower.toBase ≫ f[R.fan]⟩
      let : Smooth (R.model ↘ S) := (R.closedPoint.smoothOfRelativeDimension f[R.fan]).smooth
      let : (R.modelIso.inv ≫ R.refinement ≫ g).IsOver S := ⟨R.target_over⟩
      (E[d',hi']).comap (R.modelIso.inv ≫ R.refinement ≫ g) =
        (D.comap R.refinement).radical.comap R.modelIso.inv *
          ramificationIdealSheaf ℂ (R.modelIso.inv ≫ R.refinement ≫ g)) := by
  dsimp only
  intro hpole'
  by_cases hdegree : degree (mark[T,hT,s,g]).1 = 1
  · exact Or.inl (hT.existsUnique_toric_factorization_of_plane_degree_one
      d hi d' hi' g hg hbir D hdegree hpole hpole')
  · obtain ⟨R⟩ := nonempty_planeSarkisovDecrease d hi hT g D hg hbir hD hN hpole hdegree
    exact Or.inr ⟨R, R.target_pole hg hD hN (E[d',hi']) hpole'⟩

end QPainleve.BlowupTower.IsClosedPointTower
