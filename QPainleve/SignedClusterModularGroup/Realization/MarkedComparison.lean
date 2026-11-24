/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Period.Evaluation
public import QPainleve.SignedClusterModularGroup.Realization.Agreement
public import QPainleve.SignedClusterModularGroup.Realization.Boundary
public import QPainleve.SignedClusterModularGroup.Realization.CenterFibers

import QPainleve.Geometry.Toric.Fan.Boundary.NumberedPrime

/-!
# Independent X maps determined by marked actions

Two realizations with the same Picard pullbacks and action on the ordered branches
give the same independent rational map. At a common source center, compare the
two target evaluations by applying the fixed-center period comparison to the
residual isomorphism using `Fan.comp_contractedXEvaluation_eq_of_matching_markings`.
Then `GeometricRealization.xMap_eq_of_target_evaluation_eq_on_center_fibers` detects
equality of the independent maps through variable-center evaluation. The charge
map may have arbitrary rank.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory DihedralGroup Multiplicative
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric QPainleve.BlowupTower DiagonalizableGroup
open Scheme Scheme.IdealSheafData TopologicalSpace

namespace QPainleve.SignedClusterModularGroup

open MarkedSurface (surfaceIso boundaryIso boundaryImageIso_hom_comp imagePairIso
  imagePairIso_hom_comp imagePairIso_boundaryAction)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Xtor[" r "]" => Spec (CommRingCat.of (LaurentRing ℂ (Fin r)))

local notation "D[" P "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair P)))
section Toric

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones]
  {r m n : ℕ} [NeZero m] [NeZero n] {L₁ : Type} [AddCommGroup L₁]
  {B₁ : LinearMap.BilinForm ℤ L₁}
  {b : Module.Basis (Fin 2) ℤ N} {s : Fin r → Φ.Ray} {hΦ : Φ.IsRegular}

local notation "Dtor[" Φ "," h₀ "]" => Scheme.IdealSheafData.subscheme (Fan.boundaryIdeal Φ h₀)
local notation "center" c:arg => (fun j : Fin r ↦ c (ofAdd (Pi.single j 1)))
local notation "Model[" b "," s "," c "]" => Fan.internalBlowupTower b s (center c)
local notation "prime[" b "," s "," hΦ "," c "]" =>
  Fan.internalBlowupBoundaryPrimeEquiv hΦ b s (center c)
local notation "Pic[" Φ "," r "]" =>
  (Additive (LineBundleClass (Fan.algebraicRealization Φ)) × (Fin r → ℤ))

variable [PrestableFamily (Dtor[Φ,h₀] ↘ S)] {γ : Type*} {a : γ → (Dtor[Φ,h₀] ↘ S).smoothLocus}
  {T : NodalCycleNumbering a m} {origin : ZMod m} {ι : L₁ →ₗ[ℤ] Pic[Φ,r]}
  {c d : Multiplicative (Fin r → ℤ) →* ℂˣ} {P Q : MarkedSurface ℂ n B₁ Xtor[r]}
  (p : ContractedToricFiber b s hΦ T origin ι c P)
  (q : ContractedToricFiber b s hΦ T origin ι d Q)

namespace ContractedToricFiber

private instance : PrestableFamily (D[P].subscheme ↘ S) := P.prestable_boundaryImage

/-- The marked boundary is a Cartier cycle of rational curves and the specified
projection reverses a tower of blowups at boundary nodes. -/
structure IsNodalContraction : Prop where
  /-- The boundary is Cartier. -/
  cartier : D[P].IsEffectiveCartier
  /-- The boundary normalization has genus zero on every component. -/
  genus_zero :
    letI := P.prestable_boundaryImage
    ∀ v : irreducibleComponents (D[P].subscheme.singularLocus ℂ).blowup,
      (D[P].subscheme.blowupComponent (K := ℂ) v).toScheme.genus ℂ = 0
  /-- The nodal tower gives the specified projection from the ordered model. -/
  exists_tower : ∃ (l : ℕ) (W : Scheme) (A : BlowupTower P.surface l W)
    (_ : IsNodalBoundaryTower D[P] (P.surface ↘ S) (𝟙 P.surface) A)
    (e : W ≅ (Model[b,s,c]).1), e.inv ≫ A.toBase = p.projection

/-- The toric boundary projection remains an oriented subdivision after identifying the
marked boundary with the closed subscheme cut out by its ideal. -/
theorem isOrientedCycleSubdivision_comp_boundaryImage :
    letI : PrestableFamily (D[P].subscheme ↘ S) := P.prestable_boundaryImage
    (p.boundaryMap ≫ P.boundaryImageIso.hom).IsOrientedCycleSubdivision T P.imageCycle := by
  let : PrestableFamily (P.boundary ↘ S) := P.prestable
  exact p.orientedSubdivision.comp
    (P.boundaryImageIso.isOrientedCycleSubdivision_of_cycleOrientationSign_eq_one _ _
      (by rw [P.boundaryCycleAction_boundaryImageIso, map_one]))

variable (u : ZMod m ≃ Φ.Ray)
  (hvertices : ∀ j, Dtor[Φ,h₀].dualGraphVertexEquiv a (T.vertex j) =
    Φ.boundaryNormalizationComponentEquiv hΦ (u j))

include p hvertices in
private theorem projection_prime_origin :
    letI : PrestableFamily (P.boundary ↘ S) := P.prestable
    p.projection (prime[b,s,hΦ,c] (u origin)).val =
      P.pair.hom.left (P.cycle.componentGenericPoint 0) := by
  let : PrestableFamily (P.boundary ↘ S) := P.prestable
  have hprime := Fan.internalBlowupBoundaryPrime_val hΦ b s (center c) (u origin)
  rw [← hvertices origin, ← T.component_apply origin, ← T.componentGenericPoint_def] at hprime
  rw [hprime, ← Hom.comp_apply, ← p.boundary_comp, Hom.comp_apply, p.component_zero]

variable [Φ.algebraicRealization.IsProjectiveOver ℂ] [B₁.IsPerfPair]
  (hdet : ∀ j, b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1)
  (hnodes : ∀ j, ∃ σ : Φ.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ ∧
    (Φ.boundaryIdeal h₀).subschemeι (Dtor[Φ,h₀].dualGraphEdgeEquiv a (T.edge j)).val =
      Φ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ))

include hvertices hdet hnodes in
/-- A pair isomorphism preserving both markings and the numbered branches intertwines
the evaluations in two fibers of a fixed ordered toric presentation. The surviving
rays are the same in both fibers, and the charge map can have any rank. -/
theorem comp_evaluation_eq_of_marked_actions
    (hc : Φ.IsComplete) (hp : p.IsNodalContraction) (hq : q.IsNodalContraction)
    (hkeep : ∀ ρ : Φ.Ray, p.projection (prime[b,s,hΦ,c] ρ).val ∈ D[P].boundaryPrimes ↔
      q.projection (prime[b,s,hΦ,d] ρ).val ∈ D[Q].boundaryPrimes)
    (e : P.pair ≅ Q.pair)
    (hPic : ∀ a, LineBundleClass.pullback (surfaceIso e).hom (Q.picardMarking a).toMul =
      (P.picardMarking a).toMul)
    (hact : letI : PrestableFamily (P.boundary ↘ S) := P.prestable
            letI : PrestableFamily (Q.boundary ↘ S) := Q.prestable
            (boundaryIso e).boundaryCycleAction P.cycle Q.cycle = 1) :
    (surfaceIso e).hom.toRationalMap.comp Q.evaluation = P.evaluation := by
  let : PrestableFamily (P.boundary ↘ S) := P.prestable
  let : PrestableFamily (Q.boundary ↘ S) := Q.prestable
  let : SmoothOfRelativeDimension 2 (P.surface ↘ S) := P.smooth
  let : SmoothOfRelativeDimension 2 (Q.surface ↘ S) := Q.smooth
  let : P.surface.IsProjectiveOver ℂ := P.projective
  let : Q.surface.IsProjectiveOver ℂ := Q.projective
  let := P.isPerfPair_intersectionForm
  let := Q.isPerfPair_intersectionForm
  let vB := imagePairIso e
  have hv := imagePairIso_hom_comp e
  have hB : vB.boundaryCycleAction P.imageCycle Q.imageCycle = DihedralGroup.r 0 :=
    (imagePairIso_boundaryAction e).trans (hact.trans DihedralGroup.one_def)
  obtain ⟨_, _, A, hA, eP, heP⟩ := hp.exists_tower
  obtain ⟨_, _, B, hB', eQ, heQ⟩ := hq.exists_tower
  let f := p.boundaryMap ≫ P.boundaryImageIso.hom
  let g := q.boundaryMap ≫ Q.boundaryImageIso.hom
  have hf : f ≫ D[P].subschemeι = (Model[b,s,c]).2.boundaryι ≫ p.projection := by
    simpa only [f, Category.assoc, boundaryImageIso_hom_comp] using p.boundary_comp
  have hg : g ≫ D[Q].subschemeι = (Model[b,s,d]).2.boundaryι ≫ q.projection := by
    simpa only [g, Category.assoc, boundaryImageIso_hom_comp] using q.boundary_comp
  let x : D[P].boundaryPrimes :=
    ⟨P.boundaryPrime hp.cartier 0, P.boundaryPrime_mem_boundaryPrimes hp.cartier 0⟩
  let y : D[Q].boundaryPrimes :=
    ⟨Q.boundaryPrime hq.cartier 0, Q.boundaryPrime_mem_boundaryPrimes hq.cartier 0⟩
  rw [p.evaluation_eq, q.evaluation_eq]
  simpa only [heP, heQ] using
    (Fan.comp_contractedXEvaluation_eq_of_matching_markings b s hΦ c d hA hB' eP eQ
        P.imageCycle Q.imageCycle T hc
        (by rw [heP]; exact p.projection_over) (by rw [heQ]; exact q.projection_over)
        (by rw [← comap_comp, heP]; exact p.support_comap)
        (by rw [← comap_comp, heQ]; exact q.support_comap)
        u hvertices hdet hnodes hp.cartier hq.cartier hp.genus_zero hq.genus_zero f g
        (by simpa only [heP] using hf) (by simpa only [heQ] using hg)
        (isOrientedCycleSubdivision_comp_boundaryImage p)
        (isOrientedCycleSubdivision_comp_boundaryImage q)
        (by simpa only [heP, heQ] using hkeep)
        (surfaceIso e) vB hv (by
          intro L
          obtain ⟨a, ha⟩ := Q.picardMarking.surjective (Additive.ofMul L)
          have hL : (Q.picardMarking a).toMul = L := congrArg Additive.toMul ha
          simpa only [heP, heQ, ← hL, hPic a] using
            (p.marked_pullback a).trans (q.marked_pullback a).symm) 0 hB x y
        (by simpa only [x, P.coe_boundaryPrime] using (P.imageCycle_genericPoint 0).symm)
        (by simpa only [y, Q.coe_boundaryPrime] using (Q.imageCycle_genericPoint 0).symm)
        (u origin)
        (by simpa only [heP, x, P.coe_boundaryPrime] using p.projection_prime_origin u hvertices)
        (by simpa only [heQ, y, Q.coe_boundaryPrime] using q.projection_prime_origin u hvertices))

end ContractedToricFiber

section Realizations

open GeometricRealization (CenterPoint Point)

variable {A N₀ : Type} [AddCommGroup A] [AddCommGroup N₀] [IsAddFG A] [IsAddFG N₀]
  [Module.Free ℤ A] [Module.Free ℤ N₀]
  {L₀ : Type} [AddCommGroup L₀] {B₀ : LinearMap.BilinForm ℤ L₀}

local notation "Torus[" B "]" => groupScheme ℂ (FGCommGrpCat.of (Multiplicative B))

variable [Φ.algebraicRealization.IsProjectiveOver ℂ] [B₁.IsPerfPair]
  [Smooth (Torus[A]).X.hom] {T₁ : Over S}
  {P₀ : Point (Torus[A]).X → MarkedSurface ℂ n B₀ (Torus[A]).X.left}
  {P₁ : Point T₁ → MarkedSurface ℂ n B₁ Xtor[r]}
  {C C' : (Torus[A]).X.left.PartialMap T₁.left} [IsDominant C.hom] [IsDominant C'.hom]
  [C.IsOver (Torus[A]).X.hom T₁.hom] [C'.IsOver (Torus[A]).X.hom T₁.hom]
  {F G : (Torus[A]).X.left ⤏ Xtor[r]} [F.IsDominant] [G.IsDominant]

/-- Equality of the constant Picard pullback, boundary permutation and orientation
implies equality of the independent rational X maps. The source evaluation
comes from the charge map on a dominant torus chart. Both target realizations use a
fixed ordered toric presentation and the same surviving rays. This works for
arbitrary charge rank and for one- and two-component boundaries. -/
theorem GeometricRealization.xMap_eq_of_marked_actions_eq
    (R : GeometricRealization P₀ P₁ C F) (R' : GeometricRealization P₀ P₁ C' G)
    (hI : R.picard = R'.picard) (hperm : R.boundaryPerm = R'.boundaryPerm)
    (horient : R.orientation = R'.orientation)
    (v : A →+ N₀) (sY : Xtor[r] ⟶ S)
    [F.IsOver (Torus[A]).X.hom sY] [G.IsOver (Torus[A]).X.hom sY]
    (U : (Torus[A]).X.left.Opens) [Nonempty U] (hUC : U ≤ C.domain) (hUC' : U ≤ C'.domain)
    (hchart : ∀ t : Point (Torus[A]).X, (∃ x : S ⟶ U.toScheme, x ≫ U.ι = t.left) →
      ∃ (j : (Torus[N₀]).X.left ⤏ (P₀ t).surface) (_ : j.IsDominant),
        j.comp (P₀ t).evaluation =
          (QPainleve.CharacterTorus.evaluationAtCenter ℂ v t.left (Over.w t)).toRationalMap)
    (hc : Φ.IsComplete) (u : ZMod m ≃ Φ.Ray)
    (hvertices : ∀ j, Dtor[Φ,h₀].dualGraphVertexEquiv a (T.vertex j) =
      Φ.boundaryNormalizationComponentEquiv hΦ (u j))
    (hdet : ∀ j, b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1)
    (hnodes : ∀ j, ∃ σ : Φ.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ ∧
      (Φ.boundaryIdeal h₀).subschemeι (Dtor[Φ,h₀].dualGraphEdgeEquiv a (T.edge j)).val =
        Φ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ))
    (centers : Point T₁ → (Multiplicative (Fin r → ℤ) →* ℂˣ)) (survives : Set Φ.Ray)
    (hC : ∀ x : CenterPoint C,
      ∃ p : ContractedToricFiber b s hΦ T origin ι (centers (x ≫ C.domainTarget))
          (P₁ (x ≫ C.domainTarget)),
        p.IsNodalContraction ∧ ∀ ρ : Φ.Ray,
          p.projection (prime[b,s,hΦ,centers (x ≫ C.domainTarget)] ρ).val ∈
            D[P₁ (x ≫ C.domainTarget)].boundaryPrimes ↔ ρ ∈ survives)
    (hC' : ∀ x' : CenterPoint C',
      ∃ q : ContractedToricFiber b s hΦ T origin ι (centers (x' ≫ C'.domainTarget))
          (P₁ (x' ≫ C'.domainTarget)),
        q.IsNodalContraction ∧ ∀ ρ : Φ.Ray,
          q.projection (prime[b,s,hΦ,centers (x' ≫ C'.domainTarget)] ρ).val ∈
            D[P₁ (x' ≫ C'.domainTarget)].boundaryPrimes ↔ ρ ∈ survives) :
    F = G := by
  apply R.xMap_eq_of_target_evaluation_eq_on_center_fibers R' v sY U hUC hUC' hchart
  intro x x' hs _
  let r : FiberRealization (P₀ (x ≫ C.domainSource)) (P₁ (x' ≫ C'.domainTarget))
      G R'.picard R'.boundaryAction := hs ▸ R'.fiber x'
  obtain ⟨p, hp, hkeep⟩ := hC x
  obtain ⟨q, hq, hkeep'⟩ := hC' x'
  have hg : R.boundaryAction = R'.boundaryAction :=
    eq_of_cycleVertexPerm_eq_of_cycleOrientationSign_eq
      ((R.boundaryPerm_def.symm.trans hperm).trans R'.boundaryPerm_def)
      ((R.orientation_def.symm.trans horient).trans R'.orientation_def)
  have h := p.comp_evaluation_eq_of_marked_actions q u hvertices hdet hnodes hc hp hq
    (fun ρ ↦ (hkeep ρ).trans (hkeep' ρ).symm) ((R.fiber x).iso.symm ≪≫ r.iso)
    ((R.fiber x).pullback_picardMarking_targetIso r hI)
    ((R.fiber x).boundaryCycleAction_targetIso r hg)
  simpa only [← RationalMap.comp_assoc, RationalMap.comp_toRationalMap, Hom.toRationalMap_compHom,
    MarkedSurface.surfaceIso_trans, MarkedSurface.surfaceIso_symm, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc] using
      congrArg ((surfaceIso (R.fiber x).iso).hom.toRationalMap.comp ·) h.symm

end Realizations

end Toric

end QPainleve.SignedClusterModularGroup
