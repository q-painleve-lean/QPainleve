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
import QPainleve.Geometry.Toric.Fan.Evaluation.CenterFiber
import QPainleve.SignedClusterModularGroup.Realization.Evaluation

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

namespace GeometricRealization

open QPainleve.CharacterTorus

variable {l n : ℕ} [NeZero n] {L : Type} [AddCommGroup L]
  {B : LinearMap.BilinForm ℤ L}

local notation "Cent" => (Fin l → ℤ)
local notation "T" => Over.mk (structureMap ℂ Cent)
local notation "Xtor" => scheme ℂ (Fin l →₀ ℤ)
local notation "Torus[" U "]" => Grp.X (groupScheme ℂ (FGCommGrpCat.of (Multiplicative U)))
local notation "centerCoordinates" =>
  diagonalizableGroupSchemeIso ℂ (FGCommGrpCat.of (Multiplicative Cent))
local notation "χ[" p "]" => pointsEquiv ℂ Cent
  (Subtype.mk (Over.Hom.left (p : Point T)) (Over.w (p : Point T)))
local notation "dst[" C "," x "]" =>
  x ≫ PartialMap.domainTarget (X := T) (Y := T) C
local notation "src[" C "," x "]" =>
  x ≫ PartialMap.domainSource (X := T) (Y := T) C

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [hΦ₀ : Nonempty Φ.cones] {m : ℕ} [NeZero m]
  {b : Module.Basis (Fin 2) ℤ N} {s : Fin l → Φ.Ray} {hΦ : Φ.IsRegular}
  [PrestableFamily ((Φ.boundaryIdeal hΦ₀).subscheme ↘ S)]
  {γ : Type*} {a : γ → ((Φ.boundaryIdeal hΦ₀).subscheme ↘ S).smoothLocus}
  {τ : NodalCycleNumbering a m} {origin : ZMod m}
  {ι : L →ₗ[ℤ] Additive (LineBundleClass Φ.algebraicRealization) × (Fin l → ℤ)}
  {P : Point (Over.mk (structureMap ℂ (Fin l → ℤ))) →
    MarkedSurface ℂ n B (scheme ℂ (Fin l →₀ ℤ))}
  {C C' : (scheme ℂ (Fin l → ℤ)).PartialMap (scheme ℂ (Fin l → ℤ))}
  [IsDominant C.hom] [IsDominant C'.hom]
  [C.IsOver (Over.mk (structureMap ℂ (Fin l → ℤ))).hom
    (Over.mk (structureMap ℂ (Fin l → ℤ))).hom]
  [C'.IsOver (Over.mk (structureMap ℂ (Fin l → ℤ))).hom
    (Over.mk (structureMap ℂ (Fin l → ℤ))).hom]
  {F G : scheme ℂ (Fin l →₀ ℤ) ⤏ scheme ℂ (Fin l →₀ ℤ)} [F.IsDominant] [G.IsDominant]
  [F.IsOver (structureMap ℂ (Fin l →₀ ℤ)) (structureMap ℂ (Fin l →₀ ℤ))]
  [G.IsOver (structureMap ℂ (Fin l →₀ ℤ)) (structureMap ℂ (Fin l →₀ ℤ))]

local notation "fiberAt" c:arg => ContractedToricFiber b s hΦ τ origin ι (χ[c]) (P c)

omit [IsDominant C.hom] in
private theorem precompCenter_target
    {A : Over S} [PreirreducibleSpace A.left]
    (f : A.left.PartialMap (T).left) [IsDominant f.hom]
    [f.IsOver A.hom (T).hom] [(f.comp C).IsOver A.hom (T).hom]
    (G : Point T → Prop)
    (hG : ∀ x : CenterPoint (U := T) (V := T) C, G (dst[C,x]))
    (x : CenterPoint (U := A) (V := T) (f.comp C)) :
    G (x ≫ PartialMap.domainTarget (X := A) (Y := T) (f.comp C)) := by
  have hx := hG (x ≫ f.compDomainRight (Z := T) C)
  rw [Category.assoc, f.compDomainRight_target] at hx
  exact hx

omit [IsDominant C.hom]
  [C.IsOver (Over.mk (structureMap ℂ (Fin l → ℤ))).hom
    (Over.mk (structureMap ℂ (Fin l → ℤ))).hom] in
private theorem exists_precompCenter_chart
    [Module.Free ℤ N] [IsAddFG N] [IsIntegral Torus[Cent].left]
    (eOver : Torus[Cent] ⟶ T) (eX : Torus[Cent].left ≅ Xtor)
    (he : eOver.left = (centerCoordinates).hom)
    (hcoords : eX.hom = (centerCoordinates).hom ≫ CharacterTorus.map ℂ
      (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin l)).toAddEquiv.toAddMonoidHom)
    [IsDominant eOver.left]
    (pSource : ∀ x : CenterPoint (U := T) (V := T) C, fiberAt (src[C,x]))
    (c : Point Torus[Cent])
    (z : S ⟶ (eOver.left.toPartialMap.comp C).domain.toScheme)
    (hleft : z ≫ (eOver.left.toPartialMap.comp C).domain.ι = c.left) :
    ∃ (j : Torus[N].left ⤏ ((P (c ≫ eOver)).compEvaluation eX.inv).surface)
      (_ : j.IsDominant), j.comp ((P (c ≫ eOver)).compEvaluation eX.inv).evaluation =
        (evaluationAtCenter ℂ (Fan.rayChargeMap s).toAddMonoidHom c.left
          (Over.w c)).toRationalMap := by
  let f := eOver.left.toPartialMap
  let : f.IsOver Torus[Cent].hom (T).hom := Hom.isOver_toPartialMap (Over.w eOver)
  let t : CenterPoint (U := Torus[Cent]) (V := T) (f.comp C) :=
    Over.homMk z
      (by exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hleft).trans (Over.w c)))
  let x := t ≫ f.compDomainRight (Z := T) C
  have hx : src[C,x] = c ≫ eOver := by
    have ht : t ≫ PartialMap.domainSource (X := Torus[Cent]) (Y := T) (f.comp C) = c := by
      apply Over.OverMorphism.ext
      simpa only [t, Over.comp_left, Over.homMk_left, PartialMap.domainSource_left] using hleft
    have hf : f.domainTarget = f.domainSource ≫ eOver :=
      PartialMap.domainTarget_toPartialMap eOver rfl
    rw [Category.assoc, ← f.compDomainLeft_target (Z := T) C, hf,
      ← Category.assoc (f.compDomainLeft (Z := T) C), f.compDomainLeft_source (Z := T),
      ← Category.assoc, ht]
  let c' : (S).asOver S ⟶ Torus[Cent] :=
    Over.homMk c.left ((Over.w c).trans (Spec.map_id (CommRingCat.of ℂ)).symm)
  let χ' := schemePointsMulEquiv (R := ℂ) (A := ℂ) (FGCommGrpCat.of (Multiplicative Cent)) c'
  have hχ : χ' = χ[c ≫ eOver] := by
    apply (pointsEquiv ℂ Cent).symm.injective
    apply Subtype.ext
    rw [Equiv.symm_apply_apply]
    -- Expose the underlying scheme map to use the point comparison.
    change ((pointsEquiv ℂ Cent).symm χ').val = c'.left ≫ eOver.left
    rw [he]
    simpa only [χ', MulEquiv.symm_apply_apply] using!
      (schemePointsMulEquiv_symm_comp_diagonalizableGroupSchemeIso ℂ (B := Cent) χ').symm
  let q : ContractedToricFiber b s hΦ τ origin ι χ' (P (c ≫ eOver)) :=
    hχ.symm ▸ hx ▸ pSource x
  obtain ⟨j, hj, hchart⟩ := @Fan.exists_dominant_chart_comp_evaluationAtCenter
    N V _ _ _ i Φ hΦ₀ l b s c.left (Over.w c) hΦ
    (P (c ≫ eOver)).surface (P (c ≫ eOver)).integral q.projection q.modification
  refine ⟨j, hj, ?_⟩
  let ev := evaluationAtCenter ℂ (Fan.rayChargeMap s).toAddMonoidHom c.left (Over.w c)
  have hchart' : j.comp (P (c ≫ eOver)).evaluation = (ev ≫ eX.hom).toRationalMap := by
    rw [q.evaluation_eq, hcoords]
    exact hchart
  -- Undo the coordinate isomorphism used to apply the variable-center comparison.
  change j.comp ((P (c ≫ eOver)).compEvaluation eX.inv).evaluation = ev.toRationalMap
  rw [MarkedSurface.compEvaluation_evaluation, RationalMap.comp_compHom, hchart',
    Hom.toRationalMap_compHom, Category.assoc, eX.hom_inv_id, Category.comp_id]

/-- In character-torus coordinates, equality of the marked actions determines the
independent rational X maps. The source toric models are needed only on the first
center domain, and the target models need only agree on which boundary rays survive. -/
theorem xMap_eq_of_marked_actions_on_center_domains
    (R : GeometricRealization P P C F) (R' : GeometricRealization P P C' G)
    [Φ.algebraicRealization.IsProjectiveOver ℂ] [B.IsPerfPair]
    (hcΦ : Φ.IsComplete) (u : ZMod m ≃ Φ.Ray)
    (hvertices : ∀ j, (Φ.boundaryIdeal hΦ₀).subscheme.dualGraphVertexEquiv a (τ.vertex j) =
      Φ.boundaryNormalizationComponentEquiv hΦ (u j))
    (hdet : ∀ j, b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1)
    (hnodes : ∀ j, ∃ σ : Φ.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ ∧
      (Φ.boundaryIdeal hΦ₀).subschemeι
        ((Φ.boundaryIdeal hΦ₀).subscheme.dualGraphEdgeEquiv a (τ.edge j)).val =
        Φ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ))
    (pSource : ∀ x : CenterPoint (U := T) (V := T) C, fiberAt (src[C,x]))
    (survives : Set Φ.Ray)
    (pTarget : ∀ x : CenterPoint (U := T) (V := T) C,
      ∃ p : fiberAt (dst[C,x]), p.IsNodalContraction ∧ ∀ ρ : Φ.Ray,
        p.projection (Fan.internalBlowupBoundaryPrimeEquiv hΦ b s
          (fun j ↦ χ[dst[C,x]] (ofAdd (Pi.single j 1))) ρ).val ∈
          D[P (dst[C,x])].boundaryPrimes ↔ ρ ∈ survives)
    (qTarget : ∀ x : CenterPoint (U := T) (V := T) C',
      ∃ p : fiberAt (dst[C',x]), p.IsNodalContraction ∧ ∀ ρ : Φ.Ray,
        p.projection (Fan.internalBlowupBoundaryPrimeEquiv hΦ b s
          (fun j ↦ χ[dst[C',x]] (ofAdd (Pi.single j 1))) ρ).val ∈
          D[P (dst[C',x])].boundaryPrimes ↔ ρ ∈ survives)
    (hpic : R.picard = R'.picard) (hperm : R.boundaryPerm = R'.boundaryPerm)
    (hη : R.orientation = R'.orientation) :
    F = G := by
  -- The comparison uses the group-scheme coordinates for the joint evaluation map.
  let : Module.Free ℤ N := Module.Free.of_basis b
  let : IsAddFG N := Module.Finite.iff_addGroup_fg.mp (.of_basis b)
  let e := centerCoordinates
  let coord : (Fin l →₀ ℤ) ≃+ Additive (FGCommGrpCat.of (Multiplicative Cent)) :=
    (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin l)).toAddEquiv
  let eX : Torus[Cent].left ≅ Xtor := e ≪≫ CharacterTorus.mapIso ℂ coord
  have he : e.hom ≫ (T).hom = Torus[Cent].hom := diagonalizableGroupSchemeIso_hom_structureMap ℂ _
  have hcoords : eX.hom = e.hom ≫ CharacterTorus.map ℂ coord.toAddMonoidHom := by
    simp only [eX, Iso.trans_hom, CharacterTorus.mapIso_hom]
  have heX : eX.hom ≫ structureMap ℂ (Fin l →₀ ℤ) = Torus[Cent].hom := by
    rw [hcoords, Category.assoc, map_structureMap]
    exact he
  let : Nonempty Torus[Cent].left := ⟨e.inv (Classical.choice (inferInstance : Nonempty (T).left))⟩
  let : IsIntegral Torus[Cent].left := IsIntegral.of_isIso e.inv
  let : Smooth Torus[Cent].hom := smooth_groupScheme_of_free ℂ Cent
  let eOver : Torus[Cent] ⟶ T := Over.homMk e.hom he
  let : IsDominant eOver.left := by
    -- The underlying arrow of this over-morphism is the center-coordinate isomorphism.
    change IsDominant e.hom
    let : IsIso e.hom := Iso.isIso_hom e
    infer_instance
  let : eOver.left.toPartialMap.IsOver Torus[Cent].hom (T).hom := Hom.isOver_toPartialMap he
  let f := eOver.left.toPartialMap
  let : (f.comp C).IsOver Torus[Cent].hom (T).hom :=
    PartialMap.instIsOverCompHom_qPainleve (X := Torus[Cent]) (Y := T) (Z := T) f C
  let : (f.comp C').IsOver Torus[Cent].hom (T).hom :=
    PartialMap.instIsOverCompHom_qPainleve (X := Torus[Cent]) (Y := T) (Z := T) f C'
  let R₀ := (R.precompCenter eOver).precompEvaluation eX
  let R₁ := (R'.precompCenter eOver).precompEvaluation eX
  have hover : eX.hom.toRationalMap.IsOver Torus[Cent].hom (structureMap ℂ (Fin l →₀ ℤ)) := by
    rw [RationalMap.isOver_iff, Hom.toRationalMap_compHom, heX]
  let : (eX.hom.toRationalMap.comp F).IsOver Torus[Cent].hom
      (structureMap ℂ (Fin l →₀ ℤ)) := RationalMap.isOver_comp _ hover _ inferInstance
  let : (eX.hom.toRationalMap.comp G).IsOver Torus[Cent].hom
      (structureMap ℂ (Fin l →₀ ℤ)) := RationalMap.isOver_comp _ hover _ inferInstance
  let U := (f.comp C).domain ⊓ (f.comp C').domain
  let : Nonempty U := ((f.comp C).dense_domain.inter_of_isOpen_left
    (f.comp C').dense_domain (f.comp C).domain.is_open').nonempty.to_subtype
  let hasFiber (c : Point T) := ∃ p : fiberAt c, p.IsNodalContraction ∧ ∀ ρ : Φ.Ray,
    p.projection (Fan.internalBlowupBoundaryPrimeEquiv hΦ b s
      (fun j ↦ χ[c] (ofAdd (Pi.single j 1))) ρ).val ∈ D[P c].boundaryPrimes ↔ ρ ∈ survives
  apply RationalMap.comp_left_injective eX.hom.toRationalMap
  refine R₀.xMap_eq_of_marked_actions_eq (s := s) (origin := origin) (ι := ι) R₁
    (by simpa only [R₀, R₁, precompEvaluation_picard, precompCenter_picard] using hpic)
    (by simpa only [R₀, R₁, boundaryPerm_def, precompEvaluation_boundaryAction,
      precompCenter_boundaryAction] using hperm)
    (by simpa only [R₀, R₁, orientation_def, precompEvaluation_boundaryAction,
      precompCenter_boundaryAction] using hη)
    (Fan.rayChargeMap s).toAddMonoidHom (structureMap ℂ (Fin l →₀ ℤ)) U inf_le_left inf_le_right
    ?_ hcΦ u hvertices hdet hnodes (fun c ↦ χ[c]) survives
    (precompCenter_target (C := C) f hasFiber pTarget)
    (precompCenter_target (C := C') f hasFiber qTarget)
  rintro c ⟨z, hz⟩
  exact exists_precompCenter_chart eOver eX (by rfl) hcoords pSource c
    (z ≫ Scheme.homOfLE _ (inf_le_left : U ≤ (f.comp C).domain))
    (by rwa [Category.assoc, Scheme.homOfLE_ι])

end GeometricRealization

end QPainleve.SignedClusterModularGroup
