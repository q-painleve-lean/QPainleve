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

open MarkedSurface (surfaceIso boundaryIso)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Xtor[" r "]" => Spec (CommRingCat.of (LaurentRing ℂ (Fin r)))

section Residual

universe u

variable {k : Type u} [Field k] [IsSepClosed k] [Infinite k] {n : ℕ} [NeZero n]
  {L₀ L₁ : Type u} [AddCommGroup L₀] [AddCommGroup L₁]
  {B₀ : LinearMap.BilinForm ℤ L₀} {B₁ : LinearMap.BilinForm ℤ L₁}
  {X Y : Scheme.{u}} [IsIntegral X] [X.IsSeparated] [Y.IsSeparated]
  {M : MarkedSurface k n B₀ X} {P Q : MarkedSurface k n B₁ Y}
  {F G : X ⤏ Y} {I J : B₁.IsometryEquiv B₀} {g h : DihedralGroup n}
  (R : FiberRealization M P F I g) (R' : FiberRealization M Q G J h)

namespace FiberRealization

/-- Equality of the Picard actions makes the residual isomorphism identify the two
target markings. -/
theorem pullback_picardMarking_targetIso (hI : I = J) (a : L₁) :
    LineBundleClass.pullback (surfaceIso (R.iso.symm ≪≫ R'.iso)).hom
      (Q.picardMarking a).toMul = (P.picardMarking a).toMul := by
  apply (LineBundleClass.pullbackEquiv (surfaceIso R.iso)).injective
  have ha := congrArg Additive.toMul ((R'.picard_eq a).symm.trans
    ((congrArg (fun f : B₁.IsometryEquiv B₀ ↦ M.picardMarking (f a)) hI).symm.trans
      (R.picard_eq a)))
  simpa only [LineBundleClass.pullbackEquiv_apply, LineBundleClass.pullback_comp,
    MarkedSurface.surfaceIso_trans, MarkedSurface.surfaceIso_symm, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc, toMul_ofMul] using ha

/-- Equality of the boundary actions makes the residual isomorphism preserve every
numbered branch. -/
theorem boundaryCycleAction_targetIso (hg : g = h) :
    letI : PrestableFamily (P.boundary ↘ Spec (.of k)) := P.prestable
    letI : PrestableFamily (Q.boundary ↘ Spec (.of k)) := Q.prestable
    (boundaryIso (R.iso.symm ≪≫ R'.iso)).boundaryCycleAction P.cycle Q.cycle = 1 := by
  let : PrestableFamily (M.boundary ↘ Spec (.of k)) := M.prestable
  let : PrestableFamily (P.boundary ↘ Spec (.of k)) := P.prestable
  let : PrestableFamily (Q.boundary ↘ Spec (.of k)) := Q.prestable
  have hpair : R.iso ≪≫ (R.iso.symm ≪≫ R'.iso) = R'.iso := by simp
  have hcomp := (boundaryIso R.iso).boundaryCycleAction_trans M.cycle P.cycle
    (boundaryIso (R.iso.symm ≪≫ R'.iso)) Q.cycle
  have hmul : h = (boundaryIso (R.iso.symm ≪≫ R'.iso)).boundaryCycleAction P.cycle Q.cycle * h := by
    simpa only [← MarkedSurface.boundaryIso_trans, hpair, R'.boundaryAction_eq,
      R.boundaryAction_eq, hg] using hcomp
  exact mul_right_cancel ((one_mul h).trans hmul).symm

end FiberRealization

end Residual

local notation "D[" P "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair P)))

namespace MarkedSurface

universe u

variable {k : Type u} [Field k] [IsSepClosed k] [Infinite k] {n : ℕ} [NeZero n]
  {L : Type u} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L} {X : Scheme.{u}}
  (P : MarkedSurface k n B X)

/-- The specified closed boundary identifies with the subscheme cut out by its ideal. -/
private def boundaryImageIso : P.boundary ≅ D[P].subscheme :=
  letI : IsClosedImmersion P.pair.hom.left := P.closedImmersion
  asIso P.pair.hom.left.toImage

@[reassoc]
private theorem boundaryImageIso_hom_comp :
    (boundaryImageIso P).hom ≫ D[P].subschemeι = P.pair.hom.left :=
  P.pair.hom.left.toImage_imageι

private instance :
    (boundaryImageIso P).hom.IsOver (Spec (.of k)) := by
  constructor
  rw [over_eq_subschemeι_comp, boundaryImageIso_hom_comp_assoc]
  exact Over.w P.pair.hom

/-- The subscheme cut out by the ideal of a marked surface's boundary is prestable. -/
theorem prestable_boundaryImage : PrestableFamily (D[P].subscheme ↘ Spec (.of k)) := by
  have h : (boundaryImageIso P).hom ≫ (D[P].subscheme ↘ Spec (.of k)) =
      (P.boundary ↘ Spec (.of k)) := HomIsOver.comp_over
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @PrestableFamily)
    (boundaryImageIso P).hom _).mp (h.symm ▸ P.prestable)

end MarkedSurface

open MarkedSurface (boundaryImageIso boundaryImageIso_hom_comp boundaryImageIso_hom_comp_assoc)

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

variable (P) in
private def imageCycle :
    NodalCycleNumbering (Empty.elim : Empty → (D[P].subscheme ↘ S).smoothLocus) n :=
  letI : PrestableFamily (P.boundary ↘ S) := P.prestable
  (boundaryImageIso P).mapNodalCycleNumbering P.cycle

private theorem boundaryCycleAction_boundaryImageIso :
    letI : PrestableFamily (P.boundary ↘ S) := P.prestable
    (boundaryImageIso P).boundaryCycleAction P.cycle (imageCycle P) = 1 := by
  let : PrestableFamily (P.boundary ↘ S) := P.prestable
  refine ((boundaryImageIso P).existsUnique_boundaryCycleAction P.cycle
    (D := imageCycle P)).unique (Iso.branch_boundaryCycleAction _ _ _) ?_
  intro j l
  simpa only [map_one, Equiv.Perm.one_apply, imageCycle] using
    ((boundaryImageIso P).branch_mapNodalCycleNumbering P.cycle j l)

private theorem imageCycle_genericPoint (j : ZMod n) :
    letI : PrestableFamily (P.boundary ↘ S) := P.prestable
    D[P].subschemeι ((imageCycle P).componentGenericPoint j) =
      P.pair.hom.left (P.cycle.componentGenericPoint j) := by
  let : PrestableFamily (P.boundary ↘ S) := P.prestable
  have h := (boundaryImageIso P).apply_componentGenericPoint P.cycle (imageCycle P) j
  rw [boundaryCycleAction_boundaryImageIso, map_one, Equiv.Perm.one_apply] at h
  rw [← h, ← Scheme.Hom.comp_apply, boundaryImageIso_hom_comp]

private def imagePairIso (e : P.pair ≅ Q.pair) : D[P].subscheme ≅ D[Q].subscheme :=
  (boundaryImageIso P).symm ≪≫ (boundaryIso e ≪≫ boundaryImageIso Q)

private instance (e : P.pair ≅ Q.pair) : (imagePairIso e).hom.IsOver S :=
  inferInstanceAs (((boundaryImageIso P).inv ≫ (boundaryIso e).hom ≫
    (boundaryImageIso Q).hom).IsOver S)

private theorem imagePairIso_hom_comp (e : P.pair ≅ Q.pair) :
    (imagePairIso e).hom ≫ D[Q].subschemeι = D[P].subschemeι ≫ (surfaceIso e).hom := by
  apply (cancel_epi (boundaryImageIso P).hom).mp
  simpa only [imagePairIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
    boundaryImageIso_hom_comp_assoc, boundaryImageIso_hom_comp] using
      MarkedSurface.boundaryIso_hom_comp e

private theorem imagePairIso_boundaryAction (e : P.pair ≅ Q.pair)
    (hact : letI : PrestableFamily (P.boundary ↘ S) := P.prestable
            letI : PrestableFamily (Q.boundary ↘ S) := Q.prestable
            (boundaryIso e).boundaryCycleAction P.cycle Q.cycle = 1) :
    (imagePairIso e).boundaryCycleAction (imageCycle P) (imageCycle Q) = DihedralGroup.r 0 := by
  let : PrestableFamily (P.boundary ↘ S) := P.prestable
  let : PrestableFamily (Q.boundary ↘ S) := Q.prestable
  let : (boundaryImageIso P).symm.hom.IsOver S :=
    inferInstanceAs ((boundaryImageIso P).inv.IsOver S)
  let : (boundaryIso e ≪≫ boundaryImageIso Q).hom.IsOver S :=
    inferInstanceAs (((boundaryIso e).hom ≫ (boundaryImageIso Q).hom).IsOver S)
  calc
    _ = (boundaryIso e ≪≫ boundaryImageIso Q).boundaryCycleAction P.cycle (imageCycle Q) *
          (boundaryImageIso P).symm.boundaryCycleAction (imageCycle P) P.cycle :=
      Iso.boundaryCycleAction_trans _ _ _ _ _
    _ = _ := by
      have hinv := (boundaryImageIso P).boundaryCycleAction_symm P.cycle (imageCycle P)
      rw [boundaryCycleAction_boundaryImageIso, inv_one] at hinv
      rw [Iso.boundaryCycleAction_trans (boundaryIso e) P.cycle Q.cycle, hinv,
        boundaryCycleAction_boundaryImageIso, hact, mul_one, mul_one, DihedralGroup.one_def]

private theorem isOrientedCycleSubdivision_comp_boundaryImage :
    (p.boundaryMap ≫ (boundaryImageIso P).hom).IsOrientedCycleSubdivision T (imageCycle P) := by
  let : PrestableFamily (P.boundary ↘ S) := P.prestable
  exact p.orientedSubdivision.comp
    ((boundaryImageIso P).isOrientedCycleSubdivision_of_cycleOrientationSign_eq_one _ _
      (by rw [boundaryCycleAction_boundaryImageIso, map_one]))

variable (u : ZMod m ≃ Φ.Ray)
  (hvertices : ∀ j, Dtor[Φ,h₀].dualGraphVertexEquiv a (T.vertex j) =
    Φ.boundaryNormalizationComponentEquiv hΦ (u j))

include hvertices in
private theorem internalBlowupBoundaryPrime_val (j : ZMod m) :
    (prime[b,s,hΦ,c] (u j)).val = (Model[b,s,c]).2.boundaryι (T.componentGenericPoint j) := by
  let v := T.component j
  let ν := (Dtor[Φ,h₀].singularLocus ℂ).blowupToBase
  let jD := (Model[b,s,c]).2.boundaryι
  have hv : v = Φ.boundaryNormalizationComponentEquiv hΦ (u j) :=
    (T.component_apply j).trans (hvertices j)
  have h := (genericPoints.isGenericPoint_ofComponent v).image (ν ≫ jD).continuous
  have hr : (ν ≫ jD) '' (v : Set _) =
      Set.range ((u j).boundaryComponentι hΦ ≫ jD) := by
    have hray := Φ.range_boundaryNormalizationComponentEquiv hΦ (u j)
    rw [← hv] at hray
    simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.image_comp,
      Scheme.Opens.range_ι, Scheme.coe_blowupComponent] using congrArg (fun Z ↦ jD '' Z) hray
  rw [hr, Fan.range_rayComponent_internalBlowupBoundaryPrimeEquiv] at h
  rw [closure_closure] at h
  simpa only [Hom.comp_apply, NodalCycleNumbering.componentGenericPoint_def, v, ν, jD] using
    (h.eq isGenericPoint_closure).symm

include p hvertices in
private theorem projection_prime_origin :
    letI : PrestableFamily (P.boundary ↘ S) := P.prestable
    p.projection (prime[b,s,hΦ,c] (u origin)).val =
      P.pair.hom.left (P.cycle.componentGenericPoint 0) := by
  let : PrestableFamily (P.boundary ↘ S) := P.prestable
  rw [internalBlowupBoundaryPrime_val u hvertices, ← Hom.comp_apply, ← p.boundary_comp,
    Hom.comp_apply, p.component_zero]

private theorem boundaryPrime_mem_boundaryPrimes
    (hP : D[P].IsEffectiveCartier) : (P.boundaryPrime hP 0 : P.surface) ∈ D[P].boundaryPrimes := by
  let : PrestableFamily (P.boundary ↘ S) := P.prestable
  let : IsClosedImmersion P.pair.hom.left := P.closedImmersion
  refine mem_boundaryPrimes.mpr ⟨?_, (P.boundaryPrime hP 0).property⟩
  have hs : (D[P].support : Set P.surface) = Set.range P.pair.hom.left :=
    P.pair.hom.left.support_ker.trans P.pair.hom.left.isClosedEmbedding.isClosed_range.closure_eq
  rw [P.coe_boundaryPrime]
  rw [← SetLike.mem_coe, hs]
  exact Set.mem_range_self _

private theorem isPerfPair_intersectionForm (P : MarkedSurface ℂ n B₁ Xtor[r]) [B₁.IsPerfPair] :
    letI : SmoothOfRelativeDimension 2 (P.surface ↘ S) := P.smooth
    letI : P.surface.IsProjectiveOver ℂ := P.projective
    (Chow.intersectionBilinForm ℂ P.surface).IsPerfPair := by
  let : SmoothOfRelativeDimension 2 (P.surface ↘ S) := P.smooth
  let : P.surface.IsProjectiveOver ℂ := P.projective
  refine LinearMap.IsPerfPair.congr B₁ P.marking.toLinearEquiv.symm
    P.marking.toLinearEquiv.symm _ (LinearMap.ext₂ fun x y ↦ ?_)
  simpa only [LinearMap.compl₁₂_apply, LinearEquiv.symm_symm, LinearEquiv.coe_coe,
    LinearMap.BilinForm.IsometryEquiv.coe_toLinearEquiv] using P.marking.map_app y x

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
  let := isPerfPair_intersectionForm P
  let := isPerfPair_intersectionForm Q
  let vB := imagePairIso e
  have hv := imagePairIso_hom_comp e
  have hB := imagePairIso_boundaryAction e hact
  obtain ⟨_, _, A, hA, eP, heP⟩ := hp.exists_tower
  obtain ⟨_, _, B, hB', eQ, heQ⟩ := hq.exists_tower
  let f := p.boundaryMap ≫ (boundaryImageIso P).hom
  let g := q.boundaryMap ≫ (boundaryImageIso Q).hom
  have hf : f ≫ D[P].subschemeι = (Model[b,s,c]).2.boundaryι ≫ p.projection := by
    simpa only [f, Category.assoc, boundaryImageIso_hom_comp] using p.boundary_comp
  have hg : g ≫ D[Q].subschemeι = (Model[b,s,d]).2.boundaryι ≫ q.projection := by
    simpa only [g, Category.assoc, boundaryImageIso_hom_comp] using q.boundary_comp
  let x : D[P].boundaryPrimes :=
    ⟨P.boundaryPrime hp.cartier 0, boundaryPrime_mem_boundaryPrimes hp.cartier⟩
  let y : D[Q].boundaryPrimes :=
    ⟨Q.boundaryPrime hq.cartier 0, boundaryPrime_mem_boundaryPrimes hq.cartier⟩
  rw [p.evaluation_eq, q.evaluation_eq]
  simpa only [heP, heQ] using
    (Fan.comp_contractedXEvaluation_eq_of_matching_markings b s hΦ c d hA hB' eP eQ
        (imageCycle P) (imageCycle Q) T hc
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
        (by simpa only [x, P.coe_boundaryPrime] using (imageCycle_genericPoint (P := P) 0).symm)
        (by simpa only [y, Q.coe_boundaryPrime] using (imageCycle_genericPoint (P := Q) 0).symm)
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
