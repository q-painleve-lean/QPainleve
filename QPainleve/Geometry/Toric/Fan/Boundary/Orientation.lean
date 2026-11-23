/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Period.Basic
public import QPainleve.Geometry.Toric.Fan.Boundary.DualGraph
public import QPainleve.Geometry.Toric.Fan.Boundary.Equiv

/-!
# Branch orders under toric isomorphisms

An integral fan equivalence transports the nodes and individual branches of the
reduced toric boundary. The sign of its action on determinant characters gives
the change of orientation, hence the change of the period of a line bundle
trivial on the normalization. The period convention is that of
[Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*, Lemma 2.1][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S2
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.FanEquiv

variable {N N' V V' : Type} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'} (e : FanEquiv Φ Ψ)

private theorem branchIndex_eq_of_det {m : ℕ} [NeZero m] {u' : ZMod m ≃ Ψ.Ray}
    (b' : Module.Basis (Fin 2) ℤ N')
    (hpos' : ∀ j, b'.detDualEquiv (u' j).primitiveGenerator (u' (j + 1)).primitiveGenerator = 1)
    (l : ZMod m) (f : Fin 2 → Fin 2) (hne : f 0 ≠ f 1)
    (swap : Bool)
    (hd : b'.detDualEquiv
      (u' ((DualGraph.cycle m).endpoint l (f 0))).primitiveGenerator
      (u' ((DualGraph.cycle m).endpoint l (f 1))).primitiveGenerator =
      if swap then -1 else 1) (v : Fin 2) :
    f v = if swap then v.rev else v := by
  have hsplit : f 0 = 0 ∨ f 0 = 1 := by omega
  rcases hsplit with h | h
  · have h' : f 1 = 1 := by omega
    have hd' : (1 : ℤ) = if swap then -1 else 1 := by
      simpa [h, h', hpos'] using hd
    have hs : swap = false := by
      cases swap with
      | false => rfl
      | true => norm_num at hd'
    fin_cases v <;> simp [h, h', hs]
  · have h' : f 1 = 0 := by omega
    have hd' : (-1 : ℤ) = if swap then -1 else 1 := by
      simpa [h, h', b'.detDualEquiv_swap (u' (l + 1)).primitiveGenerator,
        hpos'] using hd
    have hs : swap = true := by
      cases swap with
      | false => norm_num at hd'
      | true => rfl
    fin_cases v <;> simp [h, h', hs, Fin.rev]

section Normalization

variable [hΦ₀ : Nonempty Φ.cones] [hΨ₀ : Nonempty Ψ.cones]
  (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)

local notation "base" => Spec (CommRingCat.of ℂ)
local notation "D[" Φ "]" => Fan.boundaryIdeal Φ inferInstance
local notation "C[" Φ "]" => Scheme.IdealSheafData.subscheme (D[Φ])
local notation "ν[" Φ "]" => Scheme.IdealSheafData.blowupToBase (Scheme.singularLocus ℂ (C[Φ]))
local notation "g" => e.boundaryIso hΦ₀ hΨ₀
local notation "gν" => Iso.hom (Iso.singularLocusBlowupIso (R := ℂ) g)

variable [PrestableFamily (C[Φ] ↘ base)] [PrestableFamily (C[Ψ] ↘ base)]

local notation "U[" Φ "," h "," ρ "]" =>
  Fan.boundaryNormalizationComponentEquiv Φ h ρ

private theorem range_normalizationComponent_to_toric
    {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
    {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]
    [PrestableFamily (C[Φ] ↘ base)] (hΦ : Φ.IsRegular) (ρ : Φ.Ray) :
    Set.range (((C[Φ]).blowupComponent (K := ℂ) (U[Φ,hΦ,ρ])).ι ≫
      ν[Φ] ≫ (D[Φ]).subschemeι) = closure {(Φ.rayBoundaryPoint hΦ ρ).val} := by
  rw [← Category.assoc, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Φ.range_boundaryNormalizationComponentEquiv hΦ ρ, ← Set.range_comp, ← TopCat.coe_comp,
    ← Scheme.Hom.comp_base, ρ.boundaryComponentι_subschemeι hΦ,
    Scheme.IdealSheafData.range_subschemeι,
    Φ.coe_support_rayBoundaryIdeal]

/-- The isomorphism of normalizations carries the component indexed by a ray
onto the component indexed by its image ray. -/
theorem image_singularLocusBlowupIso_boundaryNormalizationComponent (ρ : Φ.Ray) :
    (gν) '' (U[Φ,hΦ,ρ] : Set (Scheme.singularLocus ℂ (C[Φ])).blowup) =
      (U[Ψ,hΨ,e.rayEquiv ρ] : Set (Scheme.singularLocus ℂ (C[Ψ])).blowup) := by
  let w := U[Φ,hΦ,ρ]
  let F := ν[Ψ] ≫ (D[Ψ]).subschemeι
  let G := ν[Φ] ≫ (D[Φ]).subschemeι
  let I := gν
  have hI : I ≫ F = G ≫ e.toFanHom.algebraicMap := by
    simp only [I, F, G, Category.assoc, Iso.singularLocusBlowupIso_hom_blowupToBase_assoc,
      boundaryIso_hom_subschemeι]
  have him : I '' (w : Set _) ∈ irreducibleComponents (Scheme.singularLocus ℂ (C[Ψ])).blowup := by
    apply image_mem_irreducibleComponents_of_isPreirreducible_fiber I I.continuous
      I.homeomorph.isOpenMap (fun _ ↦ (Set.subsingleton_singleton.preimage
        I.homeomorph.injective).isPreirreducible) I.homeomorph.surjective w.property
  let w' : irreducibleComponents (Scheme.singularLocus ℂ (C[Ψ])).blowup := ⟨I '' w.val, him⟩
  have hG : G '' (w : Set _) = closure {(Φ.rayBoundaryPoint hΦ ρ).val} := by
    rw [← Scheme.coe_blowupComponent (K := ℂ) (C[Φ]) w,
      ← Scheme.Opens.range_ι, ← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base]
    exact range_normalizationComponent_to_toric hΦ ρ
  have hr :
      F '' (w' : Set _) = closure {(Ψ.rayBoundaryPoint hΨ (e.rayEquiv ρ)).val} := by
    have hpoint (x : (Scheme.singularLocus ℂ (C[Φ])).blowup) :
        F (I x) = e.toFanHom.algebraicMap (G x) := by
      simpa only [Scheme.Hom.comp_apply] using
        congrArg (fun f : _ ⟶ Ψ.algebraicRealization ↦ f x) hI
    rw [Subtype.coe_mk, Set.image_image, Set.image_congr (fun x _ ↦ hpoint x),
      ← Set.image_image, hG]
    rw [← e.toFanHom.algebraicMap.isClosedMap.closure_image_eq_of_continuous
      e.toFanHom.algebraicMap.continuous, Set.image_singleton, e.algebraicMap_rayBoundaryPoint]
  have hw' : w' = U[Ψ,hΨ,e.rayEquiv ρ] := by
    apply (C[Ψ]).eq_of_range_blowupComponent_subset (k := ℂ)
    rw [← Set.image_subset_image_iff (D[Ψ]).subschemeι.isClosedEmbedding.injective,
      ← Set.range_comp, ← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
      ← TopCat.coe_comp, ← Scheme.Hom.comp_base, Category.assoc, Category.assoc,
      range_normalizationComponent_to_toric, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι, Scheme.coe_blowupComponent]
    exact hr.le
  exact congrArg Subtype.val hw'

section Orders

variable {n m : ℕ} [NeZero n] [NeZero m]
  {α β : Type*} {p : α → (C[Φ] ↘ base).smoothLocus}
  {p' : β → (C[Ψ] ↘ base).smoothLocus}

local notation "G[" p "]" => Scheme.dualGraph (K := ℂ) _ p

/-- The induced isomorphism of singular loci sends the node of a cone to the
node of its image cone. The edge labels can come from independent numberings. -/
theorem singularLocusIso_dualGraphNodeEquiv_of_distinguishedPoint
    {σ : Φ.cones} {x : (G[p]).Edge} {y : (G[p']).Edge}
    (hx : (D[Φ]).subschemeι ((C[Φ]).dualGraphEdgeEquiv p x).val =
      Φ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ))
    (hy : (D[Ψ]).subschemeι ((C[Ψ]).dualGraphEdgeEquiv p' y).val =
      Ψ.distinguishedPointHom (e.coneEquiv σ) (IsLocalRing.closedPoint ℂ)) :
    (Iso.singularLocusIso (R := ℂ) g).hom ((C[Φ]).dualGraphNodeEquiv p x) =
      (C[Ψ]).dualGraphNodeEquiv p' y := by
  let I := Scheme.singularLocus ℂ (C[Φ])
  let J := Scheme.singularLocus ℂ (C[Ψ])
  let f := (Iso.singularLocusIso (R := ℂ) g).hom
  have h : f ≫ J.subschemeι ≫ (D[Ψ]).subschemeι =
      I.subschemeι ≫ (D[Φ]).subschemeι ≫ e.toFanHom.algebraicMap := by
    simp only [f, I, J, Iso.singularLocusIso_hom_subschemeι_assoc, boundaryIso_hom_subschemeι]
  have hp := congrArg (fun k : I.subscheme ⟶ Ψ.algebraicRealization ↦
    k ((C[Φ]).dualGraphNodeEquiv p x)) h
  let z := IsLocalRing.closedPoint ℂ
  have hσ : e.toFanHom.algebraicMap (Φ.distinguishedPointHom σ z) =
      Ψ.distinguishedPointHom (e.coneEquiv σ) z := by
    calc
      _ = (Φ.distinguishedPointHom σ ≫ e.toFanHom.algebraicMap) z :=
        (Scheme.Hom.comp_apply (Φ.distinguishedPointHom σ) e.toFanHom.algebraicMap z).symm
      _ = _ := by rw [e.distinguishedPointHom_comp_algebraicMap]
  simp only [I, Scheme.Hom.comp_apply, Scheme.subschemeι_dualGraphNodeEquiv, hx] at hp
  apply J.subschemeι.isClosedEmbedding.injective
  apply (D[Ψ]).subschemeι.isClosedEmbedding.injective
  simpa only [J, Scheme.subschemeι_dualGraphNodeEquiv, hy, z] using hp.trans hσ

variable
  {a : ZMod n ≃ (G[p]).Edge} {a' : ZMod m ≃ (G[p']).Edge}
  {o : (G[p]).Edge → Equiv.Perm (Fin 2)} {o' : (G[p']).Edge → Equiv.Perm (Fin 2)}
  {w : ZMod n ≃ (G[p]).Vertex} {w' : ZMod m ≃ (G[p']).Vertex}
  (hw : ∀ j b, (G[p]).endpoint (a j) (o (a j) b) = w ((DualGraph.cycle n).endpoint j b))
  (hw' : ∀ j b, (G[p']).endpoint (a' j) (o' (a' j) b) = w' ((DualGraph.cycle m).endpoint j b))
  {u : ZMod n ≃ Φ.Ray} {u' : ZMod m ≃ Ψ.Ray}
  (hu : ∀ j, (C[Φ]).dualGraphVertexEquiv p (w j) = U[Φ,hΦ,u j])
  (hu' : ∀ j, (C[Ψ]).dualGraphVertexEquiv p' (w' j) = U[Ψ,hΨ,u' j])
  (b : Module.Basis (Fin 2) ℤ N) (b' : Module.Basis (Fin 2) ℤ N')
  (hpos : ∀ j, b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1)
  (hpos' : ∀ j, b'.detDualEquiv (u' j).primitiveGenerator (u' (j + 1)).primitiveGenerator = 1)

include hw hw' hu hu' in
private theorem branchOrder_preserves_ray
    (j : ZMod n) (l : ZMod m) (v v' : Fin 2)
    (he : (Iso.branchSchemeIso (R := ℂ) g).hom
        ((C[Φ]).branchOrderOfDualGraph p o ((C[Φ]).dualGraphNodeEquiv p (a j)) v).val =
      ((C[Ψ]).branchOrderOfDualGraph p' o' ((C[Ψ]).dualGraphNodeEquiv p' (a' l)) v').val) :
    e.rayEquiv (u ((DualGraph.cycle n).endpoint j v)) = u' ((DualGraph.cycle m).endpoint l v') := by
  have hs := (C[Φ]).branchPointEquiv_mem_dualGraph_endpoint p (a j) (o (a j) v)
  rw [hw, hu] at hs
  have hm := Set.mem_image_of_mem gν hs
  rw [image_singularLocusBlowupIso_boundaryNormalizationComponent e hΦ hΨ] at hm
  have hh := congrArg ((C[Ψ]).branchSchemeToBlowup ℂ) he
  rw [← Scheme.Hom.comp_apply, Iso.branchSchemeIso_hom_branchSchemeToBlowup] at hh
  simp only [Scheme.Hom.comp_apply, Scheme.branchOrderOfDualGraph_apply_val,
    Scheme.branchSchemeToBlowup_dualGraphBranchEquiv] at hh
  rw [hh] at hm
  have heq := ((C[Ψ]).dualGraphVertexEquiv_endpoint_eq_iff p' (a' l) (o' (a' l) v') _).mpr hm
  rw [hw', hu'] at heq
  exact (Ψ.boundaryNormalizationComponentEquiv hΨ).injective heq.symm

include hw hw' hu hu' hpos hpos' in
/-- Relative to positive cyclic numberings on the source and target, a fan
equivalence transports each ordered branch to the same branch index when it
preserves the determinant and to the opposite index when it negates it. -/
theorem branchSchemeIso_branchOrderOfDualGraph (swap : Bool)
    (hdet : ∀ x y, b'.detDualEquiv (e.latticeEquiv x) (e.latticeEquiv y) =
      if swap then -b.detDualEquiv x y else b.detDualEquiv x y)
    (z : (Scheme.singularLocus ℂ (C[Φ])).subscheme) (v : Fin 2) :
    (Iso.branchSchemeIso (R := ℂ) g).hom ((C[Φ]).branchOrderOfDualGraph p o z v).val =
      ((C[Ψ]).branchOrderOfDualGraph p' o' ((Iso.singularLocusIso (R := ℂ) g).hom z)
        (if swap then v.rev else v)).val := by
  let z' := (Iso.singularLocusIso (R := ℂ) g).hom z
  let T := (C[Ψ]).branchOrderOfDualGraph p' o' z'
  let S := (C[Φ]).branchOrderOfDualGraph p o z
  let q := (Iso.branchSchemeIso (R := ℂ) g).hom
  let t (v : Fin 2) : {y : (C[Ψ]).branchScheme ℂ // (C[Ψ]).branchSchemeToSingularLocus ℂ y = z'} :=
    ⟨q (S v).val, by
      rw [← Scheme.Hom.comp_apply, Iso.branchSchemeIso_hom_branchSchemeToSingularLocus,
        Scheme.Hom.comp_apply, (S v).property]⟩
  let f (v : Fin 2) : Fin 2 := T.symm (t v)
  have hf (v : Fin 2) : q (S v).val = (T (f v)).val :=
    (congrArg Subtype.val (T.apply_symm_apply (t v))).symm
  have hne : f 0 ≠ f 1 := by
    intro he
    have he' : q (S 0).val = q (S 1).val := by rw [hf, hf, he]
    exact zero_ne_one (S.injective (Subtype.ext (q.homeomorph.injective he')))
  obtain ⟨j, hj⟩ := (a.trans ((C[Φ]).dualGraphNodeEquiv p)).surjective z
  obtain ⟨l, hl⟩ := (a'.trans ((C[Ψ]).dualGraphNodeEquiv p')).surjective z'
  simp only [Equiv.trans_apply] at hj hl
  have hr (v : Fin 2) :
      e.rayEquiv (u ((DualGraph.cycle n).endpoint j v)) =
        u' ((DualGraph.cycle m).endpoint l (f v)) := by
    apply branchOrder_preserves_ray e hΦ hΨ hw hw' hu hu'
    rw [hj, hl]
    exact hf v
  have hd := hdet (u j).primitiveGenerator (u (j + 1)).primitiveGenerator
  have h₀ : e.latticeEquiv (u j).primitiveGenerator =
      (u' ((DualGraph.cycle m).endpoint l (f 0))).primitiveGenerator := by
    simpa using congrArg Fan.Ray.primitiveGenerator (hr 0)
  have h₁ : e.latticeEquiv (u (j + 1)).primitiveGenerator =
      (u' ((DualGraph.cycle m).endpoint l (f 1))).primitiveGenerator := by
    simpa using congrArg Fan.Ray.primitiveGenerator (hr 1)
  rw [h₀, h₁, hpos] at hd
  have hfv := branchIndex_eq_of_det b' hpos' l f hne swap hd v
  rw [← hfv]
  exact hf v

include hu hu' hpos hpos' in
/-- Pullback along a fan equivalence preserves the period in positive cyclic
orientations when the lattice map preserves determinants. It inverts the
period when the lattice map reverses determinants. -/
theorem nodalPicardCycleMulEquiv_pullback (swap : Bool)
    (hdet : ∀ x y, b'.detDualEquiv (e.latticeEquiv x) (e.latticeEquiv y) =
      if swap then -b.detDualEquiv x y else b.detDualEquiv x y)
    (L : MonoidHom.ker (LineBundleClass.pullbackHom (ν[Ψ]))) :
    Scheme.nodalPicardCycleMulEquiv hw
      ⟨LineBundleClass.pullback (g).hom L.val,
        Iso.pullback_mem_ker_pullback_blowupToBase_singularLocus g L⟩ =
      if swap then (Scheme.nodalPicardCycleMulEquiv hw' L)⁻¹
      else Scheme.nodalPicardCycleMulEquiv hw' L := by
  exact Iso.nodalPicardCycleMulEquiv_pullback g hw hw' swap
    (e.branchSchemeIso_branchOrderOfDualGraph hΦ hΨ hw hw' hu hu' b b' hpos hpos' swap hdet) L

end Orders

end Normalization

end TauCeti.Toric.FanEquiv
