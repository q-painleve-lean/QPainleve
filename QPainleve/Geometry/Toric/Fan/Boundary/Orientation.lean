/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Period.Basic
public import QPainleve.Geometry.Toric.Fan.Boundary.DualGraph

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

universe u

variable {N N' : Type u} {V V' : Type*} [AddCommGroup N] [AddCommGroup N']
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

variable (K : Type u) [Field K] [IsSepClosed K]

variable [hΦ₀ : Nonempty Φ.cones] [hΨ₀ : Nonempty Ψ.cones]
  (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)

local notation "base" => Spec (CommRingCat.of K)
local notation "D[" Φ "]" => Fan.toricBoundaryIdeal K Φ inferInstance
local notation "C[" Φ "]" => Scheme.IdealSheafData.subscheme (D[Φ])
local notation "ν[" Φ "]" => Scheme.IdealSheafData.blowupToBase (Scheme.singularLocus K (C[Φ]))
local notation "g" => e.boundaryIso K hΦ₀ hΨ₀
local notation "gν" => Iso.hom (Iso.singularLocusBlowupIso (R := K) g)

variable [PrestableFamily ((Φ.toricBoundaryIdeal K hΦ₀).subscheme ↘ Spec (.of K))]
  [PrestableFamily ((Ψ.toricBoundaryIdeal K hΨ₀).subscheme ↘ Spec (.of K))]

local notation "U[" Φ "," h "," ρ "]" =>
  Fan.boundaryNormalizationComponentEquiv K Φ h ρ

section Orders

variable {n m : ℕ} [NeZero n] [NeZero m]
  {α β : Type*} {p : α → ((Φ.toricBoundaryIdeal K hΦ₀).subscheme ↘ Spec (.of K)).smoothLocus}
  {p' : β → ((Ψ.toricBoundaryIdeal K hΨ₀).subscheme ↘ Spec (.of K)).smoothLocus}

local notation "G[" p "]" => Scheme.dualGraph (K := K) _ p

variable
  {a : ZMod n ≃ ((Φ.toricBoundaryIdeal K hΦ₀).subscheme.dualGraph p).Edge}
  {a' : ZMod m ≃ ((Ψ.toricBoundaryIdeal K hΨ₀).subscheme.dualGraph p').Edge}
  {o : ((Φ.toricBoundaryIdeal K hΦ₀).subscheme.dualGraph p).Edge → Equiv.Perm (Fin 2)}
  {o' : ((Ψ.toricBoundaryIdeal K hΨ₀).subscheme.dualGraph p').Edge → Equiv.Perm (Fin 2)}
  {w : ZMod n ≃ ((Φ.toricBoundaryIdeal K hΦ₀).subscheme.dualGraph p).Vertex}
  {w' : ZMod m ≃ ((Ψ.toricBoundaryIdeal K hΨ₀).subscheme.dualGraph p').Vertex}
  (hw : ∀ j b, ((Φ.toricBoundaryIdeal K hΦ₀).subscheme.dualGraph p).endpoint (a j) (o (a j) b) =
    w ((DualGraph.cycle n).endpoint j b))
  (hw' : ∀ j b,
    ((Ψ.toricBoundaryIdeal K hΨ₀).subscheme.dualGraph p').endpoint (a' j) (o' (a' j) b) =
    w' ((DualGraph.cycle m).endpoint j b))
  {u : ZMod n ≃ Φ.Ray} {u' : ZMod m ≃ Ψ.Ray}
  (hu : ∀ j, (Φ.toricBoundaryIdeal K hΦ₀).subscheme.dualGraphVertexEquiv p (w j) =
    Φ.boundaryNormalizationComponentEquiv K hΦ (u j))
  (hu' : ∀ j, (Ψ.toricBoundaryIdeal K hΨ₀).subscheme.dualGraphVertexEquiv p' (w' j) =
    Ψ.boundaryNormalizationComponentEquiv K hΨ (u' j))
  (b : Module.Basis (Fin 2) ℤ N) (b' : Module.Basis (Fin 2) ℤ N')
  (hpos : ∀ j, b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1)
  (hpos' : ∀ j, b'.detDualEquiv (u' j).primitiveGenerator (u' (j + 1)).primitiveGenerator = 1)

include hw hw' hu hu' in
private theorem branchOrder_preserves_ray
    (j : ZMod n) (l : ZMod m) (v v' : Fin 2)
    (he : (Iso.branchSchemeIso (R := K) g).hom
        ((C[Φ]).branchOrderOfDualGraph p o ((C[Φ]).dualGraphNodeEquiv p (a j)) v).val =
      ((C[Ψ]).branchOrderOfDualGraph p' o' ((C[Ψ]).dualGraphNodeEquiv p' (a' l)) v').val) :
    e.rayEquiv (u ((DualGraph.cycle n).endpoint j v)) = u' ((DualGraph.cycle m).endpoint l v') := by
  have hs := (C[Φ]).branchPointEquiv_mem_dualGraph_endpoint p (a j) (o (a j) v)
  rw [hw, hu] at hs
  have hm := Set.mem_image_of_mem gν hs
  rw [image_singularLocusBlowupIso_boundaryNormalizationComponent K e hΦ hΨ] at hm
  have hh := congrArg ((C[Ψ]).branchSchemeToBlowup K) he
  rw [← Scheme.Hom.comp_apply, Iso.branchSchemeIso_hom_branchSchemeToBlowup] at hh
  simp only [Scheme.Hom.comp_apply, Scheme.branchOrderOfDualGraph_apply_val,
    Scheme.branchSchemeToBlowup_dualGraphBranchEquiv] at hh
  rw [hh] at hm
  have heq := ((C[Ψ]).dualGraphVertexEquiv_endpoint_eq_iff p' (a' l) (o' (a' l) v') _).mpr hm
  rw [hw', hu'] at heq
  exact (Ψ.boundaryNormalizationComponentEquiv K hΨ).injective heq.symm

include hw hw' hu hu' hpos hpos' in
/-- Relative to positive cyclic numberings on the source and target, a fan
equivalence transports each ordered branch to the same branch index when it
preserves the determinant and to the opposite index when it negates it. -/
theorem branchSchemeIso_branchOrderOfDualGraph (swap : Bool)
    (hdet : ∀ x y, b'.detDualEquiv (e.latticeEquiv x) (e.latticeEquiv y) =
      if swap then -b.detDualEquiv x y else b.detDualEquiv x y)
    (z : (Scheme.singularLocus K (C[Φ])).subscheme) (v : Fin 2) :
    (Iso.branchSchemeIso (R := K) g).hom ((C[Φ]).branchOrderOfDualGraph p o z v).val =
      ((C[Ψ]).branchOrderOfDualGraph p' o' ((Iso.singularLocusIso (R := K) g).hom z)
        (if swap then v.rev else v)).val := by
  let z' := (Iso.singularLocusIso (R := K) g).hom z
  let T := (C[Ψ]).branchOrderOfDualGraph p' o' z'
  let S := (C[Φ]).branchOrderOfDualGraph p o z
  let q := (Iso.branchSchemeIso (R := K) g).hom
  let t (v : Fin 2) : {y : (C[Ψ]).branchScheme K // (C[Ψ]).branchSchemeToSingularLocus K y = z'} :=
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
    apply branchOrder_preserves_ray e K hΦ hΨ hw hw' hu hu'
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

variable [IsAlgClosed K] in
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
    (e.branchSchemeIso_branchOrderOfDualGraph K hΦ hΨ hw hw' hu hu' b b' hpos hpos' swap hdet) L

end Orders

end Normalization

end TauCeti.Toric.FanEquiv
