/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Rescaling
public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Units
public import TauCeti.AlgebraicGeometry.Curves.Node.DualGraph.Basic

import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Map

/-!
# Global functions in the nodal conductor square

The native dual graph labels the points of the singular and branch schemes.
A global function on the normalization is a scalar on each component, and
evaluation at a rational point reads that component's scalar.
-/

public section

noncomputable section

open CategoryTheory Limits
open TauCeti TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u v

variable {k : Type u} [Field k]
variable (X : Scheme.{u}) [X.Over (Spec (.of k))]
  [PrestableFamily (X ↘ Spec (.of k))]
variable {ι : Type v} (p : ι → (X ↘ Spec (.of k)).smoothLocus)

private instance : IsRegular (X.singularLocus k).blowup :=
  X.isRegular_blowup_singularLocus PrestableFamily.atWorstNodalOfRelativeDimensionOne

private instance : IsClosedImmersion (X.branchSchemeToBlowup k) :=
  MorphismProperty.of_isPullback (X.isPullback_branchScheme k) inferInstance

section NodesAndBranches

variable [IsSepClosed k]

/-- The points of the singular subscheme are the edges of the native dual graph. -/
def dualGraphNodeEquiv : (X.dualGraph p).Edge ≃ (X.singularLocus k).subscheme :=
  (X.dualGraphEdgeEquiv p).trans <|
    (Set.equivOfEq ((IdealSheafData.range_subschemeι (X.singularLocus k)).trans
      X.support_singularLocus_eq_compl_smoothLocus).symm).trans <|
    (Equiv.ofInjective _ (X.singularLocus k).subschemeι.isClosedEmbedding.injective).symm

@[simp]
theorem subschemeι_dualGraphNodeEquiv (e : (X.dualGraph p).Edge) :
    (X.singularLocus k).subschemeι (X.dualGraphNodeEquiv p e) =
      (X.dualGraphEdgeEquiv p e : X) := by
  simp [dualGraphNodeEquiv, Equiv.apply_ofInjective_symm]

private def branchInBlowup (e : (X.dualGraph p).Edge) (i : Fin 2) :
    (X.singularLocus k).blowup :=
  X.branchPointEquiv (X.dualGraphEdgeEquiv p e) i

private theorem branchInBlowup_mem_range (e : (X.dualGraph p).Edge) (i : Fin 2) :
    branchInBlowup X p e i ∈ Set.range (X.branchSchemeToBlowup k) := by
  rw [X.range_branchSchemeToBlowup, Set.mem_preimage,
    X.support_singularLocus_eq_compl_smoothLocus]
  simpa only [branchInBlowup, blowupToBase_branchPointEquiv] using
    (X.dualGraphEdgeEquiv p e).property

private def branchOfEdge (ei : (X.dualGraph p).Edge × Fin 2) : X.branchScheme k :=
  (Equiv.ofInjective (X.branchSchemeToBlowup k)
    (X.branchSchemeToBlowup k).isClosedEmbedding.injective).symm
      ⟨branchInBlowup X p ei.1 ei.2, branchInBlowup_mem_range X p ei.1 ei.2⟩

private theorem branchSchemeToBlowup_branchOfEdge (ei : (X.dualGraph p).Edge × Fin 2) :
    X.branchSchemeToBlowup k (branchOfEdge X p ei) = branchInBlowup X p ei.1 ei.2 := by
  exact Equiv.apply_ofInjective_symm _ _

private theorem branchOfEdge_bijective : Function.Bijective (branchOfEdge X p) := by
  constructor
  · rintro ⟨e, i⟩ ⟨e', i'⟩ heq
    have hb := congrArg (X.branchSchemeToBlowup k) heq
    simp only [branchSchemeToBlowup_branchOfEdge] at hb
    have he : e = e' := (X.dualGraphEdgeEquiv p).injective <| Subtype.ext <| by
      simpa only [branchInBlowup, blowupToBase_branchPointEquiv] using
        congrArg (X.singularLocus k).blowupToBase hb
    subst e'
    exact congrArg (fun a ↦ (e, a)) ((X.branchPointEquiv (X.dualGraphEdgeEquiv p e)).injective
      (Subtype.ext hb))
  · intro z
    let b := X.branchSchemeToBlowup k z
    have hb : b ∈ Set.range (X.branchSchemeToBlowup k) := ⟨z, rfl⟩
    rw [X.range_branchSchemeToBlowup, X.support_singularLocus_eq_compl_smoothLocus] at hb
    obtain ⟨e, he⟩ := (X.dualGraphEdgeEquiv p).surjective
      ⟨(X.singularLocus k).blowupToBase b, hb⟩
    obtain ⟨i, hi⟩ := (X.branchPointEquiv (X.dualGraphEdgeEquiv p e)).surjective
      ⟨b, congrArg Subtype.val he.symm⟩
    refine ⟨(e, i), (X.branchSchemeToBlowup k).isClosedEmbedding.injective ?_⟩
    simpa only [branchSchemeToBlowup_branchOfEdge, branchInBlowup] using congrArg Subtype.val hi

/-- The points of the branch scheme are the two flags of each edge of the dual graph.
The two flags remain distinct when both belong to the same component. -/
def dualGraphBranchEquiv : (X.dualGraph p).Edge × Fin 2 ≃ X.branchScheme k :=
  Equiv.ofBijective (branchOfEdge X p) (branchOfEdge_bijective X p)

@[simp]
theorem branchSchemeToBlowup_dualGraphBranchEquiv (e : (X.dualGraph p).Edge) (i : Fin 2) :
    X.branchSchemeToBlowup k (X.dualGraphBranchEquiv p (e, i)) =
      (X.branchPointEquiv (X.dualGraphEdgeEquiv p e) i : (X.singularLocus k).blowup) :=
  branchSchemeToBlowup_branchOfEdge X p (e, i)

@[simp]
theorem branchSchemeToSingularLocus_dualGraphBranchEquiv (e : (X.dualGraph p).Edge) (i : Fin 2) :
    X.branchSchemeToSingularLocus k (X.dualGraphBranchEquiv p (e, i)) =
      X.dualGraphNodeEquiv p e := by
  apply (X.singularLocus k).subschemeι.isClosedEmbedding.injective
  rw [subschemeι_dualGraphNodeEquiv, ← Hom.comp_apply, branchSchemeToSingularLocus_subschemeι,
    Hom.comp_apply, branchSchemeToBlowup_dualGraphBranchEquiv, blowupToBase_branchPointEquiv]

/-- With any chosen ordering at each edge, the two flags of each node give an ordering
of the points in its actual branch-scheme fiber. -/
def branchOrderOfDualGraph (o : (X.dualGraph p).Edge → Equiv.Perm (Fin 2))
    (z : (X.singularLocus k).subscheme) :
    Fin 2 ≃ {b : X.branchScheme k // X.branchSchemeToSingularLocus k b = z} :=
  let e := (X.dualGraphNodeEquiv p).symm z
  { toFun i := ⟨X.dualGraphBranchEquiv p (e, o e i), by
      rw [branchSchemeToSingularLocus_dualGraphBranchEquiv, Equiv.apply_symm_apply]⟩
    invFun b := (o e).symm ((X.dualGraphBranchEquiv p).symm b.val).2
    left_inv i := by simp
    right_inv b := by
      obtain ⟨⟨f, j⟩, h⟩ := (X.dualGraphBranchEquiv p).surjective b.val
      have hf : f = e := (X.dualGraphNodeEquiv p).injective <| by
        rw [← branchSchemeToSingularLocus_dualGraphBranchEquiv X p f j, h,
          Equiv.apply_symm_apply]
        exact b.property
      subst f
      apply Subtype.ext
      simp only [← h, Equiv.symm_apply_apply, Equiv.apply_symm_apply] }

/-- The chosen ordering recovers the corresponding flag of the dual graph. -/
@[simp]
theorem branchOrderOfDualGraph_apply_val (o : (X.dualGraph p).Edge → Equiv.Perm (Fin 2))
    (e : (X.dualGraph p).Edge) (i : Fin 2) :
    (X.branchOrderOfDualGraph p o (X.dualGraphNodeEquiv p e) i).val =
      X.dualGraphBranchEquiv p (e, o e i) := by
  simp [branchOrderOfDualGraph]

end NodesAndBranches

variable [IsAlgClosed k]

/-- Every global function on the normalization is a scalar on each component. -/
def normalizationGlobalSectionsEquiv :
    Γ((X.singularLocus k).blowup, ⊤) ≃+* ((X.dualGraph p).Vertex → k) :=
  (X.blowupComponentGlobalSectionsEquiv (k := k)).trans
    (RingEquiv.piCongrLeft' (fun _ ↦ k) (X.dualGraphVertexEquiv p).symm)

/-- Evaluation on a rational section of the normalization reads the scalar
of the component containing the point. -/
theorem normalizationGlobalSectionsEquiv_eval (a : Γ((X.singularLocus k).blowup, ⊤))
    (s : Spec (.of k) ⟶ (X.singularLocus k).blowup)
    (hs : s ≫ (X.singularLocus k).blowupToBase ≫ X ↘ Spec (.of k) = 𝟙 _)
    (v : (X.dualGraph p).Vertex)
    (hv : s (IsLocalRing.closedPoint k) ∈ (X.dualGraphVertexEquiv p v :
      Set (X.singularLocus k).blowup)) :
    (Scheme.ΓSpecIso (.of k)).hom (s.appTop a) = X.normalizationGlobalSectionsEquiv p a v := by
  have hmem : s (IsLocalRing.closedPoint k) ∈ X.blowupComponent (X.dualGraphVertexEquiv p v) := by
    rwa [← SetLike.mem_coe, coe_blowupComponent]
  exact (blowupComponentGlobalSectionsEquiv_eq_evaluation a (X.dualGraphVertexEquiv p v)
    s hs hmem).symm

/-- The units on the normalization are the nonzero constants on its components. -/
def normalizationGlobalUnitsEquiv :
    Γ((X.singularLocus k).blowup, ⊤)ˣ ≃* ((X.dualGraph p).Vertex → kˣ) :=
  (Units.mapEquiv (X.normalizationGlobalSectionsEquiv p).toMulEquiv).trans MulEquiv.piUnits

/-- The scalar of a normalization unit is the coordinate of its underlying function. -/
@[simp]
theorem coe_normalizationGlobalUnitsEquiv (a : Γ((X.singularLocus k).blowup, ⊤)ˣ)
    (v : (X.dualGraph p).Vertex) :
    (X.normalizationGlobalUnitsEquiv p a v : k) = X.normalizationGlobalSectionsEquiv p a v :=
  (rfl)

local notation "nodal" => PrestableFamily.atWorstNodalOfRelativeDimensionOne
local notation "B" => branchScheme k X
local notation "Y" => IdealSheafData.blowup (singularLocus k X)
local notation "π" => branchSchemeToSingularLocus k X
local notation "j" => branchSchemeToBlowup k X
local notation "ν" => IdealSheafData.blowupToBase (singularLocus k X)
local notation "nodeMap" =>
  IdealSheafData.subschemeι (singularLocus k X) ≫ (X ↘ Spec (CommRingCat.of k))

/-- Restriction of a normalization unit to a branch has the value of the
component carrying that branch. -/
theorem branchSchemeGlobalUnitsEquiv_appTop_normalization
    (a : Γ(Y, ⊤)ˣ) (b : B) (v : (X.dualGraph p).Vertex)
    (hv : j b ∈ (X.dualGraphVertexEquiv p v : Set Y)) :
    X.branchSchemeGlobalUnitsEquiv PrestableFamily.atWorstNodalOfRelativeDimensionOne
      (Units.map (j).appTop.hom a) b = X.normalizationGlobalUnitsEquiv p a v := by
  let s := X.branchRationalPoint nodal b
  let x : Spec (.of k) := IsLocalRing.closedPoint k
  have hs : s ≫ π ≫ nodeMap = 𝟙 _ := X.branchRationalPoint_comp nodal b
  have hsval : s x = b := X.branchRationalPoint_apply nodal b x
  have hsbase : (s ≫ j) ≫ ν ≫ X ↘ Spec (.of k) = 𝟙 _ := by
    rw [Category.assoc, ← X.branchSchemeToSingularLocus_subschemeι_assoc k]
    exact hs
  have hsmem : (s ≫ j) x ∈ (X.dualGraphVertexEquiv p v : Set Y) := by
    rwa [Hom.comp_apply, hsval]
  have heval := X.val_branchSchemeGlobalUnitsEquiv_apply_section nodal
    (Units.map (j).appTop.hom a) s hs x
  rw [hsval, Units.coe_map] at heval
  apply Units.ext
  rw [coe_normalizationGlobalUnitsEquiv]
  refine heval.trans ?_
  have hnorm := X.normalizationGlobalSectionsEquiv_eval p a.val (s ≫ j) hsbase v hsmem
  rw [Hom.comp_appTop, CommRingCat.comp_apply] at hnorm
  exact hnorm

end AlgebraicGeometry.Scheme
