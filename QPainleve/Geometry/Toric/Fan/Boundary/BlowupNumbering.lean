/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.NumberedPrime
public import QPainleve.Geometry.Toric.Fan.Boundary.NumberedPrime
public import QPainleve.Geometry.Toric.Fan.Subdivision.Projective

import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.AlgebraicGeometry.Curves.Node.CycleAction
import QPainleve.AlgebraicGeometry.IdealSheaf.Image.Over
import QPainleve.Geometry.Toric.Fan.Boundary.DualGraph
import QPainleve.Geometry.Toric.Fan.Boundary.Prestable

/-!
# Cyclic ray numberings on ordered internal blowups

The strict toric boundary inherits the oriented dual graph of the original
boundary. A positive cyclic ray numbering therefore numbers the strict
boundary primes even when the ordered internal centers include repeated points.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower TopologicalSpace
open TauCeti TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones]

local notation "D" => Scheme.IdealSheafData.subscheme (Fan.boundaryIdeal Φ h₀)

variable {r : ℕ}

local notation "S" => Spec (CommRingCat.of ℂ)

/-- Transfer a positive cyclic ray numbering to the strict boundary of an ordered
internal blowup. Each numbered prime has the specified ray, even when some of
the internal centers coincide. -/
theorem exists_numbering_internalBlowup_of_cyclicRays
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (b : Module.Basis (Fin 2) ℤ N)
    (s : Fin r → Φ.Ray) (c : Fin r → ℂˣ) {m : ℕ} [NeZero m]
    (v : ZMod m ≃ Φ.Ray)
    (hv : ∀ j, b.detDualEquiv (v j).primitiveGenerator (v (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, (v j).toCone ≤ σ ∧ (v (j + 1)).toCone ≤ σ) :
    let U := internalBlowupTower b s c
    let E := U.2.boundaryι.ker
    letI : U.1.Over S := ⟨U.2.toTower.toBase ≫ (Φ.algebraicRealization ↘ S)⟩
    letI := Φ.isProjectiveOver_algebraicRealization_of_isComplete hΦ hc b
    letI := U.2.toTower.isNoetherian
    ∀ (hE : E.IsEffectiveCartier),
      ∃ (_ : PrestableFamily (E.subscheme ↘ S))
        (A : Scheme.NodalCycleNumbering (Empty.elim : Empty → (E.subscheme ↘ S).smoothLocus) m),
        ∀ j, A.boundaryPrimeEquiv hE j = internalBlowupBoundaryPrimeEquiv hΦ b s c (v j) := by
  intro U E hE
  let : Φ.algebraicRealization.IsProjectiveOver ℂ :=
    Φ.isProjectiveOver_algebraicRealization_of_isComplete hΦ hc b
  let : IsNoetherian U.1 := U.2.toTower.isNoetherian
  let : IsProper Φ.algebraicRealizationStructureMap := by
    rw [← Φ.algebraicRealization_over]
    infer_instance
  have hdim : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  let : PrestableFamily ((D) ↘ S) := Φ.prestableFamily_boundary hΦ hc hdim
  let : U.1.Over S := ⟨U.2.toTower.toBase ≫ (Φ.algebraicRealization ↘ S)⟩
  let j := U.2.boundaryι
  let : j.IsOver S := ⟨by
    rw [(Φ.boundaryIdeal h₀).over_eq_subschemeι_comp]
    exact U.2.boundaryι_toBase_assoc (Φ.algebraicRealization ↘ S)⟩
  let e : (D) ≅ E.subscheme := asIso j.toImage
  let : e.hom.IsOver S := inferInstanceAs (j.toImage.IsOver S)
  let : PrestableFamily (E.subscheme ↘ S) :=
    (MorphismProperty.cancel_left_of_respectsIso (P := @PrestableFamily) e.hom _).mp
      (by rw [comp_over]; infer_instance)
  let marks : Empty → ((D) ↘ S).smoothLocus := Empty.elim
  obtain ⟨edge, order, vertex, hend, hcomp, -⟩ :=
    Φ.exists_toric_boundary_dualGraph_cycle hΦ hc marks b v hv
  let P : Scheme.NodalCycleNumbering marks m := ⟨vertex, edge, order, hend⟩
  let A := e.mapNodalCycleNumbering P (q := fun x : Empty ↦ x.elim)
  refine ⟨inferInstance, A, fun i ↦ Subtype.ext ?_⟩
  have hgen := e.apply_componentGenericPoint P A i
  have hact : e.boundaryCycleAction P A = 1 := e.boundaryCycleAction_mapNodalCycleNumbering P
  rw [hact, map_one, Equiv.Perm.one_apply] at hgen
  have hcomponent : P.component i = Φ.boundaryNormalizationComponentEquiv hΦ (v i) :=
    (P.component_apply i).trans (hcomp i)
  rw [Scheme.NodalCycleNumbering.boundaryPrimeEquiv_apply_val, ← hgen, ← Scheme.Hom.comp_apply,
    asIso_hom, Scheme.Hom.toImage_imageι, Scheme.NodalCycleNumbering.componentGenericPoint_def,
    hcomponent, internalBlowupBoundaryPrime_val]

end TauCeti.Toric.Fan
