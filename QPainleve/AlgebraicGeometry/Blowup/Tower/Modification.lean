/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Composition
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Point
public import TauCeti.AlgebraicGeometry.Birational.Irreducible
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Basic

import QPainleve.AlgebraicGeometry.Blowup.Modification
import QPainleve.AlgebraicGeometry.Morphisms.Modification.Birational
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition
import TauCeti.Topology.KrullDimension.Irreducible

/-!
# Birational morphisms from closed point blowup towers

A tower of closed point blowups of a locally Noetherian irreducible scheme with at least
two points gives a modification of the original scheme. When the tower resolves
a specified birational map over a base, the resulting morphism to the target
is also a modification if the original scheme is proper and the target is
separated over the base.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {X Y Z S : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y}

section

variable [IsLocallyNoetherian X] [IrreducibleSpace X] [Nontrivial X]

/-- The projection from a tower of blowups at closed points is a modification.
The base has at least two points, so each center on the succeeding models has dense complement. -/
theorem isModification (hT : IsClosedPointTower X T) : IsModification T.toBase := by
  induction hT with
  | nil =>
    rw [toBase_nil]
    infer_instance
  | @snoc _ W V I _ x hx hI ih =>
    have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian V.toBase
    have : IrreducibleSpace W := (IsModification.birational V.toBase).irreducibleSpace
    have : Nontrivial W := V.toBase.surjective.nontrivial
    have hs : (I.support : Set W) = {x} := by
      rw [hI, Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField, hx.closure_eq]
    have h : (I.support.compl : Set W).Nonempty := by
      rw [Closeds.coe_compl, hs]
      obtain ⟨y, hy⟩ := exists_ne x
      exact ⟨y, hy⟩
    have : IsModification I.blowupToBase :=
      I.isModification_blowupToBase (I.support.compl.is_open'.dense h)
    rw [toBase_snoc]
    infer_instance

/-- A morphism over the base that resolves a specified partial isomorphism by closed point
blowups is a modification of the target. Properness comes from the tower and the source
structure morphism. -/
theorem isModification_of_resolved_partialIso (hT : IsClosedPointTower X T)
    (sX : X ⟶ S) [IsProper sX] (sZ : Z ⟶ S) [IsSeparated sZ]
    (a : X.PartialIso Z) (f : Y ⟶ Z) (hf : f ≫ sZ = T.toBase ≫ sX)
    (h : letI := hT.isModification
      letI := (IsModification.birational T.toBase).irreducibleSpace
      T.toBase.toRationalMap.comp a.toRationalMap = f.toRationalMap) : IsModification f := by
  have := hT.isModification
  have : IrreducibleSpace Y := (IsModification.birational T.toBase).irreducibleSpace
  have : IsProper (f ≫ sZ) := hf.symm ▸ inferInstanceAs (IsProper (T.toBase ≫ sX))
  have : IsProper f := IsProper.of_comp f sZ
  exact IsModification.of_resolved_partialIso T.toBase a f h

end

/-- A closed point blowup tower over an irreducible smooth surface is a modification. -/
theorem isModification_of_smoothOfRelativeDimension_two
    (hT : IsClosedPointTower X T) {k : Type u} [Field k] [IrreducibleSpace X]
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 f] : IsModification T.toBase := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : Nontrivial X := by
    rw [← not_subsingleton_iff_nontrivial, ← TauCeti.topologicalKrullDim_eq_zero_iff_subsingleton,
      topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)]
    decide
  exact hT.isModification

end QPainleve.BlowupTower.IsClosedPointTower
