/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Scheme.Stalk
public import TauCeti.AlgebraicGeometry.Curves.Node.Relative
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Stalk
public import TauCeti.AlgebraicGeometry.IdealSheaf.Stalk
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
import QPainleve.AlgebraicGeometry.Modules.Differentials.Stalk
import QPainleve.RingTheory.Node.Order
import TauCeti.RingTheory.Node.Cotangent.Basic

/-!
# Stalk order of a nodal Cartier divisor

An intrinsic node on a Cartier divisor in a smooth surface has stalk order two.
The result applies to self-nodes: the singular subscheme detects the point directly
on the curve. This gives the multiplicity used in the total transform under the
blowup of a closed point.

The proof uses the affine singular subscheme API for nodal curves and localizes the
differentials and their Fitting ideal before applying the local Hessian criterion.
-/

public section

open CategoryTheory Opposite TopologicalSpace KaehlerDifferential
open TauCeti TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- The first Fitting ideal of the differentials in the local ring of a nodal curve cuts out the
stalk of its singular subscheme, and its quotient is formally unramified. -/
theorem fittingIdeal_stalk_of_atWorstNodal
    {k : Type u} [CommRing k] {C : Scheme.{u}} [C.Over (Spec (.of k))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (C ↘ Spec (.of k))) (p : C) :
    let := hnodal.syntomic
    let := C.essFiniteType_stalk k p
    (C.singularLocus k).stalkIdeal p =
        fittingIdeal (C.presheaf.stalk p) Ω[C.presheaf.stalk p⁄k] 1 ∧
      Algebra.FormallyUnramified k ((C.presheaf.stalk p) ⧸
        fittingIdeal (C.presheaf.stalk p) Ω[C.presheaf.stalk p⁄k] 1) := by
  let := hnodal.syntomic
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top p)
  let V : C.affineOpens := ⟨U, hU⟩
  let A := Γ(C, V)
  let L := C.presheaf.stalk p
  let : Algebra k A := ((C.baseRingToStructurePresheaf k).app (op U)).hom.toAlgebra
  let := C.presheaf.algebra_section_stalk ⟨p, hpU⟩
  let : IsScalarTower k A L := isScalarTower_base_section_stalk k C ⟨p, hpU⟩
  let q := (hU.primeIdealOf ⟨p, hpU⟩).asIdeal
  have : IsLocalization q.primeCompl L := hU.isLocalization_stalk ⟨p, hpU⟩
  have : Algebra.FormallyEtale A L := .of_isLocalization q.primeCompl
  have : Algebra.FiniteType k A := finiteType_sections_of_locallyOfFiniteType k C V
  have : Algebra.EssFiniteType k L := C.essFiniteType_stalk k p
  have hfit := (KaehlerDifferential.isBaseChange_of_formallyEtale k A L).fittingIdeal_eq_map 1
  have haff := C.singularLocus_ideal (R := k) V
  refine ⟨?_, ?_⟩
  · rw [(C.singularLocus k).stalkIdeal_eq_map V p hpU, haff, hfit]
    rw [C.presheaf.stalk_open_algebraMap ⟨p, hpU⟩]
  · have : Algebra.FormallyUnramified k (A ⧸ fittingIdeal A Ω[A⁄k] 1) :=
      haff ▸ C.formallyUnramified_quotient_singularLocus_ideal hnodal V
    have : Algebra.FormallyUnramified k (Localization q.primeCompl ⧸
        fittingIdeal (Localization q.primeCompl) Ω[Localization q.primeCompl⁄k] 1) :=
      formallyUnramified_localization_quotient_fittingIdeal q.primeCompl
    let e := (IsLocalization.algEquiv q.primeCompl (Localization q.primeCompl) L).restrictScalars k
    exact .of_equiv (Ideal.quotientEquivAlg _ _ e
      (fittingIdeal_kaehlerDifferential_eq_map_algEquiv e 1))

namespace Hom

/-- An effective Cartier divisor in a smooth surface has order two at every intrinsic node.
The point is specified on the divisor, and the order is computed in the ambient surface. -/
theorem stalkOrder_eq_two_of_node
    {k : Type u} [Field k] {X C : Scheme.{u}} [C.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (i : C ⟶ X) [i.IsOver (Spec (.of k))] [IsClosedImmersion i]
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
    (hi : i.ker.IsEffectiveCartier)
    (hnodal : AtWorstNodalOfRelativeDimensionOne (C ↘ Spec (.of k))) (p : C)
    (hp : letI := hnodal.syntomic; p ∈ (C.singularLocus k).support) :
    i.ker.stalkOrder (i p) = 2 := by
  let := hnodal.syntomic
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top (i p))
  let P := X.presheaf.stalk (i p)
  let L := C.presheaf.stalk p
  obtain ⟨bP⟩ := X.nonempty_basis_kaehlerDifferential_stalk (k := k) 2 (i p)
  have := SmoothOfRelativeDimension.smooth 2 (X ↘ Spec (.of k))
  have : Algebra.EssFiniteType k P := X.essFiniteType_stalk k (i p)
  have : IsNoetherianRing P := Algebra.EssFiniteType.isNoetherianRing k P
  let π := i.stalkMapAlgHom (k := k) p
  have hπring : (π : P →+* L) = (i.stalkMap p).hom := i.stalkMapAlgHom_toRingHom (k := k) p
  obtain ⟨f, -, hf⟩ := hi.exists_map_germ_eq_span_singleton ⟨U, hU⟩ hpU
  have hker : RingHom.ker π = Ideal.span {f} := by
    rw [AlgHom.ker_coe, hπring, i.ker_stalkMap_of_isClosedImmersion p,
      i.ker.stalkIdeal_eq_map ⟨U, hU⟩ (i p) hpU, hf]
  have hπ : Function.Surjective π := by
    intro y
    simpa only [π, stalkMapAlgHom_apply] using i.stalkMap_surjective p y
  have : Algebra.EssFiniteType k L := C.essFiniteType_stalk k p
  obtain ⟨hfit, hunram⟩ := C.fittingIdeal_stalk_of_atWorstNodal hnodal p
  have hproper : fittingIdeal L Ω[L⁄k] 1 ≠ ⊤ :=
    hfit ▸ ((C.singularLocus k).mem_support_iff_stalkIdeal_ne_top p).mp hp
  have horder := QPainleve.localOrder_ker_eq_two_of_fittingIdeal (IsNoetherian.noetherian _)
    bP π hπ hker hproper
  rw [i.ker.stalkOrder_def, ← i.ker_stalkMap_of_isClosedImmersion p]
  rw [AlgHom.ker_coe, hπring] at horder
  exact horder

end Hom

end AlgebraicGeometry.Scheme
