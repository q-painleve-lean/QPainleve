/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
public import QPainleve.AlgebraicGeometry.Modules.InternalHom.Sections
public import TauCeti.AlgebraicGeometry.LineBundle.Dual
import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.Cohomology.Support
import TauCeti.AlgebraicGeometry.Cohomology.PushforwardAcyclic.Affine
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.ZeroLocus
import TauCeti.Topology.KrullDimension.Irreducible
import QPainleve.AlgebraicGeometry.IdealSheaf.Image.Cokernel
import TauCeti.AlgebraicGeometry.IdealSheaf.EulerCharacteristic

/-!
# Cohomology pairings defined by a trace

A global section of the internal Hom from `M` to `N` induces a map on cohomology.
Composing it with a trace on the cohomology of `N` gives a bilinear pairing.
In top degree on an integral projective scheme, a nonzero map between line bundles
induces a surjection because its cokernel is supported on a proper Cartier subscheme.
Consequently a nonzero trace separates global sections of the internal Hom.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace MonoidalClosed
open TauCeti TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules}

variable (R : Type u) [CommRing R] [X.Over (Spec (.of R))]

/-- Pair a cohomology class with a section by applying its morphism and then the trace. -/
def cohomologyTracePairing (q : ℕ) (tr : Cohomology N q →ₗ[R] R) :
    Cohomology M q →ₗ[R] Γ((ihom M).obj N, ⊤) →ₗ[R] R :=
  LinearMap.flip
    { toFun := fun s ↦ tr.comp (cohomologyMapBaseLinear R X (internalHomSectionsEquiv s) q)
      map_add' := fun s t ↦ by
        simp [cohomologyMapBaseLinear_add, LinearMap.comp_add]
      map_smul' := fun r s ↦ by
        ext x
        simp only [base_smul_globalSections, internalHomSectionsEquiv_smul, LinearMap.comp_apply,
          cohomologyMapBaseLinear_comp, RingHom.id_apply, LinearMap.smul_apply]
        have hs (z : Cohomology N q) :
            cohomologyMapBaseLinear R X (N.globalSectionsSmul (baseRingToGlobalSections R X r))
              q z = r • z :=
          (cohomologyMapBaseLinear_apply _ _ _ _ _).trans
            ((cohomology_smul _ _ _ _).symm.trans (base_smul_cohomology _ _ _ _ _ _).symm)
        rw [hs]
        exact tr.map_smul _ _ }

/-- Evaluation of the trace pairing on a class and a global section. -/
@[simp]
theorem cohomologyTracePairing_apply (q : ℕ) (tr : Cohomology N q →ₗ[R] R)
    (x : Cohomology M q) (s : Γ((ihom M).obj N, ⊤)) :
    cohomologyTracePairing R q tr x s =
      tr (cohomologyMapBaseLinear R X (internalHomSectionsEquiv s) q x) :=
  (rfl)

end AlgebraicGeometry.Scheme.Modules

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

open _root_.AlgebraicGeometry.Scheme.Modules

variable (k : Type u) [Field k] [Infinite k] {X : Scheme.{u}}
  [IsIntegral X] [X.Over (Spec (.of k))] [X.IsProjectiveOver k] {q : ℕ}

/-- A nonzero morphism of line bundles induces a surjection in degree `q` if the
dimension of the integral projective scheme is at most `q`. -/
theorem surjective_cohomologyMap_of_ne_zero (L K : InvertibleSheaf X)
    (f : L.obj ⟶ K.obj) (hf : f ≠ 0) (hdim : topologicalKrullDim X ≤ q) :
    Function.Surjective (cohomologyMapBaseLinear k X f q) := by
  let φ := L.twistedToUnit K f
  have hφ : φ ≠ 0 := fun h ↦ hf ((L.twistedToUnit_eq_zero_iff K f).mp h)
  let E : InvertibleSheaf X := L.tensorProduct (dual K)
  have : Mono φ := E.mono_of_ne_zero_to_unit φ hφ
  have : Mono f := (L.mono_twistedToUnit_iff K f).mp inferInstance
  let I := φ.imageIdealSheaf
  have hI : I.IsEffectiveCartier := E.isEffectiveCartier_imageIdealSheaf φ
  let i := I.subschemeι
  let : I.subscheme.Over (Spec (.of k)) := ⟨i ≫ X ↘ Spec (.of k)⟩
  let : i.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : I.subscheme.IsProjectiveOver k := Scheme.IsProjectiveOver.of_isClosedImmersion k i
  have hproper : (I.support : Set X) ≠ Set.univ := by
    intro he
    apply hI.genericPoint_notMem_support
    have hmem : genericPoint X ∈ (I.support : Set X) := by rw [he]; trivial
    exact hmem
  have hs := topologicalKrullDim_subspace_le X (I.support : Set X)
  have hfinite : topologicalKrullDim X < ⊤ :=
    hdim.trans_lt (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top q))
  have hs' := I.support.isClosed.topologicalKrullDim_lt hproper (ne_top_of_lt (hs.trans_lt hfinite))
  let e := i.isClosedEmbedding.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr I.range_subschemeι)
  have hdim' : topologicalKrullDim I.subscheme < q :=
    e.isHomeomorph.topologicalKrullDim_eq.trans_lt (hs'.trans_le hdim)
  let EK := (InvertibleSheaf.toFiniteLocallyFree X).obj K
  let V : I.subscheme.Modules := ((FiniteLocallyFreeSheaf.pullback i).obj EK).obj
  have hvan := subsingleton_cohomology_of_projective_dim_lt (k := k) V hdim'
  let eQ := cokernelIsoTensorPushforwardImageIdeal L K f ≪≫ I.tensorPushforwardSubschemeIso EK
  let eH := (cohomologyBaseLinearEquivOfIso k eQ q).trans
    (i.cohomologyPushforwardBaseLinearEquivOfIsAffineHom k V q)
  have : Subsingleton (Cohomology (cokernel f) q) := eH.injective.subsingleton
  rw [coe_cohomologyMapBaseLinear]
  intro y
  have hy : cohomologyMap (cokernel.π f) q y = 0 := Subsingleton.elim _ _
  exact (exact_cohomologyMap_cohomologyMap (TauCeti.cokernelSequence_shortExact f) q y).mp hy

/-- A nonzero top-degree trace on a line bundle separates global sections of
the internal Hom from any other line bundle on an integral projective scheme. -/
theorem cohomologyTracePairing_injective_flip (L K : InvertibleSheaf X)
    (hdim : topologicalKrullDim X ≤ q) (tr : Cohomology K.obj q →ₗ[k] k) (htr : tr ≠ 0) :
    Function.Injective (cohomologyTracePairing (M := L.obj) k q tr).flip := by
  apply (injective_iff_map_eq_zero _).mpr
  intro s hs
  by_contra h
  have hφ : internalHomSectionsEquiv s ≠ 0 := fun hzero ↦
    h (internalHomSectionsEquiv.injective (hzero.trans internalHomSectionsEquiv_zero.symm))
  have hsurj := surjective_cohomologyMap_of_ne_zero k L K _ hφ hdim
  apply htr
  ext y
  obtain ⟨x, rfl⟩ := hsurj y
  simpa only [LinearMap.flip_apply, LinearMap.zero_apply, cohomologyTracePairing_apply]
    using DFunLike.congr_fun hs x

end TauCeti.AlgebraicGeometry.InvertibleSheaf
