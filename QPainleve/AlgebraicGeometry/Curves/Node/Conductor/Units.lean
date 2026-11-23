/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import TauCeti.AlgebraicGeometry.Curves.Node.Blowup

import QPainleve.AlgebraicGeometry.Morphisms.Etale.GlobalSections
import TauCeti.AlgebraicGeometry.Curves.Node.FiniteEtale
import TauCeti.AlgebraicGeometry.Morphisms.Etale.Basic
import TauCeti.AlgebraicGeometry.Morphisms.FormallyUnramified
import TauCeti.AlgebraicGeometry.ResidueField

/-!
# Units on the branch scheme of a proper nodal curve

Over a separably closed field the singular subscheme and the branch scheme of a proper
nodal curve are split finite étale. Pullback repeats each node's scalar on its two
branches. Ordering those branches identifies the quotient of branch units by node units
with one scalar per node, the value at the first branch divided by the value at the zeroth.

In the conductor description of line-bundle gluing, the quotient accounts for rescaling
the trivialization on the singular subscheme. The resulting scalars are the gluing constants
before dividing by changes in the trivializations on the components of the normalization,
as in [Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*,
Lemma 2.1](https://arxiv.org/pdf/1211.6367#page=6).
-/

public noncomputable section

open CategoryTheory TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

variable {k : Type u} [Field k] [IsSepClosed k]
  (X : Scheme.{u}) [X.Over (Spec (.of k))]
  [SyntomicOfRelativeDimension 1 (X ↘ Spec (.of k))]
  (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k)))

local notation "N" => IdealSheafData.subscheme (singularLocus k X)
local notation "B" => branchScheme k X
local notation "π" => branchSchemeToSingularLocus k X
local notation "nodeMap" =>
  IdealSheafData.subschemeι (singularLocus k X) ≫ (X ↘ Spec (CommRingCat.of k))

/-- The fiber of the branch scheme over a node consists of two points.
This equivalence chooses an ordering. -/
def branchFiberEquivFinTwo (z : N) : Fin 2 ≃ {b : B // π b = z} := by
  have : Etale nodeMap := X.etale_singularLocus_subschemeι_comp hnodal
  have : IsFinite π := X.isFinite_branchSchemeToSingularLocus hnodal
  have : Etale π := X.etale_branchSchemeToSingularLocus hnodal
  have : IsSepClosed ((N).residueField z) :=
    (nodeMap).isSepClosed_residueField_of_formallyUnramified z
  have hcard : Nat.card {b : B // π b = z} = 2 :=
    ((π).natCard_preimage_singleton_eq_finrank z).trans
      (X.finrank_branchSchemeToSingularLocus hnodal z)
  have := Nat.finite_of_card_ne_zero (hcard.trans_ne two_ne_zero)
  exact (Finite.equivFinOfCardEq hcard).symm

variable [IsProper (X ↘ Spec (.of k))]

/-- Global units on the singular subscheme are nonzero scalars indexed by the nodes. -/
def singularLocusGlobalUnitsEquiv : Γ(N, ⊤)ˣ ≃* (N → kˣ) := by
  have : IsFinite nodeMap := X.isFinite_singularLocus_subschemeι_comp hnodal
  have : Etale nodeMap := X.etale_singularLocus_subschemeι_comp hnodal
  exact (nodeMap).finiteEtaleGlobalUnitsEquiv

/-- Global units on the branch scheme are nonzero scalars indexed by the branches. -/
def branchSchemeGlobalUnitsEquiv : Γ(B, ⊤)ˣ ≃* (B → kˣ) := by
  have : IsFinite nodeMap := X.isFinite_singularLocus_subschemeι_comp hnodal
  have : Etale nodeMap := X.etale_singularLocus_subschemeι_comp hnodal
  have : IsFinite π := X.isFinite_branchSchemeToSingularLocus hnodal
  have : Etale π := X.etale_branchSchemeToSingularLocus hnodal
  exact (π ≫ nodeMap).finiteEtaleGlobalUnitsEquiv

/-- Pullback from the singular subscheme to the branch scheme assigns the node's
scalar to each of its branches. -/
@[simp]
theorem branchSchemeGlobalUnitsEquiv_appTop (a : Γ(N, ⊤)ˣ) (b : B) :
    X.branchSchemeGlobalUnitsEquiv hnodal (Units.map ((π).appTop.hom : Γ(N, ⊤) →* Γ(B, ⊤)) a) b =
      X.singularLocusGlobalUnitsEquiv hnodal a (π b) := by
  have : IsFinite nodeMap := X.isFinite_singularLocus_subschemeι_comp hnodal
  have : Etale nodeMap := X.etale_singularLocus_subschemeι_comp hnodal
  have : IsFinite π := X.isFinite_branchSchemeToSingularLocus hnodal
  have : Etale π := X.etale_branchSchemeToSingularLocus hnodal
  exact Hom.finiteEtaleGlobalUnitsEquiv_appTop (π ≫ nodeMap) nodeMap π rfl a b

/-- At a rational point of the branch scheme, the split unit coordinate is its
pullback to the spectrum of the field. -/
theorem val_branchSchemeGlobalUnitsEquiv_apply_section (a : Γ(B, ⊤)ˣ)
    (s : Spec (.of k) ⟶ B) (hs : s ≫ π ≫ nodeMap = 𝟙 _)
    (x : Spec (.of k)) :
    (X.branchSchemeGlobalUnitsEquiv hnodal a (s x) : k) =
      (Scheme.ΓSpecIso (.of k)).hom (s.appTop a.val) := by
  have : IsFinite nodeMap := X.isFinite_singularLocus_subschemeι_comp hnodal
  have : Etale nodeMap := X.etale_singularLocus_subschemeι_comp hnodal
  have : IsFinite π := X.isFinite_branchSchemeToSingularLocus hnodal
  have : Etale π := X.etale_branchSchemeToSingularLocus hnodal
  rw [branchSchemeGlobalUnitsEquiv, Hom.val_finiteEtaleGlobalUnitsEquiv_apply,
    ← Hom.finiteEtaleGlobalSectionsEquiv_appTop (𝟙 _) (π ≫ nodeMap) s hs]
  let f : Spec (.of k) ⟶ Spec (.of k) := 𝟙 _
  have hfield := f.finiteEtaleGlobalSectionsEquiv_algebraMap
    ((Scheme.ΓSpecIso (.of k)).hom (s.appTop a.val)) x
  simpa [f] using hfield

variable (order : ∀ z : (X.singularLocus k).subscheme,
  Fin 2 ≃ {b : X.branchScheme k // X.branchSchemeToSingularLocus k b = z})

/-- The ratio of global unit values at the first and zeroth branches of each node. -/
def branchRatioHom : Γ(B, ⊤)ˣ →* (N → kˣ) :=
  (MonoidHom.pi fun z ↦
    Pi.evalMonoidHom (fun _ : B ↦ kˣ) (order z 1).val /
      Pi.evalMonoidHom (fun _ : B ↦ kˣ) (order z 0).val).comp
      (X.branchSchemeGlobalUnitsEquiv hnodal).toMonoidHom

/-- The branch ratio is the value at branch one divided by the value at branch zero. -/
@[simp]
theorem branchRatioHom_apply (a : Γ(B, ⊤)ˣ) (z : N) :
    X.branchRatioHom hnodal order a z =
      X.branchSchemeGlobalUnitsEquiv hnodal a (order z 1).val /
        X.branchSchemeGlobalUnitsEquiv hnodal a (order z 0).val := by
  rfl

private def branchCoordinates : (B → kˣ) ≃ (N → Fin 2 → kˣ) :=
  Equiv.piCongrFiberwise (f := (π : B → N)) fun z ↦
    Equiv.piCongrLeft' (fun _ ↦ kˣ) (order z).symm

omit [IsSepClosed k] [IsProper (X ↘ Spec (.of k))] in
private theorem branchCoordinates_apply (a : B → kˣ) (z : N) (i : Fin 2) :
    X.branchCoordinates order a z i = a (order z i).val := by
  simp [branchCoordinates]

/-- Any choice of one scalar per node is realized by branch units. -/
theorem branchRatioHom_surjective : Function.Surjective (X.branchRatioHom hnodal order) := by
  intro c
  obtain ⟨a, ha⟩ := ((X.branchSchemeGlobalUnitsEquiv hnodal).toEquiv.trans
    (X.branchCoordinates order)).surjective (fun z i ↦ if i = 0 then 1 else c z)
  have ha' (z : N) (i : Fin 2) :
      X.branchSchemeGlobalUnitsEquiv hnodal a (order z i).val = if i = 0 then 1 else c z := by
    have h := congrFun (congrFun ha z) i
    simp only [Equiv.trans_apply, MulEquiv.toEquiv_eq_coe, branchCoordinates_apply] at h
    exact h
  refine ⟨a, funext fun z ↦ ?_⟩
  simp [ha']

/-- A branch unit has trivial ratios exactly when it is pulled back from the singular subscheme. -/
theorem branchRatioHom_ker :
    (X.branchRatioHom hnodal order).ker =
      (Units.map ((π).appTop.hom : Γ(N, ⊤) →* Γ(B, ⊤))).range := by
  ext a
  rw [MonoidHom.mem_ker, MonoidHom.mem_range]
  constructor
  · intro ha
    let value := X.branchSchemeGlobalUnitsEquiv hnodal a
    let c : Γ(N, ⊤)ˣ := (X.singularLocusGlobalUnitsEquiv hnodal).symm
      (fun z ↦ value (order z 0).val)
    refine ⟨c, (X.branchSchemeGlobalUnitsEquiv hnodal).injective
      ((X.branchCoordinates order).injective (funext fun z ↦ funext fun i ↦ ?_))⟩
    have hz : value (order z 1).val = value (order z 0).val := by
      simpa only [branchRatioHom_apply, Pi.one_apply, div_eq_one] using congrFun ha z
    rw [branchCoordinates_apply, branchCoordinates_apply, branchSchemeGlobalUnitsEquiv_appTop,
      (order z i).property, MulEquiv.apply_symm_apply]
    -- Both branches have the value at the zeroth branch.
    change value (order z 0).val = value (order z i).val
    fin_cases i
    · rfl
    · exact hz.symm
  · rintro ⟨c, rfl⟩
    funext z
    rw [branchRatioHom_apply, branchSchemeGlobalUnitsEquiv_appTop,
      branchSchemeGlobalUnitsEquiv_appTop, (order z 0).property, (order z 1).property]
    exact div_self' _

/-- Modulo pullback of node units, gluing units are one scalar per node once the
two branches at every node are ordered. -/
def branchSchemeGlobalUnitsQuotientEquiv :
    (Γ(B, ⊤)ˣ ⧸ (Units.map ((π).appTop.hom : Γ(N, ⊤) →* Γ(B, ⊤))).range) ≃* (N → kˣ) :=
  (QuotientGroup.quotientMulEquivOfEq (X.branchRatioHom_ker hnodal order).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (X.branchRatioHom_surjective hnodal order))

/-- On a representative unit, the quotient equivalence is the branch ratio map. -/
@[simp]
theorem branchSchemeGlobalUnitsQuotientEquiv_mk (a : Γ(B, ⊤)ˣ) :
    X.branchSchemeGlobalUnitsQuotientEquiv hnodal order (QuotientGroup.mk a) =
      X.branchRatioHom hnodal order a := by
  rw [branchSchemeGlobalUnitsQuotientEquiv, MulEquiv.trans_apply,
    QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

end AlgebraicGeometry.Scheme
