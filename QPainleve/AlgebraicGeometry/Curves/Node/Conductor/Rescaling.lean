/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.DualGraph.Gluing
public import QPainleve.AlgebraicGeometry.LineBundle.GluingUnit
public import TauCeti.AlgebraicGeometry.Curves.Node.DualGraph
public import TauCeti.AlgebraicGeometry.IdealSheaf.Over

import Mathlib.Algebra.Group.Pi.Units
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import QPainleve.AlgebraicGeometry.Scheme.Sections
import TauCeti.AlgebraicGeometry.Geometrically.GlobalSections

/-!
# Normalization rescalings on nodal curves

A global unit on the normalization of a proper nodal curve over an algebraically
closed field is a tuple of constants on the normalization components. At a node,
the two branches see the two incident constants. Thus the changes of the branch
ratios caused by changing a conductor trivialization are precisely the vertex
coboundaries. For an oriented cycle, these changes have product one, including
for a self-node and for two nodes joining the same components.

This is the geometric rescaling calculation in [Gross, Hacking and Keel,
*Moduli of surfaces with an anti-canonical cycle*, Lemma 2.1][GHK].

[GHK]: https://arxiv.org/abs/1211.6367v5
-/

public noncomputable section

open CategoryTheory
open TauCeti TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

section BranchRationalPoint

variable {k : Type u} [Field k] [IsAlgClosed k] (X : Scheme.{u})
  [X.Over (Spec (.of k))] [SyntomicOfRelativeDimension 1 (X ↘ Spec (.of k))]
  (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k)))

local notation "branchMap" =>
  X.branchSchemeToSingularLocus k ≫ IdealSheafData.subschemeι (X.singularLocus k) ≫
    (X ↘ Spec (CommRingCat.of k))

omit [IsAlgClosed k] in
include hnodal in
private theorem etale_branchMap : Etale branchMap := by
  have := X.etale_singularLocus_subschemeι_comp hnodal
  have := X.etale_branchSchemeToSingularLocus hnodal
  infer_instance

/-- Over an algebraically closed field, a point of the branch scheme of a nodal
curve determines a rational point over the base field. -/
def branchRationalPoint (b : X.branchScheme k) : Spec (.of k) ⟶ X.branchScheme k :=
  have := X.etale_branchMap hnodal
  have : IsLocallyArtinian (X.branchScheme k) := .of_locallyQuasiFinite branchMap
  pointOfClosedPoint branchMap b (isClosed_discrete _)

/-- The rational point has the specified branch as its image. -/
@[simp]
theorem branchRationalPoint_apply (b : X.branchScheme k) (x : Spec (.of k)) :
    X.branchRationalPoint hnodal b x = b := by
  have := X.etale_branchMap hnodal
  unfold branchRationalPoint
  exact pointOfClosedPoint_apply ..

/-- The rational point is a section of the branch scheme's structure morphism. -/
@[reassoc (attr := simp)]
theorem branchRationalPoint_comp (b : X.branchScheme k) :
    X.branchRationalPoint hnodal b ≫ X.branchSchemeToSingularLocus k ≫
      (X.singularLocus k).subscheme ↘ Spec (.of k) = 𝟙 _ := by
  have := X.etale_branchMap hnodal
  have : IsLocallyArtinian (X.branchScheme k) := .of_locallyQuasiFinite branchMap
  unfold branchRationalPoint
  simpa only [comp_over] using pointOfClosedPoint_comp branchMap b (isClosed_discrete _)

end BranchRationalPoint

variable {k : Type u} [Field k]
  (X : Scheme.{u}) [X.Over (Spec (.of k))] [PrestableFamily (X ↘ Spec (.of k))]

local notation "N" => IdealSheafData.blowup (X.singularLocus k)
local notation "V" => irreducibleComponents N
local notation "P" => X.branchScheme k
local notation "j" => X.branchSchemeToBlowup k
local notation "g" => X.branchSchemeToSingularLocus k

/-- The normalization components form an open cover. -/
theorem iSup_blowupComponent : ⨆ a : V, X.blowupComponent (K := k) a = ⊤ := by
  have : IsRegular N := X.isRegular_blowup_singularLocus
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := X ↘ Spec (.of k)))
  apply top_unique
  intro x _
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨irreducibleComponentOf x,
    (SetLike.mem_coe.mp (by rw [X.coe_blowupComponent]; exact mem_irreducibleComponentOf x))⟩

/-- Distinct normalization components are disjoint opens. -/
theorem pairwise_disjoint_blowupComponent :
    Pairwise (Function.onFun Disjoint (X.blowupComponent (K := k))) := by
  have : IsRegular N := X.isRegular_blowup_singularLocus
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := X ↘ Spec (.of k)))
  intro a b hab
  apply TopologicalSpace.Opens.coe_disjoint.mp
  simp only [X.coe_blowupComponent]
  exact Set.disjoint_left.mpr fun _ ha hb ↦ hab
    ((irreducibleComponentOf_eq_iff.mpr ha).symm.trans (irreducibleComponentOf_eq_iff.mpr hb))

variable [IsAlgClosed k]

private def blowupComponentConstants (a : V) :
    k ≃+* Γ((X.blowupComponent (K := k) a).toScheme, ⊤) :=
  RingEquiv.ofBijective (Modules.baseRingToGlobalSections k (X.blowupComponent (K := k) a).toScheme)
    (by
      have h := (X.blowupComponent (K := k) a).toScheme
        |>.appTop_bijective_of_isAlgClosed_of_isReduced_of_connectedSpace k
      have heq : ⇑(Modules.baseRingToGlobalSections k (X.blowupComponent (K := k) a).toScheme) =
          (⇑((X.blowupComponent (K := k) a).toScheme ↘ Spec (.of k)).appTop) ∘
            (ΓSpecIso (.of k)).inv :=
        funext (Modules.baseRingToGlobalSections_apply _ _)
      rw [heq]
      exact h.comp (ConcreteCategory.bijective_of_isIso (ΓSpecIso (.of k)).inv))

/-- Global functions on the normalization are constants indexed by its components. -/
def blowupComponentGlobalSectionsEquiv : Γ(N, ⊤) ≃+* (V → k) :=
  (globalSectionsEquivOfDisjointCover (X.blowupComponent (K := k))
    (iSup_blowupComponent X) (pairwise_disjoint_blowupComponent X)).trans
    (RingEquiv.piCongrRight fun a ↦ (blowupComponentConstants X a).symm)

/-- Pullback of the constant for a component is restriction to that component. -/
theorem appTop_blowupComponent (r : Γ(N, ⊤)) (a : V) :
    (X.blowupComponent a).ι.appTop r =
      Modules.baseRingToGlobalSections k (X.blowupComponent a).toScheme
        (X.blowupComponentGlobalSectionsEquiv r a) := by
  simp only [blowupComponentGlobalSectionsEquiv, RingEquiv.trans_apply,
    RingEquiv.piCongrRight_apply, globalSectionsEquivOfDisjointCover_apply]
  exact ((blowupComponentConstants X a).apply_symm_apply _).symm

/-- Units on the blowup separating the branches of a proper nodal curve are nonzero constants
on the normalization components. -/
def blowupComponentUnits : Γ(N, ⊤)ˣ ≃* (V → kˣ) :=
  (Units.mapEquiv (X.blowupComponentGlobalSectionsEquiv (k := k)).toMulEquiv).trans MulEquiv.piUnits

/-- The tuple of constants restricts to the original global unit on each component. -/
@[simp]
theorem blowupComponentUnits_apply (r : Γ(N, ⊤)ˣ) (a : V) :
    Units.map (↑(Modules.baseRingToGlobalSections k (X.blowupComponent a).toScheme))
        (X.blowupComponentUnits (k := k) r a) =
      Units.map ((X.blowupComponent a).ι.appTop.hom :
        Γ(N, ⊤) →* Γ((X.blowupComponent a).toScheme, ⊤)) r :=
  Units.ext (X.appTop_blowupComponent r.val a).symm

local notation "ev[" p "]" =>
  Units.map (RingHom.toMonoidHom (CommRingCat.Hom.hom
    (Hom.appTop p ≫ Iso.hom (ΓSpecIso (CommRingCat.of k)))))

variable {X}

/-- Evaluation at a rational point of a normalization component gives the constant
of a global function on that component. -/
theorem blowupComponentGlobalSectionsEquiv_eq_evaluation (r : Γ(N, ⊤)) (a : V)
    (p : Spec (.of k) ⟶ N) (hp : p ≫ (X.singularLocus k).blowupToBase ≫
      (X ↘ Spec (.of k)) = 𝟙 _)
    (ha : p (IsLocalRing.closedPoint k) ∈ X.blowupComponent (K := k) a) :
    X.blowupComponentGlobalSectionsEquiv r a = (p.appTop ≫ (ΓSpecIso (.of k)).hom) r := by
  let U := X.blowupComponent (K := k) a
  have hrange : Set.range p ⊆ Set.range U.ι := by
    rw [U.range_ι]
    rintro _ ⟨x, rfl⟩
    rwa [Subsingleton.elim x (IsLocalRing.closedPoint k)]
  let q := IsOpenImmersion.lift U.ι p hrange
  have hq : q ≫ U.ι = p := IsOpenImmersion.lift_fac _ _ _
  have hqOver : q ≫ (U.toScheme ↘ Spec (.of k)) = 𝟙 _ := by
    rw [X.blowupComponent_over (K := k), ← Category.assoc, hq, hp]
  rw [← hq, Hom.comp_appTop, Category.assoc, CommRingCat.comp_apply,
    X.appTop_blowupComponent r a, Modules.baseRingToGlobalSections_apply]
  change _ = (q.appTop ≫ (ΓSpecIso (.of k)).hom)
    ((U.toScheme ↘ Spec (.of k)).appTop
      ((ΓSpecIso (.of k)).inv (X.blowupComponentGlobalSectionsEquiv r a)))
  rw [← ConcreteCategory.comp_apply, ← Category.assoc, ← Hom.comp_appTop, hqOver]
  simp

/-- A rational point of a normalization component evaluates a global unit at that component's
constant. -/
theorem blowupComponentUnits_eq_evaluation (r : Γ(N, ⊤)ˣ) (a : V)
    (p : Spec (.of k) ⟶ N) (hp : p ≫ (X.singularLocus k).blowupToBase ≫
      (X ↘ Spec (.of k)) = 𝟙 _)
    (ha : p (IsLocalRing.closedPoint k) ∈ X.blowupComponent (K := k) a) :
    X.blowupComponentUnits (k := k) r a = ev[p] r :=
  Units.ext (blowupComponentGlobalSectionsEquiv_eq_evaluation r.val a p hp ha)

/-- The ratio of the two branch values of a conductor rescaling is the ratio of
the normalization constants on the incident components. The node rescaling cancels. -/
theorem branchRatio_lineGluingCoboundary
    (r : Γ(N, ⊤)ˣ × Γ((X.singularLocus k).subscheme, ⊤)ˣ)
    (b : Fin 2 → (Spec (.of k) ⟶ P)) (a : Fin 2 → V)
    (hbase : ∀ t, (b t ≫ j) ≫ (X.singularLocus k).blowupToBase ≫
      (X ↘ Spec (.of k)) = 𝟙 _)
    (hnode : b 1 ≫ g = b 0 ≫ g)
    (ha : ∀ t, (b t ≫ j) (IsLocalRing.closedPoint k) ∈ X.blowupComponent (K := k) (a t)) :
    ev[b 1] ((j).lineGluingCoboundary g r) / ev[b 0] ((j).lineGluingCoboundary g r) =
      X.blowupComponentUnits (k := k) r.1 (a 1) / X.blowupComponentUnits (k := k) r.1 (a 0) := by
  have pull {Y Z : Scheme.{u}} (p : Spec (.of k) ⟶ Y) (f : Y ⟶ Z) (w : Γ(Z, ⊤)ˣ) :
      ev[p] (Units.map f.appTop.hom.toMonoidHom w) = ev[p ≫ f] w := by
    apply Units.ext
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, Hom.comp_appTop,
      CommRingCat.hom_comp]
    rfl
  have h₀ := blowupComponentUnits_eq_evaluation (X := X) r.1 (a 0) (b 0 ≫ j) (hbase 0) (ha 0)
  have h₁ := blowupComponentUnits_eq_evaluation (X := X) r.1 (a 1) (b 1 ≫ j) (hbase 1) (ha 1)
  rw [Hom.lineGluingCoboundary_apply]
  simp only [map_div, pull, hnode, ← h₀, ← h₁, div_div_div_cancel_right]

private theorem range_branchRatio_lineGluingCoboundary_of_sections {n : ℕ} [NeZero n]
    (a : ZMod n ≃ V) (b : ZMod n → Fin 2 → (Spec (.of k) ⟶ P))
    (hbase : ∀ i t, (b i t ≫ j) ≫ (X.singularLocus k).blowupToBase ≫
      (X ↘ Spec (.of k)) = 𝟙 _)
    (hnode : ∀ i, b i 1 ≫ g = b i 0 ≫ g)
    (hzero : ∀ i, (b i 0 ≫ j) (IsLocalRing.closedPoint k) ∈ X.blowupComponent (K := k) (a i))
    (hone : ∀ i, (b i 1 ≫ j) (IsLocalRing.closedPoint k) ∈ X.blowupComponent (K := k) (a (i + 1))) :
    Set.range (fun r i ↦
      ev[b i 1] ((j).lineGluingCoboundary g r) / ev[b i 0] ((j).lineGluingCoboundary g r)) =
        (((DualGraph.cycle n).gluingCoboundary kˣ).range : Set (ZMod n → kˣ)) := by
  have h (r : Γ(N, ⊤)ˣ × Γ((X.singularLocus k).subscheme, ⊤)ˣ) (i : ZMod n) :
      ev[b i 1] ((j).lineGluingCoboundary g r) / ev[b i 0] ((j).lineGluingCoboundary g r) =
        (DualGraph.cycle n).gluingCoboundary kˣ (X.blowupComponentUnits (k := k) r.1 ∘ a) i := by
    rw [DualGraph.gluingCoboundary_cycle_apply]
    let a' : Fin 2 → V := Fin.cases (a i) (fun _ ↦ a (i + 1))
    have ha' (t : Fin 2) : (b i t ≫ j) (IsLocalRing.closedPoint k) ∈ X.blowupComponent (a' t) := by
      fin_cases t
      · exact hzero i
      · exact hone i
    exact branchRatio_lineGluingCoboundary (X := X) r (b i) a' (hbase i) (hnode i) ha'
  ext f
  rw [SetLike.mem_coe, MonoidHom.mem_range]
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨X.blowupComponentUnits (k := k) r.1 ∘ a, (funext (h r)).symm⟩
  · rintro ⟨c, rfl⟩
    let r : Γ(N, ⊤)ˣ × Γ((X.singularLocus k).subscheme, ⊤)ˣ :=
      (X.blowupComponentUnits (k := k).symm (c ∘ a.symm), 1)
    refine ⟨r, (funext (h r)).trans ?_⟩
    simp [r, Function.comp_def]

variable (X)

local notation "hnodal" =>
  PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := X ↘ Spec (CommRingCat.of k))
local notation "nodeMap" =>
  IdealSheafData.subschemeι (X.singularLocus k) ≫ (X ↘ Spec (CommRingCat.of k))

/-- For an oriented cycle of normalization components, the image of conductor rescaling
in the branch ratios is exactly the subgroup of vertex coboundaries. At node `i`,
branch zero lies on component `i` and branch one on component `i + 1`. -/
theorem range_branchRatio_lineGluingCoboundary {n : ℕ} [NeZero n]
    (a : ZMod n ≃ V) (z : ZMod n ≃ (X.singularLocus k).subscheme)
    (order : ∀ i, Fin 2 ≃ {b : P // g b = z i})
    (hzero : ∀ i, j (order i 0).val ∈ X.blowupComponent (K := k) (a i))
    (hone : ∀ i, j (order i 1).val ∈ X.blowupComponent (K := k) (a (i + 1))) :
    Set.range (fun r i ↦
      ev[X.branchRationalPoint hnodal (order i 1).val] ((j).lineGluingCoboundary g r) /
        ev[X.branchRationalPoint hnodal (order i 0).val] ((j).lineGluingCoboundary g r)) =
          (((DualGraph.cycle n).gluingCoboundary kˣ).range : Set (ZMod n → kˣ)) := by
  let b (i : ZMod n) (t : Fin 2) := X.branchRationalPoint hnodal (order i t).val
  have happ {Y : Scheme.{u}} (f : P ⟶ Y) (i : ZMod n) (t : Fin 2) :
      (b i t ≫ f) (IsLocalRing.closedPoint k) = f (order i t).val :=
    congrArg f (X.branchRationalPoint_apply hnodal (order i t).val (IsLocalRing.closedPoint k))
  apply range_branchRatio_lineGluingCoboundary_of_sections a b
  · intro i t
    rw [Category.assoc, ← X.branchSchemeToSingularLocus_subschemeι_assoc k]
    exact X.branchRationalPoint_comp hnodal (order i t).val
  · intro i
    have := X.etale_singularLocus_subschemeι_comp hnodal
    apply ext_of_apply_closedPoint_eq nodeMap
    · exact X.branchRationalPoint_comp hnodal (order i 1).val
    · exact X.branchRationalPoint_comp hnodal (order i 0).val
    · have heq (t : Fin 2) : (b i t ≫ g) (IsLocalRing.closedPoint k) = z i :=
        (happ g i t).trans (order i t).property
      exact (heq 1).trans (heq 0).symm
  · exact fun i ↦ (happ j i 0).symm ▸ hzero i
  · exact fun i ↦ (happ j i 1).symm ▸ hone i

end AlgebraicGeometry.Scheme
