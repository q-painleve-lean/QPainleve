/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Center
public import QPainleve.Algebra.Cluster.Word.RationalMap
public import QPainleve.SignedClusterModularGroup.CenterMutation

/-!
# Joint evaluation along cluster words

A charge realization and a typed word determine a birational transformation of
the joint torus of centers and surface characters. Its center coordinates follow
the monomial transport, and the evaluation of independent X coordinates intertwines
it with the X transformation of the word. The center variables remain independent
in the function field.

For a mutation the transformation is the binomial shear of Gross, Hacking and
Keel, *Birational geometry of cluster algebras*, (1.4) and Lemma 3.2.
-/

public noncomputable section

open AlgebraicGeometry Multiplicative Quiver
open QPainleve QPainleve.Cluster QPainleve.CharacterTorus

universe u

variable {ι N : Type u} [Fintype ι] [DecidableEq ι] [AddCommGroup N] [Module.Free ℤ N]
  {B C D : SkewExchangeMatrix ι} (k : Type u) [Field k]

attribute [local instance] hasUniqueDiv_of_free_int

local notation "A" => (ι → ℤ)
local notation "Joint" => FunctionField k (A × N)

namespace QPainleve.Cluster.Step

local notation "fieldCongr" e:arg =>
  (IsFractionRing.algEquivOfAlgEquiv (AddMonoidAlgebra.domCongr k k e) : Joint ≃ₐ[k] Joint)

/-- The joint pullback of a step with a specified charge realization. A relabeling
changes only the center labels. Inversion takes the reciprocals of both the center
characters and the surface characters, in accordance with reversal of the form. -/
def jointPullback (s : B ⟶ C) (P : ChargeSeed B N) : Joint ≃ₐ[k] Joint :=
  match s.generator with
  | .mutate p => centerMutationPullback P.form P.charge p k P.isAlt
  | .permute _ => fieldCongr
      ((exponentEquiv s).prodCongr (LinearEquiv.refl ℤ N)).toAddEquiv
  | .invert => fieldCongr (AddEquiv.neg (A × N))

@[simp]
theorem jointPullback_mutate (P : ChargeSeed B N) (p : ι) :
    jointPullback k ((Generator.mutate p).toStep B) P =
      centerMutationPullback P.form P.charge p k P.isAlt := by
  rw [jointPullback, Generator.toStep_generator]

/-- Relabeling transports the center exponent and fixes the surface exponent. -/
@[simp]
theorem jointPullback_permute_monomial (P : ChargeSeed B N) (σ : Equiv.Perm ι)
    (a : A) (h : N) :
    jointPullback k ((Generator.permute σ).toStep B) P (monomial k (ofAdd (a, h))) =
      monomial k (ofAdd (LinearEquiv.funCongrLeft ℤ ℤ σ.symm a, h)) := by
  rw [jointPullback, Generator.toStep_generator]
  simp only [← AlgEquiv.toAlgHom_apply, algEquivOfAlgEquiv_domCongr_toAlgHom,
    functionFieldMap_monomial, AddEquiv.coe_toAddMonoidHom, LinearEquiv.coe_toAddEquiv,
    exponentEquiv_permute]
  rfl

/-- Inversion negates both exponents of every joint character. -/
@[simp]
theorem jointPullback_invert_monomial (P : ChargeSeed B N) (a : A) (h : N) :
    jointPullback k (Generator.invert.toStep B) P (monomial k (ofAdd (a, h))) =
      (monomial k (ofAdd (a, h)))⁻¹ := by
  rw [jointPullback, Generator.toStep_generator]
  simp only [← AlgEquiv.toAlgHom_apply, algEquivOfAlgEquiv_domCongr_toAlgHom,
    functionFieldMap_monomial, AddEquiv.coe_toAddMonoidHom, AddEquiv.neg_apply, ofAdd_neg, map_inv]

/-- The joint transformation acts on center characters by the integral exponent
substitution of the step. -/
@[simp]
theorem jointPullback_center_monomial (s : B ⟶ C) (P : ChargeSeed B N) (a : A) :
    jointPullback k s P (monomial k (ofAdd (a, (0 : N)))) =
      monomial k (ofAdd (exponentEquiv s a, (0 : N))) := by
  obtain ⟨g, rfl⟩ := s
  have hg : g.toStep B = ⟨g, rfl⟩ := Step.ext (Generator.toStep_generator g B)
  rw [← hg]
  cases g with
  | mutate p =>
    simp [P.matrix_eq]
  | permute σ => simp
  | invert =>
    simp only [jointPullback_invert_monomial, exponentEquiv_invert, LinearEquiv.neg_apply,
      ← map_inv, ← ofAdd_neg, Prod.neg_mk, neg_zero]

/-- Evaluation at the target charge realization intertwines the joint and independent X
pullbacks of each of the three generators. -/
theorem jointPullback_comp_xEvaluationPullback (s : B ⟶ C) (P : ChargeSeed B N) :
    (jointPullback k s P).toAlgHom.comp (xEvaluationPullback (chargeTarget s P).charge k) =
      (xEvaluationPullback P.charge k).comp (xPullback k s).toAlgHom := by
  obtain ⟨g, rfl⟩ := s
  have hg : g.toStep B = ⟨g, rfl⟩ := Step.ext (Generator.toStep_generator g B)
  rw [← hg]
  cases g with
  | mutate p =>
    simpa only [jointPullback_mutate, chargeTarget_mutate_charge, xPullback_toStep,
      Generator.xPullback_mutate, ← P.matrix_eq] using
      centerMutationPullback_comp_xEvaluationPullback P.form P.charge p k P.isAlt
  | permute σ =>
    apply functionField_hom_ext_basis (Finsupp.basisSingleOne (R := ℤ) (ι := ι))
    intro j
    have hs : LinearEquiv.funCongrLeft ℤ ℤ σ.symm (Pi.single j 1) = Pi.single (σ j) 1 := by
      funext i
      simpa only [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Function.comp_apply,
        Equiv.symm_symm] using congrFun (Pi.single_comp_equiv σ.symm j (1 : ℤ)) i
    rw [Finsupp.coe_basisSingleOne, monomial_ofAdd]
    simp only [← xCoordinate_def, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
      chargeTarget_permute_charge, xPullback_toStep, Generator.xPullback_permute,
      xReindex_apply_xCoordinate, xEvaluationPullback_xCoordinate, LinearMap.comp_apply,
      LinearEquiv.coe_coe, jointPullback_permute_monomial, hs]
  | invert =>
    apply functionField_hom_ext_basis (Finsupp.basisSingleOne (R := ℤ) (ι := ι))
    intro j
    rw [Finsupp.coe_basisSingleOne, monomial_ofAdd]
    simp only [← xCoordinate_def, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
      chargeTarget_invert_charge, xPullback_toStep, Generator.xPullback_invert,
      xInversion_apply_xCoordinate, map_inv₀, xEvaluationPullback_xCoordinate,
      jointPullback_invert_monomial]

end QPainleve.Cluster.Step

namespace Quiver.Path

/-- The joint pullback of a word uses the charge realization at each successive step
and composes pullbacks in reverse execution order. -/
def jointPullback : {C : SkewExchangeMatrix ι} → Word B C → ChargeSeed B N → Joint ≃ₐ[k] Joint
  | _, .nil, _ => 1
  | _, .cons w s, P => jointPullback w P * Step.jointPullback k s (w.chargeTarget P)

@[simp]
theorem jointPullback_nil (P : ChargeSeed B N) :
    (Path.nil : Word B B).jointPullback k P = 1 :=
  (rfl)

@[simp]
theorem jointPullback_cons (w : Word B C) (s : C ⟶ D) (P : ChargeSeed B N) :
    (w.cons s).jointPullback k P =
      w.jointPullback k P * Step.jointPullback k s (w.chargeTarget P) :=
  (rfl)

@[simp]
theorem jointPullback_toPath (s : B ⟶ C) (P : ChargeSeed B N) :
    s.toPath.jointPullback k P = Step.jointPullback k s P := by
  simp [Hom.toPath]

/-- Concatenation composes the two joint pullbacks, with the intermediate charge realization
as the input for the second word. -/
@[simp]
theorem jointPullback_comp (w : Word B C) (v : Word C D) (P : ChargeSeed B N) :
    (w.comp v).jointPullback k P = w.jointPullback k P * v.jointPullback k (w.chargeTarget P) := by
  induction v with
  | nil => simp
  | cons v s ih => simp [ih, mul_assoc]

/-- The joint pullback induces the word's monomial transport on all center characters. -/
@[simp]
theorem jointPullback_center_monomial (w : Word B C) (P : ChargeSeed B N) (a : A) :
    w.jointPullback k P (monomial k (ofAdd (a, (0 : N)))) =
      monomial k (ofAdd (w.exponentEquiv a, (0 : N))) := by
  induction w generalizing a with
  | nil => simp
  | cons w s ih =>
    simp only [jointPullback_cons, AlgEquiv.mul_apply, Step.jointPullback_center_monomial k,
      ih, exponentEquiv_cons, LinearEquiv.trans_apply]

/-- For every typed signed word, evaluating the final X coordinates and pulling back on
the joint field agrees with pulling back the independent X functions and then evaluating
at the initial charge realization. The identity holds on the entire X function field. -/
theorem jointPullback_comp_xEvaluationPullback (w : Word B C) (P : ChargeSeed B N) :
    (w.jointPullback k P).toAlgHom.comp (xEvaluationPullback (w.chargeTarget P).charge k) =
      (xEvaluationPullback P.charge k).comp (w.xPullback k).toAlgHom := by
  induction w with
  | nil =>
    simp only [chargeTarget_nil, jointPullback_nil, xPullback_nil]
    exact AlgHom.ext fun _ ↦ rfl
  | cons w s ih =>
    apply AlgHom.ext
    intro x
    simp only [chargeTarget_cons, jointPullback_cons, xPullback_cons, AlgHom.comp_apply,
      AlgEquiv.toAlgHom_apply, AlgEquiv.mul_apply]
    have hs := DFunLike.congr_fun
      (Step.jointPullback_comp_xEvaluationPullback k s (w.chargeTarget P)) x
    simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply] at hs
    rw [hs]
    exact DFunLike.congr_fun ih (Step.xPullback k s x)

section RationalMap

variable [Module.Finite ℤ N]

local notation "T" => scheme k (A × N)
local notation "jointRep" w:arg P:arg =>
  Equiv.symm (rationalPullbackEquiv k) (AlgEquiv.toAlgHom (jointPullback k w P))

/-- The rational transformation of the joint center and surface torus along a word
and its transported charge realizations. -/
def jointRationalMap (w : Word B C) (P : ChargeSeed B N) : T ⤏ T :=
  (jointRep w P).val

instance (w : Word B C) (P : ChargeSeed B N) : (w.jointRationalMap k P).IsDominant :=
  (jointRep w P).property.left

instance (w : Word B C) (P : ChargeSeed B N) :
    (w.jointRationalMap k P).IsOver (structureMap k (A × N)) (structureMap k (A × N)) :=
  (jointRep w P).property.right

/-- The rational transformation of the joint torus induces the joint pullback. -/
@[simp]
theorem affineRationalPullback_jointRationalMap (w : Word B C) (P : ChargeSeed B N) :
    affineRationalPullback k (w.jointRationalMap k P) = (w.jointPullback k P).toRingHom :=
  affineRationalPullback_rationalPullbackEquiv_symm k _

@[simp]
theorem jointRationalMap_nil (P : ChargeSeed B N) :
    (Path.nil : Word B B).jointRationalMap k P = Scheme.RationalMap.id T := by
  apply (affineRationalPullback_eq_iff _ _).mp
  simp only [affineRationalPullback_jointRationalMap, affineRationalPullback_id, jointPullback_nil]
  rfl

/-- Joint rational transformations compose in execution order. -/
@[simp]
theorem jointRationalMap_comp (w : Word B C) (v : Word C D) (P : ChargeSeed B N) :
    (w.comp v).jointRationalMap k P =
      (w.jointRationalMap k P).comp (v.jointRationalMap k (w.chargeTarget P)) := by
  apply (affineRationalPullback_eq_iff _ _).mp
  simp only [affineRationalPullback_jointRationalMap, affineRationalPullback_comp,
    jointPullback_comp]
  rfl

/-- On the common rational domain, applying a word to the joint torus and then
evaluating with the final charges agrees with evaluating with the initial charges
and then applying its independent X rational map. -/
theorem jointRationalMap_comp_xEvaluationMap (w : Word B C) (P : ChargeSeed B N) :
    (w.jointRationalMap k P).comp
        (xEvaluationMap (w.chargeTarget P).charge k).toRationalMap =
      (xEvaluationMap P.charge k).toRationalMap.comp (w.xRationalMap k) := by
  apply (affineRationalPullback_eq_iff _ _).mp
  simp only [affineRationalPullback_comp, affineRationalPullback_jointRationalMap,
    affineRationalPullback_xEvaluationMap, affineRationalPullback_xRationalMap]
  exact congrArg AlgHom.toRingHom (w.jointPullback_comp_xEvaluationPullback k P)

/-- Projecting the joint torus to the center torus intertwines the joint rational
transformation with the monomial center isomorphism of the word. -/
theorem jointRationalMap_comp_centerProjection (w : Word B C) (P : ChargeSeed B N) :
    let π := CharacterTorus.map k (AddMonoidHom.inl A N)
    letI : IsDominant π := isDominant_map k _ fun _ _ h ↦ congrArg Prod.fst h
    (w.jointRationalMap k P).comp π.toRationalMap =
      π.toRationalMap.comp (w.centerIso k).hom.toRationalMap := by
  have hinj : Function.Injective (AddMonoidHom.inl A N) := fun _ _ h ↦ congrArg Prod.fst h
  have := isDominant_map k (AddMonoidHom.inl A N) hinj
  dsimp only
  apply (affineRationalPullback_eq_iff _ _).mp
  let f := w.exponentEquiv.toAddEquiv.toAddMonoidHom
  have hf : Function.Injective f := w.exponentEquiv.injective
  have hcenter :
      affineRationalPullback k (w.centerIso k).hom.toRationalMap =
        (functionFieldMap k f hf).toRingHom := by
    simpa only [f, ← centerIso_hom k w] using affineRationalPullback_map (k := k) f hf
  simp only [affineRationalPullback_comp, affineRationalPullback_jointRationalMap,
    affineRationalPullback_map (AddMonoidHom.inl A N) hinj, hcenter]
  suffices h :
      (w.jointPullback k P).toAlgHom.comp (functionFieldMap k (AddMonoidHom.inl A N) hinj) =
        (functionFieldMap k (AddMonoidHom.inl A N) hinj).comp
          (functionFieldMap k f hf) by
    exact congrArg AlgHom.toRingHom h
  apply functionField_hom_ext
  intro a
  simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, functionFieldMap_monomial,
    f, AddEquiv.coe_toAddMonoidHom, LinearEquiv.coe_toAddEquiv, AddMonoidHom.inl_apply,
    jointPullback_center_monomial]
  rfl

end RationalMap

end Quiver.Path
