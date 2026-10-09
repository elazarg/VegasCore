/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeSource
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # The answer and forced publication in the actual source protocol -/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeSource

open SourceProgram GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

def bobBindingChoice (bit : Bool) (answer : Answer) :
    setup.intendedModel.Choice bob (bobBindingSite bit).1 :=
  ⟨some (.commit bob 3 (.range 0 5) (.success answer)), by
    change some bob = some bob ∧ ∃ value ∈ intendedValues bob answerGuard _,
      (OwnAction.commit bob 3 (BaseTy.range 0 5) (.success answer) :
        OwnAction Player simpleExpr) =
        OwnAction.commit bob 3 (BaseTy.range 0 5) (.success value)
    exact ⟨rfl, answer, Or.inl (fun _ => rfl), rfl⟩⟩

theorem bobBindingChoice_injective (bit : Bool) : Function.Injective (bobBindingChoice bit) := by
  intro first second same
  have actions := congrArg Subtype.val same
  change some (OwnAction.commit bob 3 (BaseTy.range 0 5) (.success first) :
    OwnAction Player simpleExpr) = some (.commit bob 3 (BaseTy.range 0 5) (.success second))
      at actions
  simpa only [Option.some.injEq, OwnAction.commit.injEq, heq_eq_eq, true_and,
    PublicationResult.success.injEq] using actions

theorem bobBindingChoice_surjective (bit : Bool) : Function.Surjective (bobBindingChoice bit) := by
  intro choice
  have allowed := choice.property
  cases value : choice.val with
  | none =>
      rw [value] at allowed
      change some bob ≠ some bob at allowed
      exact (allowed rfl).elim
  | some action =>
      rw [value] at allowed
      change some bob = some bob ∧ ∃ answer ∈ intendedValues bob answerGuard _,
        action = OwnAction.commit bob 3 (BaseTy.range 0 5) (.success answer) at allowed
      obtain ⟨answer, _, addressed⟩ := allowed.2
      refine ⟨answer, Subtype.ext ?_⟩
      exact value.trans (congrArg some addressed) |>.symm

def bobChoiceEquiv (bit : Bool) : Answer ≃ setup.intendedModel.Choice bob (bobBindingSite bit).1 :=
  Equiv.ofBijective (bobBindingChoice bit)
    ⟨bobBindingChoice_injective bit, bobBindingChoice_surjective bit⟩

def bobAnswerLaw (profile : ∀ who, setup.intendedModel.BehavioralPolicy who) (bit : Bool) :
    PMF Answer := (profile bob (bobBindingSite bit).1).map (bobChoiceEquiv bit).symm

def boundConfig (bit : Bool) (label : Fin 3) (answer : Answer) :=
  commitSuccessor 3 answerGuard
    (revealSuccessor 2 .here (setup.initialConfig (sourceInitial bit label)) true) (.success answer)

def boundState (bit : Bool) (label : Fin 3) (answer : Answer) : setup.ProtocolState :=
  some (.inr (.inr (.inl (boundConfig bit label answer))))

def finishedState (bit : Bool) (label : Fin 3) (answer : Answer) : setup.ProtocolState :=
  some (.inr (.inr (.inr (revealSuccessor 4 .here (boundConfig bit label answer) true))))

private def bindingJoint (answer : Answer) (who : Player) : Option (OwnAction Player simpleExpr) :=
  if who = bob then some (.commit bob 3 (.range 0 5) (.success answer)) else none

private theorem bindingJointLegal (bit : Bool) (label : Fin 3) (answer : Answer) :
    setup.intendedProtocol.Legal (openedState bit label) (bindingJoint answer) := by
  refine ⟨not_false, ?_⟩
  intro who
  fin_cases who
  · change some bob ≠ some alice
    decide
  · change some bob = some bob ∧ ∃ value ∈ intendedValues bob answerGuard _,
      (OwnAction.commit bob 3 (BaseTy.range 0 5) (.success answer) :
        OwnAction Player simpleExpr) =
        OwnAction.commit bob 3 (BaseTy.range 0 5) (.success value)
    exact ⟨rfl, answer, Or.inl (fun _ => rfl), rfl⟩

private theorem binding_step (bit : Bool) (label : Fin 3) (answer : Answer) :
    setup.intendedProtocol.step (openedState bit label)
      ⟨bindingJoint answer, bindingJointLegal bit label answer⟩ =
      PMF.pure (boundState bit label answer) := by
  change (ProtocolState.step program
    (.inr (.inl (revealSuccessor 2 .here (setup.initialConfig (sourceInitial bit label)) true)))
      (bindingJoint answer)).map some = _
  simp only [ProtocolState.step, program, Sum.elim_inr, Sum.elim_inl,
    bindingJoint, ↓reduceIte, OwnAction.binding_commit, PMF.pure_map]
  rfl

def boundHistory (bit : Bool) (label : Fin 3) (answer : Answer) :
    setup.intendedProtocol.History :=
  (openedHistory bit label).extend (target := boundState bit label answer)
    (bindingJointLegal bit label answer) (by
      change boundState bit label answer ∈
        (setup.intendedProtocol.step (openedState bit label)
          ⟨bindingJoint answer, bindingJointLegal bit label answer⟩).support
      rw [binding_step]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl)

private def publicationJoint (who : Player) : Option (OwnAction Player simpleExpr) :=
  if who = bob then some (.reveal bob 3 true) else none

private theorem publicationJointLegal (bit : Bool) (label : Fin 3) (answer : Answer) :
    setup.intendedProtocol.Legal (boundState bit label answer) publicationJoint := by
  refine ⟨not_false, ?_⟩
  intro who
  fin_cases who
  · change some bob ≠ some alice
    decide
  · change some bob = some bob ∧
      OwnAction.reveal bob 3 true ∈ ({OwnAction.reveal bob 3 true} :
        Set (OwnAction Player simpleExpr))
    exact ⟨rfl, rfl⟩

private theorem publication_step (bit : Bool) (label : Fin 3) (answer : Answer) :
    setup.intendedProtocol.step (boundState bit label answer)
      ⟨publicationJoint, publicationJointLegal bit label answer⟩ =
      PMF.pure (finishedState bit label answer) := by
  change (ProtocolState.step program (.inr (.inr (.inl (boundConfig bit label answer))))
    publicationJoint).map some = _
  simp only [ProtocolState.step, program, Sum.elim_inr, Sum.elim_inl, PMF.pure_map]
  rfl

def finishedHistory (bit : Bool) (label : Fin 3) (answer : Answer) :
    setup.intendedProtocol.History :=
  (boundHistory bit label answer).extend (target := finishedState bit label answer)
    (publicationJointLegal bit label answer) (by
      change finishedState bit label answer ∈
        (setup.intendedProtocol.step (boundState bit label answer)
          ⟨publicationJoint, publicationJointLegal bit label answer⟩).support
      rw [publication_step]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl)

theorem finishedHistory_readout (bit : Bool) (label : Fin 3) (answer : Answer) :
    setup.protocolReadout (finishedHistory bit label answer).state =
      some (finalState bit label true answer true) := by
  rfl

private theorem bob_choice_bound (bit : Bool) (label : Fin 3) (answer : Answer)
    (choice : setup.intendedModel.Choice bob
      (setup.intendedModel.infoOf bob (boundHistory bit label answer).trace)) :
    choice.val = some (.reveal bob 3 true) := by
  have allowed := choice.property
  cases value : choice.val with
  | none =>
      rw [value] at allowed
      change some bob ≠ some bob at allowed
      exact (allowed rfl).elim
  | some action =>
      rw [value] at allowed
      change some bob = some bob ∧
        action ∈ ({OwnAction.reveal bob 3 true} : Set (OwnAction Player simpleExpr)) at allowed
      exact congrArg some allowed.2

private theorem publication_joint_bound
    (profile : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (bit : Bool) (label : Fin 3) (answer : Answer) :
    setup.intendedModel.behavioralJoint profile (boundHistory bit label answer).trace
      (publicationJointLegal bit label answer).1 =
      PMF.pure ⟨publicationJoint, publicationJointLegal bit label answer⟩ := by
  classical
  have unique (who : Player)
      (acts : setup.intendedProtocol.active (boundState bit label answer) who) : who = bob := by
    change some bob = some who at acts
    exact (Option.some.inj acts).symm
  rw [setup.intendedModel.behavioralJoint_eq_map_of_at_most_one_active profile
    (boundHistory bit label answer).trace (publicationJointLegal bit label answer).1 bob unique]
  apply pmf_eq_pure_of_support_subset_singleton
  intro draw supported
  rw [PMF.support_map] at supported
  obtain ⟨choice, _, rfl⟩ := supported
  apply Subtype.ext
  funext who
  change setup.intendedProtocol.singletonJoint bob choice.val who = publicationJoint who
  by_cases same : who = bob
  · subst who
    simp only [ExecutionProtocol.singletonJoint, ↓reduceDIte]
    exact bob_choice_bound bit label answer choice
  · simp [ExecutionProtocol.singletonJoint, same, publicationJoint]

theorem publication_round
    (profile : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (bit : Bool) (label : Fin 3) (answer : Answer) :
    setup.intendedModel.runBehavioralFrom profile 1 (boundHistory bit label answer) =
      PMF.pure (finishedHistory bit label answer) := by
  rw [setup.intendedModel.runBehavioralFrom_succ_of_not_terminal profile 0
      (publicationJointLegal bit label answer).1,
    publication_joint_bound, PMF.pure_bind]
  apply pmf_eq_pure_of_support_subset_singleton
  intro final supported
  simp only [PMF.support_bindOnSupport, Set.mem_iUnion] at supported
  obtain ⟨target, realized, supported⟩ := supported
  have targetEq : target = finishedState bit label answer :=
    (PMF.mem_support_pure_iff _ _).mp (publication_step bit label answer ▸ realized)
  subst target
  change final ∈ (PMF.pure (finishedHistory bit label answer)).support at supported
  exact (PMF.mem_support_pure_iff _ _).mp supported

private theorem binding_joint_opened
    (profile : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (bit : Bool) (label : Fin 3) :
    setup.intendedModel.behavioralJoint profile (openedHistory bit label).trace
      (bindingJointLegal bit label safe).1 =
      (bobAnswerLaw profile bit).map
        (fun answer => ⟨bindingJoint answer, bindingJointLegal bit label answer⟩) := by
  classical
  have unique (who : Player)
      (acts : setup.intendedProtocol.active (openedState bit label) who) : who = bob := by
    change some bob = some who at acts
    exact (Option.some.inj acts).symm
  have collapse := congrArg (PMF.map Subtype.val)
    (setup.intendedModel.behavioralJoint_eq_map_of_at_most_one_active profile
      (openedHistory bit label).trace (bindingJointLegal bit label safe).1 bob unique)
  simp only [PMF.map_comp] at collapse
  change (setup.intendedModel.behavioralJoint profile (openedHistory bit label).trace
    (bindingJointLegal bit label safe).1).map Subtype.val =
      (profile bob (setup.intendedModel.infoOf bob (openedHistory bit label).trace)).map
        (fun choice => setup.intendedProtocol.singletonJoint bob choice.val) at collapse
  rw [bobBindingInfo_opened] at collapse
  apply pmf_map_injective (f := Subtype.val) Subtype.val_injective
  rw [collapse, PMF.map_comp, bobAnswerLaw, PMF.map_comp]
  congr 1
  funext choice
  have encoded := congrArg Subtype.val ((bobChoiceEquiv bit).apply_symm_apply choice)
  change some (.commit bob 3 (BaseTy.range 0 5)
    (.success ((bobChoiceEquiv bit).symm choice)) : OwnAction Player simpleExpr) = choice.val
      at encoded
  rw [← encoded]
  funext who
  by_cases same : who = bob
  · subst who
    rfl
  · simp [ExecutionProtocol.singletonJoint, same, bindingJoint]

theorem bobContinuation_rounds
    (profile : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (bit : Bool) (label : Fin 3) :
    setup.intendedModel.runBehavioralFrom profile 2 (openedHistory bit label) =
      (bobAnswerLaw profile bit).map (fun answer => finishedHistory bit label answer) := by
  rw [setup.intendedModel.runBehavioralFrom_succ_of_not_terminal profile 1
      (bindingJointLegal bit label safe).1,
    binding_joint_opened, PMF.bind_map]
  change (bobAnswerLaw profile bit).bind (fun answer =>
    (setup.intendedProtocol.step (openedState bit label)
      ⟨bindingJoint answer, bindingJointLegal bit label answer⟩).bindOnSupport
      (fun target realized => setup.intendedModel.runBehavioralFrom profile 1
        ((openedHistory bit label).extend (bindingJointLegal bit label answer) realized))) = _
  calc
    _ = (bobAnswerLaw profile bit).bind
        (fun answer => PMF.pure (finishedHistory bit label answer)) := by
      apply bind_congr_on_support
      intro answer _
      apply pmf_eq_pure_of_support_subset_singleton
      intro final supported
      simp only [PMF.support_bindOnSupport, Set.mem_iUnion] at supported
      obtain ⟨target, realized, supported⟩ := supported
      have targetEq : target = boundState bit label answer :=
        (PMF.mem_support_pure_iff _ _).mp (binding_step bit label answer ▸ realized)
      subst target
      change final ∈ (setup.intendedModel.runBehavioralFrom profile 1
        (boundHistory bit label answer)).support at supported
      rw [publication_round] at supported
      exact (PMF.mem_support_pure_iff _ _).mp supported
    _ = _ := PMF.bind_pure_comp _ _

/-- From Bob's binding decision, an arbitrary intended policy draws its answer
and publishes it. No later strategic choice changes the terminal store. -/
theorem bobContinuation_readout
    (profile : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (bit : Bool) (label : Fin 3) :
    (setup.intendedModel.runBehavioralTerminalFrom
      setup.intended_bounded.wellFoundedHistories profile (openedHistory bit label)).map
        (fun final => setup.protocolReadout final.state) =
      (bobAnswerLaw profile bit).map
        (fun answer => some (finalState bit label true answer true)) := by
  rw [setup.intendedModel.runBehavioralTerminalFrom_eq_remaining
    setup.intended_bounded.wellFoundedHistories profile setup.intended_bounded]
  change (setup.intendedModel.runBehavioralFrom profile 2 (openedHistory bit label)).map _ = _
  rw [bobContinuation_rounds, PMF.map_comp]
  rfl

/-- The initialized source draws its private parameter once and then draws
Bob's answer from his policy at the observed bit. Both publications are forced. -/
theorem intendedTerminal_histories
    (profile : ∀ who, setup.intendedModel.BehavioralPolicy who) :
    setup.intendedModel.runBehavioralTerminalFrom
      setup.intended_bounded.wellFoundedHistories profile setup.intendedProtocol.initHistory =
      prior.bind (fun parameter => (bobAnswerLaw profile parameter.1).map
        (fun answer => finishedHistory parameter.1 parameter.2 answer)) := by
  rw [setup.intendedModel.runBehavioralTerminalFrom_initHistory
    setup.intended_bounded.wellFoundedHistories profile setup.intended_bounded]
  change setup.intendedModel.runBehavioralFrom profile (2 + 2)
    setup.intendedProtocol.initHistory = _
  rw [setup.intendedModel.runBehavioralFrom_add]
  change (setup.intendedModel.runBehavioral profile 2).bind
    (setup.intendedModel.runBehavioralFrom profile 2) = _
  rw [opening_prefix, PMF.bind_map]
  simp only [Function.comp_def, bobContinuation_rounds]

theorem intendedTerminal_readout
    (profile : ∀ who, setup.intendedModel.BehavioralPolicy who) :
    (setup.intendedModel.runBehavioralTerminalFrom
      setup.intended_bounded.wellFoundedHistories profile setup.intendedProtocol.initHistory).map
        (fun final => setup.protocolReadout final.state) =
      prior.bind (fun parameter => (bobAnswerLaw profile parameter.1).map
        (fun answer => some (finalState parameter.1 parameter.2 true answer true))) := by
  rw [intendedTerminal_histories, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def, finishedHistory_readout]

end Vegas.Examples.LateOpeningRuntimeSource
