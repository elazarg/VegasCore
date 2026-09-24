/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationSourceCursor
import GameTheoryExtensions.Analysis.Protocol.FixedDepthBayes

/-! # Conditional beliefs at the source guessing decisions

The finite behavioral protocol uses its ordinary Bayes beliefs. At every
guessing information set without a public Alice certificate, the successful
false and true bindings have equal mass in the common perturbation sequence.
The equality permits failure mass and includes off-path information sets.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.NamedSource

open Vegas Interaction GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

def hasAliceBit {Claim : Type} (bit : Bool) (state : (application Claim).ProtocolState) : Prop :=
  state.elim False fun control => control.execution.application.owns alice (0, bit)

theorem hasAliceBit_carol {Claim : Type} (sample : BindingSample Claim) (bit : Bool) :
    hasAliceBit bit (some ⟨80, some carol,
      carolInput sample.first sample.second sample.binding⟩) ↔ sample.value = .success bit := by
  change (State.mk (carolInput sample.first sample.second sample.binding).application.core
    none 0).owns alice (0, bit) ↔ _
  rw [carolInput_core, owns_alice]
  simp only [true_and]
  rfl

theorem hasAliceBit_bob {Claim : Type} (sample : GuessSample Claim) (bit : Bool) :
    hasAliceBit bit (some ⟨74, some bob,
      bobInput sample.1.first sample.1.second sample.1.binding sample.2⟩) ↔
      sample.1.value = .success bit := by
  change (State.mk
    (bobInput sample.1.first sample.1.second sample.1.binding sample.2).application.core
    none 0).owns alice (0, bit) ↔ _
  rw [bobInput_core, owns_carol]
  simp only [true_and]
  simp only [alice, carol, Fin.reduceEq, false_and, or_false]
  rfl

theorem history_observe (Claim : Type) [Fintype Claim] (who : Player)
    (history : (arena Claim).History) :
    (model Claim).infoOf who history.trace = (application Claim).observe who history.state :=
  (menu Claim).info (FinDist.pure initial) horizon (scheduler Claim) who history.trace

theorem carol_history_joint (Claim : Type) [Fintype Claim]
    (strategy : ∀ who, (model Claim).BehavioralPolicy who)
    (info : List (application Claim).PlayerEntry × (application Claim).PlayerView) (bit : Bool) :
    ((model Claim).runBehavioral strategy 13).probOf
        {history | (model Claim).infoOf carol history.trace = some info ∧
          hasAliceBit bit history.state} =
      (bindingLaw ((menu Claim).decodeProfile (FinDist.pure initial)
        horizon (scheduler Claim) strategy)).probOf
          {sample | sample.carolInformation = info ∧ sample.value = .success bit} := by
  have mapped := congrArg (fun law : FinDist (application Claim).ProtocolState =>
    law.probOf {state | (application Claim).observe carol state = some info ∧
      hasAliceBit bit state})
    (model_run_state Claim strategy 13)
  rw [FinDist.probOf_map, controlLaw_carol, FinDist.probOf_map] at mapped
  simpa only [Set.preimage_ofPred_eq, history_observe, ReactiveApplication.observe,
    ite_true, Option.some.injEq, hasAliceBit_carol, BindingSample.carolInformation]
    using mapped

theorem bob_history_joint (Claim : Type) [Fintype Claim]
    (strategy : ∀ who, (model Claim).BehavioralPolicy who)
    (info : List (application Claim).PlayerEntry × (application Claim).PlayerView) (bit : Bool) :
    ((model Claim).runBehavioral strategy 20).probOf
        {history | (model Claim).infoOf bob history.trace = some info ∧
          hasAliceBit bit history.state} =
      (guessLaw ((menu Claim).decodeProfile (FinDist.pure initial)
        horizon (scheduler Claim) strategy)).probOf
          {sample | bobInformation sample = info ∧ sample.1.value = .success bit} := by
  have mapped := congrArg (fun law : FinDist (application Claim).ProtocolState =>
    law.probOf {state | (application Claim).observe bob state = some info ∧ hasAliceBit bit state})
    (model_run_state Claim strategy 20)
  rw [FinDist.probOf_map, controlLaw_bob, FinDist.probOf_map] at mapped
  simpa only [Set.preimage_ofPred_eq, history_observe, ReactiveApplication.observe,
    ite_true, Option.some.injEq, hasAliceBit_bob, bobInformation] using mapped

theorem tremble_belief_eq (Claim : Type) [Fintype Claim] (defaultClaim : Claim)
    (weight : ℝ) (positive : 0 < weight) (atMostOne : weight ≤ 1)
    (who : Player) (site : (model Claim).InformationSite who) :
    (tremble Claim defaultClaim weight positive atMostOne).belief who site =
      (model Claim).bayesBelief
        (tremble Claim defaultClaim weight positive atMostOne).strategy who site
        ((menu Claim).decisionInformationAntichain (FinDist.pure initial)
          horizon (scheduler Claim) who site)
        ((tremble_fullyMixed Claim defaultClaim weight positive atMostOne).informationMass_pos
          who site) := rfl

theorem tremble_bit_belief_eq (Claim : Type) [Fintype Claim] (defaultClaim : Claim)
    (weight : ℝ) (positive : 0 < weight) (atMostOne : weight ≤ 1)
    (who : Player) (site : (model Claim).InformationSite who) (depth : Nat)
    (sameDepth : ∀ history : (model Claim).InformationHistory who site.1,
      history.1.trace.length = depth) (bit : Bool) :
    ((tremble Claim defaultClaim weight positive atMostOne).belief who site).probOf
        {history | hasAliceBit bit history.1.state} =
      ((model Claim).runBehavioral
        (tremble Claim defaultClaim weight positive atMostOne).strategy depth).probOf
          {history | (model Claim).infoOf who history.trace = site.1 ∧
            hasAliceBit bit history.state} /
      ((model Claim).runBehavioral
        (tremble Claim defaultClaim weight positive atMostOne).strategy depth).probOf
          {history | (model Claim).infoOf who history.trace = site.1} := by
  have meet : ∃ history ∈ {history | (model Claim).infoOf who history.trace = site.1},
      history ∈ ((model Claim).runBehavioral
        (tremble Claim defaultClaim weight positive atMostOne).strategy depth).support := by
    obtain ⟨history, _⟩ := site.2
    refine ⟨history.1, history.2, ?_⟩
    have mixed := tremble_fullyMixed Claim defaultClaim weight positive atMostOne
    have reached := mixed.history_supported history.1.trace
    rwa [sameDepth history] at reached
  have conditioned := (model Claim).bayesBelief_map_eq_condOn
    (tremble Claim defaultClaim weight positive atMostOne).strategy who site depth sameDepth
    ((menu Claim).decisionInformationAntichain (FinDist.pure initial)
      horizon (scheduler Claim) who site)
    ((tremble_fullyMixed Claim defaultClaim weight positive atMostOne).informationMass_pos
      who site) meet
  rw [← tremble_belief_eq] at conditioned
  have events := congrArg
    (fun law : FinDist (arena Claim).History =>
      law.probOf {history | hasAliceBit bit history.state})
    conditioned
  rw [FinDist.probOf_map, FinDist.probOf_condOn_eq_inter] at events
  exact events

theorem carol_tremble_fair (Claim : Type) [Fintype Claim] (defaultClaim : Claim)
    (weight : ℝ) (positive : 0 < weight) (atMostOne : weight ≤ 1)
    (site : (model Claim).InformationSite carol)
    (past : List (application Claim).PlayerEntry) (view : (application Claim).PlayerView)
    (observed : site.1 = some (past, view)) (granted : view.application.visit = some 1)
    (hidden : NoPublicAlice view) :
    ((tremble Claim defaultClaim weight positive atMostOne).belief carol site).probOf
        {history | hasAliceBit false history.1.state} =
      ((tremble Claim defaultClaim weight positive atMostOne).belief carol site).probOf
        {history | hasAliceBit true history.1.state} := by
  have sameDepth (history : (model Claim).InformationHistory carol site.1) :
      history.1.trace.length = 13 :=
    carol_information_depth Claim past view granted ⟨history.1, history.2.trans observed⟩
  rw [tremble_bit_belief_eq Claim defaultClaim weight positive atMostOne carol site 13 sameDepth,
    tremble_bit_belief_eq Claim defaultClaim weight positive atMostOne carol site 13 sameDepth,
    observed, carol_history_joint, carol_history_joint]
  exact congrArg (fun numerator => numerator / _) (carol_joint_fair
    (tremblePlayers Claim defaultClaim weight positive atMostOne)
    (tremble_alice_symmetric Claim defaultClaim weight positive atMostOne) (past, view) hidden)

theorem bob_tremble_fair (Claim : Type) [Fintype Claim] (defaultClaim : Claim)
    (weight : ℝ) (positive : 0 < weight) (atMostOne : weight ≤ 1)
    (site : (model Claim).InformationSite bob)
    (past : List (application Claim).PlayerEntry) (view : (application Claim).PlayerView)
    (observed : site.1 = some (past, view)) (granted : view.application.visit = some 2)
    (hidden : NoPublicAlice view) :
    ((tremble Claim defaultClaim weight positive atMostOne).belief bob site).probOf
        {history | hasAliceBit false history.1.state} =
      ((tremble Claim defaultClaim weight positive atMostOne).belief bob site).probOf
        {history | hasAliceBit true history.1.state} := by
  have sameDepth (history : (model Claim).InformationHistory bob site.1) :
      history.1.trace.length = 20 :=
    bob_information_depth Claim past view granted ⟨history.1, history.2.trans observed⟩
  rw [tremble_bit_belief_eq Claim defaultClaim weight positive atMostOne bob site 20 sameDepth,
    tremble_bit_belief_eq Claim defaultClaim weight positive atMostOne bob site 20 sameDepth,
    observed, bob_history_joint, bob_history_joint]
  exact congrArg (fun numerator => numerator / _) (bob_joint_fair
    (tremblePlayers Claim defaultClaim weight positive atMostOne)
    (tremble_alice_symmetric Claim defaultClaim weight positive atMostOne) (past, view) hidden)

end VegasTests.SelectiveAssociation.NamedSource
