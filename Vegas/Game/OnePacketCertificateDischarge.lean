/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketSequentialPreservation
import Vegas.Game.OnePacketSlotLaw
import Interaction.ReactiveSupportedRounds
import Vegas.Game.OnePacketEventSuccess

/-! # Discharging inputs of the one-packet certificate

As-if-honest play never reaches a late delivery: every information state it
reaches is a round-supported state of as-if-honest play read as native
policies, whose rounds are those of the first-turn clients of the intended
effective opening, and those clients have submitted for every event they had a
turn at (`Vegas.not_lateDelivery_of_honestReached`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability GameTheory.Enforcement
  Interaction EventGraphRuntime Filter

section Honest

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  [Fintype Player] (bounds : MessageBounds (graph setup))

/-- Within the horizon, as-if-honest play read as native policies reaches the
executions the first-turn clients of the intended effective opening reach. -/
theorem roundsFrom_honest_eq_openingClients (wellFormed : setup.WellFormed) {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (assessment : setup.intendedModel.BehavioralAssessment)
    (retains : RetainsCoveredCanonical setup leaks bounds horizon scheduler bound) {count : Nat}
    (within : count ≤ horizon) :
    (application setup leaks).roundsFrom (initialLaw setup) scheduler
        ((bounds.onePacketMenu (runtime setup) leaks).decodeProfile (initialLaw setup) horizon
          scheduler (honestProfile setup leaks bounds (initialLaw setup) horizon scheduler
            assessment)) count =
      (application setup leaks).roundsFrom (initialLaw setup) scheduler
        (openingClients setup leaks bound 0 assessment.strategy) count := by
  unfold ReactiveApplication.roundsFrom
  apply bind_congr_on_support _
  intro state stateMem
  exact runRounds_honest_eq_openingClients bounds wellFormed contract timely 0 assessment retains
    count 0 (by omega) _
    ((PMF.mem_support_bind_iff _ _ _).mpr ⟨state, stateMem, (PMF.mem_support_pure_iff _ _).mpr rfl⟩)
    ((bounds.onePacketMenu (runtime setup) leaks).trace_initial (initialLaw setup) horizon
      scheduler state stateMem)

/-- **As-if-honest play never reaches a late delivery.** For a well-formed
setup, under the asynchronous contract with timely delays and retention of
first covered canonical packets, no information state as-if-honest play
reaches is a late delivery. -/
theorem not_lateDelivery_of_honestReached (wellFormed : setup.WellFormed) {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (assessment : setup.intendedModel.BehavioralAssessment)
    (retains : RetainsCoveredCanonical setup leaks bounds horizon scheduler bound)
    {who : Player} {info : (application setup leaks).Info}
    (reached : HonestReached setup leaks bounds horizon scheduler assessment who info) :
    ¬ LateDelivery setup leaks who info := by
  let app := application setup leaks
  let menu := bounds.onePacketMenu (runtime setup) leaks
  obtain ⟨fuel, history, mem, infoEq⟩ := reached
  have supported := menu.roundSupported_of_mem_run (initialLaw setup) horizon scheduler
    (honestProfile setup leaks bounds (initialLaw setup) horizon scheduler assessment) fuel
    history mem
  have observed : app.observe who history.state = info :=
    (menu.info (initialLaw setup) horizon scheduler who history.trace).symm.trans infoEq
  rintro ⟨past, view, event, same, pending, entry, member, activated⟩
  subst same
  obtain ⟨_, _, owned, unrecorded⟩ := pendingEvent_spec pending
  generalize history.state = state at supported observed
  rcases state with _ | ⟨remaining, actor, execution⟩
  · cases observed
  rcases actor with _ | player
  · simp [ReactiveApplication.observe] at observed
  by_cases same : player = who
  · subst same
    simp only [ReactiveApplication.observe, ↓reduceIte, Option.some.injEq, Prod.mk.injEq]
      at observed
    obtain ⟨pastEq, _⟩ := observed
    obtain ⟨accounted, count, prior, command, position, priorMem, _, _, stepped⟩ := supported
    have within : count ≤ horizon := by dsimp at accounted position; omega
    rw [roundsFrom_honest_eq_openingClients bounds wellFormed contract timely assessment retains
      within] at priorMem
    have recalled : execution.recall player = prior.recall player :=
      congrFun (app.environmentStep_recall prior execution command stepped) player
    have recorded := openingClients_recorded_of_seen wellFormed contract timely 0
      assessment.strategy within priorMem player event owned
      ⟨entry, by rw [← recalled, pastEq]; exact member, activated⟩
    rw [← recalled, pastEq, unrecorded] at recorded
    cases recorded
  · simp [ReactiveApplication.observe, same] at observed

end Honest

section Law

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)
  [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

local notation "onePacketN" =>
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
private theorem apply_eq_one_of_subsingleton {α : Type} [Subsingleton α] (law : PMF α) (a : α) :
    law a = 1 := by
  rw [← law.tsum_coe, tsum_eq_single a (fun other different =>
    (different (Subsingleton.elim other a)).elim)]

/-- **Mixtures of one-packet components keep as-if-honest play away from late
deliveries.** At every forced information state that some history reaches and
that is not a late delivery, every mixture of the components of the one-packet
certificate gives each choice at least the slot retention of the scale times
its as-if-honest mass: its components are all the slot-trembled prescribed
component. -/
theorem onePacketMixture_ge_honest_of_not_late
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat} (n : ℕ)
    (weights : ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    {who : Player} {info : (application setup leaks).Info}
    (notLate : ¬ LateDelivery setup leaks who info)
    (occurs : ∃ history : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History, (onePacketN).infoOf who history.trace = info)
    (forced : forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
      scheduler who info)
    (choice : (onePacketN).Choice who info) :
    slotRetention (scale n) * ((honestProfile setup leaks bounds (initialLaw setup) horizon
        scheduler (sequence n) who info) choice).toReal ≤
      (((onePacketN).agentBehavior (onePacketN).playedInformation
        (onePacketFallback setup leaks bounds horizon scheduler)
        (fun agent => (weights (onePacketPool setup leaks bounds horizon scheduler agent)).bind
          (freeKeyedComponent
            (onePacketUnforced setup leaks bounds horizon scheduler scale scale_pos scale_le_one n)
            (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
              scale_le_one n)
            (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
              scale_le_one (slots := slots) n) agent)) who info) choice).toReal := by
  classical
  have retention_le_one := slotRetention_le_one (scale_pos n).le (scale_le_one n)
  by_cases present : info ∈ (onePacketN).playedInformation who
  · let agent : (onePacketN).InformationAgent (onePacketN).playedInformation :=
      ⟨who, ⟨info, present⟩⟩
    have notFree : ¬ UnforcedAgent setup leaks bounds horizon scheduler agent :=
      fun unforced => unforced forced
    have notKeyed : ¬ ownedKeyed (UnforcedAgent setup leaks bounds horizon scheduler)
        (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler) agent :=
      fun keyed => notLate keyed.1
    obtain ⟨identify, componentEq⟩ := freeKeyedComponent_of_not_free
      (key := agentLateKey setup leaks bounds (initialLaw setup) horizon scheduler)
      (onePacketUnforced setup leaks bounds horizon scheduler scale scale_pos scale_le_one n)
      (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one n)
      (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one (slots := slots) n) notFree
    have constant : ∀ part, freeKeyedComponent
        (onePacketUnforced setup leaks bounds horizon scheduler scale scale_pos scale_le_one n)
        (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one n)
        (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one (slots := slots) n) agent part =
        onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one n agent := fun part => by
      rw [componentEq]
      exact keyedComponent_of_not_keyed _ _ notKeyed _
    have atAgent := (onePacketN).agentBehavior_at (onePacketN).playedInformation
      (onePacketFallback setup leaks bounds horizon scheduler)
      (fun agent => (weights (onePacketPool setup leaks bounds horizon scheduler agent)).bind
        (freeKeyedComponent
          (onePacketUnforced setup leaks bounds horizon scheduler scale scale_pos scale_le_one n)
          (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one n)
          (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one (slots := slots) n) agent)) agent
    change _ ≤ (((onePacketN).agentBehavior _ _ _ agent.1 agent.2.1) choice).toReal
    have mixture : (weights (onePacketPool setup leaks bounds horizon scheduler agent)).bind
        (freeKeyedComponent
          (onePacketUnforced setup leaks bounds horizon scheduler scale scale_pos scale_le_one n)
          (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one n)
          (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one (slots := slots) n) agent) =
        onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one n agent := by
      rw [show freeKeyedComponent
          (onePacketUnforced setup leaks bounds horizon scheduler scale scale_pos scale_le_one n)
          (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one n)
          (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one (slots := slots) n) agent = fun _ =>
          onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one n agent from funext constant]
      exact PMF.bind_const _ _
    rw [atAgent]
    refine le_of_le_of_eq (slotTrembledChoice_ge_main setup leaks bounds (initialLaw setup) horizon
      scheduler (scale_pos n).le (scale_le_one n) who info
      (honestChoice setup leaks bounds (initialLaw setup) horizon scheduler (sequence n) who info)
      (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who info))
      (slotChoice setup leaks bounds (initialLaw setup) horizon scheduler (sequence n) who info)
      choice) ?_
    exact congrArg (fun law => (law choice).toReal) mixture.symm
  · have none : info = none := by
      obtain ⟨history, infoEq⟩ := occurs
      cases infoCase : info with
      | none => rfl
      | some observed =>
          exfalso
          apply present
          rw [← infoEq]
          apply (onePacketN).mem_playedInformation
          have active : (application setup leaks).observe who history.state = some observed :=
            ((bounds.onePacketMenu (runtime setup) leaks).info (initialLaw setup) horizon
              scheduler who history.trace).symm.trans (infoEq.trans infoCase)
          have isSome := ((application setup leaks).observe_isSome who history.state).mp
            (by rw [active]; rfl)
          intro stopped
          revert stopped isSome
          cases history.state with
          | none => exact fun _ stopped => stopped.elim
          | some control =>
              rintro actorSome ⟨_, actorNone⟩
              simp [ReactiveApplication.actor, actorNone] at actorSome
    subst none
    have : Subsingleton ((onePacketN).Choice who none) :=
      InformationModel.subsingleton_choice_of_menu_subsingleton _ _ Set.subsingleton_singleton
    rw [apply_eq_one_of_subsingleton _ choice, apply_eq_one_of_subsingleton _ choice,
      ENNReal.toReal_one, mul_one]
    exact retention_le_one

/-- **Mixtures of one-packet components keep as-if-honest play.** Under the
hypotheses of `Vegas.not_lateDelivery_of_honestReached`, at every forced
information state as-if-honest play reaches, every mixture of the components
of the one-packet certificate gives each choice at least the slot retention of
the scale times its as-if-honest mass: such a state is not a late delivery, so
its components are all the slot-trembled prescribed component. -/
theorem onePacketMixture_ge_honest (wellFormed : setup.WellFormed)
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (retains : RetainsCoveredCanonical setup leaks bounds horizon scheduler bound)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat} (n : ℕ)
    (weights : ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    {who : Player} {info : (application setup leaks).Info}
    (reachedInfo : HonestReached setup leaks bounds horizon scheduler (sequence n) who info)
    (forced : forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
      scheduler who info)
    (choice : (onePacketN).Choice who info) :
    slotRetention (scale n) * ((honestProfile setup leaks bounds (initialLaw setup) horizon
        scheduler (sequence n) who info) choice).toReal ≤
      (((onePacketN).agentBehavior (onePacketN).playedInformation
        (onePacketFallback setup leaks bounds horizon scheduler)
        (fun agent => (weights (onePacketPool setup leaks bounds horizon scheduler agent)).bind
          (freeKeyedComponent
            (onePacketUnforced setup leaks bounds horizon scheduler scale scale_pos scale_le_one n)
            (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
              scale_le_one n)
            (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
              scale_le_one (slots := slots) n) agent)) who info) choice).toReal :=
  onePacketMixture_ge_honest_of_not_late setup leaks bounds horizon scheduler sequence scale
    scale_pos scale_le_one n weights
    (not_lateDelivery_of_honestReached bounds wellFormed contract timely (sequence n) retains
      reachedInfo)
    (by
      obtain ⟨_, history, _, infoEq⟩ := reachedInfo
      exact ⟨history, infoEq⟩)
    forced choice

/-- **The law approximation of the one-packet certificate.** For a
well-formed setup, under the asynchronous contract with timely delays and
retention of first covered canonical packets, along vanishing tremble scales in
`(0, 1]`, every sequence of profiles assembled from mixtures of the components
of the one-packet certificate has a joint law of typed readout and exclusion
payoff within a vanishing error of the intended joint law under the source
sequence. -/
theorem onePacket_certificate_lawApproximation (wellFormed : setup.WellFormed)
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (retains : RetainsCoveredCanonical setup leaks bounds horizon scheduler bound)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    (scale_vanishing : Tendsto scale atTop (nhds 0)) {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : ∀ n, (targetSequence n).strategy = (onePacketN).agentBehavior
      (onePacketN).playedInformation (onePacketFallback setup leaks bounds horizon scheduler)
      fun agent => (weights n (onePacketPool setup leaks bounds horizon scheduler agent)).bind
        (freeKeyedComponent
          (onePacketUnforced setup leaks bounds horizon scheduler scale scale_pos scale_le_one n)
          (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one n)
          (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one (slots := slots) n) agent)) :
    ∃ lawError : ℕ → ℝ, Tendsto lawError atTop (nhds 0) ∧
      ∀ n outcome,
        |((((onePacketN).runBehavioral (targetSequence n).strategy (2 * horizon + 1)).map
            (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter
              utility excludedPayoff)) outcome).toReal -
          (((setup.intendedModel.runBehavioral (sequence n).strategy
            (instructionCount setup.program + 1)).map
            (intendedReadoutExclusion setup parameter utility excludedPayoff))
            outcome).toReal| ≤ lawError n :=
  onePacket_exclusion_lawApproximation bounds wellFormed contract timely retains parameter utility
    excludedPayoff sequence (fun n => slotRetention (scale n))
    (fun n => slotRetention_nonneg (scale_pos n).le (scale_le_one n))
    (fun n => slotRetention_le_one (scale_pos n).le (scale_le_one n))
    (tendsto_slotRetention scale_vanishing) (fun n => (targetSequence n).strategy)
    fun n who info reachedInfo forced choice => by
      rw [assembled n]
      exact onePacketMixture_ge_honest setup leaks bounds horizon scheduler wellFormed contract
        timely retains sequence scale scale_pos scale_le_one n (weights n) reachedInfo forced
        choice

end Law

section Open

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)
  [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

local notation "onePacketN" =>
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

/-- **The failure set of an agent of the one-packet game**: the event-level
failed histories of its pending event, and none without one. -/
def onePacketFailed (agent : (onePacketN).InformationAgent (onePacketN).playedInformation) :
    Set ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History :=
  match pendingEvent setup leaks agent.1 agent.2.1 with
  | none => ∅
  | some event => EventFailedHistory setup leaks bounds horizon scheduler agent.1 event

omit [Finite setup.intendedProtocol.History] in
/-- Failure of an agent's pending event pays exactly its exclusion payoff. -/
theorem onePacketFailed_pays
    (agent : (onePacketN).InformationAgent (onePacketN).playedInformation) :
    ∀ history ∈ onePacketFailed setup leaks bounds horizon scheduler agent,
      payoffComponent setup (readoutExclusion setup leaks bounds (initialLaw setup) horizon
        scheduler parameter utility excludedPayoff history) agent.1 = excludedPayoff agent.1 := by
  intro history member
  unfold onePacketFailed at member
  split at member
  · exact member.elim
  · exact exclusionReadoutUtility_of_eventFailedHistory bounds horizon scheduler parameter
      utility excludedPayoff agent.1 _ history member

open Classical in
/-- **The open inputs of the one-packet certificate** for one source sequence:
the tremble scales and the obligations not yet discharged, named after their
mathematical content. The failure set of each agent is the event-level failure
of its pending event (`Vegas.onePacketFailed`). -/
structure OnePacketOpenInputs (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (slots : Nat) where
  /-- The tremble scale at each index. -/
  scale : ℕ → ℝ
  scale_pos : ∀ n, 0 < scale n
  scale_le_one : ∀ n, scale n ≤ 1
  scale_vanishing : Tendsto scale atTop (nhds 0)
  /-- A bound on the gap between a continuation value and the exclusion payoff. -/
  gapBound : ℝ
  gapBound_nonneg : 0 ≤ gapBound
  /-- The marked choices of each site. -/
  compared : ∀ who (site : (onePacketN).InformationSite who), (onePacketN).Choice who site.1 → Prop
  /-- **The one-dimensional decomposition of late delivery, with its value
  bounds and site-level commonness.** At every forced late-delivery decision
  site, failure pays the exclusion payoff at most the site's continuation value
  up to a vanishing error with gap at most the gap bound, the successful part of
  each late option is its success probability times that continuation value up
  to the error, and each option fails, belief-averaged, within a vanishing drift
  of one minus its score at the site's late-delivery key. -/
  decomposition : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler
      slots p))
          (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
        (∀ n, (targetSequence n).strategy = (onePacketN).agentBehavior
            (onePacketN).playedInformation (onePacketFallback setup leaks bounds horizon scheduler)
          fun agent => (weights n (onePacketPool setup leaks bounds horizon scheduler agent)).bind
            (freeKeyedComponent ((onePacketUnforced setup leaks bounds horizon scheduler scale
                scale_pos
            scale_le_one) n) ((onePacketPrescribed setup leaks bounds horizon scheduler sequence
                scale
            scale_pos scale_le_one) n) ((onePacketLate setup leaks bounds horizon scheduler
                sequence scale scale_pos
            scale_le_one (slots := slots)) n) agent)) →
        (∀ n, (targetSequence n).IsFullyMixed) →
        (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
          ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
            (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
        ∃ (continuation : ℕ → (onePacketN).InformationAgent (onePacketN).playedInformation → ℝ)
          (score : ℕ → Option (LateKey setup leaks) → LateOption slots → ℝ) (error drift : ℕ → ℝ),
          Tendsto error atTop (nhds 0) ∧ Tendsto drift atTop (nhds 0) ∧ (∀ n, 0 ≤ drift n) ∧
          ∀ n (agent : (onePacketN).InformationAgent (onePacketN).playedInformation), ownedKeyed
              (UnforcedAgent setup leaks bounds horizon scheduler)
              (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler) agent →
            ∀ decision : (onePacketN).IsDecisionInfo agent.1 agent.2.1,
            excludedPayoff agent.1 ≤ continuation n agent + error n ∧
            continuation n agent - excludedPayoff agent.1 ≤ gapBound ∧
            (∀ option, |localSuccessValue (2 * horizon + 1) (readoutExclusion setup leaks bounds
                (initialLaw setup) horizon
            scheduler parameter utility excludedPayoff) (payoffComponent setup) (targetSequence n)
                (who := agent.1) ⟨agent.2.1, decision⟩ (onePacketFailed setup leaks bounds horizon
                    scheduler agent) ((onePacketLate setup leaks
                    bounds horizon scheduler sequence scale scale_pos
            scale_le_one (slots := slots)) n agent option) -
              (1 - localFailure (2 * horizon + 1) (targetSequence n) (who := agent.1) ⟨agent.2.1,
                  decision⟩
                (onePacketFailed setup leaks bounds horizon scheduler agent) ((onePacketLate setup
                    leaks bounds horizon scheduler sequence scale
                    scale_pos
            scale_le_one (slots := slots)) n agent option)) * continuation n agent| ≤ error n) ∧
            ∀ option, |localFailure (2 * horizon + 1) (targetSequence n) (who := agent.1)
                ⟨agent.2.1, decision⟩
                (onePacketFailed setup leaks bounds horizon scheduler agent) ((onePacketLate setup
                    leaks bounds horizon scheduler sequence scale
                    scale_pos
            scale_le_one (slots := slots)) n agent option) - (1 - score n (agentLateKey setup leaks
                bounds (initialLaw setup) horizon scheduler agent) option)| ≤
              drift n
  /-- **The ranking of marked choices.** At every forced site, each marked
  choice decomposes the same way; at a late delivery it fails within the drift
  of one minus the score of some option, or surely; at a first activation the
  prescribed component fails at most as often up to a vanishing slack, or the
  choice fails surely. -/
  ranking : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
          (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
        (∀ n, (targetSequence n).strategy = (onePacketN).agentBehavior
            (onePacketN).playedInformation (onePacketFallback setup leaks bounds horizon scheduler)
          fun agent => (weights n (onePacketPool setup leaks bounds horizon scheduler agent)).bind
            (freeKeyedComponent ((onePacketUnforced setup leaks bounds horizon scheduler scale
                scale_pos
            scale_le_one) n) ((onePacketPrescribed setup leaks bounds horizon scheduler sequence
                scale
            scale_pos scale_le_one) n) ((onePacketLate setup leaks bounds horizon scheduler
                sequence scale scale_pos
            scale_le_one (slots := slots)) n) agent)) →
        (∀ n, (targetSequence n).IsFullyMixed) →
        (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
          ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
            (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
        ∃ (continuation : ℕ → (onePacketN).InformationAgent (onePacketN).playedInformation → ℝ)
          (score : ℕ → Option (LateKey setup leaks) → LateOption slots → ℝ) (error drift slack : ℕ
              → ℝ),
          Tendsto error atTop (nhds 0) ∧ Tendsto drift atTop (nhds 0) ∧
          Tendsto slack atTop (nhds 0) ∧ (∀ n, 0 ≤ drift n) ∧ (∀ n, 0 ≤ slack n) ∧
          ∀ n who (site : (onePacketN).InformationSite who) (choice : (onePacketN).Choice who
              site.1),
            ¬ UnforcedAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
                compared who site choice →
            excludedPayoff who ≤ continuation n ((onePacketN).agentAt site) + error n ∧
            continuation n ((onePacketN).agentAt site) - excludedPayoff who ≤ gapBound ∧
            |localSuccessValue (2 * horizon + 1) (readoutExclusion setup leaks bounds (initialLaw
                setup) horizon
            scheduler parameter utility excludedPayoff) (payoffComponent setup) (targetSequence n)
                site (onePacketFailed setup leaks bounds horizon scheduler ((onePacketN).agentAt
                    site))
                (PMF.pure choice) -
              (1 - localFailure (2 * horizon + 1) (targetSequence n) site
                (onePacketFailed setup leaks bounds horizon scheduler ((onePacketN).agentAt site))
                    (PMF.pure choice)) *
                continuation n ((onePacketN).agentAt site)| ≤ error n ∧
            (ownedKeyed (UnforcedAgent setup leaks bounds horizon scheduler)
              (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
                  ((onePacketN).agentAt site) →
              (∀ option, |localSuccessValue (2 * horizon + 1) (readoutExclusion setup leaks bounds
                  (initialLaw setup) horizon
            scheduler parameter utility excludedPayoff) (payoffComponent setup) (targetSequence n)
                site
                  (onePacketFailed setup leaks bounds horizon scheduler ((onePacketN).agentAt
                      site)) ((onePacketLate setup leaks bounds horizon
                      scheduler sequence scale scale_pos
            scale_le_one (slots := slots)) n ((onePacketN).agentAt site) option) -
                (1 - localFailure (2 * horizon + 1) (targetSequence n) site (onePacketFailed setup
                    leaks bounds horizon scheduler ((onePacketN).agentAt site))
                  ((onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one (slots := slots)) n ((onePacketN).agentAt site) option)) * continuation n
                ((onePacketN).agentAt site)| ≤
                error n) ∧
              (∀ option, |localFailure (2 * horizon + 1) (targetSequence n) site (onePacketFailed
                  setup leaks bounds horizon scheduler ((onePacketN).agentAt site))
                  ((onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one (slots := slots)) n ((onePacketN).agentAt site) option) -
                (1 - score n (agentLateKey setup leaks bounds (initialLaw setup) horizon scheduler
              ((onePacketN).agentAt site)) option)| ≤ drift n) ∧
              ((∃ option, |localFailure (2 * horizon + 1) (targetSequence n) site (onePacketFailed
                  setup leaks bounds horizon scheduler ((onePacketN).agentAt site))
                  (PMF.pure choice) - (1 - score n (agentLateKey setup leaks bounds (initialLaw
                      setup) horizon scheduler
              ((onePacketN).agentAt site)) option)| ≤ drift n) ∨
                localFailure (2 * horizon + 1) (targetSequence n) site
                  (onePacketFailed setup leaks bounds horizon scheduler ((onePacketN).agentAt
                      site)) (PMF.pure choice) = 1)) ∧
            (¬ ownedKeyed (UnforcedAgent setup leaks bounds horizon scheduler)
              (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
                  ((onePacketN).agentAt site) →
              |localSuccessValue (2 * horizon + 1) (readoutExclusion setup leaks bounds (initialLaw
                  setup) horizon
            scheduler parameter utility excludedPayoff) (payoffComponent setup) (targetSequence n)
                site
                (onePacketFailed setup leaks bounds horizon scheduler ((onePacketN).agentAt site))
                  ((onePacketPrescribed setup leaks bounds horizon scheduler sequence scale
            scale_pos scale_le_one) n ((onePacketN).agentAt site)) -
                (1 - localFailure (2 * horizon + 1) (targetSequence n) site (onePacketFailed setup
                    leaks bounds horizon scheduler ((onePacketN).agentAt site))
                  ((onePacketPrescribed setup leaks bounds horizon scheduler sequence scale
            scale_pos scale_le_one) n ((onePacketN).agentAt site))) * continuation n
                ((onePacketN).agentAt site)| ≤ error n ∧
              (localFailure (2 * horizon + 1) (targetSequence n) site (onePacketFailed setup leaks
                  bounds horizon scheduler ((onePacketN).agentAt site))
                  ((onePacketPrescribed setup leaks bounds horizon scheduler sequence scale
            scale_pos scale_le_one) n ((onePacketN).agentAt site)) ≤
                localFailure (2 * horizon + 1) (targetSequence n) site
                  (onePacketFailed setup leaks bounds horizon scheduler ((onePacketN).agentAt
                      site)) (PMF.pure choice) + slack n ∨
                localFailure (2 * horizon + 1) (targetSequence n) site
                  (onePacketFailed setup leaks bounds horizon scheduler ((onePacketN).agentAt
                      site)) (PMF.pure choice) = 1))
  /-- **The comparisons of unmarked choices.** Every unmarked choice at a forced
  site meets one of the three local comparisons of a pooled limit certificate
  on its own: values outside the intended menu, bad bindings, charged packets. -/
  otherComparisons : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler
      slots p))
          (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
        (∀ n, (targetSequence n).strategy = (onePacketN).agentBehavior
            (onePacketN).playedInformation (onePacketFallback setup leaks bounds horizon scheduler)
          fun agent => (weights n (onePacketPool setup leaks bounds horizon scheduler agent)).bind
            (freeKeyedComponent ((onePacketUnforced setup leaks bounds horizon scheduler scale
                scale_pos
            scale_le_one) n) ((onePacketPrescribed setup leaks bounds horizon scheduler sequence
                scale
            scale_pos scale_le_one) n) ((onePacketLate setup leaks bounds horizon scheduler
                sequence scale scale_pos
            scale_le_one (slots := slots)) n) agent)) →
        (∀ n, (targetSequence n).IsFullyMixed) →
        (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
          ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
            (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
        (∀ n (alternative : ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
            p,
          ∑ agent ∈ Finset.univ.filter (fun agent => onePacketPool setup leaks bounds horizon
              scheduler agent = p),
            (if decision : (onePacketN).IsDecisionInfo agent.1 agent.2.1 then
              let comparison := (onePacketN).assessmentComparisonWith ((onePacketN).truncatedRunner
                  (2 * horizon + 1))
                (readoutExclusion setup leaks bounds (initialLaw setup) horizon
            scheduler parameter utility excludedPayoff) (targetSequence n) agent.1
                (⟨agent.2.1, decision⟩, ((targetSequence n).strategy agent.1).withLaw agent.2.1
                  ((alternative (onePacketPool setup leaks bounds horizon scheduler agent)).bind
                    (freeKeyedComponent ((onePacketUnforced setup leaks bounds horizon scheduler
                        scale scale_pos
            scale_le_one) n) ((onePacketPrescribed setup leaks bounds horizon scheduler sequence
                scale
            scale_pos scale_le_one) n) ((onePacketLate setup leaks bounds horizon scheduler
                sequence scale scale_pos
            scale_le_one (slots := slots)) n) agent)))
              expect comparison.alternative ((payoffComponent setup) · agent.1) -
                expect comparison.prescribed ((payoffComponent setup) · agent.1)
            else 0) ≤ 0) →
        ∃ otherError : ℕ → ℝ, Tendsto otherError atTop (nhds 0) ∧
          ∀ n who (site : (onePacketN).InformationSite who), (onePacketN).agentAt site ∉
              Finset.univ.filter (UnforcedAgent setup leaks bounds horizon scheduler) →
            ∀ choice : (onePacketN).Choice who site.1, ¬ compared who site choice →
            let gain := fun law : PMF ((onePacketN).Choice who site.1) =>
              let comparison := (onePacketN).assessmentComparisonWith ((onePacketN).truncatedRunner
                  (2 * horizon + 1)) (readoutExclusion setup leaks bounds (initialLaw setup) horizon
            scheduler parameter utility excludedPayoff) (targetSequence n)
                who (site, ((targetSequence n).strategy who).withLaw site.1 law)
              expect comparison.alternative ((payoffComponent setup) · who) -
                expect comparison.prescribed ((payoffComponent setup) · who)
            gain (PMF.pure choice) ≤ otherError n ∨
              (∃ alternative : PMF (OnePacketPart setup leaks bounds horizon scheduler slots
                  (onePacketPool setup leaks bounds horizon scheduler ((onePacketN).agentAt site))),
                gain (PMF.pure choice) ≤
                  gain (alternative.bind (freeKeyedComponent ((onePacketUnforced setup leaks bounds
                      horizon scheduler scale scale_pos
            scale_le_one) n) ((onePacketPrescribed setup leaks bounds horizon scheduler sequence
                scale
            scale_pos scale_le_one) n) ((onePacketLate setup leaks bounds horizon scheduler
                sequence scale scale_pos
            scale_le_one (slots := slots)) n)
                    ((onePacketN).agentAt site))) + otherError n) ∨
              ∃ mixture : PMF (setup.intendedModel.AssessmentDeviation who),
                gain (PMF.pure choice) ≤
                  expect mixture (fun deviation =>
                    let sourceComparison := setup.intendedModel.assessmentComparisonWith
                        (setup.intendedModel.truncatedRunner
                        (instructionCount setup.program + 1)) (intendedReadoutExclusion setup
                            parameter utility excludedPayoff)
                      (sequence n) who deviation
                    expect sourceComparison.alternative ((payoffComponent setup) · who) -
                      expect sourceComparison.prescribed ((payoffComponent setup) · who)) +
                          otherError n

/-- **The certificate inputs from the open inputs.** For a well-formed setup,
under the asynchronous contract with timely delays and retention of first
covered canonical packets, the open inputs give the inputs of the one-packet
certificate: the failure sets are the event-level failures of pending events,
and the law approximation holds. -/
def OnePacketOpenInputs.toCertificateInputs
    {sequence : ℕ → setup.intendedModel.BehavioralAssessment} {slots : Nat}
    (inputs : OnePacketOpenInputs setup leaks bounds horizon scheduler parameter utility
      excludedPayoff sequence slots)
    (wellFormed : setup.WellFormed) {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (retains : RetainsCoveredCanonical setup leaks bounds horizon scheduler bound) :
    OnePacketCertificateInputs setup leaks bounds horizon scheduler parameter utility
      excludedPayoff sequence slots where
  scale := inputs.scale
  scale_pos := inputs.scale_pos
  scale_le_one := inputs.scale_le_one
  scale_vanishing := inputs.scale_vanishing
  failed := onePacketFailed setup leaks bounds horizon scheduler
  failed_pays := onePacketFailed_pays setup leaks bounds horizon scheduler parameter utility
    excludedPayoff
  gapBound := inputs.gapBound
  gapBound_nonneg := inputs.gapBound_nonneg
  compared := inputs.compared
  decomposition := inputs.decomposition
  ranking := inputs.ranking
  otherComparisons := inputs.otherComparisons
  lawApproximation weights targetSequence assembled _ _ _ :=
    onePacket_certificate_lawApproximation setup leaks bounds horizon scheduler wellFormed
      contract timely retains parameter utility excludedPayoff sequence inputs.scale
      inputs.scale_pos inputs.scale_le_one inputs.scale_vanishing weights targetSequence assembled

/-- **Sequential equilibrium of the one-packet game from the open inputs.** For
a well-formed setup, under the asynchronous contract with timely delays and
retention of first covered canonical packets, for every sequential equilibrium
of the intended game, if every fully mixed Bayes sequence converging to it
supplies the open inputs, there is a sequential equilibrium of the one-packet
game under the exclusion payoff whose joint law of typed readout and exclusion
payoff is the intended one. -/
theorem onePacket_intended_sequentialEquilibrium_of_openInputs (wellFormed : setup.WellFormed)
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (retains : RetainsCoveredCanonical setup leaks bounds horizon scheduler bound)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : intended.IsSequentialEquilibrium setup.intended_decision_antichain
      setup.intended_bounded.wellFoundedHistories
      (fun who final => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who)))
    {slots : Nat}
    (inputs : ∀ sequence : ℕ → setup.intendedModel.BehavioralAssessment,
      (∀ n, (sequence n).IsFullyMixed) →
      (∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent setup.intendedModel
        (sequence n) setup.intended_decision_antichain) →
      InformationModel.BehavioralAssessmentConvergesPointwise sequence intended →
      OnePacketOpenInputs setup leaks bounds horizon scheduler parameter utility
        excludedPayoff sequence slots) :
    ∃ target : (onePacketModel setup leaks bounds (initialLaw setup) horizon
        scheduler).BehavioralAssessment,
      target.IsSequentialEquilibrium
        ((bounds.onePacketMenu (runtime setup) leaks).decisionInformationAntichain
          (initialLaw setup) horizon scheduler)
        ((bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup) horizon
          scheduler).wellFoundedHistories
        (fun who final => exclusionBase setup parameter utility excludedPayoff leaks final.state
          who) ∧
      ((onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).runBehavioral
          target.strategy (2 * horizon + 1)).map
          (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter
            utility excludedPayoff) =
        (setup.intendedModel.runBehavioral intended.strategy
          (instructionCount setup.program + 1)).map
          (intendedReadoutExclusion setup parameter utility excludedPayoff) :=
  onePacket_intended_sequentialEquilibrium_of_inputs setup leaks bounds horizon scheduler
    parameter utility excludedPayoff wellFormed intended equilibrium
    fun sequence mixed bayes converges =>
      (inputs sequence mixed bayes converges).toCertificateInputs setup leaks bounds horizon
        scheduler parameter utility excludedPayoff wellFormed contract timely retains

/-- **Sequential equilibrium of the bounded raw runtime from the open inputs.**
Under the hypotheses of
`Vegas.onePacket_intended_sequentialEquilibrium_of_openInputs`, bounds on the
utility, and a count-evidence service with a deposit covering the spread of the
exclusion payoff, there is a sequential equilibrium of the bounded raw runtime
under the exclusion payoff minus the deposit for each collected count charge,
that charges nobody on its paths, whose joint law of typed readout and realized
payoffs is the intended joint law of typed readout and exclusion payoff. -/
theorem onePacket_intended_raw_sequentialEquilibrium_of_openInputs
    (wellFormed : setup.WellFormed) {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (retains : RetainsCoveredCanonical setup leaks bounds horizon scheduler bound)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : intended.IsSequentialEquilibrium setup.intended_decision_antichain
      setup.intended_bounded.wellFoundedHistories
      (fun who final => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who)))
    {slots : Nat}
    (inputs : ∀ sequence : ℕ → setup.intendedModel.BehavioralAssessment,
      (∀ n, (sequence n).IsFullyMixed) →
      (∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent setup.intendedModel
        (sequence n) setup.intended_decision_antichain) →
      InformationModel.BehavioralAssessmentConvergesPointwise sequence intended →
      OnePacketOpenInputs setup leaks bounds horizon scheduler parameter utility
        excludedPayoff sequence slots)
    (service : EvidenceReportService (CountEvidence (graph setup)))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : CountEvidenceCoverage service observationRate deliveryRate)
    (lowerUtility upperUtility : Player → ℝ)
    (lower_le : ∀ outcome who, lowerUtility who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upperUtility who)
    (deposit : Player → ℝ) (deposit_nonnegative : ∀ who, 0 ≤ deposit who)
    (sufficient : ∀ who,
      max 0 (max (excludedPayoff who) (upperUtility who)) -
          min 0 (min (excludedPayoff who) (lowerUtility who)) ≤
        observationRate who * deliveryRate who * deposit who) :
    let raw := bounds.rawMenu (runtime setup) leaks
    let observe := (application setup leaks).stateTraffic
    let audit := (runtime setup).countAudit leaks service.sample
    let base := exclusionBase setup parameter utility excludedPayoff leaks
    let payoff := TerminalAudit.utility base observe audit deposit
    let settle := TerminalAudit.settlement base observe audit deposit
    ∃ target : (raw.information (initialLaw setup) horizon scheduler).BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        (raw.decisionInformationAntichain (initialLaw setup) horizon scheduler)
        (fun who site => target.truncatedContinuationContext site
          (fun history => payoff history.state who) (2 * horizon + 1)) ∧
      (∀ final ∈ ((raw.information (initialLaw setup) horizon scheduler).runBehavioral
          target.strategy (2 * horizon + 1)).support,
        ∀ who, TerminalAudit.charge observe audit final.state who = 0) ∧
      ((raw.information (initialLaw setup) horizon scheduler).runBehavioral target.strategy
          (2 * horizon + 1)).bind
          (fun final => (settle final.state).map fun payoffs =>
            (sourceReadout setup leaks final.state, payoffs)) =
        (setup.intendedModel.runBehavioral intended.strategy
          (instructionCount setup.program + 1)).map
          (intendedReadoutExclusion setup parameter utility excludedPayoff) :=
  onePacket_intended_raw_sequentialEquilibrium_of_inputs setup leaks bounds horizon scheduler
    parameter utility excludedPayoff wellFormed intended equilibrium
    (fun sequence mixed bayes converges =>
      (inputs sequence mixed bayes converges).toCertificateInputs setup leaks bounds horizon
        scheduler parameter utility excludedPayoff wellFormed contract timely retains)
    service observationRate deliveryRate delivery_nonnegative coverage lowerUtility upperUtility
    lower_le le_upper deposit deposit_nonnegative sufficient

end Open

end Vegas
