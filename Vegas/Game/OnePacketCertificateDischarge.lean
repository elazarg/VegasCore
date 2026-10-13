/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketSequentialPreservation
import Vegas.Game.OnePacketSlotLaw
import Interaction.ReactiveSupportedRounds

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
              scale_le_one (slots := slots) n) agent)) who info) choice).toReal := by
  classical
  have notLate := not_lateDelivery_of_honestReached bounds wellFormed contract timely
    (sequence n) retains reachedInfo
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
      obtain ⟨fuel, history, _, infoEq⟩ := reachedInfo
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

end Vegas
