/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketSequentialPreservation
import Vegas.Game.OnePacketSlotLaw
import Interaction.ReactiveSupportedRounds
import Vegas.Game.OnePacketEventSuccess
import Vegas.Game.OnePacketSourceTurn
import Vegas.Game.OnePacketBindingSite
import Vegas.Game.OnePacketSureFailure

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

section Transmits

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A source action other than withholding encodes, at a publication event, to
disclosure. -/
theorem encodeEventAction?_discloses :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (event : Fin (eventCount program)) →
    (action : OwnAction Player L) → (∀ owner name, action ≠ .reveal owner name false) →
    ∀ encoded, encodeEventAction? program event action = some encoded →
    ∀ payload (publication : outputLayout program event = .publication payload),
      cast (congrArg EventGraph.EventField.Action publication) encoded = true
  | _, _, .ret _, event, _, _, _, _ => nomatch event
  | _, _, .sample name fresh law next, event, action, discloses, encoded, encodes => by
      cases event using Fin.cases with
      | zero => cases encodes
      | succ tail =>
          exact encodeEventAction?_discloses next tail action discloses encoded encodes
  | _, _, .commit name owner fresh guard next, event, action, discloses, encoded, encodes => by
      cases event using Fin.cases with
      | zero =>
          intro _ publication
          cases publication
      | succ tail =>
          exact encodeEventAction?_discloses next tail action discloses encoded encodes
  | _, _, .reveal published owner name fresh selected unresolved next, event, action, discloses,
      encoded, encodes => by
      cases event using Fin.cases with
      | zero =>
          intro _ publication
          cases action with
          | commit => cases encodes
          | reveal actionOwner actionName disclose =>
              simp only [encodeEventAction?, Fin.cases_zero] at encodes
              split_ifs at encodes with ownerEq nameEq
              cases encodes
              cases publication
              revert encoded
              change ∀ value : Bool, (∀ owner name, OwnAction.reveal actionOwner actionName value ≠
                .reveal owner name false) → value = true
              intro value discloses
              cases value
              · exact (discloses actionOwner actionName rfl).elim
              · rfl
      | succ tail =>
          exact encodeEventAction?_discloses next tail action discloses encoded encodes

end Transmits

section FirstActivation

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
private theorem commitsValue_of_success {action : OwnAction Player L}
    (success : ∀ owner name payload, action ≠ .commit owner name payload .failure) :
    action.CommitsValue := by
  cases action with
  | commit owner name payload choice =>
      cases choice with
      | failure => exact (success owner name payload rfl).elim
      | success value => exact ⟨value, rfl⟩
  | reveal => trivial

omit [Fintype Player] in
private theorem effectiveDecision_of_encode {event : (graph setup).EventId}
    {action : OwnAction Player L} {graphAction : (graph setup).Action event}
    (encoded : encodeEventAction? setup.program event action = some graphAction)
    (commits : action.CommitsValue) : EffectiveDecision event graphAction := by
  unfold EffectiveDecision
  cases node : nodeView (graph setup) event with
  | bind owner payload outputEq codeEq =>
      exact encodeEventAction?_commitsValue setup.program event action commits graphAction
        encoded owner payload outputEq
  | resolve => trivial
  | sample => trivial

omit [Fintype Player] in
private theorem bindSuccess_of_effective {event : (graph setup).EventId}
    {action : (graph setup).Action event} (effective : EffectiveDecision event action) :
    ∀ owner payload outputEq codeEq,
      nodeView (graph setup) event = .bind owner payload outputEq codeEq →
        ∃ value, (cast (congrArg EventGraph.EventField.Action outputEq) action :
          PublicationResult (L.Val payload)) = .success value := by
  intro owner payload outputEq codeEq node
  unfold EffectiveDecision at effective
  rw [node] at effective
  obtain ⟨value, rfl⟩ := effective
  exact ⟨value, by simp⟩

/-- **Transmitting first activations.** At a forced first activation for
`event` with recall `past` and view `view`, the canonical decision of every
source action encoding at the event, committing no failure and disclosing,
transmits. -/
def CanonicalTransmitsAt (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId) : Prop :=
  ∀ action graphAction, encodeEventAction? setup.program event action = some graphAction →
    (∀ owner name payload, action ≠ .commit owner name payload .failure) →
    (∀ owner name, action ≠ .reveal owner name false) →
    ((runtime setup).canonicalServiceDecision leaks who past view event graphAction).transmission ≠
      none

open Classical in
/-- **As-if-honest play never fails a transmitting first activation.** Under
the asynchronous contract with timely delays and retention of first covered
canonical packets, at a forced site of `who` that is a first activation for
`event` and at which the canonical decisions of as-if-honest play transmit,
as-if-honest play has event-level failure zero for `event`, for every
assessment and every player. -/
theorem honestChoice_localFailure_eq_zero
    [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)]
    [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History]
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (retains : RetainsCoveredCanonical setup leaks bounds horizon scheduler bound)
    (source : setup.intendedModel.BehavioralAssessment)
    (assessment : (onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).BehavioralAssessment)
    {who : Player} (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId)
    (decision : (onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).IsDecisionInfo who (some (past, view)))
    (forced : forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
      scheduler who (some (past, view)))
    (pending : pendingEvent setup leaks who (some (past, view)) = some event)
    (never : ∀ entry ∈ past, ¬ ActivatedAt setup leaks who event entry)
    (transmits : CanonicalTransmitsAt setup leaks who past view event) (player : Player) :
    InformationModel.localFailure (2 * horizon + 1) assessment ⟨some (past, view), decision⟩
      (EventFailedHistory setup leaks bounds horizon scheduler player event)
      (honestChoice setup leaks bounds (initialLaw setup) horizon scheduler source who
        (some (past, view))) = 0 := by
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler
  let site : model.InformationSite who := ⟨some (past, view), decision⟩
  let := Fintype.ofFinite (menu.protocol (initialLaw setup) horizon scheduler).History
  obtain ⟨turn, _, _, unrecorded⟩ := pendingEvent_spec pending
  obtain ⟨history, infoEq, forcedState⟩ := forced
  have observed : (application setup leaks).observe who history.state = some (past, view) :=
    (menu.info (initialLaw setup) horizon scheduler who history.trace).symm.trans infoEq
  have menuTrace := history.trace
  generalize history.state = state at observed forcedState menuTrace
  rcases state with _ | ⟨remaining, actor, execution⟩
  · exact forcedState.elim
  by_cases active : actor = some who
  swap
  · simp [ReactiveApplication.observe, active] at observed
  subst active
  simp only [ReactiveApplication.observe, ↓reduceIte, Option.some.injEq, Prod.mk.injEq]
    at observed
  obtain ⟨pastEq, viewEq⟩ := observed
  subst pastEq
  subst viewEq
  obtain ⟨rank, point, ordered, decoded, _⟩ := forcedState
  have turnExec : execution.application.publicView.ownTurn? who = some event := turn
  have fits := firstActivation_inclusionFits contract timely
    (menu.toRawTrace (initialLaw setup) horizon scheduler menuTrace) rfl event turnExec never
  have zero : ∀ choice ∈ (honestChoice setup leaks bounds (initialLaw setup) horizon scheduler
      source who (some (execution.recall who,
        execution.observe (application setup leaks) who))).support,
      InformationModel.localFailure (2 * horizon + 1) assessment site
        (EventFailedHistory setup leaks bounds horizon scheduler player event)
        (PMF.pure choice) = 0 := by
    intro choice supported
    obtain ⟨response, responded, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    have responded' := responded
    unfold honestResponse at responded'
    rw [turn] at responded'
    obtain ⟨sourceChoice, chosen, responseEq⟩ := (PMF.mem_support_map_iff _ _ _).mp responded'
    have encodes := asIfHonestProfile_encodes source who execution rank ordered point
      decoded (execution.recall who) event turnExec sourceChoice chosen
    rcases sourceChoice with _ | action
    · simp at encodes
    cases encoded : encodeEventAction? setup.program event action with
    | none => simp [encoded] at encodes
    | some graphAction =>
        have success := asIfHonestProfile_success source who execution rank ordered
          point decoded (execution.recall who) action chosen
        have sends := transmits action graphAction encoded success.1 success.2
        obtain ⟨material, submits⟩ := Option.ne_none_iff_exists'.mp sends
        have effective := effectiveDecision_of_encode setup encoded
          (commitsValue_of_success success.1)
        have member := canonical_mem_onePacket_of_pending bounds menuTrace who event turnExec
          unrecorded graphAction
          (retains menuTrace who event graphAction turnExec unrecorded fits effective sends)
        simp only [Option.bind_some, encoded] at responseEq
        subst responseEq
        have selected : (responseChoice setup leaks bounds (initialLaw setup) horizon scheduler who
            (some (execution.recall who, execution.observe (application setup leaks) who))
            ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
              (execution.observe (application setup leaks) who) event graphAction)).1 =
            some ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
              (execution.observe (application setup leaks) who) event graphAction) := by
          unfold responseChoice
          simp only [member, ↓reduceDIte]
        convert firstActivation_localFailure_eq_zero bounds horizon scheduler contract timely
          assessment site (execution.recall who) (execution.observe (application setup leaks) who)
          rfl event turn never graphAction material submits
          (bindSuccess_of_effective setup effective) _ selected player
  have finiteChoice : Finite (model.Choice who site.1) :=
    model.finite_choice_of_played (model.site_mem_playedInformation site)
  have bounded := menu.bounded (initialLaw setup) horizon scheduler
  have actsOnce := (menu.decisionRecall (initialLaw setup) horizon
    scheduler).actsOnceWhereItMatters
  change InformationModel.localFailure (2 * horizon + 1) assessment site _ _ = 0
  rw [← PMF.bind_pure (honestChoice setup leaks bounds (initialLaw setup) horizon scheduler
    source who _), InformationModel.localFailure_bind (2 * horizon + 1) assessment site bounded
    actsOnce]
  exact (expect_congr_on_support (g := fun _ => 0) zero).trans (expect_constant _ _)

end FirstActivation

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

/-- Profiles assembled from mixtures of the components of the one-packet
certificate: at each index, every agent mixes its pool's components with the
pool's weights. -/
def OnePacketAssembled (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment) : Prop :=
  ∀ n, (targetSequence n).strategy = (onePacketN).agentBehavior (onePacketN).playedInformation
    (onePacketFallback setup leaks bounds horizon scheduler)
    fun agent => (weights n (onePacketPool setup leaks bounds horizon scheduler agent)).bind
      (freeKeyedComponent
        (onePacketUnforced setup leaks bounds horizon scheduler scale scale_pos scale_le_one n)
        (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one n)
        (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one (slots := slots) n) agent)

/-- The local failure probability of a law at a site of the one-packet game:
the probability of the event-level failure of the site's pending event. -/
def onePacketSiteFailure (assessment : (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who) (law : PMF ((onePacketN).Choice who site.1)) :
    ℝ :=
  localFailure (2 * horizon + 1) assessment site
    (onePacketFailed setup leaks bounds horizon scheduler ((onePacketN).agentAt site)) law

/-- The successful part of the local exclusion payoff of a law at a site of the
one-packet game: its value on histories outside the event-level failure of the
site's pending event. -/
def onePacketSiteSuccess (assessment : (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who) (law : PMF ((onePacketN).Choice who site.1)) :
    ℝ :=
  localSuccessValue (2 * horizon + 1)
    (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter utility
      excludedPayoff) (payoffComponent setup) assessment site
    (onePacketFailed setup leaks bounds horizon scheduler ((onePacketN).agentAt site)) law

/-- **First activations transmit or fail surely.** At every forced first
activation of `who` for `event`, either the canonical decisions of encoded
source actions committing no failure and disclosing transmit, or every choice
fails `event` surely, under every assessment. -/
def FirstActivationTransmits : Prop :=
  ∀ who (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId),
    forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
      scheduler who (some (past, view)) →
    pendingEvent setup leaks who (some (past, view)) = some event →
    (∀ entry ∈ past, ¬ ActivatedAt setup leaks who event entry) →
    CanonicalTransmitsAt setup leaks who past view event ∨
      ∀ (assessment : (onePacketN).BehavioralAssessment)
        (decision : (onePacketN).IsDecisionInfo who (some (past, view)))
        (choice : (onePacketN).Choice who (some (past, view))),
        localFailure (2 * horizon + 1) assessment ⟨some (past, view), decision⟩
          (EventFailedHistory setup leaks bounds horizon scheduler who event)
          (PMF.pure choice) = 1

omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History] in
/-- **First activations transmit or fail surely.** Under the asynchronous
contract, at every forced first activation: a binding always has a canonical
slot, so its canonical decisions transmit; a disclosure transmits its opening
when the owner's binding resolves to a value, and otherwise the resolution
publishes a failure at every history of the information state, so every choice
fails the event surely. -/
theorem firstActivationTransmits_of_contract {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound) :
    FirstActivationTransmits setup leaks bounds horizon scheduler := by
  let app := application setup leaks
  let menu := bounds.onePacketMenu (runtime setup) leaks
  intro who past view event forced pending _
  obtain ⟨turn, _, owned, _⟩ := pendingEvent_spec pending
  obtain ⟨history, infoEq, forcedState⟩ := forced
  have observed : app.observe who history.state = some (past, view) :=
    (menu.info (initialLaw setup) horizon scheduler who history.trace).symm.trans infoEq
  have menuTrace := history.trace
  generalize history.state = state at observed forcedState menuTrace
  rcases state with _ | ⟨remaining, actor, execution⟩
  · exact forcedState.elim
  by_cases active : actor = some who
  swap
  · simp [ReactiveApplication.observe, active] at observed
  subst active
  simp only [ReactiveApplication.observe, ↓reduceIte, Option.some.injEq, Prod.mk.injEq]
    at observed
  obtain ⟨pastEq, viewEq⟩ := observed
  subst pastEq
  subst viewEq
  have turnExec : execution.application.publicView.ownTurn? who = some event := turn
  have ready : execution.application.config.cut.Ready event :=
    (execution.application.publicView_eventReady event).mp
      (PublicView.ownTurn?_spec _ who event turnExec).1
  cases node : nodeView (graph setup) event with
  | sample payload law outputEq codeEq =>
      have none := nodeView_sample_actor outputEq codeEq
      rw [owned] at none
      cases none
  | bind owner payload outputEq codeEq =>
      left
      intro action graphAction _ _ _
      obtain ⟨serial, slot⟩ := onePacket_canonicalFreshSlot_exists menuTrace who
      simp only [EventGraphRuntime.canonicalServiceDecision,
        EventGraphRuntime.canonicalReactiveDecision, node]
      dsimp only at slot
      erw [slot]
      simp [ReactiveApplication.SubmissionNormalization.action]
  | resolve owner payload binding checks outputEq codeEq =>
      have ownerEq : owner = who :=
        Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
      subst ownerEq
      have available : (EventGraph.EventCode.resolveOutput? binding checks true
          execution.application.config.store).isSome = true := by
        apply EventGraph.EventCode.resolveOutput?_isSome
        intro field member
        apply execution.application.config.read_available ready
        rw [← EventGraph.EventCode.readFields_cast outputEq ((graph setup).nodes event), codeEq]
        exact member
      obtain ⟨result, resolved⟩ := Option.isSome_iff_exists.mp available
      cases result with
      | success value =>
          left
          intro action graphAction encoded _ discloses
          have disclose := encodeEventAction?_discloses setup.program event action discloses
            graphAction encoded payload outputEq
          let inputs : PMF (graph setup).Inputs := setup.initialLaw.map setup.eventInputs
          have initialEq : inputs.map
              (EventGraphRuntime.State.initial (graph := graph setup)) = initialLaw setup := by
            rw [PMF.map_comp]
            rfl
          have valid := (runtime setup).reactiveBindingInvariant_history leaks inputs horizon
            scheduler (by
              rw [initialEq]
              exact menu.toRawTrace (initialLaw setup) horizon scheduler menuTrace)
          obtain ⟨candidate, _, _, _, packet⟩ :=
            EventGraphRuntime.reactiveResolutionPacket_provenance (runtime setup) leaks
              execution.application valid owner event payload binding checks outputEq graphAction
              disclose value resolved
          simp only [EventGraphRuntime.canonicalServiceDecision,
            EventGraphRuntime.canonicalReactiveDecision, node]
          change ((EventGraphRuntime.reactiveNormalization (runtime setup) leaks).action owner
            (execution.recall owner) (execution.observe app owner)
            ⟨(EventGraphRuntime.reactiveResolutionPacket owner event payload binding checks
              outputEq graphAction ((runtime setup).reactiveApplication leaks |>.observePlayer
                execution.application owner)).map fun packet =>
              (disclosureSubmission packet).normalizeReactive owner
                ((runtime setup).reactiveApplication leaks |>.observePlayer
                  execution.application owner) []⟩).transmission ≠ none
          rw [packet]
          simp only [Option.map_some, ReactiveApplication.SubmissionNormalization.action, ne_eq,
            reduceCtorEq, not_false_eq_true]
      | failure =>
          right
          intro assessment decision choice
          refine doomedDisclosure_localFailure_eq_one bounds horizon scheduler contract.completes
            assessment ⟨_, decision⟩ (PMF.pure choice) outputEq codeEq ?_
          rintro ⟨other, otherInfo⟩ _
          have otherObserved : app.observe owner other.state =
              some (execution.recall owner, execution.observe app owner) :=
            (menu.info (initialLaw setup) horizon scheduler owner other.trace).symm.trans
              otherInfo
          generalize other.state = otherState at otherObserved ⊢
          rcases otherState with _ | ⟨otherRemaining, otherActor, otherExecution⟩
          · cases otherObserved
          by_cases otherActive : otherActor = some owner
          swap
          · simp [ReactiveApplication.observe, otherActive] at otherObserved
          subst otherActive
          simp only [ReactiveApplication.observe, ↓reduceIte, Option.some.injEq, Prod.mk.injEq]
            at otherObserved
          have sameView := otherObserved.2
          have otherTurn : otherExecution.application.publicView.ownTurn? owner = some event := by
            have viewed := congrArg (fun view : app.PlayerView =>
              view.application.publicView.ownTurn? owner) sameView
            exact viewed.trans turnExec
          have otherReady : otherExecution.application.config.cut.Ready event :=
            (otherExecution.application.publicView_eventReady event).mp
              (PublicView.ownTurn?_spec _ owner event otherTurn).1
          have sameStore := congrArg (fun view : app.PlayerView =>
            view.application.observation.store) sameView
          refine ⟨_, rfl, otherReady, ?_⟩
          calc EventGraph.EventCode.resolveOutput? binding checks true
                otherExecution.application.config.store
              = EventGraph.EventCode.resolveOutput? binding checks true
                  ((graph setup).playerStore owner otherExecution.application.config.store) :=
                (EventGraph.EventCode.resolveOutput?_playerStore binding checks _ true).symm
            _ = EventGraph.EventCode.resolveOutput? binding checks true
                  ((graph setup).playerStore owner execution.application.config.store) :=
                congrArg (EventGraph.EventCode.resolveOutput? binding checks true) sameStore
            _ = EventGraph.EventCode.resolveOutput? binding checks true
                  execution.application.config.store :=
                EventGraph.EventCode.resolveOutput?_playerStore binding checks _ true
            _ = some .failure := resolved

omit [Finite setup.intendedProtocol.History] in
/-- **The prescribed failure bound.** For a well-formed setup, under the
asynchronous contract with timely delays and retention of first covered
canonical packets, if first activations transmit or fail surely, then along
vanishing tremble scales, at every forced site outside late deliveries, the
prescribed component fails at most as often as every choice up to one minus
the slot retention of the scale, or the choice fails surely. -/
theorem onePacket_prescribedFailure {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (retains : RetainsCoveredCanonical setup leaks bounds horizon scheduler bound)
    (transmitting : FirstActivationTransmits setup leaks bounds horizon scheduler)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    (scale_vanishing : Tendsto scale atTop (nhds 0))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment) :
    ∃ slack : ℕ → ℝ, Tendsto slack atTop (nhds 0) ∧ (∀ n, 0 ≤ slack n) ∧
      ∀ n who (site : (onePacketN).InformationSite who) choice,
        ¬ UnforcedAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ¬ ownedKeyed (UnforcedAgent setup leaks bounds horizon scheduler)
          (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
          ((onePacketN).agentAt site) →
        onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n) site
            (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
              scale_le_one n ((onePacketN).agentAt site)) ≤
          onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n) site
            (PMF.pure choice) + slack n ∨
        onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n) site
          (PMF.pure choice) = 1 := by
  refine ⟨fun n => 1 - slotRetention (scale n), ?_, fun n =>
    sub_nonneg.mpr (slotRetention_le_one (scale_pos n).le (scale_le_one n)), ?_⟩
  · simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_slotRetention scale_vanishing)
  intro n who site choice notFree unkeyed
  obtain ⟨info, decision⟩ := site
  have failureNonneg := localFailure_nonneg (2 * horizon + 1) (targetSequence n)
    (⟨info, decision⟩ : (onePacketN).InformationSite who)
    (onePacketFailed setup leaks bounds horizon scheduler
      ((onePacketN).agentAt ⟨info, decision⟩)) (PMF.pure choice)
  have slackNonneg : 0 ≤ 1 - slotRetention (scale n) :=
    sub_nonneg.mpr (slotRetention_le_one (scale_pos n).le (scale_le_one n))
  cases pendCase : pendingEvent setup leaks who info with
  | none =>
      left
      have empty : onePacketFailed setup leaks bounds horizon scheduler
          ((onePacketN).agentAt ⟨info, decision⟩) = ∅ := by
        unfold onePacketFailed
        simp only [pendCase]
      have zero : onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n)
          ⟨info, decision⟩ (onePacketPrescribed setup leaks bounds horizon scheduler sequence
            scale scale_pos scale_le_one n ((onePacketN).agentAt ⟨info, decision⟩)) = 0 := by
        unfold onePacketSiteFailure localFailure
        rw [empty]
        simp only [Set.mem_empty_iff_false, ↓reduceIte]
        exact expect_constant _ _
      unfold onePacketSiteFailure at zero ⊢
      rw [zero]
      linarith
  | some event =>
      rcases info with _ | ⟨past, view⟩
      · cases pendCase
      have notLate : ¬ LateDelivery setup leaks who (some (past, view)) :=
        fun late => unkeyed ⟨late, notFree⟩
      have never : ∀ entry ∈ past, ¬ ActivatedAt setup leaks who event entry := by
        intro entry member activated
        exact notLate ⟨past, view, event, rfl, pendCase, entry, member, activated⟩
      have forced : forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup)
          horizon scheduler who (some (past, view)) := Classical.not_not.mp notFree
      have failEq : onePacketFailed setup leaks bounds horizon scheduler
          ((onePacketN).agentAt ⟨some (past, view), decision⟩) =
          EventFailedHistory setup leaks bounds horizon scheduler who event := by
        unfold onePacketFailed
        simp only [pendCase]
      unfold onePacketSiteFailure
      rw [failEq]
      rcases transmitting who past view event forced pendCase never with transmits | sure
      · left
        have honestZero := honestChoice_localFailure_eq_zero setup leaks bounds horizon scheduler
          contract timely retains (sequence n) (targetSequence n) past view event decision forced
          pendCase never transmits who
        have bounded := (bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup)
          horizon scheduler
        have actsOnce := ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
          (initialLaw setup) horizon scheduler).actsOnceWhereItMatters
        have prescribedLe := localFailure_le_of_mass (2 * horizon + 1) (targetSequence n)
          (⟨some (past, view), decision⟩ : (onePacketN).InformationSite who) bounded actsOnce
          (EventFailedHistory setup leaks bounds horizon scheduler who event)
          (1 - slotRetention (scale n)) slackNonneg
          (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one n ((onePacketN).agentAt ⟨some (past, view), decision⟩))
          (honestChoice setup leaks bounds (initialLaw setup) horizon scheduler (sequence n) who
            (some (past, view)))
          (fun chosen => by
            rw [sub_sub_cancel]
            exact slotTrembledChoice_ge_main setup leaks bounds (initialLaw setup) horizon
              scheduler (scale_pos n).le (scale_le_one n) who (some (past, view)) _ _ _ chosen)
        have choiceNonneg := localFailure_nonneg (2 * horizon + 1) (targetSequence n)
          (⟨some (past, view), decision⟩ : (onePacketN).InformationSite who)
          (EventFailedHistory setup leaks bounds horizon scheduler who event) (PMF.pure choice)
        rw [honestZero] at prescribedLe
        linarith
      · right
        exact sure (targetSequence n) decision choice

/-- A response commits no value: it transmits no commitment packet. -/
def CommitsNoValue (response : (application setup leaks).Action) : Prop :=
  ∀ material, response.transmission = some material →
    ∀ event handle, material.call.packet ≠ .commitment event handle

/-- **The marked choices of the one-packet certificate**: the choices that
commit no value, such as silence and disclosures. Their success continuation is
the agent's continuation value; every choice committing a value is compared
with source deviations instead. -/
def onePacketCompared (who : Player) (site : (onePacketN).InformationSite who)
    (choice : (onePacketN).Choice who site.1) : Prop :=
  ∀ response, choice.1 = some response → CommitsNoValue setup leaks response

open Classical in
/-- **The open inputs of the one-packet certificate** for one source sequence:
the tremble scales and the obligations not yet discharged, each a statement
along every fully mixed Bayes sequence of profiles assembled from the
certificate's components, at the forced sites. -/
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
  /-- **The value decomposition at late deliveries.** At every forced late
  delivery, the exclusion payoff is at most the agent's continuation value up to
  a vanishing error, with gap at most the gap bound, and the successful part of
  every marked choice and of every late option is its success probability times
  that continuation value up to the error. -/
  lateDecomposition : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon
      scheduler slots p)) (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
    OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos scale_le_one
      weights targetSequence →
    (∀ n, (targetSequence n).IsFullyMixed) →
    (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
    ∃ (continuation : ℕ → (onePacketN).InformationAgent (onePacketN).playedInformation → ℝ)
      (error : ℕ → ℝ), Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (onePacketN).InformationSite who),
        ¬ UnforcedAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ownedKeyed (UnforcedAgent setup leaks bounds horizon scheduler)
          (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
          ((onePacketN).agentAt site) →
        excludedPayoff who ≤ continuation n ((onePacketN).agentAt site) + error n ∧
        continuation n ((onePacketN).agentAt site) - excludedPayoff who ≤ gapBound ∧
        (∀ choice, onePacketCompared setup leaks bounds horizon scheduler who site choice →
          |onePacketSiteSuccess setup leaks bounds horizon scheduler parameter utility
              excludedPayoff (targetSequence n) site (PMF.pure choice) -
            (1 - onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n)
              site (PMF.pure choice)) * continuation n ((onePacketN).agentAt site)| ≤
            error n) ∧
        ∀ option,
          |onePacketSiteSuccess setup leaks bounds horizon scheduler parameter utility
              excludedPayoff (targetSequence n) site
              (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
                scale_le_one (slots := slots) n ((onePacketN).agentAt site) option) -
            (1 - onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n)
              site (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
                scale_le_one (slots := slots) n ((onePacketN).agentAt site) option)) *
              continuation n ((onePacketN).agentAt site)| ≤ error n
  /-- **The value decomposition away from late deliveries.** At every forced site
  that is not a late delivery, the exclusion payoff is at most the agent's
  continuation value up to a vanishing error, with gap at most the gap bound, and
  the successful part of every marked choice and of the prescribed component is
  its success probability times that continuation value up to the error. -/
  nonLateDecomposition : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon
      scheduler slots p)) (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
    OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos scale_le_one
      weights targetSequence →
    (∀ n, (targetSequence n).IsFullyMixed) →
    (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
    ∃ (continuation : ℕ → (onePacketN).InformationAgent (onePacketN).playedInformation → ℝ)
      (error : ℕ → ℝ), Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (onePacketN).InformationSite who),
        ¬ UnforcedAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ¬ ownedKeyed (UnforcedAgent setup leaks bounds horizon scheduler)
          (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
          ((onePacketN).agentAt site) →
        excludedPayoff who ≤ continuation n ((onePacketN).agentAt site) + error n ∧
        continuation n ((onePacketN).agentAt site) - excludedPayoff who ≤ gapBound ∧
        (∀ choice, onePacketCompared setup leaks bounds horizon scheduler who site choice →
          |onePacketSiteSuccess setup leaks bounds horizon scheduler parameter utility
              excludedPayoff (targetSequence n) site (PMF.pure choice) -
            (1 - onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n)
              site (PMF.pure choice)) * continuation n ((onePacketN).agentAt site)| ≤
            error n) ∧
        |onePacketSiteSuccess setup leaks bounds horizon scheduler parameter utility
            excludedPayoff (targetSequence n) site
            (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
              scale_le_one n ((onePacketN).agentAt site)) -
          (1 - onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n) site
            (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
              scale_le_one n ((onePacketN).agentAt site))) *
            continuation n ((onePacketN).agentAt site)| ≤ error n
  /-- **Site commonness at late deliveries.** There are scores of the late
  options at each late-delivery key such that, at every forced late delivery,
  each late option fails within a vanishing drift of one minus its score at the
  site's key, and every marked choice fails within that drift of one minus the
  score of some option, or surely. -/
  siteCommonness : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler
      slots p)) (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
    OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos scale_le_one
      weights targetSequence →
    (∀ n, (targetSequence n).IsFullyMixed) →
    (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
    ∃ (score : ℕ → Option (LateKey setup leaks) → LateOption slots → ℝ) (drift : ℕ → ℝ),
      Tendsto drift atTop (nhds 0) ∧ (∀ n, 0 ≤ drift n) ∧
      ∀ n who (site : (onePacketN).InformationSite who),
        ¬ UnforcedAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ownedKeyed (UnforcedAgent setup leaks bounds horizon scheduler)
          (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
          ((onePacketN).agentAt site) →
        (∀ option,
          |onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n) site
              (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
                scale_le_one (slots := slots) n ((onePacketN).agentAt site) option) -
            (1 - score n (agentLateKey setup leaks bounds (initialLaw setup) horizon scheduler
              ((onePacketN).agentAt site)) option)| ≤ drift n) ∧
        ∀ choice, onePacketCompared setup leaks bounds horizon scheduler who site choice →
          (∃ option,
            |onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n) site
                (PMF.pure choice) -
              (1 - score n (agentLateKey setup leaks bounds (initialLaw setup) horizon scheduler
                ((onePacketN).agentAt site)) option)| ≤ drift n) ∨
          onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n) site
            (PMF.pure choice) = 1
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
            ∀ choice : (onePacketN).Choice who site.1,
              ¬ onePacketCompared setup leaks bounds horizon scheduler who site choice →
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
  compared := onePacketCompared setup leaks bounds horizon scheduler
  decomposition weights targetSequence assembled mixed bayes := by
    obtain ⟨continuation, error, errorLimit, value⟩ :=
      inputs.lateDecomposition weights targetSequence assembled mixed bayes
    obtain ⟨score, drift, driftLimit, driftNonneg, common⟩ :=
      inputs.siteCommonness weights targetSequence assembled mixed bayes
    refine ⟨continuation, score, error, drift, errorLimit, driftLimit, driftNonneg,
      fun n agent keyed decision => ?_⟩
    obtain ⟨low, gap, _, late⟩ := value n agent.1 ⟨agent.2.1, decision⟩ keyed.2 keyed
    exact ⟨low, gap, late, (common n agent.1 ⟨agent.2.1, decision⟩ keyed.2 keyed).1⟩
  ranking weights targetSequence assembled mixed bayes := by
    classical
    obtain ⟨lateContinuation, lateError, lateLimit, lateValue⟩ :=
      inputs.lateDecomposition weights targetSequence assembled mixed bayes
    obtain ⟨otherContinuation, otherError, otherLimit, otherValue⟩ :=
      inputs.nonLateDecomposition weights targetSequence assembled mixed bayes
    obtain ⟨score, drift, driftLimit, driftNonneg, common⟩ :=
      inputs.siteCommonness weights targetSequence assembled mixed bayes
    obtain ⟨slack, slackLimit, slackNonneg, prescribed⟩ :=
      onePacket_prescribedFailure setup leaks bounds horizon scheduler contract timely retains
        (firstActivationTransmits_of_contract setup leaks bounds horizon scheduler contract)
        sequence inputs.scale inputs.scale_pos inputs.scale_le_one inputs.scale_vanishing
        targetSequence
    refine ⟨fun n agent => if ownedKeyed (UnforcedAgent setup leaks bounds horizon scheduler)
        (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler) agent then
          lateContinuation n agent else otherContinuation n agent, score,
      fun n => max (lateError n) (otherError n), drift, slack,
      by simpa using lateLimit.max otherLimit, driftLimit, slackLimit, driftNonneg, slackNonneg,
      fun n who site choice notFree marked => ?_⟩
    by_cases keyed : ownedKeyed (UnforcedAgent setup leaks bounds horizon scheduler)
        (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
        ((onePacketN).agentAt site)
    · obtain ⟨low, gap, chosen, late⟩ := lateValue n who site notFree keyed
      obtain ⟨options, near⟩ := common n who site notFree keyed
      simp only [keyed, ↓reduceIte]
      have bound := le_max_left (lateError n) (otherError n)
      refine ⟨by linarith, gap, (chosen choice marked).trans bound, fun _ =>
        ⟨fun option => (late option).trans bound, options, near choice marked⟩,
        fun unkeyed => (unkeyed trivial).elim⟩
    · obtain ⟨low, gap, chosen, other⟩ := otherValue n who site notFree keyed
      simp only [keyed, ↓reduceIte]
      have bound := le_max_right (lateError n) (otherError n)
      refine ⟨by linarith, gap, (chosen choice marked).trans bound,
        fun isKeyed => isKeyed.elim,
        fun _ => ⟨other.trans bound, prescribed n who site choice notFree keyed⟩⟩
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
