/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketSequentialPreservation
import Vegas.Game.OnePacketSlotLaw
import Interaction.ReactiveSupportedRounds
import Vegas.Game.OnePacketEventSuccess
import Vegas.Game.OnePacketSourceTurn
import Vegas.Game.OnePacketBindingSite
import Vegas.Game.OnePacketSureFailure
import GameTheoryExtensions.Analysis.Protocol.SourceGainTransport
import Vegas.Game.OnePacketOwnSubmissions
import Vegas.Game.OnePacketForcedRegular
import Vegas.Game.OnePacketForcedBeliefs
import Vegas.Game.OnePacketPathwise
import Vegas.Game.OnePacketLateLumping
import Vegas.Game.OnePacketOperationalReads
import Vegas.Game.OnePacketFailureBridge
import Vegas.Game.OnePacketUnintendedCommitment
import Vegas.Game.OnePacketSiteLumping
import Vegas.Game.OnePacketSlotLawDischarge
import Vegas.Game.OnePacketOwnDisclosure
import Vegas.Game.OnePacketOpeningLaw
import Vegas.Game.OnePacketRelevantLumping
import Vegas.Game.OnePacketSwapFiberSum
import Vegas.Source.PrivateInputsIndependent

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
    have notFree : ¬ FreeAgent setup leaks bounds horizon scheduler agent :=
      fun unforced => unforced forced
    have notKeyed : ¬ ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
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
        ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ¬ ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
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
          horizon scheduler who (some (past, view)) :=
        forcedAgent_of_not_free setup leaks bounds horizon scheduler notFree
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

/-- **The marked choices of the one-packet certificate**: silence at a late
delivery, and elsewhere the choices that commit no value and send only for the
event at the player's own turn. Their success continuation is the agent's
continuation value; every other choice is compared with a late option, a
source deviation, the prescribed component, or has no gain. -/
def onePacketCompared (who : Player) (site : (onePacketN).InformationSite who)
    (choice : (onePacketN).Choice who site.1) : Prop :=
  (LateDelivery setup leaks who site.1 → choice.1 = some ⟨none⟩) ∧
    ∀ response, choice.1 = some response → CommitsNoValue setup leaks response ∧
      ∀ event, (runtime setup).submittedEvent? leaks response = some event →
        ∃ past view, site.1 = some (past, view) ∧
          view.application.publicView.ownTurn? who = some event

omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)] in
/-- At a decision input, every choice is some response of the one-packet menu. -/
theorem choice_response {who : Player} (site : (onePacketN).InformationSite who)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    (choice : (onePacketN).Choice who site.1) :
    ∃ response, choice.1 = some response ∧
      response ∈ bounds.onePacketActions (runtime setup) leaks who past view := by
  obtain ⟨info, decision⟩ := site
  change info = some (past, view) at atSite
  subst atSite
  obtain ⟨action, member, actionEq⟩ := choice.2
  exact ⟨action, actionEq, member⟩


variable {setup leaks bounds horizon scheduler} in
omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **One packet per event.** At every history of the default runtime, a
response of the one-packet menu transmitting for an event is sent before the
recall has submitted for that event. -/
theorem onePacket_unrecorded_of_member {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (who : Player) (event : (graph setup).EventId) (response : (application setup leaks).Action)
    (member : response ∈ bounds.onePacketActions (runtime setup) leaks who
      (control.execution.recall who) (control.execution.observe (application setup leaks) who))
    (submitted : (runtime setup).submittedEvent? leaks response = some event) :
    (runtime setup).eventRecorded leaks (control.execution.recall who) event = false := by
  let app := application setup leaks
  cases recorded : (runtime setup).eventRecorded leaks (control.execution.recall who) event with
  | false => rfl
  | true =>
      exfalso
      obtain ⟨_, sent⟩ := (bounds.mem_onePacketActions (runtime setup) leaks who _ _ _).mp member
      rcases sent with silent | ⟨material, transmits, permitted⟩
      · unfold EventGraphRuntime.submittedEvent? at submitted
        rw [silent] at submitted
        cases submitted
      · have named : material.call.packet.event? (graph setup) = some event := by
          unfold EventGraphRuntime.submittedEvent? at submitted
          rw [transmits] at submitted
          exact submitted
        have recalled := (runtime setup).countRecall_history leaks trace
        rw [(runtime setup).localEnvelope_eq_of_recall leaks control.execution recalled.1
          recalled.2.1 who material, countPermits_eq_true_iff] at permitted
        obtain ⟨entry, entryMember, entrySubmitted⟩ :=
          ((runtime setup).eventRecorded_iff leaks _ event).mp recorded
        obtain ⟨entryMaterial, entryTransmits⟩ : ∃ entryMaterial,
            entry.action.transmission = some entryMaterial := by
          unfold EventGraphRuntime.submittedEvent? at entrySubmitted
          cases transmission : entry.action.transmission with
          | none => rw [transmission] at entrySubmitted; cases entrySubmitted
          | some entryMaterial => exact ⟨entryMaterial, rfl⟩
        have entryNamed : entryMaterial.call.packet.event? (graph setup) = some event := by
          unfold EventGraphRuntime.submittedEvent? at entrySubmitted
          rw [entryTransmits] at entrySubmitted
          exact entrySubmitted
        obtain ⟨message, emitted, call⟩ :=
          ((transmissionsEmitted_serviceInvariant scheduler).history (initialLaw setup) horizon
            (fun _ _ _ entry member => (List.not_mem_nil member).elim) trace) who entry
            entryMember entryMaterial entryTransmits
        have output : message ∈ app.outputs (control.execution.recall who) :=
          List.mem_filterMap.mpr ⟨entry, entryMember, emitted⟩
        have earlier := earlierOwnPacket_of_output trace who
          (app.packet (app.submit control.execution.application who material) who
            (control.execution.network.known who) material) message output
        apply permitted.2.2 message earlier
        change message.payload.call.event? (graph setup) =
          material.call.packet.event? (graph setup)
        rw [call, entryNamed, named]

omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **A submission for the turn's event leaves it pending.** At a site whose
view has `event` as the player's turn, if some choice submits for `event`, then
`event` is pending: the one-packet menu sends for an event only before the
recall has submitted for it. -/
theorem pendingEvent_of_turnSubmission {who : Player} (site : (onePacketN).InformationSite who)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? who = some event)
    (choice : (onePacketN).Choice who site.1) {response : (application setup leaks).Action}
    (selected : choice.1 = some response)
    (submitted : (runtime setup).submittedEvent? leaks response = some event) :
    pendingEvent setup leaks who site.1 = some event := by
  let menu := bounds.onePacketMenu (runtime setup) leaks
  obtain ⟨offered, offeredEq, member⟩ := choice_response setup leaks bounds horizon scheduler
    site atSite choice
  rw [selected, Option.some.injEq] at offeredEq
  rw [← offeredEq] at member
  obtain ⟨⟨start, observed⟩, _⟩ := site.2
  have observedState : (application setup leaks).observe who start.state =
      some (past, view) :=
    (menu.info (initialLaw setup) horizon scheduler who start.trace).symm.trans
      (observed.trans atSite)
  rcases startState : start.state with _ | ⟨remaining, actor, execution⟩
  · rw [startState] at observedState
    cases observedState
  rw [startState] at observedState
  have actorEq : actor = some who := by
    by_contra different
    simp only [ReactiveApplication.observe, different, ↓reduceIte] at observedState
    cases observedState
  subst actorEq
  simp only [ReactiveApplication.observe, ↓reduceIte, Option.some.injEq, Prod.mk.injEq]
    at observedState
  obtain ⟨rfl, rfl⟩ := observedState
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩) :=
    menu.toRawTrace (initialLaw setup) horizon scheduler (startState ▸ start.trace)
  rw [atSite]
  exact pendingEvent_of_spec turn
    (onePacket_unrecorded_of_member rawTrace who event response member submitted)

omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)] in
/-- A transmitting response of the one-packet menu names an event. -/
theorem submittedEvent_of_transmits {who : Player}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} {response : (application setup leaks).Action}
    (member : response ∈ bounds.onePacketActions (runtime setup) leaks who past view)
    {material : (application setup leaks).Submission}
    (sends : response.transmission = some material) :
    ∃ event, (runtime setup).submittedEvent? leaks response = some event := by
  unfold EventGraphRuntime.submittedEvent?
  rw [sends]
  cases packet : material.call.packet with
  | commitment event _ => exact ⟨event, by simp only [packet, Payload.event?]⟩
  | opening event _ _ => exact ⟨event, by simp only [packet, Payload.event?]⟩
  | malformed raw => exact (onePacket_not_malformed bounds member sends raw packet).elim

/-- A choice at a site transmits a packet for the event at the player's own
turn. -/
def CommitsAtTurn (who : Player) (site : (onePacketN).InformationSite who)
    (choice : (onePacketN).Choice who site.1) : Prop :=
  ∃ past view response event, site.1 = some (past, view) ∧ choice.1 = some response ∧
    (runtime setup).submittedEvent? leaks response = some event ∧
    view.application.publicView.ownTurn? who = some event

omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)] in
/-- **Owing a failure fixes the exclusion payoff.** At a history whose decoded
point makes `who` owe a failure, under a scheduler completing play, every
deviation of `who` has history gain zero: every continuation pays `who` its
exclusion payoff. -/
theorem historyGain_eq_zero_of_owes
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    {profile : BehavioralProfile setup.program}
    (assessment : (onePacketN).BehavioralAssessment) {who : Player}
    (deviation : (onePacketN).AssessmentDeviation who)
    (history : (onePacketN).InformationHistory who deviation.1.1)
    (owed : DecodedState setup leaks profile (ProtocolState.OwesFailure who setup.program)
      history.1.state) :
    (onePacketN).historyGain ((onePacketN).truncatedRunner (2 * horizon + 1))
      (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter utility
        excludedPayoff) (payoffComponent setup) assessment deviation history = 0 := by
  let menu := bounds.onePacketMenu (runtime setup) leaks
  have bounded := menu.bounded (initialLaw setup) horizon scheduler
  let certificate := bounded.wellFoundedHistories
  have excluded : ∀ players : ∀ player, (onePacketN).BehavioralPolicy player,
      expect (((onePacketN).truncatedRunner (2 * horizon + 1) players history.1).map
        (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter
          utility excludedPayoff)) (payoffComponent setup · who) = excludedPayoff who := by
    intro players
    rw [expect_map]
    refine (expect_congr_on_support (g := fun _ => excludedPayoff who)
      (fun final reached => ?_)).trans (expect_constant _ _)
    change final ∈ ((onePacketN).runBehavioralFrom players (2 * horizon + 1) history.1).support
      at reached
    rw [← (onePacketN).runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate
      bounded] at reached
    exact exclusionReadoutUtility_of_failedReadout setup parameter utility excludedPayoff who _
      (decoded_owesFailure_failedReadout setup menu horizon scheduler completes certificate
        players who history.1 owed final reached)
  unfold InformationModel.historyGain
  rw [excluded, excluded, sub_self]

omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)] in
/-- **Commitments away from the turn are owed failures.** For a well-formed
setup, at every history of a site, a choice transmitting a packet for an event
that is not the player's own turn leaves the player owing a failure at the
decoded point: a readiness token is issued only once all earlier events have
completed. -/
theorem owes_of_not_commitsAtTurn (wellFormed : setup.WellFormed)
    (profile : BehavioralProfile setup.program) {who : Player}
    (site : (onePacketN).InformationSite who) (choice : (onePacketN).Choice who site.1)
    (offTurn : ¬ CommitsAtTurn setup leaks bounds horizon scheduler who site choice)
    {response : (application setup leaks).Action} (chosen : choice.1 = some response)
    {event : (graph setup).EventId}
    (submitted : (runtime setup).submittedEvent? leaks response = some event)
    (history : (onePacketN).InformationHistory who site.1) :
    DecodedState setup leaks profile (ProtocolState.OwesFailure who setup.program)
      history.1.state := by
  let app := application setup leaks
  let menu := bounds.onePacketMenu (runtime setup) leaks
  obtain ⟨fullHistory, infoEq⟩ := history
  have observed : app.observe who fullHistory.state = site.1 :=
    (menu.info (initialLaw setup) horizon scheduler who fullHistory.trace).symm.trans infoEq
  have menuTrace := fullHistory.trace
  change DecodedState setup leaks profile _ fullHistory.state
  generalize fullHistory.state = state at observed menuTrace
  rcases state with _ | ⟨remaining, actor, execution⟩
  · obtain ⟨info, decision⟩ := site
    change none = info at observed
    subst observed
    have legal := choice.2
    change choice.1 ∈ ({none} : Set _) at legal
    rw [chosen] at legal
    cases legal
  by_cases active : actor = some who
  swap
  · obtain ⟨info, decision⟩ := site
    simp only [ReactiveApplication.observe, active, ↓reduceIte] at observed
    change none = info at observed
    subst observed
    have legal := choice.2
    change choice.1 ∈ ({none} : Set _) at legal
    rw [chosen] at legal
    cases legal
  subst active
  have atSite : site.1 = some (execution.recall who, execution.observe app who) := by
    rw [← observed]
    simp [ReactiveApplication.observe]
  obtain ⟨rank, ⟨residual⟩, _⟩ := decodedState_intended_or_owes wellFormed profile menu horizon
    scheduler menuTrace _ rfl
  have legal := choice.2
  obtain ⟨info, decision⟩ := site
  change info = _ at atSite
  subst atSite
  obtain ⟨action, member, actionEq⟩ := legal
  rw [chosen] at actionEq
  cases Option.some.inj actionEq
  rcases onePacket_submission_atTurn bounds profile
      (menu.toRawTrace (initialLaw setup) horizon scheduler menuTrace) residual response member
      event submitted with turn | owes
  · exact (offTurn ⟨_, _, response, event, rfl, chosen, submitted, turn⟩).elim
  · exact ⟨rank, ⟨residual⟩, owes⟩

/-- A site at which `who` owes no failure at the decoded point of any history. -/
def SiteDebtFree {who : Player} (site : (onePacketN).InformationSite who) : Prop :=
  ∀ history : (onePacketN).InformationHistory who site.1,
    ∀ point, nativeDecodedState setup leaks history.1.state = some point →
      ¬ ProtocolState.OwesFailure who setup.program point

omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)] in
/-- **Owing is uniform over a decision input.** At a decision input of `who`
at which `who` owes a failure at the decoded point of some history, `who` owes
one at the decoded point of every history. -/
theorem owes_of_not_siteDebtFree (profile : BehavioralProfile setup.program) {who : Player}
    (site : (onePacketN).InformationSite who) {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    (owing : ¬ SiteDebtFree setup leaks bounds horizon scheduler site)
    (history : (onePacketN).InformationHistory who site.1) :
    DecodedState setup leaks profile (ProtocolState.OwesFailure who setup.program)
      history.1.state := by
  obtain ⟨info, decision⟩ := site
  change info = some (past, view) at atSite
  subst atSite
  unfold SiteDebtFree at owing
  push Not at owing
  obtain ⟨first, firstPoint, firstDecoded, firstOwes⟩ := owing
  obtain ⟨full, infoEq⟩ := history
  have observed : (application setup leaks).observe who full.state = some (past, view) :=
    ((bounds.onePacketMenu (runtime setup) leaks).info (initialLaw setup) horizon scheduler who
      full.trace).symm.trans infoEq
  have fullTrace := full.trace
  change DecodedState setup leaks profile _ full.state
  cases state : full.state with
  | none =>
      rw [state] at observed
      cases observed
  | some control =>
      rw [state] at fullTrace
      obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual profile
        (bounds.onePacketMenu (runtime setup) leaks) horizon scheduler fullTrace control rfl
      have decoded : nativeDecodedState setup leaks full.state = some
          (residual.lift (ProtocolState.entry residual.program residual.source)) := by
        rw [state]
        exact decodedPoint_eq residual
      have owes := (owesFailure_iff_of_infoOf first ⟨full, infoEq⟩ firstDecoded decoded).mp
        firstOwes
      refine ⟨rank, ⟨residual⟩, fun point decodedPoint => ?_⟩
      rw [residual.decode] at decodedPoint
      cases Option.some.inj decodedPoint
      exact owes

omit [Finite setup.intendedProtocol.History] in
/-- The agent of a debt-free site owes no failure. -/
theorem not_owingAgent_of_siteDebtFree {who : Player} {site : (onePacketN).InformationSite who}
    (debtFree : SiteDebtFree setup leaks bounds horizon scheduler site) :
    ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) :=
  fun ⟨history, point, decoded, owes⟩ => debtFree history point decoded owes

omit [Finite setup.intendedProtocol.History] in
/-- The site of an agent owing no failure is debt free. -/
theorem siteDebtFree_of_not_owing {who : Player} {site : (onePacketN).InformationSite who}
    (notOwing : ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site)) :
    SiteDebtFree setup leaks bounds horizon scheduler site :=
  fun history point decoded owes => notOwing ⟨history, point, decoded, owes⟩

/-- A forced site outside late deliveries, at which the player owes no failure,
with a choice committing an intended value at the player's own turn. -/
def ValueChangingSite {who : Player} (site : (onePacketN).InformationSite who) : Prop :=
  ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) ∧
    ¬ ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
        (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
        ((onePacketN).agentAt site) ∧
    SiteDebtFree setup leaks bounds horizon scheduler site ∧
    ∃ choice, ¬ onePacketCompared setup leaks bounds horizon scheduler who site choice ∧
      CommitsAtTurn setup leaks bounds horizon scheduler who site choice ∧
      IntendedCommitment setup leaks bounds horizon scheduler site choice

omit [Finite setup.intendedProtocol.History] in
theorem valueChangingSite_input {who : Player} {site : (onePacketN).InformationSite who}
    (changing : ValueChangingSite setup leaks bounds horizon scheduler site) :
    ∃ input : List (application setup leaks).PlayerEntry × (application setup leaks).PlayerView,
      site.1 = some input ∧ ∃ event, input.2.application.publicView.ownTurn? who = some event := by
  obtain ⟨_, _, _, _, _, ⟨past, view, _, event, atSite, _, _, turn⟩, _⟩ := changing
  exact ⟨(past, view), atSite, event, turn⟩

/-- The decision input of a forced site with a value-changing choice. -/
def changingInput {who : Player} {site : (onePacketN).InformationSite who}
    (changing : ValueChangingSite setup leaks bounds horizon scheduler site) :
    List (application setup leaks).PlayerEntry × (application setup leaks).PlayerView :=
  Classical.choose (valueChangingSite_input setup leaks bounds horizon scheduler changing)

omit [Finite setup.intendedProtocol.History] in
theorem changingInput_decision {who : Player} {site : (onePacketN).InformationSite who}
    (changing : ValueChangingSite setup leaks bounds horizon scheduler site) :
    site.1 = some ((changingInput setup leaks bounds horizon scheduler changing).1,
      (changingInput setup leaks bounds horizon scheduler changing).2) :=
  (Classical.choose_spec (valueChangingSite_input setup leaks bounds horizon scheduler
    changing)).1

omit [Finite setup.intendedProtocol.History] in
theorem changingInput_turn {who : Player} {site : (onePacketN).InformationSite who}
    (changing : ValueChangingSite setup leaks bounds horizon scheduler site) :
    ∃ event, (changingInput setup leaks bounds horizon scheduler
      changing).2.application.publicView.ownTurn? who = some event :=
  (Classical.choose_spec (valueChangingSite_input setup leaks bounds horizon scheduler
    changing)).2

omit [Finite setup.intendedProtocol.History] in
/-- **Projected decisions at value-changing sites.** For a well-formed setup, the
projected view of a forced site with a value-changing choice is a decision site
of the intended game: the site is debt free and shows the player's own turn. -/
theorem valueChangingSite_projectedDecision (wellFormed : setup.WellFormed) {who : Player}
    {site : (onePacketN).InformationSite who}
    (changing : ValueChangingSite setup leaks bounds horizon scheduler site) :
    setup.intendedModel.IsDecisionInfo who (projectView setup leaks who site.1) :=
  projectedDecision_of_forcedAgent wellFormed
    (forcedAgent_of_not_free setup leaks bounds horizon scheduler changing.1)
    (changingInput_decision setup leaks bounds horizon scheduler changing)
    (changingInput_turn setup leaks bounds horizon scheduler changing).choose_spec
    changing.2.2.1

open Classical in
/-- **The honest counterparts at one site** along a source sequence and a
target sequence: a tremble scale negligible against a floor to a depth, and at
every stage an honest counterpart of each history at which another player
responded irregularly, reached at least the floor to the depth times the square
of the scale as often as the irregular history up to the cube of the scale. -/
structure OnePacketCounterpartInputs (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who) where
  /-- The tremble scale of irregular histories. -/
  scale : ℕ → ℝ
  /-- The floor of honest masses. -/
  floors : ℕ → ℝ
  /-- The depth of the floor. -/
  depth : ℕ
  /-- The slack of the honest counterparts. -/
  slack : ℝ
  floors_pos : ∀ n, 0 < floors n
  scale_nonneg : ∀ n, 0 ≤ scale n
  negligible : Tendsto (fun n => scale n / floors n ^ depth) atTop (nhds 0)
  slack_nonneg : 0 ≤ slack
  /-- The honest counterpart of each irregular history at each stage. -/
  counterpart : ℕ → (onePacketN).InformationHistory who site.1 →
    (onePacketN).InformationHistory who site.1
  /-- The weight common to an irregular history and its counterpart. -/
  commonWeight : ℕ → (onePacketN).InformationHistory who site.1 → ℝ
  counterpart_regular : ∀ n history, ¬ RegularTrace setup leaks bounds horizon scheduler
      (sequence n) who history.1.trace →
    RegularTrace setup leaks bounds horizon scheduler (sequence n) who
      (counterpart n history).1.trace
  irregular_le : ∀ n history, ¬ RegularTrace setup leaks bounds horizon scheduler (sequence n)
      who history.1.trace →
    ((onePacketN).historyReachWeight (targetSequence n).strategy history.1).toReal ≤
      scale n ^ 3 * commonWeight n history
  counterpart_ge : ∀ n history, ¬ RegularTrace setup leaks bounds horizon scheduler
      (sequence n) who history.1.trace →
    scale n ^ 2 * floors n ^ depth * commonWeight n history ≤
      slack * ((onePacketN).historyReachWeight (targetSequence n).strategy
        (counterpart n history).1).toReal

open Classical in
/-- **The own and replay inputs at one own-turn site** along a source sequence
and a target sequence: operational steps for the target profiles, and at every
stage the intended own completions of regular histories and the common fibers
of the replay projection. -/
structure OnePacketOwnInputs (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who)
    (sourceSite : setup.intendedModel.InformationSite who)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView}
    (decision : site.1 = some (past, view))
    (projected : sourceSite.1 = projectView setup leaks who site.1) where
  /-- Operational steps of the target profiles. -/
  steps : OperationalSteps setup leaks bounds horizon scheduler sequence
    (fun n => (targetSequence n).strategy) who
  /-- Own completions along regular histories decode to intended actions. -/
  ownIntended : ∀ n (history : (onePacketN).InformationHistory who site.1),
    RegularTrace setup leaks bounds horizon scheduler (sequence n) who history.1.trace →
    OwnCompletionsIntended (bounds := bounds) (horizon := horizon) (scheduler := scheduler) who
      history.1.trace
  /-- The common operational mass of the fibers at each stage. -/
  fiberMass : ℕ → ℝ
  fiber : ∀ n point, ∑ history with RegularTrace setup leaks bounds horizon scheduler
      (sequence n) who history.1.trace ∧
      replayProjection setup leaks bounds horizon scheduler sourceSite site decision projected
        history = point,
    operationalWeight setup leaks who (steps.mass n)
      (operationalRecord setup leaks bounds horizon scheduler history.1.trace) = fiberMass n

/-- **The forced-belief inputs at one own-turn site** along a source sequence
and a target sequence: the honest counterparts of irregular histories, and the
own and replay inputs. -/
structure OnePacketBeliefInputs (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who)
    (sourceSite : setup.intendedModel.InformationSite who)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView}
    (decision : site.1 = some (past, view))
    (projected : sourceSite.1 = projectView setup leaks who site.1) extends
    OnePacketCounterpartInputs setup leaks bounds horizon scheduler sequence targetSequence site,
    OnePacketOwnInputs setup leaks bounds horizon scheduler sequence targetSequence site
      sourceSite decision projected

omit [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)] in
/-- **Beliefs converge at an own-turn site.** For a well-formed setup, at a
forced site of `who` at its own turn whose projected view is an intended site,
along a fully mixed Bayes source sequence and a fully mixed Bayes target
sequence with the forced-belief inputs, the native belief pushed forward along
the replay projection approaches the intended belief in `ℓ¹`. -/
theorem onePacket_beliefConverges (wellFormed : setup.WellFormed)
    {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (sourceBayes : ∀ n, BehavioralAssessment.IsBayesConsistent setup.intendedModel (sequence n)
      setup.intended_decision_antichain)
    {targetSequence : ℕ → (onePacketN).BehavioralAssessment}
    (mixed : ∀ n, (targetSequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain)
    {who : Player} {site : (onePacketN).InformationSite who}
    {sourceSite : setup.intendedModel.InformationSite who}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView}
    (decision : site.1 = some (past, view))
    (projected : sourceSite.1 = projectView setup leaks who site.1)
    (forced : forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
      scheduler who site.1)
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? who = some event)
    (inputs : OnePacketBeliefInputs setup leaks bounds horizon scheduler sequence targetSequence
      site sourceSite decision projected) :
    Tendsto (fun n => ∑' point,
      |((((targetSequence n).belief who site).map
          (replayProjection setup leaks bounds horizon scheduler sourceSite site decision
            projected)) point).toReal -
        ((sequence n).belief who sourceSite point).toReal|) atTop (nhds 0) := by
  classical
  let := Fintype.ofFinite (setup.intendedModel.InformationHistory who sourceSite.1)
  simp only [tsum_fintype]
  exact tendsto_projectedBelief_sub
    (fun n => ForcedBeliefInputs.ofRegularHistories (n := n) wellFormed forced decision turn
      projected (sourceMixed n) (inputs.ownIntended n) (inputs.fiberMass n) (inputs.fiber n)
      (inputs.counterpart n) (inputs.commonWeight n) (inputs.counterpart_regular n)
      (inputs.irregular_le n) (inputs.counterpart_ge n))
    decision (fun _ => rfl) mixed bayes sourceMixed sourceBayes inputs.floors_pos
    inputs.scale_nonneg inputs.negligible inputs.slack_nonneg

omit [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)] in
open Classical in
/-- **Irregular histories vanish at a site with honest counterparts.** Along a
fully mixed Bayes target sequence, the belief mass of the histories at which
another player responded irregularly vanishes when each has an honest
counterpart reached more often by a factor the tremble scale over the floor to
the depth makes negligible. -/
theorem onePacket_irregularVanishes {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {targetSequence : ℕ → (onePacketN).BehavioralAssessment}
    (mixed : ∀ n, (targetSequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain)
    {who : Player} {site : (onePacketN).InformationSite who}
    (inputs : OnePacketCounterpartInputs setup leaks bounds horizon scheduler sequence
      targetSequence site) :
    Tendsto (fun n => expect ((targetSequence n).belief who site) (fun history =>
      if RegularTrace setup leaks bounds horizon scheduler (sequence n) who history.1.trace
      then (0 : ℝ) else 1)) atTop (nhds 0) := by
  let := Fintype.ofFinite ((onePacketN).InformationHistory who site.1)
  have limit := tendsto_irregularRatio (slack := inputs.slack) inputs.negligible
    (Fintype.card ((onePacketN).InformationHistory who site.1))
  refine squeeze_zero (fun n => expect_nonneg _ _ fun history _ => by split <;> norm_num)
    (fun n => ?_) limit
  rw [expect_eq_sum]
  have bound := sum_belief_le_of_counterpart
    (fun history : (onePacketN).InformationHistory who site.1 =>
      ¬ RegularTrace setup leaks bounds horizon scheduler (sequence n) who history.1.trace)
    (inputs.counterpart n) (bayes n)
    (InformationModel.informationMass_pos_of_fullSupport _ _ (mixed n) who site)
    (div_nonneg (mul_nonneg inputs.slack_nonneg (inputs.scale_nonneg n))
      (pow_nonneg (inputs.floors_pos n).le _))
    (fun history irregular => not_not.mpr (inputs.counterpart_regular n history irregular))
    (fun history irregular => le_mul_of_tremble_counterpart (inputs.scale_nonneg n)
      (inputs.floors_pos n) (inputs.irregular_le n history irregular)
      (inputs.counterpart_ge n history irregular))
  refine le_trans (le_of_eq ?_) bound
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun history _ => ?_
  split_ifs <;> simp

omit [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)] in
open Classical in
/-- **Histories outside the forced region vanish at a forced site.** Along a
fully mixed Bayes target sequence, at a forced decision input with honest
counterparts, the belief mass of the histories outside the forced region
vanishes when the owner's own completions along regular histories are
intended: such a regular history is in a forced state
(`Vegas.forcedState_of_regular`), and irregular histories vanish
(`Vegas.onePacket_irregularVanishes`). -/
theorem onePacket_unforcedVanishes (wellFormed : setup.WellFormed)
    {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {targetSequence : ℕ → (onePacketN).BehavioralAssessment}
    (mixed : ∀ n, (targetSequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain)
    {who : Player} {site : (onePacketN).InformationSite who}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView}
    (decision : site.1 = some (past, view))
    (forced : forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
      scheduler who site.1)
    (counterparts : OnePacketCounterpartInputs setup leaks bounds horizon scheduler sequence
      targetSequence site)
    (ownIntended : ∀ n (history : (onePacketN).InformationHistory who site.1),
      RegularTrace setup leaks bounds horizon scheduler (sequence n) who history.1.trace →
      OwnCompletionsIntended (bounds := bounds) (horizon := horizon) (scheduler := scheduler) who
        history.1.trace) :
    Tendsto (fun n => expect ((targetSequence n).belief who site) (fun history =>
      if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1)) atTop (nhds 0) := by
  refine squeeze_zero (fun n => expect_nonneg _ _ fun history _ => by split <;> norm_num)
    (fun n => ?_) (onePacket_irregularVanishes setup leaks bounds horizon scheduler mixed bayes
      counterparts)
  refine expect_mono (fun history _ => ?_) (payoffIntegrable_of_finite _ _)
    (payoffIntegrable_of_finite _ _)
  by_cases regular : RegularTrace setup leaks bounds horizon scheduler (sequence n) who
    history.1.trace
  · have inForced := forcedState_of_regular wellFormed (sequence n) decision forced history
      regular (ownIntended n history regular)
    simp only [inForced, regular, ↓reduceIte, le_refl]
  · simp only [regular, ↓reduceIte]
    split <;> norm_num

omit [Finite setup.intendedProtocol.History] in
/-- A function bounded by `bound` has expectations under two laws on a finite
type within `bound` times their `ℓ¹` distance. -/
theorem expect_sub_le_of_bounded {α : Type*} [Finite α] (first second : PMF α) (value : α → ℝ)
    {bound : ℝ} (bounded : ∀ point, |value point| ≤ bound) :
    expect first value - expect second value ≤
      bound * ∑' point, |(first point).toReal - (second point).toReal| := by
  let := Fintype.ofFinite α
  rw [tsum_fintype, expect_eq_sum, expect_eq_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun point _ => ?_
  rw [← sub_mul]
  calc _ ≤ |((first point).toReal - (second point).toReal) * value point| := le_abs_self _
    _ = |(first point).toReal - (second point).toReal| * |value point| := abs_mul _ _
    _ ≤ _ := by
        rw [mul_comm bound]
        exact mul_le_mul_of_nonneg_left (bounded point) (abs_nonneg _)

/-- The local gain at a site of the one-packet game of installing a law: the
expected exclusion payoff of the deviation minus that of the assessment. -/
def onePacketSiteGain (assessment : (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who) (law : PMF ((onePacketN).Choice who site.1)) : ℝ :=
  let comparison := (onePacketN).assessmentComparisonWith
    ((onePacketN).truncatedRunner (2 * horizon + 1))
    (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter utility
      excludedPayoff) assessment who (site, (assessment.strategy who).withLaw site.1 law)
  expect comparison.alternative ((payoffComponent setup) · who) -
    expect comparison.prescribed ((payoffComponent setup) · who)

open Classical in
/-- The failure probability, from one history of a site, of installing a law
there: the probability of the event-level failure of the site's pending event. -/
def lateHistoryFailure (assessment : (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who) (law : PMF ((onePacketN).Choice who site.1))
    (history : (onePacketN).InformationHistory who site.1) : ℝ :=
  expect (localHistoryRun (2 * horizon + 1) assessment site law history) fun final =>
    if final ∈ onePacketFailed setup leaks bounds horizon scheduler ((onePacketN).agentAt site)
    then 1 else 0

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L]
  [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History] in
private theorem unit_expect {α : Type*} (μ : PMF α) (f : α → ℝ)
    (unit : ∀ a, 0 ≤ f a ∧ f a ≤ 1) : 0 ≤ expect μ f ∧ expect μ f ≤ 1 :=
  ⟨expect_nonneg μ f fun a _ => (unit a).1,
    expect_le_const μ f (payoffIntegrable_of_bounded μ f (C := 1) fun a => by
      rw [abs_le]
      constructor <;> linarith [unit a]) 1 fun a _ => (unit a).2⟩

omit [Fintype Player] [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)] in
/-- **A late delivery decides its pending event.** At a decision input of `who`
with pending event `event`, along a history whose recall of `who` is the
input's, the late-delivery key decides `event`. -/
theorem decidedEvent_eq_of_pending {who : Player}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} {event : (graph setup).EventId}
    (pending : pendingEvent setup leaks who (some (past, view)) = some event)
    {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (recallEq : control.execution.recall who = past) {key : LateKey setup leaks}
    (siteKey : lateKey setup leaks who (some (past, view)) = some key) :
    decidedEvent key = some event := by
  obtain ⟨turn, _, owned, unrecorded⟩ := pendingEvent_spec pending
  simp only [lateKey, Option.some.injEq] at siteKey
  subst siteKey
  cases node : nodeView (graph setup) event with
  | sample payload law outputEq codeEq =>
      have none := nodeView_sample_actor outputEq codeEq
      rw [owned] at none
      cases none
  | resolve owner payload binding checks outputEq codeEq =>
      have ownerEq : owner = who :=
        Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
      subst ownerEq
      unfold decidedEvent
      rw [turnEvent_of_publicationTurn ⟨turn, payload, binding, checks, outputEq, codeEq, node⟩]
  | bind owner payload outputEq codeEq =>
      have ownerEq : owner = who :=
        Option.some.inj ((EventGraph.actor?_of_outputLayout_binding _ outputEq).symm.trans
          owned)
      subst ownerEq
      have noPublication : turnEvent (setup := setup) (leaks := leaks)
          { owner := owner, current := operationalView setup leaks view,
            recalled := past.map fun entry =>
              (operationalView setup leaks entry.beforeView, entry.emitted),
            delivered := deliveredValue setup leaks owner view } = none := by
        cases found : turnEvent (setup := setup) (leaks := leaks) _ with
        | none => rfl
        | some other =>
            obtain ⟨otherTurn, _, _, _, _, _, otherNode⟩ := publicationTurn_of_turnEvent found
            have same : other = event := Option.some.inj (otherTurn.symm.trans turn)
            subst same
            rw [node] at otherNode
            cases otherNode
      have unsent : UnsentFor (setup := setup) (leaks := leaks)
          { owner := owner, current := operationalView setup leaks view,
            recalled := past.map fun entry =>
              (operationalView setup leaks entry.beforeView, entry.emitted),
            delivered := deliveredValue setup leaks owner view } event := by
        intro recalledEntry member message emitted named
        obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
        have recorded := (history_eventRecorded_iff trace owner event).mpr
          ⟨message, by
            rw [recallEq]
            exact List.mem_filterMap.mpr ⟨entry, entryMember, emitted⟩, named⟩
        rw [recallEq, unrecorded] at recorded
        cases recorded
      have binding : BindingTurn (setup := setup) (leaks := leaks)
          { owner := owner, current := operationalView setup leaks view,
            recalled := past.map fun entry =>
              (operationalView setup leaks entry.beforeView, entry.emitted),
            delivered := deliveredValue setup leaks owner view } event payload :=
        ⟨turn, ⟨outputEq, codeEq, node⟩, unsent⟩
      unfold decidedEvent
      rw [noPublication]
      cases found : bindingTurn (setup := setup) (leaks := leaks) _ with
      | none =>
          unfold bindingTurn at found
          split at found
          · cases found
          · rename_i noTurn
            exact (noTurn ⟨(event, payload), binding⟩).elim
      | some decided =>
          obtain ⟨decidedTurn, _, _⟩ := bindingTurn_spec found
          exact congrArg some (Option.some.inj (decidedTurn.symm.trans turn))

omit [Finite setup.intendedProtocol.History] in
/-- **Event-level failure is store-level failure of the decided event.** Under a
scheduler completing play, at a late delivery of `who`, every final history of
play for the horizon from a history of the site is an event-level failed history
of the site's agent exactly when its store records a failure of the event the
late-delivery key decides. -/
theorem onePacketFailed_iff_decisionFailed
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (decoding : BehavioralProfile setup.program)
    {who : Player} (site : (onePacketN).InformationSite who)
    (late : LateDelivery setup leaks who site.1) {key : LateKey setup leaks}
    (siteKey : lateKey setup leaks who site.1 = some key)
    (history : (onePacketN).InformationHistory who site.1)
    (profile : ∀ player, (onePacketN).BehavioralPolicy player)
    (final : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (reached : final ∈ ((onePacketN).runBehavioralFrom profile (2 * horizon + 1)
      history.1).support) :
    final ∈ onePacketFailed setup leaks bounds horizon scheduler ((onePacketN).agentAt site) ↔
      DecisionFailed key final.state := by
  let menu := bounds.onePacketMenu (runtime setup) leaks
  have bounded := menu.bounded (initialLaw setup) horizon scheduler
  let certificate := bounded.wellFoundedHistories
  obtain ⟨past, view, event, atSite, pending, _⟩ := late
  rw [atSite] at pending
  obtain ⟨_, _, owned, _⟩ := pendingEvent_spec pending
  -- the decided event, read at the site's history
  obtain ⟨fullHistory, infoEq⟩ := history
  have observed : (application setup leaks).observe who fullHistory.state = some (past, view) :=
    (menu.info (initialLaw setup) horizon scheduler who fullHistory.trace).symm.trans
      (infoEq.trans atSite)
  have historyTrace := fullHistory.trace
  have decided : decidedEvent key = some event := by
    generalize fullHistory.state = state at observed historyTrace
    rcases state with _ | ⟨remaining, actor, execution⟩
    · cases observed
    by_cases active : actor = some who
    swap
    · simp [ReactiveApplication.observe, active] at observed
    subst active
    simp only [ReactiveApplication.observe, ↓reduceIte, Option.some.injEq, Prod.mk.injEq]
      at observed
    exact decidedEvent_eq_of_pending setup leaks horizon scheduler pending
      (menu.toRawTrace (initialLaw setup) horizon scheduler historyTrace) observed.1
      (atSite ▸ siteKey)
  -- the final history is terminal
  have terminalReached : final ∈ ((onePacketN).runBehavioralTerminalFrom certificate profile
      fullHistory).support := by
    rw [(onePacketN).runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate
      bounded]
    exact reached
  have stopped := (onePacketN).runBehavioralTerminalFrom_support_terminal certificate profile
    fullHistory final terminalReached
  have failedEq : onePacketFailed setup leaks bounds horizon scheduler
      ((onePacketN).agentAt ⟨site.1, site.2⟩) =
      EventFailedHistory setup leaks bounds horizon scheduler who event := by
    unfold onePacketFailed
    change (match pendingEvent setup leaks who site.1 with
      | none => ∅
      | some event => EventFailedHistory setup leaks bounds horizon scheduler who event) = _
    rw [atSite, pending]
  change final ∈ onePacketFailed setup leaks bounds horizon scheduler
    ((onePacketN).agentAt ⟨site.1, site.2⟩) ↔ _
  rw [failedEq]
  have finalTrace := final.trace
  cases finalState : final.state with
  | none => rw [finalState] at stopped; exact stopped.elim
  | some control =>
      have rawTrace := menu.toRawTrace (initialLaw setup) horizon scheduler finalTrace
      rw [finalState] at rawTrace stopped
      have cutTerminal := completes control rawTrace stopped
      unfold DecisionFailed
      rw [decided]
      constructor
      · intro failedHistory
        change sourceReadout setup leaks final.state ∈ EventFailedReadout setup who event
          at failedHistory
        rw [finalState] at failedHistory
        obtain ⟨terminal, read, _, cellFailed⟩ := failedHistory
        exact ⟨by rw [cutTerminal]; exact Finset.mem_univ _,
          storeEventFailed_of_readout setup leaks control event read cellFailed⟩
      · rintro ⟨_, storeFailed⟩
        exact eventFailedHistory_of_storeEventFailed bounds horizon scheduler decoding
          completes certificate profile final
          (by rw [finalState]; exact stopped) finalState owned storeFailed

/-- **A late key.** The key owner's turn event, for which it has sent nothing,
was its turn at one of its recalled views. -/
def KeyLate (key : LateKey setup leaks) : Prop :=
  ∃ event, key.current.1.ownTurn? key.owner = some event ∧ UnsentFor key event ∧
    ∃ entry ∈ key.recalled, entry.1.1.ownTurn? key.owner = some event

omit [Fintype Player] [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)] in
/-- Along a history, the owner has sent nothing for an event exactly when its
recall has not recorded the event. -/
theorem unsentFor_iff_unrecorded {who : Player}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (recallEq : control.execution.recall who = past) {key : LateKey setup leaks}
    (siteKey : lateKey setup leaks who (some (past, view)) = some key)
    (event : (graph setup).EventId) :
    UnsentFor key event ↔ (runtime setup).eventRecorded leaks past event = false := by
  simp only [lateKey, Option.some.injEq] at siteKey
  subst siteKey
  constructor
  · intro unsent
    apply Bool.eq_false_of_not_eq_true
    intro recorded
    rw [← recallEq] at recorded
    obtain ⟨message, member, named⟩ := (history_eventRecorded_iff trace who event).mp recorded
    rw [recallEq] at member
    obtain ⟨entry, entryMember, emitted⟩ := List.mem_filterMap.mp member
    exact unsent _ (List.mem_map_of_mem entryMember) message emitted named
  · intro unrecorded recalledEntry member message emitted named
    obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
    have recorded := (history_eventRecorded_iff trace who event).mpr
      ⟨message, by
        rw [recallEq]
        exact List.mem_filterMap.mpr ⟨entry, entryMember, emitted⟩, named⟩
    rw [recallEq, unrecorded] at recorded
    cases recorded

omit [Fintype Player] [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)] in
/-- **Lateness is read off the key.** Along a history, the late-delivery key of
a decision input is late exactly when the input is a late delivery. -/
theorem keyLate_iff_lateDelivery {who : Player}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (recallEq : control.execution.recall who = past) {key : LateKey setup leaks}
    (siteKey : lateKey setup leaks who (some (past, view)) = some key) :
    KeyLate setup leaks key ↔ LateDelivery setup leaks who (some (past, view)) := by
  have unsentIff := unsentFor_iff_unrecorded setup leaks horizon scheduler trace recallEq siteKey
  simp only [lateKey, Option.some.injEq] at siteKey
  subst siteKey
  constructor
  · rintro ⟨event, turn, unsent, recalledEntry, member, activated⟩
    obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
    exact ⟨past, view, event, rfl,
      pendingEvent_of_spec turn ((unsentIff event).mp unsent), entry, entryMember, activated⟩
  · rintro ⟨past', view', event, same, pending, entry, entryMember, activated⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
    obtain ⟨turn, _, _, unrecorded⟩ := pendingEvent_spec pending
    exact ⟨event, turn, (unsentIff event).mpr unrecorded, _,
      List.mem_map_of_mem entryMember, activated⟩

/-- The failure expectation of `fuel` steps of a lumping's image kernel from the
image read off an operational record. -/
def lumpedFailure {assessment : (onePacketN).BehavioralAssessment} {who : Player}
    {LateOption : Type}
    {profileOf : (onePacketN).InformationSite who → LateOption → ∀ player,
      (onePacketN).BehavioralPolicy player}
    {failedState : LateKey setup leaks → (application setup leaks).ProtocolState → Prop}
    {relevant : (onePacketN).InformationSite who → Prop}
    {δ : ℝ} {Y : Type}
    (lumping : PendingLumpingOn assessment who relevant profileOf failedState δ Y)
    (fuel : Nat) (key : LateKey setup leaks) (option : LateOption)
    (record : List (Option (OperationalState setup leaks))) : ℝ :=
  expect ((fun law => law.bind (lumping.kernel key option))^[fuel]
    (PMF.pure (lumping.start key record))) (lumping.failure key)

open Classical in
omit [Finite setup.intendedProtocol.History] in
/-- **Late failure from lumping.** Given a one-step lumping at late deliveries of
the profiles installing the late options, whose failed states agree with the
failure sets on the final histories of play from forced histories of the belief,
the failure of each late option from each forced history of a late delivery is
within `(2 * horizon + 1) * δ` of the lumped failure read off its operational
record. -/
theorem lateHistoryFailure_near_lumped (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat} (n : ℕ) (assessment : (onePacketN).BehavioralAssessment) (who : Player)
    {failedState : LateKey setup leaks → (application setup leaks).ProtocolState → Prop}
    {δ : ℝ} {Y : Type} {relevant : (onePacketN).InformationSite who → Prop}
    (lumping : PendingLumpingOn assessment who relevant
      (fun site option => Profile.update (sig := (onePacketN).behavioralSignature)
        assessment.strategy who ((assessment.strategy who).withLaw site.1
          (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one (slots := slots) n ((onePacketN).agentAt site) option)))
      failedState δ Y)
    (site : (onePacketN).InformationSite who) (isRelevant : relevant site)
    (key : LateKey setup leaks) (siteKey : lateKey setup leaks who site.1 = some key)
    (option : LateOption slots)
    (agrees : ∀ history ∈ (assessment.belief who site).support,
        ForcedState setup leaks who history.1.state →
        ∀ final ∈ ((onePacketN).runBehavioralFrom (Profile.update
            (sig := (onePacketN).behavioralSignature) assessment.strategy who
            ((assessment.strategy who).withLaw site.1
              (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
                scale_le_one (slots := slots) n ((onePacketN).agentAt site) option)))
            (2 * horizon + 1) history.1).support,
          (final ∈ onePacketFailed setup leaks bounds horizon scheduler
            ((onePacketN).agentAt site) ↔ failedState key final.state))
    (history : (onePacketN).InformationHistory who site.1)
    (supported : history ∈ (assessment.belief who site).support)
    (forced : ForcedState setup leaks who history.1.state) :
    |lateHistoryFailure setup leaks bounds horizon scheduler assessment site
        (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one (slots := slots) n ((onePacketN).agentAt site) option) history -
      lumpedFailure setup leaks bounds horizon scheduler lumping (2 * horizon + 1) key option
        (operationalRecord setup leaks bounds horizon scheduler history.1.trace)| ≤
      ((2 * horizon + 1 : ℕ) : ℝ) * δ := by
  have near := lumping.pathwise (2 * horizon + 1) site isRelevant key siteKey option history
    supported forced
  have same : lateHistoryFailure setup leaks bounds horizon scheduler assessment site
      (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one (slots := slots) n ((onePacketN).agentAt site) option) history =
      expect ((onePacketN).runBehavioralFrom (Profile.update
          (sig := (onePacketN).behavioralSignature) assessment.strategy who
          ((assessment.strategy who).withLaw site.1
            (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
              scale_le_one (slots := slots) n ((onePacketN).agentAt site) option)))
          (2 * horizon + 1) history.1)
        (fun final => if failedState key final.state then 1 else 0) := by
    unfold lateHistoryFailure localHistoryRun
    refine expect_congr_on_support fun final reached => ?_
    have iff := agrees history supported forced final reached
    by_cases failed : failedState key final.state
    · simp only [iff.mpr failed, failed, ↓reduceIte]
    · simp only [mt iff.mp failed, failed, ↓reduceIte]
  rw [same]
  exact_mod_cast near

omit [Finite setup.intendedProtocol.History] in
/-- A law fails at least as often as its mass on a choice times that choice's
failure. -/
theorem localFailure_ge_apply (assessment : (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who)
    (failed : Set ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History)
    (law : PMF ((onePacketN).Choice who site.1)) (choice : (onePacketN).Choice who site.1) :
    (law choice).toReal * localFailure (2 * horizon + 1) assessment site failed
        (PMF.pure choice) ≤
      localFailure (2 * horizon + 1) assessment site failed law := by
  have finiteChoice : Finite ((onePacketN).Choice who site.1) :=
    (onePacketN).finite_choice_of_played ((onePacketN).site_mem_playedInformation site)
  let := Fintype.ofFinite ((onePacketN).Choice who site.1)
  have bounded := (bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup)
    horizon scheduler
  have actsOnce := ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
    (initialLaw setup) horizon scheduler).actsOnceWhereItMatters
  conv_rhs => rw [← PMF.bind_pure law]
  rw [localFailure_bind (2 * horizon + 1) assessment site bounded actsOnce, expect_eq_sum]
  exact Finset.single_le_sum (f := fun other => (law other).toReal *
      localFailure (2 * horizon + 1) assessment site failed (PMF.pure other))
    (fun other _ => mul_nonneg ENNReal.toReal_nonneg (localFailure_nonneg _ _ _ _ _))
    (Finset.mem_univ choice)

omit [Finite setup.intendedProtocol.History] in
/-- **Silence fails like waiting.** At a decision input, silence fails within
one minus the slot retention of the scale of the late option that waits. -/
theorem abs_localFailure_silence_sub_wait_le
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat} (n : ℕ) (assessment : (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who)
    (failed : Set ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    (choice : (onePacketN).Choice who site.1) (silent : choice.1 = some ⟨none⟩) :
    |localFailure (2 * horizon + 1) assessment site failed (PMF.pure choice) -
        localFailure (2 * horizon + 1) assessment site failed
          (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one (slots := slots) n ((onePacketN).agentAt site) none)| ≤
      1 - slotRetention (scale n) := by
  obtain ⟨info, decision⟩ := site
  change info = some (past, view) at atSite
  subst atSite
  have bounded := (bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup)
    horizon scheduler
  have actsOnce := ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
    (initialLaw setup) horizon scheduler).actsOnceWhereItMatters
  have retentionLe := slotRetention_le_one (scale_pos n).le (scale_le_one n)
  have retentionNonneg := slotRetention_nonneg (scale_pos n).le (scale_le_one n)
  have isSilence : choice = silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler
      who (some (past, view)) :=
    Subtype.ext (silent.trans (by
      simp only [silenceChoice, responseChoice]
      split <;> rfl))
  have mainEq : lateChoice setup leaks bounds (initialLaw setup) horizon scheduler (sequence n)
      who (some (past, view)) (none : LateOption slots) = PMF.pure choice := by
    rw [isSilence]
    simp only [lateChoice, lateResponse, PMF.pure_map]
    rfl
  have mass : ∀ other, (1 - (1 - slotRetention (scale n))) * ((PMF.pure choice) other).toReal ≤
      ((onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos scale_le_one
        (slots := slots) n ((onePacketN).agentAt ⟨some (past, view), decision⟩) none)
          other).toReal := fun other => by
    rw [sub_sub_cancel, ← mainEq]
    exact slotTrembledChoice_ge_main setup leaks bounds (initialLaw setup) horizon scheduler
      (scale_pos n).le (scale_le_one n) who _ _ _ _ other
  have upper := localFailure_le_of_mass (2 * horizon + 1) assessment
    (⟨some (past, view), decision⟩ : (onePacketN).InformationSite who) bounded actsOnce failed
    (1 - slotRetention (scale n)) (by linarith) _ _ mass
  have lower := localFailure_ge_apply setup leaks bounds horizon scheduler assessment
    (⟨some (past, view), decision⟩ : (onePacketN).InformationSite who) failed
    (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos scale_le_one
      (slots := slots) n ((onePacketN).agentAt ⟨some (past, view), decision⟩) none) choice
  have massSelf := mass choice
  rw [PMF.pure_apply_self, ENNReal.toReal_one, mul_one, sub_sub_cancel] at massSelf
  have failureLe := localFailure_le_one (2 * horizon + 1) assessment
    (⟨some (past, view), decision⟩ : (onePacketN).InformationSite who) failed (PMF.pure choice)
  have failureNonneg := localFailure_nonneg (2 * horizon + 1) assessment
    (⟨some (past, view), decision⟩ : (onePacketN).InformationSite who) failed (PMF.pure choice)
  have scaled := mul_le_mul_of_nonneg_right massSelf failureNonneg
  rw [abs_le]
  constructor <;> nlinarith

open Classical in
omit [Finite setup.intendedProtocol.History] in
/-- **Site commonness from late failure blindness.** Along a target sequence,
suppose that at every forced late delivery each late option fails, from every
forced history of the belief, within a path drift of a failure function of the
key, the option and the history's operational record; the belief mass outside
the forced region is within an unforced drift; and the belief's records give the
failure function within a belief drift of its expectation under a record law at
the key. If every marked choice at a forced late delivery fails within a
vanishing drift of some late option or surely, then the late options fail within
a vanishing drift of one minus a score of the late-delivery key, and so does
every marked choice or it fails surely. -/
theorem onePacket_siteCommonness (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat} (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (pathDrift unforcedDrift beliefDrift markDrift : ℕ → ℝ)
    (pathLimit : Tendsto pathDrift atTop (nhds 0))
    (unforcedLimit : Tendsto unforcedDrift atTop (nhds 0))
    (beliefLimit : Tendsto beliefDrift atTop (nhds 0))
    (markLimit : Tendsto markDrift atTop (nhds 0))
    (pathNonneg : ∀ n, 0 ≤ pathDrift n) (markNonneg : ∀ n, 0 ≤ markDrift n)
    (failureOf : ℕ → LateKey setup leaks → LateOption slots →
      List (Option (OperationalState setup leaks)) → ℝ)
    (recordLaw : ℕ → LateKey setup leaks → PMF (List (Option (OperationalState setup leaks))))
    (failureUnit : ∀ n key option record,
      0 ≤ failureOf n key option record ∧ failureOf n key option record ≤ 1)
    (pathwise : ∀ n who (site : (onePacketN).InformationSite who),
      ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
      ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
      ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
        (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
        ((onePacketN).agentAt site) →
      ∀ key, lateKey setup leaks who site.1 = some key → ∀ option,
      ∀ history ∈ ((targetSequence n).belief who site).support,
        ForcedState setup leaks who history.1.state →
        |lateHistoryFailure setup leaks bounds horizon scheduler (targetSequence n) site
            (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
              scale_le_one (slots := slots) n ((onePacketN).agentAt site) option) history -
          failureOf n key option
            (operationalRecord setup leaks bounds horizon scheduler history.1.trace)| ≤
          pathDrift n)
    (unforced : ∀ n who (site : (onePacketN).InformationSite who),
      ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
      ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
      ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
        (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
        ((onePacketN).agentAt site) →
      expect ((targetSequence n).belief who site) (fun history =>
        if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1) ≤ unforcedDrift n)
    (keyed : ∀ n who (site : (onePacketN).InformationSite who),
      ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
      ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
      ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
        (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
        ((onePacketN).agentAt site) →
      ∀ key, lateKey setup leaks who site.1 = some key → ∀ option,
      |expect (((targetSequence n).belief who site).map fun history =>
          operationalRecord setup leaks bounds horizon scheduler history.1.trace)
          (failureOf n key option) -
        expect (recordLaw n key) (failureOf n key option)| ≤ beliefDrift n)
    (marked : ∀ n who (site : (onePacketN).InformationSite who),
      ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
      ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
      ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
        (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
        ((onePacketN).agentAt site) →
      ∀ choice, onePacketCompared setup leaks bounds horizon scheduler who site choice →
        (∃ option,
          |onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n) site
              (PMF.pure choice) -
            onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n) site
              (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
                scale_le_one (slots := slots) n ((onePacketN).agentAt site) option)| ≤
            markDrift n) ∨
        onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n) site
          (PMF.pure choice) = 1) :
    ∃ (score : ℕ → Option (LateKey setup leaks) → LateOption slots → ℝ) (drift : ℕ → ℝ),
      Tendsto drift atTop (nhds 0) ∧ (∀ n, 0 ≤ drift n) ∧
      ∀ n who (site : (onePacketN).InformationSite who),
        ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
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
            (PMF.pure choice) = 1 := by
  refine ⟨fun n key option => match key with
      | none => 0
      | some key => 1 - expect (recordLaw n key) (failureOf n key option),
    fun n => pathDrift n + |unforcedDrift n| + |beliefDrift n| + markDrift n, ?_,
    fun n => add_nonneg (add_nonneg (add_nonneg (pathNonneg n) (abs_nonneg _)) (abs_nonneg _))
      (markNonneg n), ?_⟩
  · simpa using ((pathLimit.add unforcedLimit.abs).add beliefLimit.abs).add markLimit
  intro n who site notFree notOwing isKeyed
  obtain ⟨past, view, event, atSite, _, _⟩ := isKeyed.1
  obtain ⟨info, decision⟩ := site
  change info = some (past, view) at atSite
  subst atSite
  have optionNear : ∀ option,
      |onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n)
          ⟨some (past, view), decision⟩
          (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one (slots := slots) n
            ((onePacketN).agentAt ⟨some (past, view), decision⟩) option) -
        (1 - (match agentLateKey setup leaks bounds (initialLaw setup) horizon scheduler
            ((onePacketN).agentAt ⟨some (past, view), decision⟩) with
          | none => 0
          | some key => 1 - expect (recordLaw n key) (failureOf n key option)))| ≤
        pathDrift n + |unforcedDrift n| + |beliefDrift n| := by
    intro option
    have unit : ∀ history, 0 ≤ lateHistoryFailure setup leaks bounds horizon scheduler
        (targetSequence n) ⟨some (past, view), decision⟩
        (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one (slots := slots) n
          ((onePacketN).agentAt ⟨some (past, view), decision⟩) option) history ∧
        lateHistoryFailure setup leaks bounds horizon scheduler
          (targetSequence n) ⟨some (past, view), decision⟩
          (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one (slots := slots) n
            ((onePacketN).agentAt ⟨some (past, view), decision⟩) option) history ≤ 1 :=
      fun history => unit_expect _ _ fun final => by split <;> norm_num
    have path := expect_near_of_record ((targetSequence n).belief who ⟨some (past, view), decision⟩)
      (fun history => operationalRecord setup leaks bounds horizon scheduler history.1.trace)
      _ (failureOf n _ option) (fun history => ForcedState setup leaks who history.1.state)
      (pathDrift n) (pathNonneg n) unit (failureUnit n _ option)
      (pathwise n who ⟨some (past, view), decision⟩ notFree notOwing isKeyed _ rfl option)
    have mass := unforced n who ⟨some (past, view), decision⟩ notFree notOwing isKeyed
    have belief := keyed n who ⟨some (past, view), decision⟩ notFree notOwing isKeyed _ rfl
      option
    have bridge : onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n)
        ⟨some (past, view), decision⟩
        (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one (slots := slots) n
          ((onePacketN).agentAt ⟨some (past, view), decision⟩) option) =
        expect ((targetSequence n).belief who ⟨some (past, view), decision⟩) fun history =>
          lateHistoryFailure setup leaks bounds horizon scheduler (targetSequence n)
            ⟨some (past, view), decision⟩
            (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
              scale_le_one (slots := slots) n
              ((onePacketN).agentAt ⟨some (past, view), decision⟩) option) history :=
      expect_localRun _ _ _ _ _
    rw [bridge]
    change |expect _ _ - (1 - (1 - expect (recordLaw n _) (failureOf n _ option)))| ≤ _
    rw [sub_sub_cancel]
    have pathBounds := abs_le.mp path
    have beliefBounds := abs_le.mp belief
    rw [abs_le]
    constructor <;> linarith [le_abs_self (unforcedDrift n), le_abs_self (beliefDrift n)]
  refine ⟨fun option => (optionNear option).trans (by linarith [markNonneg n]),
    fun choice isMarked => ?_⟩
  rcases marked n who ⟨some (past, view), decision⟩ notFree notOwing isKeyed choice isMarked
    with
    ⟨option, close⟩ | sure
  · left
    refine ⟨option, ?_⟩
    have := optionNear option
    calc _ ≤ _ := abs_sub_le _ (onePacketSiteFailure setup leaks bounds horizon scheduler
            (targetSequence n) ⟨some (past, view), decision⟩
            (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
              scale_le_one (slots := slots) n
              ((onePacketN).agentAt ⟨some (past, view), decision⟩) option)) _
      _ ≤ _ := by linarith
  · exact Or.inr sure

omit [Finite setup.intendedProtocol.History] in
/-- At a late delivery every late option is the component of some part of the
agent's pool. -/
theorem exists_part_eq_late (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat} (n : ℕ)
    {agent : (onePacketN).InformationAgent (onePacketN).playedInformation}
    (isKeyed : ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
      (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler) agent)
    (option : LateOption slots) :
    ∃ part, freeKeyedComponent (free := FreeAgent setup leaks bounds horizon scheduler)
        (keyed := LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
        (key := agentLateKey setup leaks bounds (initialLaw setup) horizon scheduler)
        (onePacketUnforced setup leaks bounds horizon scheduler scale scale_pos scale_le_one n)
        (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one n)
        (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one (slots := slots) n) agent part =
      onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos scale_le_one
        n agent option := by
  obtain ⟨identify, componentEq⟩ := freeKeyedComponent_of_not_free
    (key := agentLateKey setup leaks bounds (initialLaw setup) horizon scheduler)
    (onePacketUnforced setup leaks bounds horizon scheduler scale scale_pos scale_le_one n)
    (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one n)
    (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one (slots := slots) n) isKeyed.2
  have keyedEq : ∀ keyedPart, ∃ part, identify part = keyedPart := fun keyedPart =>
    ⟨identify.symm keyedPart, identify.apply_symm_apply keyedPart⟩
  have optionPart : ∃ keyedPart, keyedComponent
      (keyed := ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
        (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler))
      (key := agentLateKey setup leaks bounds (initialLaw setup) horizon scheduler)
      (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one n)
      (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one (slots := slots) n) agent keyedPart =
      onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos scale_le_one
        n agent option := by
    unfold keyedComponent
    rw [keyedPool_of_keyed isKeyed]
    exact ⟨option, rfl⟩
  obtain ⟨keyedPart, keyedPartEq⟩ := optionPart
  obtain ⟨part, rfl⟩ := keyedEq keyedPart
  exact ⟨part, (componentEq part).trans keyedPartEq⟩

/-- The intended site at the projected view of a site, when that view is an
intended decision site. -/
def projectedSite {who : Player} {info : (application setup leaks).Info}
    (decision : setup.intendedModel.IsDecisionInfo who (projectView setup leaks who info)) :
    setup.intendedModel.InformationSite who :=
  ⟨projectView setup leaks who info, decision⟩

omit [Finite setup.intendedProtocol.History] in
/-- **Unintended commitments are dominated by any law with a decomposed
value.** For a well-formed setup, under a scheduler completing play, at a
debt-free decision input of `who` showing its turn at `event`, a choice
committing `event` without committing an intended value gains at most what a
law gains, up to twice the error of that law's decomposition against a
continuation value at least the exclusion payoff up to the error. -/
theorem unintendedCommitment_gain_le (wellFormed : setup.WellFormed)
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (assessment : (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who) {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? who = some event)
    (choice : (onePacketN).Choice who site.1) {response : (application setup leaks).Action}
    (chosen : choice.1 = some response) {material : (application setup leaks).Submission}
    (sends : response.transmission = some material) {candidate : Handle (graph setup)}
    (packet : material.call.packet = .commitment event candidate)
    (debtFree : SiteDebtFree setup leaks bounds horizon scheduler site)
    (unintended : ¬ IntendedCommitment setup leaks bounds horizon scheduler site choice)
    (law : PMF ((onePacketN).Choice who site.1)) {continuation error : ℝ}
    (low : excludedPayoff who ≤ continuation + error)
    (near : |onePacketSiteSuccess setup leaks bounds horizon scheduler parameter utility
        excludedPayoff assessment site law -
      (1 - onePacketSiteFailure setup leaks bounds horizon scheduler assessment site law) *
        continuation| ≤ error) :
    onePacketSiteGain setup leaks bounds horizon scheduler parameter utility excludedPayoff
        assessment site (PMF.pure choice) ≤
      onePacketSiteGain setup leaks bounds horizon scheduler parameter utility excludedPayoff
        assessment site law + 2 * error := by
  have support := unintendedCommitment_localRun_support bounds horizon scheduler wellFormed
    completes parameter utility excludedPayoff assessment site atSite turn choice chosen sends
    packet debtFree unintended
  have valueChoice : localValue (2 * horizon + 1)
      (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter utility
        excludedPayoff) (payoffComponent setup) assessment site (PMF.pure choice) =
      excludedPayoff who := by
    unfold localValue localLaw
    rw [expect_map]
    have constant := (expect_congr_on_support (g := fun _ => excludedPayoff who)
      fun final reached => support final reached).trans (expect_constant _ _)
    convert constant using 3
    rfl
  have valueLaw := localValue_eq_successValue_add (2 * horizon + 1)
    (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter utility
      excludedPayoff) (payoffComponent setup) assessment site
    (onePacketFailed setup leaks bounds horizon scheduler ((onePacketN).agentAt site))
    (excludedPayoff who)
    (onePacketFailed_pays setup leaks bounds horizon scheduler parameter utility excludedPayoff
      ((onePacketN).agentAt site)) law
  have failureNonneg := localFailure_nonneg (2 * horizon + 1) assessment site
    (onePacketFailed setup leaks bounds horizon scheduler ((onePacketN).agentAt site)) law
  have failureLe := localFailure_le_one (2 * horizon + 1) assessment site
    (onePacketFailed setup leaks bounds horizon scheduler ((onePacketN).agentAt site)) law
  have nearBounds := abs_le.mp near
  have errorNonneg : 0 ≤ error := (abs_nonneg _).trans near
  unfold onePacketSiteSuccess onePacketSiteFailure at nearBounds
  have scaled := mul_le_mul_of_nonneg_left (show excludedPayoff who - error ≤ continuation by
    linarith) (show 0 ≤ 1 - localFailure (2 * horizon + 1) assessment site
      (onePacketFailed setup leaks bounds horizon scheduler ((onePacketN).agentAt site)) law by
    linarith)
  have product := mul_nonneg failureNonneg errorNonneg
  change localGain (2 * horizon + 1) (readoutExclusion setup leaks bounds (initialLaw setup)
      horizon scheduler parameter utility excludedPayoff) (payoffComponent setup) assessment site
      (PMF.pure choice) ≤
    localGain (2 * horizon + 1) (readoutExclusion setup leaks bounds (initialLaw setup)
      horizon scheduler parameter utility excludedPayoff) (payoffComponent setup) assessment site
      law + 2 * error
  rw [localGain_eq_sub, localGain_eq_sub, valueChoice, valueLaw]
  nlinarith [nearBounds.1]

open Classical in
/-- The total absolute exclusion payoff over the players and the one-packet
histories: a bound on every expected payoff. -/
def onePacketPayoffBound : ℝ :=
  ∑ who : Player, ∑ history : ((bounds.onePacketMenu (runtime setup) leaks).protocol
      (initialLaw setup) horizon scheduler).History,
    |payoffComponent setup (readoutExclusion setup leaks bounds (initialLaw setup) horizon
      scheduler parameter utility excludedPayoff history) who|

omit [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
theorem onePacketPayoffBound_nonneg :
    0 ≤ onePacketPayoffBound setup leaks bounds horizon scheduler parameter utility
      excludedPayoff :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

omit [Finite setup.intendedProtocol.History] in
/-- **Site gains are bounded by the payoffs.** Every law's gain at a site is at
most twice the payoff bound in absolute value. -/
theorem abs_onePacketSiteGain_le (assessment : (onePacketN).BehavioralAssessment)
    {who : Player} (site : (onePacketN).InformationSite who)
    (law : PMF ((onePacketN).Choice who site.1)) :
    |onePacketSiteGain setup leaks bounds horizon scheduler parameter utility excludedPayoff
        assessment site law| ≤
      2 * onePacketPayoffBound setup leaks bounds horizon scheduler parameter utility
        excludedPayoff := by
  classical
  have pointwise : ∀ history : ((bounds.onePacketMenu (runtime setup) leaks).protocol
      (initialLaw setup) horizon scheduler).History,
      |payoffComponent setup (readoutExclusion setup leaks bounds (initialLaw setup) horizon
        scheduler parameter utility excludedPayoff history) who| ≤
        onePacketPayoffBound setup leaks bounds horizon scheduler parameter utility
          excludedPayoff := by
    intro history
    unfold onePacketPayoffBound
    refine le_trans ?_ (Finset.single_le_sum (fun player _ =>
      Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ who))
    convert Finset.single_le_sum (f := fun history : ((bounds.onePacketMenu (runtime setup)
        leaks).protocol (initialLaw setup) horizon scheduler).History =>
        |payoffComponent setup (readoutExclusion setup leaks bounds (initialLaw setup) horizon
          scheduler parameter utility excludedPayoff history) who|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ history) using 2
  have boundNonneg := onePacketPayoffBound_nonneg setup leaks bounds horizon scheduler parameter
    utility excludedPayoff
  have expectBound : ∀ law' : PMF ((bounds.onePacketMenu (runtime setup) leaks).protocol
      (initialLaw setup) horizon scheduler).History,
      |expect (law'.map (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler
        parameter utility excludedPayoff)) ((payoffComponent setup) · who)| ≤
        onePacketPayoffBound setup leaks bounds horizon scheduler parameter utility
          excludedPayoff := by
    intro law'
    rw [expect_map]
    exact expect_abs_le_of_bounded boundNonneg pointwise
  unfold onePacketSiteGain
  dsimp only
  unfold InformationModel.assessmentComparisonWith
  dsimp only
  have first := expectBound (((onePacketN).assessmentLawWith ((onePacketN).truncatedRunner
    (2 * horizon + 1)) assessment site ((assessment.strategy who).withLaw site.1 law)))
  have second := expectBound (((onePacketN).assessmentLawWith ((onePacketN).truncatedRunner
    (2 * horizon + 1)) assessment site (assessment.strategy who)))
  have := abs_sub _ _ |>.trans (add_le_add first second)
  linarith [abs_sub (expect (((onePacketN).assessmentLawWith ((onePacketN).truncatedRunner
    (2 * horizon + 1)) assessment site ((assessment.strategy who).withLaw site.1 law)).map
      (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter utility
        excludedPayoff)) ((payoffComponent setup) · who))
    (expect (((onePacketN).assessmentLawWith ((onePacketN).truncatedRunner
    (2 * horizon + 1)) assessment site (assessment.strategy who)).map
      (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter utility
        excludedPayoff)) ((payoffComponent setup) · who))]

omit [Finite setup.intendedProtocol.History] in
/-- **Trembles move a site gain by the scale.** The gain of a slot-trembled law
at a site is within six times the scale times bound of the gain of its main
law, when bound bounds the gain of every choice. -/
theorem abs_siteGain_slotTrembled_sub_le (assessment : (onePacketN).BehavioralAssessment)
    {who : Player} (site : (onePacketN).InformationSite who) {scale : ℝ}
    (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (main alternative slot : PMF ((onePacketN).Choice who site.1)) {bound : ℝ}
    (bounded : ∀ choice, |onePacketSiteGain setup leaks bounds horizon scheduler parameter
      utility excludedPayoff assessment site (PMF.pure choice)| ≤ bound) :
    |onePacketSiteGain setup leaks bounds horizon scheduler parameter utility excludedPayoff
        assessment site (slotTrembledChoice setup leaks bounds (initialLaw setup) horizon
          scheduler scale nonnegative le_one who site.1 main alternative slot) -
      onePacketSiteGain setup leaks bounds horizon scheduler parameter utility excludedPayoff
        assessment site main| ≤ 6 * scale * bound := by
  have : Finite ((onePacketN).Choice who site.1) :=
    (onePacketN).finite_choice_of_played ((onePacketN).site_mem_playedInformation site)
  let gain := fun law : PMF ((onePacketN).Choice who site.1) =>
    onePacketSiteGain setup leaks bounds horizon scheduler parameter utility excludedPayoff
      assessment site law
  have asExpect : ∀ law, gain law = expect law fun choice => gain (PMF.pure choice) := by
    intro law
    have bound := localGain_bind (2 * horizon + 1)
      (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter utility
        excludedPayoff) (payoffComponent setup) assessment site
      ((bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup) horizon scheduler)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall (initialLaw setup) horizon
        scheduler).actsOnceWhereItMatters law PMF.pure
    rw [PMF.bind_pure] at bound
    exact bound
  have boundNonneg : 0 ≤ bound := by
    obtain ⟨choice, _⟩ := main.support_nonempty
    exact (abs_nonneg _).trans (bounded choice)
  change |gain _ - gain main| ≤ _
  rw [asExpect, asExpect main]
  set value := fun choice => gain (PMF.pure choice)
  set target := expect main value
  have gap : ∀ law : PMF ((onePacketN).Choice who site.1), |expect law value - target| ≤
      2 * bound := by
    intro law
    have inside := abs_le.mp (expect_abs_le_of_bounded (μ := law) boundNonneg bounded)
    have targetInside := abs_le.mp (expect_abs_le_of_bounded (μ := main) boundNonneg bounded)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  unfold slotTrembledChoice
  rw [expect_mix_of_finite, expect_mix_of_finite, expect_mix_of_finite]
  set uniform := expect ((bounds.onePacketMenu (runtime setup) leaks).uniformPolicy
    (initialLaw setup) horizon scheduler who site.1) value
  set slotted := expect slot value
  set alternate := expect alternative value
  have regroup : scale ^ 3 * uniform + (1 - scale ^ 3) * (scale ^ 2 * slotted +
      (1 - scale ^ 2) * (scale * alternate + (1 - scale) * target)) - target =
      scale ^ 3 * (uniform - target) + (1 - scale ^ 3) * (scale ^ 2 * (slotted - target) +
        (1 - scale ^ 2) * (scale * (alternate - target))) := by ring
  rw [regroup]
  have cube : scale ^ 3 ≤ scale := pow_le_of_le_one nonnegative le_one (by norm_num)
  have square : scale ^ 2 ≤ scale := pow_le_of_le_one nonnegative le_one (by norm_num)
  have cubeLe : scale ^ 3 ≤ 1 := pow_le_one₀ nonnegative le_one
  have squareLe : scale ^ 2 ≤ 1 := pow_le_one₀ nonnegative le_one
  have u := abs_le.mp (gap ((bounds.onePacketMenu (runtime setup) leaks).uniformPolicy
    (initialLaw setup) horizon scheduler who site.1))
  have s := abs_le.mp (gap slot)
  have a := abs_le.mp (gap alternative)
  have cubeNonneg : 0 ≤ scale ^ 3 := pow_nonneg nonnegative 3
  have squareNonneg : 0 ≤ scale ^ 2 := pow_nonneg nonnegative 2
  rw [abs_le]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left u.1 cubeNonneg,
    mul_le_mul_of_nonneg_left u.2 cubeNonneg, mul_le_mul_of_nonneg_left s.1 squareNonneg,
    mul_le_mul_of_nonneg_left s.2 squareNonneg, mul_le_mul_of_nonneg_left a.1 nonnegative,
    mul_le_mul_of_nonneg_left a.2 nonnegative, mul_nonneg (sub_nonneg.mpr cubeLe)
      (sub_nonneg.mpr squareLe)]


omit [Finite setup.intendedProtocol.History] in
/-- **Late openings are a late option's main choice.** For a well-formed setup,
at a forced late delivery at which the player owes no failure, a choice
opening the event of its turn is the canonical disclosure, the main choice of
every late option sending at a slot, so it gains at most what that option gains,
up to six times the scale times a bound on the gains of the choices. -/
theorem lateOpening_siteGain_le (wellFormed : setup.WellFormed)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat} (n : ℕ) (assessment : (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who)
    (forced : ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site))
    (late : LateDelivery setup leaks who site.1)
    (debtFree : SiteDebtFree setup leaks bounds horizon scheduler site)
    (choice : (onePacketN).Choice who site.1)
    (atTurn : CommitsAtTurn setup leaks bounds horizon scheduler who site choice)
    {response : (application setup leaks).Action} (chosen : choice.1 = some response)
    {material : (application setup leaks).Submission}
    (sends : response.transmission = some material) {event : (graph setup).EventId}
    {handle : Handle (graph setup)} {raw : Raw L}
    (packet : material.call.packet = .opening event handle raw) (slot : Fin slots) {bound : ℝ}
    (bounded : ∀ choice, |onePacketSiteGain setup leaks bounds horizon scheduler parameter
      utility excludedPayoff assessment site (PMF.pure choice)| ≤ bound) :
    onePacketSiteGain setup leaks bounds horizon scheduler parameter utility excludedPayoff
        assessment site (PMF.pure choice) ≤
      onePacketSiteGain setup leaks bounds horizon scheduler parameter utility excludedPayoff
          assessment site (onePacketLate setup leaks bounds horizon scheduler sequence scale
            scale_pos scale_le_one (slots := slots) n ((onePacketN).agentAt site) (some slot)) +
        6 * scale n * bound := by
  have notOwed := debtFree
  obtain ⟨native, seen, forcedNative⟩ :=
    forcedAgent_of_not_free setup leaks bounds horizon scheduler forced
  obtain ⟨past, view, pending', atSite, pending, _⟩ := late
  rw [atSite] at pending
  obtain ⟨past, view, turnResponse, turnEvent, turnSite, turnChosen, submitted, turn⟩ :=
    atTurn
  rw [atSite, Option.some.injEq, Prod.mk.injEq] at turnSite
  obtain ⟨pastEq, viewEq⟩ := turnSite
  subst pastEq viewEq
  have sameResponse : turnResponse = response := Option.some.inj (turnChosen.symm.trans chosen)
  subst sameResponse
  have eventEq : turnEvent = event := by
    have named : (runtime setup).submittedEvent? leaks turnResponse = some event := by
      unfold EventGraphRuntime.submittedEvent?
      rw [sends]
      exact (congrArg (Payload.event? (graph setup)) packet).trans rfl
    exact Option.some.inj (submitted.symm.trans named)
  subst eventEq
  have pendingEq : pending' = turnEvent :=
    Option.some.inj ((pendingEvent_spec (setup := setup) pending).1.symm.trans turn)
  subst pendingEq
  obtain ⟨response', chosen', member⟩ := choice_response setup leaks bounds horizon scheduler
    site atSite choice
  have sameResponse : response' = turnResponse := Option.some.inj (chosen'.symm.trans chosen)
  subst sameResponse
  obtain ⟨payload, binding, checks, outputEq, codeEq, node⟩ :=
    onePacket_opening_node member sends packet
  -- A native history of the site in a forced state.
  have owed := notOwed ⟨native, seen⟩
  obtain ⟨info, decision⟩ := site
  change info = some (past, view) at atSite
  subst atSite
  obtain ⟨state, trace⟩ := native
  change (onePacketInformation setup leaks bounds horizon scheduler).infoOf who trace =
    some (past, view) at seen
  rw [onePacket_infoOf] at seen
  cases state with
  | none => cases seen
  | some control =>
  rcases control with ⟨remaining, actor, execution⟩
  by_cases active : actor = some who
  swap
  · simp only [ReactiveApplication.observe, active, ↓reduceIte] at seen
    cases seen
  subst active
  simp only [ReactiveApplication.observe, ↓reduceIte] at seen
  obtain ⟨pastEq, viewEq⟩ := Prod.mk.inj (Option.some.inj seen)
  subst pastEq viewEq
  have resolves := disclosureResolves_of_debtFree wellFormed trace who forcedNative owed
  obtain ⟨disclosed, sendsDisclosure⟩ := Option.ne_none_iff_exists'.mp
    (resolves _ pending who payload binding checks outputEq codeEq node)
  have responseEq := onePacket_opening_eq_disclosure trace who _ node disclosed sendsDisclosure
    response' member material sends ((congrArg (Payload.event? (graph setup)) packet).trans rfl)
  have lateEq := lateChoice_reveal (sequence n) trace who _ turn node slot
  have choiceEq : choice = responseChoice setup leaks bounds (initialLaw setup) horizon
      scheduler who _ ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
        (execution.observe (application setup leaks) who) _
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)) := by
    rw [← responseEq]
    apply Subtype.ext
    rw [chosen]
    simp only [responseChoice, member, ↓reduceDIte]
  have trembled := abs_siteGain_slotTrembled_sub_le setup leaks bounds horizon scheduler
    parameter utility excludedPayoff assessment _ (scale_pos n).le (scale_le_one n)
    (PMF.pure choice) (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon
      scheduler who _))
    (slotChoice setup leaks bounds (initialLaw setup) horizon scheduler (sequence n) who _)
    bounded
  have lawEq : onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one (slots := slots) n ((onePacketN).agentAt ⟨_, decision⟩) (some slot) =
      slotTrembledChoice setup leaks bounds (initialLaw setup) horizon scheduler (scale n)
        (scale_pos n).le (scale_le_one n) who _ (PMF.pure choice)
        (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who _))
        (slotChoice setup leaks bounds (initialLaw setup) horizon scheduler (sequence n) who
          _) := by
    change lateComponent setup leaks bounds (initialLaw setup) horizon scheduler (sequence n)
      (scale n) (scale_pos n).le (scale_le_one n) who _ (some slot) = _
    unfold lateComponent
    rw [lateEq, ← choiceEq]
  rw [lawEq]
  linarith [(abs_le.mp trembled).1]

omit [Finite setup.intendedProtocol.History] in
/-- **Owing sites have no gain.** Under a scheduler completing play, at a
decision input at which the player owes a failure, every law gains nothing:
the player gets its exclusion payoff on every continuation. -/
theorem onePacketSiteGain_eq_zero_of_owing
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (assessment : (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who) {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    (owing : ¬ SiteDebtFree setup leaks bounds horizon scheduler site)
    (law : PMF ((onePacketN).Choice who site.1)) :
    onePacketSiteGain setup leaks bounds horizon scheduler parameter utility excludedPayoff
      assessment site law = 0 := by
  have zero := (onePacketN).gain_eq_expect_historyGain
    ((onePacketN).truncatedRunner (2 * horizon + 1))
    (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter
      utility excludedPayoff) (payoffComponent setup) assessment
    (site, (assessment.strategy who).withLaw site.1 law)
  rw [expect_congr_on_support (g := fun _ => 0) (fun history _ =>
    historyGain_eq_zero_of_owes setup leaks bounds horizon scheduler parameter utility
      excludedPayoff completes assessment _ history
      (owes_of_not_siteDebtFree setup leaks bounds horizon scheduler
        (failureProfile setup.program) site atSite owing history)), expect_constant] at zero
  exact zero

omit [Finite setup.intendedProtocol.History] in
/-- **Owing agents gain nothing.** Under a scheduler completing play, at the
site of an agent owing a failure every law gains nothing: at an empty input the
player has a single choice, and otherwise it gets its exclusion payoff on every
continuation (`Vegas.onePacketSiteGain_eq_zero_of_owing`). -/
theorem localGain_eq_zero_of_owingAgent
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (assessment : (onePacketN).BehavioralAssessment) (who : Player)
    (site : (onePacketN).InformationSite who)
    (owing : OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site))
    (law : PMF ((onePacketN).Choice who site.1)) :
    localGain (2 * horizon + 1) (readoutExclusion setup leaks bounds (initialLaw setup) horizon
      scheduler parameter utility excludedPayoff) (payoffComponent setup) assessment site law =
      0 := by
  obtain ⟨info, decision⟩ := site
  cases info with
  | none =>
      have : Subsingleton ((onePacketN).Choice who none) :=
        InformationModel.subsingleton_choice_of_menu_subsingleton _ _ Set.subsingleton_singleton
      have same : law = assessment.strategy who none := PMF.ext fun choice => by
        rw [apply_eq_one_of_subsingleton _ choice, apply_eq_one_of_subsingleton _ choice]
      rw [same]
      exact localGain_self _ _ _ _ _
  | some input =>
      obtain ⟨history, point, decoded, owes⟩ := owing
      exact onePacketSiteGain_eq_zero_of_owing setup leaks bounds horizon scheduler parameter
        utility excludedPayoff completes assessment ⟨some input, decision⟩ rfl
        (fun debtFree => debtFree history point decoded owes) law

open Classical in
/-- The options of the certificate's lumping at a late key: the installed option
at the key, and the key's weights at every other key. -/
def certificateOptions {slots : Nat}
    (weights : ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (key : LateKey setup leaks) (option : LateOption slots) (other : LateKey setup leaks) :
    PMF (LateOption slots) :=
  if other = key then PMF.pure option
  else keyWeights setup leaks bounds horizon scheduler weights (some other)

omit [Finite setup.intendedProtocol.History] in
/-- **The certificate's components at forced decisions.** At a history in a
forced state of `who` acting at a decision with an event ready that `who` was
activated for, a profile assembled from the certificate's components plays the
late component of the key's weights while `who` has not sent for the event, and
the slot-trembled prescribed component once it has. -/
theorem certificate_strategyShape (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence) (n : ℕ) (who : Player)
    (history : (onePacketProtocol setup leaks bounds horizon scheduler).History)
    (remaining : Nat) (execution : (application setup leaks).Execution)
    (event : (graph setup).EventId)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (forcedState : ForcedState setup leaks who history.state)
    (ready : execution.application.config.cut.Ready event)
    (activated : ∃ entry ∈ execution.recall who, ActivatedAt setup leaks who event entry) :
    ((runtime setup).eventRecorded leaks (execution.recall who) event = false →
      (targetSequence n).strategy who
          (some (execution.recall who, execution.observe (application setup leaks) who)) =
        slotTrembledChoice setup leaks bounds (initialLaw setup) horizon scheduler (scale n)
          (scale_pos n).le (scale_le_one n) who
          (some (execution.recall who, execution.observe (application setup leaks) who))
          ((keyWeights setup leaks bounds horizon scheduler (weights n)
              (some (LateKey.ofView setup leaks who (execution.recall who)
                (execution.observe (application setup leaks) who)))).bind
            (lateChoice setup leaks bounds (initialLaw setup) horizon scheduler (sequence n) who
              (some (execution.recall who, execution.observe (application setup leaks) who))))
          (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who
            (some (execution.recall who, execution.observe (application setup leaks) who))))
          (slotChoice setup leaks bounds (initialLaw setup) horizon scheduler (sequence n) who
            (some (execution.recall who, execution.observe (application setup leaks) who)))) ∧
    ((runtime setup).eventRecorded leaks (execution.recall who) event = true →
      ∃ main : PMF ((onePacketModel setup leaks bounds (initialLaw setup) horizon
          scheduler).Choice who (some (execution.recall who,
            execution.observe (application setup leaks) who))),
        (main = honestChoice setup leaks bounds (initialLaw setup) horizon scheduler
            (sequence n) who (some (execution.recall who,
              execution.observe (application setup leaks) who)) ∨
          ∃ others : PMF (LateOption slots), main = others.bind
            (lateChoice setup leaks bounds (initialLaw setup) horizon scheduler (sequence n) who
              (some (execution.recall who,
                execution.observe (application setup leaks) who)))) ∧
        (targetSequence n).strategy who (some (execution.recall who,
            execution.observe (application setup leaks) who)) =
          slotTrembledChoice setup leaks bounds (initialLaw setup) horizon scheduler (scale n)
            (scale_pos n).le (scale_le_one n) who (some (execution.recall who,
              execution.observe (application setup leaks) who)) main
            (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler
              who (some (execution.recall who,
                execution.observe (application setup leaks) who))))
            (slotChoice setup leaks bounds (initialLaw setup) horizon scheduler (sequence n) who
              (some (execution.recall who,
                execution.observe (application setup leaks) who)))) := by
  have observed : (onePacketN).infoOf who history.trace =
      some (execution.recall who, execution.observe (application setup leaks) who) := by
    refine ((bounds.onePacketMenu (runtime setup) leaks).info (initialLaw setup) horizon
      scheduler who history.trace).trans ?_
    rw [current]
    simp [ReactiveApplication.observe]
  have running : ¬ (onePacketProtocol setup leaks bounds horizon scheduler).terminal
      history.state := by
    rw [current]
    rintro ⟨_, actorNone⟩
    cases actorNone
  have played := (onePacketN).mem_playedInformation (who := who) running
  rw [observed] at played
  have forced : forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup)
      horizon scheduler who (some (execution.recall who,
        execution.observe (application setup leaks) who)) :=
    observed ▸ forcedAgent_of_history history forcedState
  let agent : (onePacketN).InformationAgent (onePacketN).playedInformation :=
    ⟨who, ⟨_, played⟩⟩
  have notFree : ¬ FreeAgent setup leaks bounds horizon scheduler agent :=
    fun unforced => unforced forced
  have atAgent := (onePacketN).agentBehavior_at (onePacketN).playedInformation
    (onePacketFallback setup leaks bounds horizon scheduler)
    (fun agent => (weights n (onePacketPool setup leaks bounds horizon scheduler agent)).bind
      (freeKeyedComponent
        (onePacketUnforced setup leaks bounds horizon scheduler scale scale_pos scale_le_one n)
        (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one n)
        (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one (slots := slots) n) agent)) agent
  obtain ⟨entry, member, activatedAt⟩ := activated
  have owned : (graph setup).actor? event = some who :=
    (PublicView.ownTurn?_spec _ who event activatedAt).2
  have turn : execution.application.publicView.ownTurn? who = some event :=
    ownTurn?_of_ready setup execution.application ready owned
  constructor
  · intro unrecorded
    have late : LateDelivery setup leaks who (some (execution.recall who,
        execution.observe (application setup leaks) who)) :=
      ⟨_, _, event, rfl, pendingEvent_of_spec turn unrecorded, entry, member, activatedAt⟩
    have keyed : ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
        (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler) agent :=
      ⟨late, notFree⟩
    have weightsEq : keyWeights setup leaks bounds horizon scheduler (weights n)
        (some (LateKey.ofView setup leaks who (execution.recall who)
          (execution.observe (application setup leaks) who))) =
        weights n (.inr (some ⟨agentLateKey setup leaks bounds (initialLaw setup) horizon
          scheduler agent, ⟨agent, keyed⟩, rfl⟩)) := by
      have present : some (LateKey.ofView setup leaks who (execution.recall who)
          (execution.observe (application setup leaks) who)) ∈ Set.range
            fun agent : {agent : (onePacketN).InformationAgent (onePacketN).playedInformation //
              ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
                (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
                  agent} =>
            agentLateKey setup leaks bounds (initialLaw setup) horizon scheduler agent.1 :=
        ⟨⟨agent, keyed⟩, rfl⟩
      unfold keyWeights
      rw [dite_eq_left_of_eq_true (eq_true present)]
      rfl
    have mixture := freeKeyedMixture_of_keyed (key := agentLateKey setup leaks bounds
      (initialLaw setup) horizon scheduler) (weights n)
      (onePacketUnforced setup leaks bounds horizon scheduler scale scale_pos scale_le_one n)
      (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one n)
      (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one (slots := slots) n) notFree keyed
    rw [assembled n]
    change (onePacketN).agentBehavior _ _ _ agent.1 agent.2.1 = _
    rw [atAgent, mixture, weightsEq]
    exact bind_lateComponent setup leaks bounds (initialLaw setup) horizon scheduler
      (sequence n) _ (scale n) (scale_pos n).le (scale_le_one n) who _
  · intro recorded
    have notLate : ¬ LateDelivery setup leaks who (some (execution.recall who,
        execution.observe (application setup leaks) who)) := by
      rintro ⟨_, _, other, same, pending, _⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
      obtain ⟨otherTurn, _, _, unrecorded⟩ := pendingEvent_spec pending
      have sameEvent : other = event := Option.some.inj (otherTurn.symm.trans turn)
      subst sameEvent
      rw [recorded] at unrecorded
      cases unrecorded
    have unkeyed : ¬ ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
        (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler) agent :=
      fun keyed => notLate keyed.1
    have mixture := freeKeyedMixture_of_not_keyed (key := agentLateKey setup leaks bounds
      (initialLaw setup) horizon scheduler) (weights n)
      (onePacketUnforced setup leaks bounds horizon scheduler scale scale_pos scale_le_one n)
      (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one n)
      (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one (slots := slots) n) notFree unkeyed
    refine ⟨_, Or.inl rfl, ?_⟩
    rw [assembled n]
    change (onePacketN).agentBehavior _ _ _ agent.1 agent.2.1 = _
    rw [atAgent, mixture]
    rfl

/-- **The owner's debt is clear at an event.** The event has completed, or it is
ready and the owner owes no failure at the decoded point. -/
def DebtClear (who : Player) (event : (graph setup).EventId) :
    (application setup leaks).ProtocolState → Prop
  | none => True
  | some control => event ∈ control.execution.application.config.cut.completed ∨
      (control.execution.application.config.cut.Ready event ∧
        ∀ point, decodedPoint setup control.execution.application.config = some point →
          ¬ ProtocolState.OwesFailure who setup.program point)

/-- The event of the owner's turn at an information state, if any. -/
def siteTurnEvent (who : Player) : (application setup leaks).Info → Option (graph setup).EventId
  | none => none
  | some (_, view) => view.application.publicView.ownTurn? who

/-- **States through a debt-free site.** States consistent with a site at which
the owner's debt is clear at the site's turn event. -/
def SiteThrough (who : Player) (info : (application setup leaks).Info)
    (state : (application setup leaks).ProtocolState) : Prop :=
  SiteConsistent who info state ∧
    ∀ event, siteTurnEvent setup leaks who info = some event → DebtClear setup leaks who event state

/-- **The activation past a site.** At a state whose owner's recall extends the
site's, the first entry past the site's recall was taken at a view showing the
site's pending event as the owner's turn. -/
def SiteActivated (who : Player) (info : (application setup leaks).Info)
    (state : (application setup leaks).ProtocolState) : Prop :=
  ∀ control, state = some control → ∀ entry rest,
    control.execution.recall who = infoRecall info ++ entry :: rest →
      ∀ event, pendingEvent setup leaks who info = some event →
        ActivatedAt setup leaks who event entry

/-- The site is a late delivery, or play past it recalls the activation of its
pending event. -/
def ActivationTracked (who : Player) (info : (application setup leaks).Info)
    (state : (application setup leaks).ProtocolState) : Prop :=
  LateDelivery setup leaks who info ∨ SiteActivated setup leaks who info state

omit [Fintype Player] [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- The control step appends to the recall of an acting player one entry taken at
its current view, and keeps every other player's recall. -/
theorem controlStep_recall_entry (players : Player → (application setup leaks).Policy)
    (control : (application setup leaks).Control) {next : (application setup leaks).ProtocolState}
    (member : next ∈ ((application setup leaks).controlStep (initialLaw setup) horizon scheduler
      players (some control)).support) (who : Player) :
    ∃ control', next = some control' ∧
      (control.actor = some who → ∃ entry : (application setup leaks).PlayerEntry,
        entry.beforeView = control.execution.observe (application setup leaks) who ∧
          control'.execution.recall who = control.execution.recall who ++ [entry]) ∧
      (control.actor ≠ some who →
        control'.execution.recall who = control.execution.recall who) := by
  rcases control with ⟨remaining, actor, execution⟩
  unfold ReactiveApplication.controlStep at member
  cases actor with
  | none =>
      have idle : (none : Option Player) ≠ some who := fun same => by cases same
      cases remaining with
      | zero =>
          exact ⟨_, (PMF.mem_support_pure_iff _ _).mp member, fun acting => (idle acting).elim,
            fun _ => rfl⟩
      | succ remaining =>
          obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ member)
          obtain ⟨next', supported, rfl⟩ := PMF.support_map .. ▸ moved
          exact ⟨_, rfl, fun acting => (idle acting).elim, fun _ => congrFun
            ((application setup leaks).environmentStep_recall execution next' command supported)
            who⟩
  | some actor =>
      simp only [ReactiveApplication.actor, Option.bind_some] at member
      rw [PMF.mem_support_bind_iff] at member
      obtain ⟨action, _, reached⟩ := member
      refine ⟨_, (PMF.mem_support_pure_iff _ _).mp reached, ?_, ?_⟩
      · intro acting
        cases Option.some.inj acting
        simp only [↓reduceIte, Option.getD_some, ReactiveApplication.Execution.respond]
        rcases action with ⟨_ | _⟩ <;> exact ⟨_, rfl, rfl⟩
      · intro idle
        have different : who ≠ actor := fun same => idle (by rw [same])
        simp only [↓reduceIte, Option.getD_some]
        exact (application setup leaks).respond_recall_other execution actor who different _

omit [Fintype Player] [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **The activation stays tracked along play.** A control step from a state
consistent with a site keeps the activation of its pending event tracked: the
first entry past the site's recall is taken at the site's own view. -/
theorem activationTracked_step (players : Player → (application setup leaks).Policy)
    (who : Player) (info : (application setup leaks).Info)
    {state : (application setup leaks).ProtocolState} (consistent : SiteConsistent who info state)
    (tracked : ActivationTracked setup leaks who info state)
    {next : (application setup leaks).ProtocolState}
    (member : next ∈ ((application setup leaks).controlStep (initialLaw setup) horizon scheduler
      players state).support) :
    ActivationTracked setup leaks who info next := by
  rcases tracked with late | activated
  · exact Or.inl late
  right
  cases state with
  | none => exact consistent.elim
  | some control =>
      obtain ⟨control', rfl, acted, idle⟩ := controlStep_recall_entry setup leaks horizon
        scheduler players control member who
      intro other otherEq entry rest recallEq event pending
      have same := Option.some.inj otherEq
      subst same
      rcases consistent with ⟨isSome, atSite⟩ | ⟨first, earlier, longer⟩
      · have acting : control.actor = some who := by
          by_contra notActing
          simp only [ReactiveApplication.observe, notActing, ↓reduceIte] at atSite
          rw [← atSite] at isSome
          cases isSome
        obtain ⟨added, before, appended⟩ := acted acting
        simp only [ReactiveApplication.observe, acting, ↓reduceIte] at atSite
        subst atSite
        rw [appended] at recallEq
        change control.execution.recall who ++ [added] =
          control.execution.recall who ++ entry :: rest at recallEq
        obtain ⟨rfl, -⟩ := List.cons.inj (List.append_cancel_left recallEq)
        unfold ActivatedAt
        rw [before]
        exact (pendingEvent_spec (setup := setup) pending).1
      · have activatedFirst := activated _ rfl first earlier longer event pending
        by_cases acting : control.actor = some who
        · obtain ⟨added, _, appended⟩ := acted acting
          rw [appended, longer, List.append_assoc, List.cons_append] at recallEq
          obtain ⟨rfl, -⟩ := List.cons.inj (List.append_cancel_left recallEq)
          exact activatedFirst
        · rw [idle acting, longer] at recallEq
          obtain ⟨rfl, -⟩ := List.cons.inj (List.append_cancel_left recallEq)
          exact activatedFirst

omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- The histories of a site track the activation of its pending event: their
owner's recall is the site's. -/
theorem siteActivated_of_history {who : Player} {site : (onePacketN).InformationSite who}
    (history : (onePacketN).InformationHistory who site.1) :
    SiteActivated setup leaks who site.1 history.1.state := by
  obtain ⟨⟨state, trace⟩, seen⟩ := history
  change (onePacketInformation setup leaks bounds horizon scheduler).infoOf who trace = site.1
    at seen
  rw [onePacket_infoOf] at seen
  intro control current entry rest recallEq event pending
  change state = some control at current
  rw [current] at seen
  by_cases acting : control.actor = some who
  · simp only [ReactiveApplication.observe, acting, ↓reduceIte] at seen
    rw [← seen] at recallEq
    change control.execution.recall who = control.execution.recall who ++ entry :: rest
      at recallEq
    have lengths := congrArg List.length recallEq
    simp at lengths
  · simp only [ReactiveApplication.observe, acting, ↓reduceIte] at seen
    rw [← seen] at pending
    cases pending

omit [Fintype Player] [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **Debt stays clear along play.** A control step from an initialized state
keeps the owner's debt clear at an event: the configuration is unchanged, or the
one ready event completes, so a ready event either stays ready with the same
decoded point or completes. -/
theorem debtClear_step (players : Player → (application setup leaks).Policy)
    (who : Player) (event : (graph setup).EventId) {control : (application setup leaks).Control}
    (clear : DebtClear setup leaks who event (some control))
    {next : (application setup leaks).ProtocolState}
    (member : next ∈ ((application setup leaks).controlStep (initialLaw setup) horizon scheduler
      players (some control)).support) :
    DebtClear setup leaks who event next := by
  obtain ⟨control', rfl, step⟩ := controlStep_configStep (horizon := horizon)
    (scheduler := scheduler) players control member
  change control'.execution.application.config = control.execution.application.config ∨ _
    at step
  rcases step with same | ⟨completed, completedReady, action, completedMember⟩
  · change event ∈ control'.execution.application.config.cut.completed ∨ _
    rw [same]
    exact clear
  · change event ∈ control'.execution.application.config.cut.completed ∨ _
    left
    rw [control.execution.application.config.step_cut completed completedReady action _
      completedMember, EventOrder.Cut.mem_complete]
    rcases clear with done | ⟨ready, _⟩
    · exact Or.inr done
    · exact Or.inl (setup.eventGraph.sequentialize_ready_unique _ ready completedReady)

open Classical in
omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **The site shape of an installed late component, through the site.** As
`Vegas.siteComponentShape_of_installed`, for a predicate of states refining
consistency with the site, with the strategy's shape asked only at the site's
turn event at states of the predicate, and the activation of the turn event
recalled at the predicate's states past the site. -/
theorem siteComponentShape_of_installed_within
    (assessment : setup.intendedModel.BehavioralAssessment)
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) {slots : Nat} {who : Player}
    (site : (onePacketN).InformationSite who)
    {key : LateKey setup leaks} (siteKey : lateKey setup leaks who site.1 = some key)
    (option : LateOption slots) (weights : LateKey setup leaks → PMF (LateOption slots))
    (profile : ∀ player, (onePacketN).BehavioralPolicy player)
    (strategy : (onePacketN).BehavioralPolicy who)
    (allowed : (application setup leaks).ProtocolState → Prop)
    (within : ∀ state, allowed state → SiteConsistent who site.1 state)
    (installed : profile who site.1 =
      slotTrembledChoice setup leaks bounds (initialLaw setup) horizon scheduler scale
        nonnegative le_one who site.1
        ((PMF.pure option).bind (lateChoice setup leaks bounds (initialLaw setup) horizon
          scheduler assessment who site.1))
        (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who
          site.1))
        (slotChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment who
          site.1))
    (away : ∀ info, info ≠ site.1 → profile who info = strategy info)
    (activated : ∀ event, (PublicationTurn key event ∨ ∃ payload, BindingTurn key event payload) →
      ∀ (remaining : Nat) (execution : (application setup leaks).Execution),
        allowed (some ⟨remaining, some who, execution⟩) →
        (∃ entry rest, execution.recall who = infoRecall site.1 ++ entry :: rest) →
          ∃ entry ∈ execution.recall who, ActivatedAt setup leaks who event entry)
    (strategyShape : ∀ (history : (onePacketProtocol setup leaks bounds horizon
        scheduler).History) (remaining : Nat) (execution : (application setup leaks).Execution)
        (event : (graph setup).EventId),
      (PublicationTurn key event ∨ ∃ payload, BindingTurn key event payload) →
      history.state = some ⟨remaining, some who, execution⟩ →
      allowed history.state →
      ForcedState setup leaks who history.state →
      execution.application.config.cut.Ready event →
      (∃ entry ∈ execution.recall who, ActivatedAt setup leaks who event entry) →
      ((runtime setup).eventRecorded leaks (execution.recall who) event = false →
        strategy (some (execution.recall who, execution.observe (application setup leaks) who)) =
          slotTrembledChoice setup leaks bounds (initialLaw setup) horizon scheduler scale
            nonnegative le_one who (some (execution.recall who,
              execution.observe (application setup leaks) who))
            ((weights (LateKey.ofView setup leaks who (execution.recall who)
                (execution.observe (application setup leaks) who))).bind
              (lateChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment who
                (some (execution.recall who, execution.observe (application setup leaks) who))))
            (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who
              (some (execution.recall who, execution.observe (application setup leaks) who))))
            (slotChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment who
              (some (execution.recall who, execution.observe (application setup leaks) who)))) ∧
      ((runtime setup).eventRecorded leaks (execution.recall who) event = true →
        ∃ main : PMF ((onePacketModel setup leaks bounds (initialLaw setup) horizon
            scheduler).Choice who (some (execution.recall who,
              execution.observe (application setup leaks) who))),
          (main = honestChoice setup leaks bounds (initialLaw setup) horizon scheduler
              assessment who (some (execution.recall who,
                execution.observe (application setup leaks) who)) ∨
            ∃ others : PMF (LateOption slots), main = others.bind
              (lateChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment who
                (some (execution.recall who,
                  execution.observe (application setup leaks) who)))) ∧
          strategy (some (execution.recall who,
              execution.observe (application setup leaks) who)) =
            slotTrembledChoice setup leaks bounds (initialLaw setup) horizon scheduler scale
              nonnegative le_one who (some (execution.recall who,
                execution.observe (application setup leaks) who)) main
              (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler
                who (some (execution.recall who,
                  execution.observe (application setup leaks) who))))
              (slotChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment who
                (some (execution.recall who,
                  execution.observe (application setup leaks) who))))) :
    SiteComponentShape assessment scale nonnegative le_one
      (fun other => if other = key then PMF.pure option else weights other) key profile
      allowed := by
  have ownerEq : key.owner = who := owner_of_lateKey siteKey
  subst ownerEq
  intro event turn history remaining execution current allowedState forced ready
  have consistent := within _ allowedState
  rw [current] at consistent
  by_cases atSite : (application setup leaks).observe key.owner
      (some ⟨remaining, some key.owner, execution⟩) = site.1
  · have infoEq : site.1 = some (execution.recall key.owner,
        execution.observe (application setup leaks) key.owner) := by
      rw [← atSite]
      simp only [ReactiveApplication.observe, ↓reduceIte]
    have keyEq : LateKey.ofView setup leaks key.owner (execution.recall key.owner)
        (execution.observe (application setup leaks) key.owner) = key := by
      rw [infoEq] at siteKey
      exact Option.some.inj siteKey
    rw [infoEq] at installed
    constructor
    · intro _
      rw [installed]
      beta_reduce
      rw [keyEq]
      simp only [↓reduceIte]
    · intro _
      exact ⟨_, Or.inr ⟨PMF.pure option, rfl⟩, installed⟩
  · have notSite : some (execution.recall key.owner,
        execution.observe (application setup leaks) key.owner) ≠ site.1 := by
      intro same
      apply atSite
      rw [← same]
      simp only [ReactiveApplication.observe, ↓reduceIte]
    have keyNe : LateKey.ofView setup leaks key.owner (execution.recall key.owner)
        (execution.observe (application setup leaks) key.owner) ≠ key := fun same =>
      atSite (siteConsistent_key siteKey consistent same)
    have longer : ∃ entry rest, execution.recall key.owner =
        infoRecall site.1 ++ entry :: rest := by
      rcases consistent with ⟨_, sameInfo⟩ | longer
      · exact (atSite sameInfo).elim
      · exact longer
    have recalledActivation := activated event turn remaining execution
      (current ▸ allowedState) longer
    have shapes := strategyShape history remaining execution event turn current allowedState
      forced ready recalledActivation
    rw [away _ notSite]
    beta_reduce
    simp only [keyNe, ↓reduceIte]
    exact shapes

omit [Finite setup.intendedProtocol.History] in
/-- **The site shape of the certificate at a pending site.** At a late delivery
or first activation of `who`, the profile installing a late option at the site
and otherwise following a profile assembled from the certificate's components
has the site shape over a predicate of states consistent with the site that
tracks the activation of its pending event, with the installed option at the
site's key and the key weights elsewhere. -/
theorem certificate_siteComponentShape_of_pending
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence) (n : ℕ) {who : Player}
    (site : (onePacketN).InformationSite who)
    (pendingSite : LateDelivery setup leaks who site.1 ∨ FirstActivation setup leaks who site.1)
    {key : LateKey setup leaks} (siteKey : lateKey setup leaks who site.1 = some key)
    (option : LateOption slots) (allowed : (application setup leaks).ProtocolState → Prop)
    (within : ∀ state, allowed state → SiteConsistent who site.1 state)
    (tracked : ∀ state, allowed state → ActivationTracked setup leaks who site.1 state) :
    SiteComponentShape (sequence n) (scale n) (scale_pos n).le (scale_le_one n)
      (certificateOptions setup leaks bounds horizon scheduler (weights n) key option) key
      (Profile.update (sig := (onePacketN).behavioralSignature) (targetSequence n).strategy who
        (((targetSequence n).strategy who).withLaw site.1
          (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one (slots := slots) n ((onePacketN).agentAt site) option)))
      allowed := by
  obtain ⟨past, view, pendingEvent', atSite, pending⟩ : ∃ past view event,
      site.1 = some (past, view) ∧ pendingEvent setup leaks who site.1 = some event := by
    rcases pendingSite with ⟨past, view, event, atSite, pending, _⟩ |
      ⟨past, view, event, atSite, pending, _⟩ <;> exact ⟨past, view, event, atSite, pending⟩
  have turn : view.application.publicView.ownTurn? who = some pendingEvent' := by
    have pendingHere := pending
    rw [atSite] at pendingHere
    exact (pendingEvent_spec pendingHere).1
  refine siteComponentShape_of_installed_within setup leaks bounds horizon scheduler (sequence n)
    (scale n) (scale_pos n).le (scale_le_one n) site siteKey option
    (fun other => keyWeights setup leaks bounds horizon scheduler (weights n) (some other))
    _ ((targetSequence n).strategy who) allowed within ?_ ?_ ?_ ?_
  · rw [Profile.update_same, BehavioralPolicy.withLaw_self, PMF.pure_bind]
    rfl
  · intro info different
    rw [Profile.update_same, BehavioralPolicy.withLaw_of_ne _ _ _ different]
  · intro event decided remaining execution allowedState longer
    have keyTurn : key.current.1.ownTurn? key.owner = some event := by
      rcases decided with publication | ⟨payload, binding⟩
      · exact publication.1
      · exact binding.1
    have sameEvent : event = pendingEvent' := by
      rw [atSite] at siteKey
      simp only [lateKey, Option.some.injEq] at siteKey
      subst siteKey
      exact Option.some.inj (keyTurn.symm.trans turn)
    subst sameEvent
    obtain ⟨entry, rest, recallEq⟩ := longer
    rcases tracked _ allowedState with late | activated
    · obtain ⟨past', view', event', atSite', pending', earlier, member, activatedAt⟩ := late
      have sameEvent : event' = event := Option.some.inj (pending'.symm.trans pending)
      subst sameEvent
      refine ⟨earlier, ?_, activatedAt⟩
      rw [recallEq]
      exact List.mem_append_left _ (by rw [atSite']; exact member)
    · refine ⟨entry, ?_, activated _ rfl entry rest recallEq event pending⟩
      rw [recallEq]
      exact List.mem_append_right _ (List.mem_cons.mpr (Or.inl rfl))
  · intro history remaining execution event _ current _ forcedState ready activated
    exact certificate_strategyShape setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence assembled n who history remaining execution event
      current forcedState ready activated

omit [Finite setup.intendedProtocol.History] in
/-- **The site shape of the certificate at a late delivery.** At a late
delivery of `who`, the profile installing a late option at the site and
otherwise following a profile assembled from the certificate's components has
the site shape, with the installed option at the site's key and the key weights
elsewhere (`Vegas.certificate_siteComponentShape_of_pending`). -/
theorem certificate_siteComponentShape
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence) (n : ℕ) {who : Player}
    (site : (onePacketN).InformationSite who) (late : LateDelivery setup leaks who site.1)
    {key : LateKey setup leaks} (siteKey : lateKey setup leaks who site.1 = some key)
    (option : LateOption slots) (allowed : (application setup leaks).ProtocolState → Prop)
    (within : ∀ state, allowed state → SiteConsistent who site.1 state) :
    SiteComponentShape (sequence n) (scale n) (scale_pos n).le (scale_le_one n)
      (certificateOptions setup leaks bounds horizon scheduler (weights n) key option) key
      (Profile.update (sig := (onePacketN).behavioralSignature) (targetSequence n).strategy who
        (((targetSequence n).strategy who).withLaw site.1
          (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one (slots := slots) n ((onePacketN).agentAt site) option)))
      allowed :=
  certificate_siteComponentShape_of_pending setup leaks bounds horizon scheduler sequence scale
    scale_pos scale_le_one weights targetSequence assembled n site (Or.inl late) siteKey option
    allowed within fun _ _ => Or.inl late

/-- The gain of a deviation at a site of the intended game under the exclusion
payoff: the expected exclusion payoff of the deviation minus that of the
assessment. -/
def intendedSiteGain (assessment : setup.intendedModel.BehavioralAssessment) {who : Player}
    (deviation : setup.intendedModel.AssessmentDeviation who) : ℝ :=
  let comparison := setup.intendedModel.assessmentComparisonWith
    (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
    (intendedReadoutExclusion setup parameter utility excludedPayoff) assessment who deviation
  expect comparison.alternative ((payoffComponent setup) · who) -
    expect comparison.prescribed ((payoffComponent setup) · who)

omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **The histories of a debt-free pending site pass through it.** At a late
delivery or first activation whose owner owes no failure, every history of the
site's belief is at a state consistent with the site at which the owner's debt
is clear at the site's turn event. -/
theorem siteThrough_of_pendingHistory {who : Player} {site : (onePacketN).InformationSite who}
    (pendingSite : LateDelivery setup leaks who site.1 ∨ FirstActivation setup leaks who site.1)
    (debtFree : SiteDebtFree setup leaks bounds horizon scheduler site)
    {key : LateKey setup leaks} (siteKey : lateKey setup leaks who site.1 = some key)
    (history : (onePacketN).InformationHistory who site.1) :
    SiteThrough setup leaks who site.1 history.1.state := by
  refine ⟨siteConsistent_of_history siteKey history, fun event siteTurn => ?_⟩
  obtain ⟨past, view, pending', atSite, pending⟩ : ∃ past view event,
      site.1 = some (past, view) ∧ pendingEvent setup leaks who site.1 = some event := by
    rcases pendingSite with ⟨past, view, event, atSite, pending, _⟩ |
      ⟨past, view, event, atSite, pending, _⟩ <;> exact ⟨past, view, event, atSite, pending⟩
  rw [atSite] at pending
  obtain ⟨turn, readyView, _, _⟩ := pendingEvent_spec (setup := setup) pending
  have sameEvent : pending' = event := by
    rw [atSite] at siteTurn
    exact Option.some.inj (turn.symm.trans siteTurn)
  subst sameEvent
  have notOwed := debtFree history
  obtain ⟨⟨state, trace⟩, seen⟩ := history
  change (onePacketInformation setup leaks bounds horizon scheduler).infoOf who trace = site.1
    at seen
  rw [onePacket_infoOf, atSite] at seen
  cases state with
  | none => cases seen
  | some control =>
  rcases control with ⟨remaining, actor, execution⟩
  by_cases active : actor = some who
  swap
  · simp only [ReactiveApplication.observe, active, ↓reduceIte] at seen
    cases seen
  subst active
  simp only [ReactiveApplication.observe, ↓reduceIte] at seen
  obtain ⟨pastEq, viewEq⟩ := Prod.mk.inj (Option.some.inj seen)
  subst pastEq viewEq
  exact Or.inr ⟨(State.publicView_eventReady _ pending').mp readyView, notOwed⟩


omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **The histories of a debt-free late delivery pass through it**
(`Vegas.siteThrough_of_pendingHistory`). -/
theorem siteThrough_of_history {who : Player} {site : (onePacketN).InformationSite who}
    (late : LateDelivery setup leaks who site.1)
    (debtFree : SiteDebtFree setup leaks bounds horizon scheduler site)
    {key : LateKey setup leaks} (siteKey : lateKey setup leaks who site.1 = some key)
    (history : (onePacketN).InformationHistory who site.1) :
    SiteThrough setup leaks who site.1 history.1.state :=
  siteThrough_of_pendingHistory setup leaks bounds horizon scheduler (Or.inl late) debtFree
    siteKey history

/-- **The certificate's lumping at debt-free pending sites.** For an assembled
sequence, at every stage and for every owner, the native kernel of the profiles
installing the late options lumps onto the decision image at late deliveries
and first activations at which the owner owes no failure, with drift twice the
cube of the scale. At a first activation the installed wait option is silence up
to the scale's trembles. Play from such a site stays at states consistent with
it at which the owner's debt is clear at the site's turn event
(`Vegas.debtClear_step`) and the activation of its pending event is recalled
(`Vegas.activationTracked_step`), and the installed profiles have the site shape
there (`Vegas.certificate_siteComponentShape_of_pending`). -/
def certificateLumping (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat} (covers : bounds.CoversOutputValues) (capacity : 1 ≤ bounds.candidateCount)
    (slotsLe : slots ≤ bounds.candidateCount)
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence) (n : ℕ) (who : Player) :
    PendingLumpingOn (targetSequence n) who
      (fun site => (LateDelivery setup leaks who site.1 ∨ FirstActivation setup leaks who site.1) ∧
        SiteDebtFree setup leaks bounds horizon scheduler site)
      (fun site option => Profile.update (sig := (onePacketN).behavioralSignature)
        (targetSequence n).strategy who (((targetSequence n).strategy who).withLaw site.1
          (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one (slots := slots) n ((onePacketN).agentAt site) option)))
      DecisionFailed (scale n ^ 3 + scale n ^ 3)
      (DecisionImage (setup := setup) (leaks := leaks)) :=
  have nonnegative := (scale_pos n).le
  onePacketLateLumpingOn (targetSequence n) who
    (fun site => (LateDelivery setup leaks who site.1 ∨ FirstActivation setup leaks who site.1) ∧
      SiteDebtFree setup leaks bounds horizon scheduler site) _
    (by have := pow_nonneg nonnegative 3; linarith) (pow_nonneg nonnegative 3)
    (by linarith) (openingKernel bounds horizon scheduler
      (fun key option => lateOpeningSilence bounds horizon scheduler (sequence n) (scale n)
        nonnegative (scale_le_one n)
        (certificateOptions setup leaks bounds horizon scheduler (weights n) key option) key))
    (fun key option => lateBindingMoves bounds horizon scheduler (scale n) nonnegative
      (scale_le_one n)
      (certificateOptions setup leaks bounds horizon scheduler (weights n) key option) key)
    (fun site state => SiteThrough setup leaks who site.1 state ∧
      ActivationTracked setup leaks who site.1 state)
    (fun _ relevant _ siteKey history _ _ =>
      ⟨siteThrough_of_pendingHistory setup leaks bounds horizon scheduler relevant.1 relevant.2
        siteKey history, Or.inr (siteActivated_of_history setup leaks bounds horizon scheduler
          history)⟩)
    (fun site _ _ state through next member => by
      refine ⟨?_, activationTracked_step setup leaks horizon scheduler _ who site.1 through.1.1
        through.2 member⟩
      cases state with
      | none => exact through.1.1.elim
      | some control =>
          exact ⟨siteConsistent_step _ who site.1 through.1.1 member, fun event siteTurn =>
            debtClear_step setup leaks horizon scheduler _ who event
              (through.1.2 event siteTurn) member⟩)
    (fun site relevant key siteKey option => ownerStepClose_of_openingLaw bounds _ key option _
      (ownerOpeningLaw_of_siteComponents (sequence n) covers (scale n) nonnegative
        (scale_le_one n) (certificateOptions setup leaks bounds horizon scheduler (weights n))
        key option _ _ (certificate_siteComponentShape_of_pending setup leaks bounds horizon
          scheduler sequence scale scale_pos scale_le_one weights targetSequence assembled n site
          relevant.1 siteKey option _ (fun _ through => through.1.1) fun _ through => through.2)))
    (fun site relevant key siteKey option => ownerBindingLaw_of_siteComponents (sequence n)
      covers capacity slotsLe (scale n) nonnegative (scale_le_one n)
      (certificateOptions setup leaks bounds horizon scheduler (weights n)) key option _ _
      (certificate_siteComponentShape_of_pending setup leaks bounds horizon scheduler sequence
        scale scale_pos scale_le_one weights targetSequence assembled n site relevant.1 siteKey
        option _ (fun _ through => through.1.1) fun _ through => through.2))

omit [Fintype Player] [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- A late delivery is a decision input showing the player's own turn. -/
theorem lateDelivery_input {who : Player} {info : (application setup leaks).Info}
    (late : LateDelivery setup leaks who info) :
    ∃ input : List (application setup leaks).PlayerEntry × (application setup leaks).PlayerView,
      info = some input ∧ ∃ event, input.2.application.publicView.ownTurn? who = some event := by
  obtain ⟨past, view, event, atSite, pending, _⟩ := late
  rw [atSite] at pending
  exact ⟨(past, view), atSite, event, (pendingEvent_spec (setup := setup) pending).1⟩

open Classical in
/-- **The base inputs of the one-packet certificate** for one source sequence:
the tremble scales and the obligations not yet discharged other than the value
decompositions and late commitments, each a statement along every fully mixed
Bayes sequence of profiles assembled from the certificate's components, at the
forced sites. -/
structure OnePacketBaseInputs (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (slots : Nat) where
  /-- The tremble scale at each index. -/
  scale : ℕ → ℝ
  scale_pos : ∀ n, 0 < scale n
  scale_le_one : ∀ n, scale n ≤ 1
  scale_vanishing : Tendsto scale atTop (nhds 0)
  /-- A bound on the gap between a continuation value and the exclusion payoff. -/
  gapBound : ℝ
  gapBound_nonneg : 0 ≤ gapBound
  /-- Every binding and publication value is a bounded value. -/
  covers : bounds.CoversOutputValues
  /-- Every value of an initial binding input is a bounded value. -/
  coversInputs : bounds.CoversInputValues
  /-- At least one prepared slot is bounded. -/
  capacity : 1 ≤ bounds.candidateCount
  /-- The late options use bounded slots. -/
  slotsLe : slots ≤ bounds.candidateCount
  /-- **Late records.** At late deliveries of agents that are not free and owe
  no failure, the belief's operational records give the certificate's lumped failure within a
  vanishing drift of its expectation under a law of records at the key. -/
  lateRecords : setup.PrivateInputsIndependent →
    ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon
      scheduler slots p)) (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence),
    (∀ n, (targetSequence n).IsFullyMixed) →
    (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
    ∃ beliefDrift : ℕ → ℝ, Tendsto beliefDrift atTop (nhds 0) ∧
      ∀ n who, ∃ recordLaw : LateKey setup leaks →
          PMF (List (Option (OperationalState setup leaks))),
        ∀ (site : (onePacketN).InformationSite who),
          ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
          ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
          ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
            (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
            ((onePacketN).agentAt site) →
          ∀ key, lateKey setup leaks who site.1 = some key → ∀ option,
          |expect (((targetSequence n).belief who site).map fun history =>
              operationalRecord setup leaks bounds horizon scheduler history.1.trace)
              (lumpedFailure setup leaks bounds horizon scheduler
                (certificateLumping setup leaks bounds horizon scheduler sequence scale scale_pos
                  scale_le_one covers capacity slotsLe weights targetSequence assembled n who)
                (2 * horizon + 1) key option) -
            expect (recordLaw key)
              (lumpedFailure setup leaks bounds horizon scheduler
                (certificateLumping setup leaks bounds horizon scheduler sequence scale scale_pos
                  scale_le_one covers capacity slotsLe weights targetSequence assembled n who)
                (2 * horizon + 1) key option)| ≤ beliefDrift n
  /-- **The honest counterparts** at every forced decision input at the player's
  own turn at which the player owes no failure, along every fully mixed Bayes
  sequence of assembled profiles. -/
  counterpartInputs : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon
      scheduler slots p)) (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
    OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos scale_le_one
      weights targetSequence →
    (∀ n, (targetSequence n).IsFullyMixed) →
    (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
    ∀ who (site : (onePacketN).InformationSite who),
      ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
      ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
      ∀ {past : List (application setup leaks).PlayerEntry}
        {view : (application setup leaks).PlayerView}, site.1 = some (past, view) →
      ∀ {event : (graph setup).EventId},
      view.application.publicView.ownTurn? who = some event →
      OnePacketCounterpartInputs setup leaks bounds horizon scheduler sequence targetSequence site
  /-- **The own and replay inputs** at every forced decision input at the
  player's own turn at which the player owes no failure, along every fully mixed
  Bayes sequence of assembled profiles. These are the sites with a projected
  decision (`Vegas.projectedDecision_of_forcedAgent`), late deliveries
  included. -/
  ownInputs : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon
      scheduler slots p)) (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
    OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos scale_le_one
      weights targetSequence →
    (∀ n, (targetSequence n).IsFullyMixed) →
    (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
    ∀ who (site : (onePacketN).InformationSite who),
      ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
      ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
      ∀ {past : List (application setup leaks).PlayerEntry}
        {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
        {event : (graph setup).EventId},
      view.application.publicView.ownTurn? who = some event →
      ∀ decision : setup.intendedModel.IsDecisionInfo who (projectView setup leaks who site.1),
      OnePacketOwnInputs setup leaks bounds horizon scheduler sequence targetSequence site
        (projectedSite setup leaks decision) atSite rfl
  /-- Some late option sends at a slot. -/
  slots_pos : 0 < slots

/-- **The forced-belief inputs** at a forced decision input at the player's own
turn at which the player owes no failure: the honest counterparts and the own
and replay inputs there. -/
def OnePacketBaseInputs.beliefInputs {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {slots : Nat}
    (inputs : OnePacketBaseInputs setup leaks bounds horizon scheduler sequence slots)
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence inputs.scale
      inputs.scale_pos inputs.scale_le_one weights targetSequence)
    (mixed : ∀ n, (targetSequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain)
    (who : Player) (site : (onePacketN).InformationSite who)
    (forced : ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site))
    (notOwing : ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site))
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? who = some event)
    (decision : setup.intendedModel.IsDecisionInfo who (projectView setup leaks who site.1)) :
    OnePacketBeliefInputs setup leaks bounds horizon scheduler sequence targetSequence site
      (projectedSite setup leaks decision) atSite rfl where
  toOnePacketCounterpartInputs := inputs.counterpartInputs weights targetSequence assembled mixed
    bayes who site forced notOwing atSite turn
  toOnePacketOwnInputs := inputs.ownInputs weights targetSequence assembled mixed bayes who site
    forced notOwing atSite turn decision

omit [Finite setup.intendedProtocol.History] in
open Classical in
/-- **Histories outside the forced region vanish at late deliveries.** For a
well-formed setup, along every fully mixed Bayes sequence of assembled profiles,
the belief mass outside the forced region at late deliveries of agents that are
not free and owe no failure vanishes uniformly: such a site is forced, debt free and at the
owner's turn, where the honest counterparts and the intended own completions
make it vanish (`Vegas.onePacket_unforcedVanishes`). -/
theorem OnePacketBaseInputs.lateUnforced {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {slots : Nat}
    (inputs : OnePacketBaseInputs setup leaks bounds horizon scheduler sequence slots)
    (wellFormed : setup.WellFormed)
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence inputs.scale
      inputs.scale_pos inputs.scale_le_one weights targetSequence)
    (mixed : ∀ n, (targetSequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) :
    ∃ unforcedDrift : ℕ → ℝ, Tendsto unforcedDrift atTop (nhds 0) ∧
      ∀ n who (site : (onePacketN).InformationSite who),
        ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
          (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
          ((onePacketN).agentAt site) →
        expect ((targetSequence n).belief who site) (fun history =>
          if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1) ≤
          unforcedDrift n := by
  let LateSite := fun {who : Player} (site : (onePacketN).InformationSite who) =>
    ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) ∧
      ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) ∧
      ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
        (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
        ((onePacketN).agentAt site)
  let mass := fun (n : ℕ) {who : Player} (site : (onePacketN).InformationSite who) =>
    expect ((targetSequence n).belief who site) (fun history =>
      if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1)
  let agentMass := fun (n : ℕ)
      (agent : (onePacketN).InformationAgent (onePacketN).playedInformation) =>
    if present : ∃ decision : (onePacketN).IsDecisionInfo agent.1 agent.2.1,
        LateSite (⟨agent.2.1, decision⟩ : (onePacketN).InformationSite agent.1) then
      mass n ⟨agent.2.1, present.1⟩ else 0
  have massNonneg : ∀ n agent, 0 ≤ agentMass n agent := fun n agent => by
    simp only [agentMass]
    split
    · exact expect_nonneg _ _ fun history _ => by split <;> norm_num
    · exact le_rfl
  refine ⟨fun n => ∑ agent, agentMass n agent, ?_,
    fun n who site notFree notOwing keyed => ?_⟩
  · rw [show (0 : ℝ) = ∑ _agent : (onePacketN).InformationAgent (onePacketN).playedInformation,
      (0 : ℝ) by simp]
    refine tendsto_finsetSum _ fun agent _ => ?_
    by_cases present : ∃ decision : (onePacketN).IsDecisionInfo agent.1 agent.2.1,
        LateSite (⟨agent.2.1, decision⟩ : (onePacketN).InformationSite agent.1)
    · simp only [agentMass, present, ↓reduceDIte]
      obtain ⟨input, atSite, event, turn⟩ := lateDelivery_input setup leaks present.2.2.2.1
      have notFree := present.2.1
      have notOwing := present.2.2.1
      have forced := forcedAgent_of_not_free setup leaks bounds horizon scheduler notFree
      have debtFree := siteDebtFree_of_not_owing setup leaks bounds horizon scheduler notOwing
      have decision := projectedDecision_of_forcedAgent wellFormed forced atSite turn debtFree
      exact onePacket_unforcedVanishes setup leaks bounds horizon scheduler wellFormed mixed bayes
        atSite forced
        (inputs.counterpartInputs weights targetSequence assembled mixed bayes agent.1
          ⟨agent.2.1, present.1⟩ notFree notOwing atSite turn)
        (inputs.ownInputs weights targetSequence assembled mixed bayes agent.1
          ⟨agent.2.1, present.1⟩ notFree notOwing atSite turn decision).ownIntended
    · simp only [agentMass, present, ↓reduceDIte]
      exact tendsto_const_nhds
  · have single := Finset.single_le_sum (fun agent _ => massNonneg n agent)
      (Finset.mem_univ ((onePacketN).agentAt site))
    refine le_trans (le_of_eq ?_) single
    have present : ∃ decision : (onePacketN).IsDecisionInfo who site.1,
        LateSite (⟨site.1, decision⟩ : (onePacketN).InformationSite who) :=
      ⟨site.2, notFree, notOwing, keyed⟩
    simp only [agentMass, present, ↓reduceDIte]
    rfl

open Classical in
/-- **The open inputs of the one-packet certificate other than the value
decompositions** for one source sequence: the base inputs and late commitments
of intended values. -/
structure OnePacketCoreInputs (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (slots : Nat) extends OnePacketBaseInputs setup leaks bounds horizon scheduler sequence
      slots where
  /-- **The gain transport.** Away from late deliveries, at a site where the
  player owes no failure, every choice committing an intended value at the
  player's own turn has an intended policy at the projected site whose gain at
  the projected belief bounds the choice's gain, up to a vanishing error and the
  belief mass of histories at which another player responded irregularly, times
  a bound on the intended history gains. -/
  valueTransport : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon
      scheduler slots p)) (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
    OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos scale_le_one
      weights targetSequence →
    (∀ n, (targetSequence n).IsFullyMixed) →
    (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
    ∃ (valueError : ℕ → ℝ) (bound : ℝ), Tendsto valueError atTop (nhds 0) ∧ 0 ≤ bound ∧
      ∀ n who (site : (onePacketN).InformationSite who) choice,
        ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ¬ ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
          (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
          ((onePacketN).agentAt site) →
        CommitsAtTurn setup leaks bounds horizon scheduler who site choice →
        SiteDebtFree setup leaks bounds horizon scheduler site →
        IntendedCommitment setup leaks bounds horizon scheduler site choice →
        ∀ (decision : setup.intendedModel.IsDecisionInfo who (projectView setup leaks who site.1))
          {past : List (application setup leaks).PlayerEntry}
          {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view)),
        ∃ policy : setup.intendedModel.BehavioralPolicy who,
          onePacketSiteGain setup leaks bounds horizon scheduler parameter utility excludedPayoff
              (targetSequence n) site (PMF.pure choice) ≤
            expect (((targetSequence n).belief who site).map
                (replayProjection setup leaks bounds horizon scheduler
                  (projectedSite setup leaks decision) site atSite rfl))
                (setup.intendedModel.historyGain
                  (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
                  (intendedReadoutExclusion setup parameter utility excludedPayoff)
                  (payoffComponent setup) (sequence n)
                  (projectedSite setup leaks decision, policy)) +
              valueError n +
              bound * expect ((targetSequence n).belief who site) (fun history =>
                if RegularTrace setup leaks bounds horizon scheduler (sequence n) who
                  history.1.trace then 0 else 1) ∧
          ∀ point, |setup.intendedModel.historyGain
              (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
              (intendedReadoutExclusion setup parameter utility excludedPayoff)
              (payoffComponent setup) (sequence n) (projectedSite setup leaks decision, policy)
              point| ≤ bound
  /-- **Late commitments of intended values.** At every forced late delivery at
  which the player owes no failure, every choice committing an intended value at
  the player's own turn gains at most what some late option gains plus a weight
  in [0, 1] times the gain of a source deviation at the projected site, up to a
  vanishing error. Sending now at a slot fails as the late option sending at
  that slot does whatever the committed value, and on success the committed
  value is worth its source continuation: the weight is the success probability
  and the deviation commits that value. -/
  lateCommitments : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon
      scheduler slots p)) (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
    OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos scale_le_one
      weights targetSequence →
    (∀ n, (targetSequence n).IsFullyMixed) →
    (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
    ∃ lateError : ℕ → ℝ, Tendsto lateError atTop (nhds 0) ∧
      ∀ n who (site : (onePacketN).InformationSite who) choice,
        ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
          (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
          ((onePacketN).agentAt site) →
        CommitsAtTurn setup leaks bounds horizon scheduler who site choice →
        SiteDebtFree setup leaks bounds horizon scheduler site →
        IntendedCommitment setup leaks bounds horizon scheduler site choice →
        ∀ decision : setup.intendedModel.IsDecisionInfo who (projectView setup leaks who site.1),
        ∃ (option : LateOption slots) (policy : setup.intendedModel.BehavioralPolicy who)
          (weight : ℝ), 0 ≤ weight ∧ weight ≤ 1 ∧
          onePacketSiteGain setup leaks bounds horizon scheduler parameter utility excludedPayoff
              (targetSequence n) site (PMF.pure choice) ≤
            onePacketSiteGain setup leaks bounds horizon scheduler parameter utility
                excludedPayoff (targetSequence n) site
                (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
                  scale_le_one (slots := slots) n ((onePacketN).agentAt site) option) +
              weight * intendedSiteGain setup parameter utility excludedPayoff (sequence n)
                (projectedSite setup leaks decision, policy) +
              lateError n

open Classical in
/-- **Best pool weights.** No alternative weights of a pool raise the summed
gain of its agents at the assessments of a sequence. -/
def OnePacketPoolBest (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat} (targetSequence : ℕ → (onePacketN).BehavioralAssessment) : Prop :=
  ∀ n (alternative : ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p)) p,
    ∑ agent ∈ Finset.univ.filter (fun agent => onePacketPool setup leaks bounds horizon
        scheduler agent = p),
      (if decision : (onePacketN).IsDecisionInfo agent.1 agent.2.1 then
        let comparison := (onePacketN).assessmentComparisonWith ((onePacketN).truncatedRunner
            (2 * horizon + 1))
          (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter
            utility excludedPayoff) (targetSequence n) agent.1
          (⟨agent.2.1, decision⟩, ((targetSequence n).strategy agent.1).withLaw agent.2.1
            ((alternative (onePacketPool setup leaks bounds horizon scheduler agent)).bind
              (freeKeyedComponent
                (onePacketUnforced setup leaks bounds horizon scheduler scale scale_pos
                  scale_le_one n)
                (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale
                  scale_pos scale_le_one n)
                (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
                  scale_le_one (slots := slots) n) agent)))
        expect comparison.alternative ((payoffComponent setup) · agent.1) -
          expect comparison.prescribed ((payoffComponent setup) · agent.1)
      else 0) ≤ 0

open Classical in
/-- **The open inputs of the one-packet certificate** for one source sequence:
the other open inputs and the value decompositions. -/
structure OnePacketOpenInputs (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (slots : Nat) extends OnePacketCoreInputs setup leaks bounds horizon scheduler parameter
      utility excludedPayoff sequence slots where
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
        ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
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
  continuation value up to a vanishing error, with gap at most the gap bound, or
  the site has no pending event; and the successful part of every marked choice
  and of the prescribed component is its success probability times that
  continuation value up to the error. -/
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
        ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ¬ ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
          (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
          ((onePacketN).agentAt site) →
        ((excludedPayoff who ≤ continuation n ((onePacketN).agentAt site) + error n ∧
            continuation n ((onePacketN).agentAt site) - excludedPayoff who ≤ gapBound) ∨
          pendingEvent setup leaks who site.1 = none) ∧
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


omit [Finite setup.intendedProtocol.History] in
/-- Site commonness of the open inputs, under a scheduler completing play, from
the lumped late deliveries and marked choices failing like late options. -/
theorem OnePacketOpenInputs.siteCommonness
    {sequence : ℕ → setup.intendedModel.BehavioralAssessment} {slots : Nat}
    (inputs : OnePacketOpenInputs setup leaks bounds horizon scheduler parameter utility
      excludedPayoff sequence slots)
    (wellFormed : setup.WellFormed)
    (independent : setup.PrivateInputsIndependent)
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence inputs.scale
      inputs.scale_pos inputs.scale_le_one weights targetSequence)
    (mixed : ∀ n, (targetSequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) :
    ∃ (score : ℕ → Option (LateKey setup leaks) → LateOption slots → ℝ) (drift : ℕ → ℝ),
      Tendsto drift atTop (nhds 0) ∧ (∀ n, 0 ≤ drift n) ∧
      ∀ n who (site : (onePacketN).InformationSite who),
        ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
          (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
          ((onePacketN).agentAt site) →
        (∀ option,
          |onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n) site
              (onePacketLate setup leaks bounds horizon scheduler sequence inputs.scale
                inputs.scale_pos inputs.scale_le_one (slots := slots) n
                ((onePacketN).agentAt site) option) -
            (1 - score n (agentLateKey setup leaks bounds (initialLaw setup) horizon scheduler
              ((onePacketN).agentAt site)) option)| ≤ drift n) ∧
        ∀ choice, onePacketCompared setup leaks bounds horizon scheduler who site choice →
          (∃ option,
            |onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n) site
                (PMF.pure choice) -
              (1 - score n (agentLateKey setup leaks bounds (initialLaw setup) horizon scheduler
                ((onePacketN).agentAt site)) option)| ≤ drift n) ∨
          onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n) site
            (PMF.pure choice) = 1 := by
  obtain ⟨beliefDrift, beliefLimit, records⟩ :=
    inputs.lateRecords independent weights targetSequence assembled mixed bayes
  obtain ⟨unforcedDrift, unforcedLimit, unforced⟩ := inputs.lateUnforced setup leaks bounds
    horizon scheduler wellFormed weights targetSequence assembled mixed bayes
  let lumping := fun n who => certificateLumping setup leaks bounds horizon scheduler sequence
    inputs.scale inputs.scale_pos inputs.scale_le_one inputs.covers inputs.capacity
    inputs.slotsLe weights targetSequence assembled n who
  let recordLaw := fun n (key : LateKey setup leaks) => (records n key.owner).choose key
  let failureOf := fun n (key : LateKey setup leaks) option record =>
    lumpedFailure setup leaks bounds horizon scheduler (lumping n key.owner) (2 * horizon + 1)
      key option record
  have ownerEq : ∀ {who : Player} {site : (onePacketN).InformationSite who}
      {key : LateKey setup leaks}, lateKey setup leaks who site.1 = some key → key.owner = who := by
    intro who site key siteKey
    obtain ⟨info, _⟩ := site
    cases info with
    | none => simp [lateKey] at siteKey
    | some input =>
        simp only [lateKey, Option.some.injEq] at siteKey
        rw [← siteKey]
  let pathDrift := fun n => ((2 * horizon + 1 : ℕ) : ℝ) * (inputs.scale n ^ 3 + inputs.scale n ^ 3)
  have pathLimit : Tendsto pathDrift atTop (nhds 0) := by
    have cube := inputs.scale_vanishing.pow 3
    simpa [pathDrift] using (cube.add cube).const_mul ((2 * horizon + 1 : ℕ) : ℝ)
  have pathNonneg : ∀ n, 0 ≤ pathDrift n := fun n => by
    have := (inputs.scale_pos n).le
    positivity
  have markLimit : Tendsto (fun n => 1 - slotRetention (inputs.scale n)) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_slotRetention inputs.scale_vanishing)
  have markNonneg : ∀ n, 0 ≤ 1 - slotRetention (inputs.scale n) := fun n =>
    sub_nonneg.mpr (slotRetention_le_one (inputs.scale_pos n).le (inputs.scale_le_one n))
  have marked : ∀ n who (site : (onePacketN).InformationSite who),
      ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
      ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
      ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
        (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
        ((onePacketN).agentAt site) →
      ∀ choice, onePacketCompared setup leaks bounds horizon scheduler who site choice →
        (∃ option,
          |onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n) site
              (PMF.pure choice) -
            onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n) site
              (onePacketLate setup leaks bounds horizon scheduler sequence inputs.scale
                inputs.scale_pos inputs.scale_le_one (slots := slots) n
                ((onePacketN).agentAt site) option)| ≤
            1 - slotRetention (inputs.scale n)) ∨
        onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n) site
          (PMF.pure choice) = 1 := by
    intro n who site _ _ keyed choice isMarked
    obtain ⟨past, view, _, atSite, _⟩ := keyed.1
    exact Or.inl ⟨none, abs_localFailure_silence_sub_wait_le setup leaks bounds horizon scheduler
      sequence inputs.scale inputs.scale_pos inputs.scale_le_one n (targetSequence n) site _
      atSite choice (isMarked.1 keyed.1)⟩
  refine onePacket_siteCommonness setup leaks bounds horizon scheduler sequence inputs.scale
    inputs.scale_pos inputs.scale_le_one targetSequence pathDrift unforcedDrift beliefDrift
    (fun n => 1 - slotRetention (inputs.scale n)) pathLimit unforcedLimit beliefLimit markLimit
    pathNonneg markNonneg failureOf recordLaw
    (fun n key option record => unit_expect _ _ ((lumping n key.owner).failure_unit key))
    (fun n who site _ notOwing keyed key siteKey option history supported forced => ?_)
    unforced
    (fun n who site notFree notOwing keyed key siteKey option => ?_) marked
  · have owner := ownerEq siteKey
    subst owner
    exact lateHistoryFailure_near_lumped setup leaks bounds horizon scheduler sequence
      inputs.scale inputs.scale_pos inputs.scale_le_one n (targetSequence n) key.owner
      (lumping n key.owner) site
      ⟨Or.inl keyed.1, siteDebtFree_of_not_owing setup leaks bounds horizon scheduler notOwing⟩
      key
      siteKey option
      (fun history _ _ final reached =>
        onePacketFailed_iff_decisionFailed setup leaks bounds horizon scheduler completes
          (setup.intendedOpeningProfile (sequence n).strategy) site keyed.1 siteKey history _
          final reached)
      history supported forced
  · have owner := ownerEq siteKey
    subst owner
    exact (records n key.owner).choose_spec site notFree notOwing keyed key siteKey option

omit [Finite setup.intendedProtocol.History] in
/-- **Late options gain vanishingly.** Under a scheduler completing play, along
every fully mixed Bayes sequence of assembled profiles with best pool weights,
every late option at a forced late delivery gains at most a vanishing error:
the late options of a key fail in common, so the key's best weights are a
common best response of its pool. -/
theorem OnePacketOpenInputs.lateMemberGain_le
    {sequence : ℕ → setup.intendedModel.BehavioralAssessment} {slots : Nat}
    (inputs : OnePacketOpenInputs setup leaks bounds horizon scheduler parameter utility
      excludedPayoff sequence slots)
    (wellFormed : setup.WellFormed)
    (independent : setup.PrivateInputsIndependent)
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence inputs.scale
      inputs.scale_pos inputs.scale_le_one weights targetSequence)
    (mixed : ∀ n, (targetSequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain)
    (poolBest : OnePacketPoolBest setup leaks bounds horizon scheduler parameter utility
      excludedPayoff sequence inputs.scale inputs.scale_pos inputs.scale_le_one
      (slots := slots) targetSequence) :
    ∃ memberError : ℕ → ℝ, Tendsto memberError atTop (nhds 0) ∧
      ∀ n who (site : (onePacketN).InformationSite who),
        ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
          (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
          ((onePacketN).agentAt site) →
        ∀ option : LateOption slots,
          onePacketSiteGain setup leaks bounds horizon scheduler parameter utility excludedPayoff
              (targetSequence n) site
              (onePacketLate setup leaks bounds horizon scheduler sequence inputs.scale
                inputs.scale_pos inputs.scale_le_one (slots := slots) n
                ((onePacketN).agentAt site) option) ≤
            memberError n := by
  classical
  have rational := freeKeyedMemberRational (2 * horizon + 1)
    ((bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup) horizon scheduler)
    ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall (initialLaw setup) horizon
      scheduler)
    (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter utility
      excludedPayoff) (payoffComponent setup)
    (onePacketFallback setup leaks bounds horizon scheduler)
    (FreeAgent setup leaks bounds horizon scheduler)
    (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
    (agentLateKey setup leaks bounds (initialLaw setup) horizon scheduler)
    (OwingAgent setup leaks bounds horizon scheduler)
    (fun n => onePacketUnforced setup leaks bounds horizon scheduler inputs.scale
      inputs.scale_pos inputs.scale_le_one n)
    (fun n => onePacketPrescribed setup leaks bounds horizon scheduler sequence inputs.scale
      inputs.scale_pos inputs.scale_le_one n)
    (fun n => onePacketLate setup leaks bounds horizon scheduler sequence inputs.scale
      inputs.scale_pos inputs.scale_le_one (slots := slots) n)
    (onePacketFailed setup leaks bounds horizon scheduler) excludedPayoff
    (onePacketFailed_pays setup leaks bounds horizon scheduler parameter utility excludedPayoff)
    inputs.gapBound inputs.gapBound_nonneg
    (localGain_eq_zero_of_owingAgent setup leaks bounds horizon scheduler parameter utility
      excludedPayoff completes)
    (fun weights targetSequence assembled mixed bayes => by
      obtain ⟨continuation, error, errorLimit, value⟩ :=
        inputs.lateDecomposition weights targetSequence assembled mixed bayes
      obtain ⟨score, drift, driftLimit, driftNonneg, common⟩ :=
        inputs.siteCommonness setup leaks bounds horizon scheduler parameter utility
          excludedPayoff wellFormed independent completes weights targetSequence assembled mixed
          bayes
      refine ⟨continuation, score, error, drift, errorLimit, driftLimit, driftNonneg,
        fun n agent keyed notOwing decision => ?_⟩
      obtain ⟨low, gap, _, late⟩ := value n agent.1 ⟨agent.2.1, decision⟩ keyed.2 notOwing keyed
      exact ⟨low, gap, late,
        (common n agent.1 ⟨agent.2.1, decision⟩ keyed.2 notOwing keyed).1⟩)
  obtain ⟨memberError, memberLimit, member⟩ := rational weights targetSequence assembled mixed
    bayes (by unfold OnePacketPoolBest at poolBest; convert poolBest)
  refine ⟨memberError, memberLimit, fun n who site keyed option => ?_⟩
  obtain ⟨part, partEq⟩ := exists_part_eq_late setup leaks bounds horizon scheduler sequence
    inputs.scale inputs.scale_pos inputs.scale_le_one n keyed option
  have bound := member n who site (PMF.pure part)
  rw [PMF.pure_bind, partEq] at bound
  exact bound

/-- **The certificate inputs from the open inputs.** For a well-formed setup,
under the asynchronous contract with timely delays and retention of first
covered canonical packets, the open inputs give the inputs of the one-packet
certificate: the failure sets are the event-level failures of pending events,
and the law approximation holds. -/
def OnePacketOpenInputs.toCertificateInputs
    {sequence : ℕ → setup.intendedModel.BehavioralAssessment} {slots : Nat}
    (inputs : OnePacketOpenInputs setup leaks bounds horizon scheduler parameter utility
      excludedPayoff sequence slots)
    (wellFormed : setup.WellFormed)
    (independent : setup.PrivateInputsIndependent) {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (retains : RetainsCoveredCanonical setup leaks bounds horizon scheduler bound)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (sourceBayes : ∀ n, BehavioralAssessment.IsBayesConsistent setup.intendedModel (sequence n)
      setup.intended_decision_antichain) :
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
  owing_noGain := localGain_eq_zero_of_owingAgent setup leaks bounds horizon scheduler parameter
    utility excludedPayoff contract.completes
  decomposition weights targetSequence assembled mixed bayes := by
    obtain ⟨continuation, error, errorLimit, value⟩ :=
      inputs.lateDecomposition weights targetSequence assembled mixed bayes
    obtain ⟨score, drift, driftLimit, driftNonneg, common⟩ :=
      inputs.siteCommonness setup leaks bounds horizon scheduler parameter utility
        excludedPayoff wellFormed independent contract.completes weights targetSequence assembled
        mixed bayes
    refine ⟨continuation, score, error, drift, errorLimit, driftLimit, driftNonneg,
      fun n agent keyed notOwing decision => ?_⟩
    obtain ⟨low, gap, _, late⟩ := value n agent.1 ⟨agent.2.1, decision⟩ keyed.2 notOwing keyed
    exact ⟨low, gap, late, (common n agent.1 ⟨agent.2.1, decision⟩ keyed.2 notOwing keyed).1⟩
  ranking weights targetSequence assembled mixed bayes := by
    classical
    obtain ⟨lateContinuation, lateError, lateLimit, lateValue⟩ :=
      inputs.lateDecomposition weights targetSequence assembled mixed bayes
    obtain ⟨otherContinuation, otherError, otherLimit, otherValue⟩ :=
      inputs.nonLateDecomposition weights targetSequence assembled mixed bayes
    obtain ⟨score, drift, driftLimit, driftNonneg, common⟩ :=
      inputs.siteCommonness setup leaks bounds horizon scheduler parameter utility
        excludedPayoff wellFormed independent contract.completes weights targetSequence assembled
        mixed bayes
    obtain ⟨slack, slackLimit, slackNonneg, prescribed⟩ :=
      onePacket_prescribedFailure setup leaks bounds horizon scheduler contract timely retains
        (firstActivationTransmits_of_contract setup leaks bounds horizon scheduler contract)
        sequence inputs.scale inputs.scale_pos inputs.scale_le_one inputs.scale_vanishing
        targetSequence
    refine ⟨fun n agent => if ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
        (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler) agent then
          lateContinuation n agent else otherContinuation n agent, score,
      fun n => max (lateError n) (otherError n), drift, slack,
      by simpa using lateLimit.max otherLimit, driftLimit, slackLimit, driftNonneg, slackNonneg,
      fun n who site choice notFree notOwing marked => ?_⟩
    by_cases keyed : ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
        (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
        ((onePacketN).agentAt site)
    · obtain ⟨low, gap, chosen, late⟩ := lateValue n who site notFree notOwing keyed
      obtain ⟨options, near⟩ := common n who site notFree notOwing keyed
      simp only [keyed, ↓reduceIte]
      have bound := le_max_left (lateError n) (otherError n)
      refine ⟨Or.inl ⟨by linarith, gap⟩, (chosen choice marked).trans bound, fun _ =>
        ⟨fun option => (late option).trans bound, options, near choice marked⟩,
        fun unkeyed => (unkeyed trivial).elim⟩
    · obtain ⟨lowGap, chosen, other⟩ := otherValue n who site notFree keyed
      simp only [keyed, ↓reduceIte]
      have bound := le_max_right (lateError n) (otherError n)
      refine ⟨?_, (chosen choice marked).trans bound,
        fun isKeyed => isKeyed.elim,
        fun _ => ⟨other.trans bound, prescribed n who site choice notFree keyed⟩⟩
      rcases lowGap with ⟨low, gap⟩ | pending
      · exact Or.inl ⟨by linarith, gap⟩
      · right
        unfold onePacketFailed
        change (match pendingEvent setup leaks who site.1 with
          | none => ∅
          | some event => EventFailedHistory setup leaks bounds horizon scheduler who event) = _
        rw [pending]
  otherComparisons weights targetSequence assembled mixed bayes poolBest := by
    classical
    obtain ⟨memberError, memberLimit, member⟩ := inputs.lateMemberGain_le setup leaks bounds
      horizon scheduler parameter utility excludedPayoff wellFormed independent contract.completes
      weights targetSequence assembled mixed bayes poolBest
    obtain ⟨lateContinuation, lateValueError, lateValueLimit, lateValue⟩ :=
      inputs.lateDecomposition weights targetSequence assembled mixed bayes
    have decided : ∀ {who : Player} {site : (onePacketN).InformationSite who},
        ValueChangingSite setup leaks bounds horizon scheduler site →
          setup.intendedModel.IsDecisionInfo who (projectView setup leaks who site.1) :=
      fun changing => valueChangingSite_projectedDecision setup leaks bounds horizon scheduler
        wellFormed changing
    obtain ⟨valueError, bound, valueLimit, boundNonneg, transport⟩ :=
      inputs.valueTransport weights targetSequence assembled mixed bayes
    obtain ⟨lateError, lateLimit, late⟩ :=
      inputs.lateCommitments weights targetSequence assembled mixed bayes
    obtain ⟨otherContinuation, otherError, otherLimit, otherValue⟩ :=
      inputs.nonLateDecomposition weights targetSequence assembled mixed bayes
    let distance := fun (n : ℕ) {who : Player} (site : (onePacketN).InformationSite who)
        (changing : ValueChangingSite setup leaks bounds horizon scheduler site) =>
      ∑' point, |((((targetSequence n).belief who site).map
          (replayProjection setup leaks bounds horizon scheduler
          (projectedSite setup leaks (decided changing)) site
          (changingInput_decision setup leaks bounds horizon scheduler changing)
          rfl)) point).toReal -
        ((sequence n).belief who
          (projectedSite setup leaks (decided changing)) point).toReal|
    let agentDistance := fun (n : ℕ)
        (agent : (onePacketN).InformationAgent (onePacketN).playedInformation) =>
      if present : ∃ decision : (onePacketN).IsDecisionInfo agent.1 agent.2.1,
          ValueChangingSite setup leaks bounds horizon scheduler
            (⟨agent.2.1, decision⟩ : (onePacketN).InformationSite agent.1) then
        distance n ⟨agent.2.1, present.1⟩ present.2 else 0
    have distanceNonneg : ∀ n agent, 0 ≤ agentDistance n agent := fun n agent => by
      simp only [agentDistance]
      split
      · exact tsum_nonneg fun _ => abs_nonneg _
      · exact le_rfl
    let agentIrregular := fun (n : ℕ)
        (agent : (onePacketN).InformationAgent (onePacketN).playedInformation) =>
      if present : ∃ decision : (onePacketN).IsDecisionInfo agent.1 agent.2.1,
          ValueChangingSite setup leaks bounds horizon scheduler
            (⟨agent.2.1, decision⟩ : (onePacketN).InformationSite agent.1) then
        expect ((targetSequence n).belief agent.1 ⟨agent.2.1, present.1⟩) (fun history =>
          if RegularTrace setup leaks bounds horizon scheduler (sequence n) agent.1
            history.1.trace then (0 : ℝ) else 1) else 0
    have irregularNonneg : ∀ n agent, 0 ≤ agentIrregular n agent := fun n agent => by
      simp only [agentIrregular]
      split
      · refine expect_nonneg _ _ fun history => ?_
        split <;> norm_num
      · exact le_rfl
    have irregularLimit : Tendsto (fun n => ∑ agent, agentIrregular n agent) atTop
        (nhds 0) := by
      rw [show (0 : ℝ) = ∑ _agent : (onePacketN).InformationAgent (onePacketN).playedInformation,
        (0 : ℝ) by simp]
      refine tendsto_finsetSum _ fun agent _ => ?_
      by_cases present : ∃ decision : (onePacketN).IsDecisionInfo agent.1 agent.2.1,
          ValueChangingSite setup leaks bounds horizon scheduler
            (⟨agent.2.1, decision⟩ : (onePacketN).InformationSite agent.1)
      · simp only [agentIrregular, present, ↓reduceDIte]
        exact onePacket_irregularVanishes setup leaks bounds horizon scheduler mixed bayes
          (inputs.counterpartInputs weights targetSequence assembled mixed bayes agent.1
            ⟨agent.2.1, present.1⟩ present.2.1
            (not_owingAgent_of_siteDebtFree setup leaks bounds horizon scheduler present.2.2.2.1)
            (changingInput_decision setup leaks bounds horizon scheduler present.2)
            (changingInput_turn setup leaks bounds horizon scheduler present.2).choose_spec)
      · simp only [agentIrregular, present, ↓reduceDIte]
        exact tendsto_const_nhds
    have beliefLimit : Tendsto (fun n => ∑ agent, agentDistance n agent) atTop (nhds 0) := by
      rw [show (0 : ℝ) = ∑ _agent : (onePacketN).InformationAgent (onePacketN).playedInformation,
        (0 : ℝ) by simp]
      refine tendsto_finsetSum _ fun agent _ => ?_
      by_cases present : ∃ decision : (onePacketN).IsDecisionInfo agent.1 agent.2.1,
          ValueChangingSite setup leaks bounds horizon scheduler
            (⟨agent.2.1, decision⟩ : (onePacketN).InformationSite agent.1)
      · simp only [agentDistance, present, ↓reduceDIte]
        exact onePacket_beliefConverges setup leaks bounds horizon scheduler wellFormed
          sourceMixed sourceBayes mixed bayes
          (changingInput_decision setup leaks bounds horizon scheduler present.2)
          rfl
          (forcedAgent_of_not_free setup leaks bounds horizon scheduler present.2.1)
          (changingInput_turn setup leaks bounds horizon scheduler present.2).choose_spec
          (inputs.beliefInputs setup leaks bounds horizon scheduler weights targetSequence
            assembled mixed bayes agent.1
            ⟨agent.2.1, present.1⟩ present.2.1
            (not_owingAgent_of_siteDebtFree setup leaks bounds horizon scheduler present.2.2.2.1)
            (changingInput_decision setup leaks bounds horizon scheduler present.2)
            (changingInput_turn setup leaks bounds horizon scheduler present.2).choose_spec
            (decided present.2))
      · simp only [agentDistance, present, ↓reduceDIte]
        exact tendsto_const_nhds
    let payoffBound := onePacketPayoffBound setup leaks bounds horizon scheduler parameter
      utility excludedPayoff
    have totalLimit : Tendsto (fun n => |valueError n| + bound * ∑ agent, agentDistance n agent +
        |lateError n| + 2 * |otherError n| + |memberError n| + 2 * |lateValueError n| +
        6 * inputs.scale n * (2 * payoffBound) + bound * ∑ agent, agentIrregular n agent) atTop
        (nhds 0) := by
      simpa using ((((((valueLimit.abs.add (beliefLimit.const_mul bound)).add lateLimit.abs).add
        (otherLimit.abs.const_mul 2)).add memberLimit.abs).add
          (lateValueLimit.abs.const_mul 2)).add
        ((inputs.scale_vanishing.const_mul 6).mul_const (2 * payoffBound))).add
        (irregularLimit.const_mul bound)
    refine ⟨fun n => |valueError n| + bound * ∑ agent, agentDistance n agent + |lateError n| +
        2 * |otherError n| + |memberError n| + 2 * |lateValueError n| +
        6 * inputs.scale n * (2 * payoffBound) + bound * ∑ agent, agentIrregular n agent,
      totalLimit,
      fun n who site notFree notOwing choice unmarked => ?_⟩
    have payoffNonneg : 0 ≤ payoffBound := onePacketPayoffBound_nonneg setup leaks bounds horizon
      scheduler parameter utility excludedPayoff
    have scaleTerm : 0 ≤ 6 * inputs.scale n * (2 * payoffBound) := by
      have := (inputs.scale_pos n).le
      positivity
    have := abs_nonneg (memberError n)
    have := abs_nonneg (lateValueError n)
    have forced : ¬ FreeAgent setup leaks bounds horizon scheduler
        ((onePacketN).agentAt site) := fun unforced =>
      notFree (Finset.mem_filter.mpr ⟨Finset.mem_univ _, unforced⟩)
    have sumNonneg : 0 ≤ bound * ∑ agent, agentDistance n agent :=
      mul_nonneg boundNonneg (Finset.sum_nonneg fun agent _ => distanceNonneg n agent)
    have irregularSumNonneg : 0 ≤ bound * ∑ agent, agentIrregular n agent :=
      mul_nonneg boundNonneg (Finset.sum_nonneg fun agent _ => irregularNonneg n agent)
    by_cases atTurn : CommitsAtTurn setup leaks bounds horizon scheduler who site choice
    swap
    · left
      obtain ⟨response, chosen, event, submitted⟩ : ∃ response, choice.1 = some response ∧
          ∃ event, (runtime setup).submittedEvent? leaks response = some event := by
        by_contra none
        push Not at none
        apply unmarked
        refine ⟨fun late => ?_, fun response chosen => ⟨?_, fun event submitted =>
          (none response chosen event submitted).elim⟩⟩
        · obtain ⟨past, view, _, atSite, _⟩ := late
          obtain ⟨response, chosen, member⟩ := choice_response setup leaks bounds horizon
            scheduler site atSite choice
          rw [chosen]
          rcases response with ⟨transmission⟩
          cases transmission with
          | none => rfl
          | some material =>
              obtain ⟨event, submitted⟩ := submittedEvent_of_transmits setup leaks bounds member
                (material := material) rfl
              exact (none _ chosen event submitted).elim
        · intro material sends event handle packet
          apply none response chosen event
          unfold EventGraphRuntime.submittedEvent?
          rw [sends]
          exact (congrArg (Payload.event? (graph setup)) packet).trans rfl
      have zero := (onePacketN).gain_eq_expect_historyGain
        ((onePacketN).truncatedRunner (2 * horizon + 1))
        (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter
          utility excludedPayoff) (payoffComponent setup) (targetSequence n)
        (site, ((targetSequence n).strategy who).withLaw site.1 (PMF.pure choice))
      rw [expect_congr_on_support (g := fun _ => 0) (fun history _ =>
        historyGain_eq_zero_of_owes setup leaks bounds horizon scheduler parameter utility
          excludedPayoff contract.completes (targetSequence n) _ history
          (owes_of_not_commitsAtTurn setup leaks bounds horizon scheduler wellFormed
            (setup.intendedOpeningProfile (sequence n).strategy) site choice atTurn chosen
            submitted history)), expect_constant] at zero
      dsimp only
      rw [zero]
      positivity
    by_cases keyedSite : ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
        (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
        ((onePacketN).agentAt site)
    · obtain ⟨past, view, turnResponse, event, atSite, turnChosen, submittedTurn, turn⟩ :=
        id atTurn
      have := abs_nonneg (valueError n)
      have := abs_nonneg (lateError n)
      have := abs_nonneg (otherError n)
      have debtFree := siteDebtFree_of_not_owing setup leaks bounds horizon scheduler notOwing
      obtain ⟨material, sends⟩ : ∃ material, turnResponse.transmission = some material := by
        unfold EventGraphRuntime.submittedEvent? at submittedTurn
        cases transmits : turnResponse.transmission with
        | none =>
            rw [transmits] at submittedTurn
            cases submittedTurn
        | some material => exact ⟨material, rfl⟩
      have named : material.call.packet.event? (graph setup) = some event := by
        unfold EventGraphRuntime.submittedEvent? at submittedTurn
        rw [sends] at submittedTurn
        exact submittedTurn
      cases packet : material.call.packet with
      | malformed raw =>
          rw [packet] at named
          cases named
      | opening opened handle raw =>
          right
          left
          obtain ⟨part, partEq⟩ := exists_part_eq_late setup leaks bounds horizon scheduler
            sequence inputs.scale inputs.scale_pos inputs.scale_le_one n keyedSite
            (some ⟨0, inputs.slots_pos⟩)
          refine ⟨PMF.pure part, ?_⟩
          rw [PMF.pure_bind, partEq]
          have opening := lateOpening_siteGain_le setup leaks bounds horizon scheduler parameter
            utility excludedPayoff wellFormed sequence inputs.scale inputs.scale_pos
            inputs.scale_le_one n (targetSequence n) site forced keyedSite.1 debtFree choice
            atTurn turnChosen sends packet ⟨0, inputs.slots_pos⟩
            (fun choice => abs_onePacketSiteGain_le setup leaks bounds horizon scheduler
              parameter utility excludedPayoff (targetSequence n) site (PMF.pure choice))
          change onePacketSiteGain setup leaks bounds horizon scheduler parameter utility
              excludedPayoff (targetSequence n) site (PMF.pure choice) ≤
            onePacketSiteGain setup leaks bounds horizon scheduler parameter utility
              excludedPayoff (targetSequence n) site (onePacketLate setup leaks bounds horizon
                scheduler sequence inputs.scale inputs.scale_pos inputs.scale_le_one
                (slots := slots) n ((onePacketN).agentAt site) (some ⟨0, inputs.slots_pos⟩)) + _
          linarith
      | commitment committed handle =>
          have committedEq : committed = event := by
            rw [packet] at named
            exact Option.some.inj named
          subst committedEq
          by_cases intended : IntendedCommitment setup leaks bounds horizon scheduler site choice
          · right
            right
            have decision := projectedDecision_of_forcedAgent wellFormed
              (forcedAgent_of_not_free setup leaks bounds horizon scheduler forced) atSite turn
                debtFree
            obtain ⟨option, policy, weight, weightNonneg, weightLe, lateBound⟩ :=
              late n who site choice forced notOwing keyedSite atTurn debtFree intended
                decision
            have memberBound := member n who site keyedSite option
            let deviations := mix weight weightNonneg weightLe
              (PMF.pure (projectedSite setup leaks decision, policy))
              (PMF.pure (projectedSite setup leaks decision, (sequence n).strategy who))
            refine ⟨deviations, ?_⟩
            have mixed : expect deviations (fun deviation =>
                intendedSiteGain setup parameter utility excludedPayoff (sequence n) deviation) =
                weight * intendedSiteGain setup parameter utility excludedPayoff (sequence n)
                  (projectedSite setup leaks decision, policy) := by
              have zero : intendedSiteGain setup parameter utility excludedPayoff (sequence n)
                  (projectedSite setup leaks decision, (sequence n).strategy who) = 0 :=
                sub_self _
              rw [expect_mix _ _ _ _ _ _ (payoffIntegrable_pure _ _) (payoffIntegrable_pure _ _),
                expect_pure, expect_pure, zero, mul_zero, add_zero]
            change onePacketSiteGain setup leaks bounds horizon scheduler parameter utility
                excludedPayoff (targetSequence n) site (PMF.pure choice) ≤
              expect deviations (fun deviation =>
                intendedSiteGain setup parameter utility excludedPayoff (sequence n) deviation) +
                _
            rw [mixed]
            linarith [le_abs_self (memberError n), le_abs_self (lateError n)]
          · right
            left
            obtain ⟨low, _, _, lateNear⟩ := lateValue n who site forced notOwing keyedSite
            obtain ⟨part, partEq⟩ := exists_part_eq_late setup leaks bounds horizon scheduler
              sequence inputs.scale inputs.scale_pos inputs.scale_le_one n keyedSite none
            refine ⟨PMF.pure part, ?_⟩
            rw [PMF.pure_bind, partEq]
            have dominated := unintendedCommitment_gain_le setup leaks bounds horizon scheduler
              parameter utility excludedPayoff wellFormed contract.completes (targetSequence n)
              site atSite turn choice turnChosen sends packet debtFree intended
              (onePacketLate setup leaks bounds horizon scheduler sequence inputs.scale
                inputs.scale_pos inputs.scale_le_one (slots := slots) n
                ((onePacketN).agentAt site) none) low (lateNear none)
            change onePacketSiteGain setup leaks bounds horizon scheduler parameter utility
                excludedPayoff (targetSequence n) site (PMF.pure choice) ≤
              onePacketSiteGain setup leaks bounds horizon scheduler parameter utility
                excludedPayoff (targetSequence n) site (onePacketLate setup leaks bounds horizon
                  scheduler sequence inputs.scale inputs.scale_pos inputs.scale_le_one
                  (slots := slots) n ((onePacketN).agentAt site) none) + _
            linarith [le_abs_self (lateValueError n)]
    have unkeyed := keyedSite
    obtain ⟨response, chosen, material, sends, event', handle, packet⟩ : ∃ response,
        choice.1 = some response ∧ ∃ material, response.transmission = some material ∧
          ∃ event handle, material.call.packet = .commitment event handle := by
      by_contra none
      apply unmarked
      refine ⟨fun late => (keyedSite ⟨late, forced⟩).elim, fun response chosen =>
        ⟨fun material sends event handle packet =>
          none ⟨response, chosen, material, sends, event, handle, packet⟩,
        fun event submitted => ?_⟩⟩
      obtain ⟨past, view, turnResponse, turnEvent, atSite, turnChosen, submittedTurn, turn⟩ :=
        atTurn
      have sameResponse : turnResponse = response :=
        Option.some.inj (turnChosen.symm.trans chosen)
      subst sameResponse
      have sameEvent : turnEvent = event := Option.some.inj (submittedTurn.symm.trans submitted)
      subst sameEvent
      exact ⟨past, view, atSite, turn⟩
    obtain ⟨past, view, turnResponse, event, atSite, turnChosen, submittedTurn, turn⟩ := atTurn
    have sameResponse : turnResponse = response :=
      Option.some.inj (turnChosen.symm.trans chosen)
    subst sameResponse
    have eventEq : event' = event := by
      have submitted : (runtime setup).submittedEvent? leaks turnResponse = some event' := by
        unfold EventGraphRuntime.submittedEvent?
        rw [sends]
        exact (congrArg (Payload.event? (graph setup)) packet).trans rfl
      exact Option.some.inj (submitted.symm.trans submittedTurn)
    subst eventEq
    have atTurn : CommitsAtTurn setup leaks bounds horizon scheduler who site choice :=
      ⟨past, view, turnResponse, event', atSite, turnChosen, submittedTurn, turn⟩
    have debtFree := siteDebtFree_of_not_owing setup leaks bounds horizon scheduler notOwing
    by_cases intended : IntendedCommitment setup leaks bounds horizon scheduler site choice
    swap
    · right
      left
      obtain ⟨lowGap, _, prescribedNear⟩ := otherValue n who site forced keyedSite
      have pending := pendingEvent_of_turnSubmission setup leaks bounds horizon scheduler site
        atSite turn choice turnChosen submittedTurn
      obtain ⟨low, _⟩ := lowGap.resolve_right fun unpending => by
        rw [unpending] at pending
        cases pending
      let part : OnePacketPart setup leaks bounds horizon scheduler slots
          (onePacketPool setup leaks bounds horizon scheduler ((onePacketN).agentAt site)) :=
        Classical.arbitrary _
      have componentEq : freeKeyedComponent
          (onePacketUnforced setup leaks bounds horizon scheduler inputs.scale inputs.scale_pos
            inputs.scale_le_one n)
          (onePacketPrescribed setup leaks bounds horizon scheduler sequence inputs.scale
            inputs.scale_pos inputs.scale_le_one n)
          (onePacketLate setup leaks bounds horizon scheduler sequence inputs.scale
            inputs.scale_pos inputs.scale_le_one (slots := slots) n)
          ((onePacketN).agentAt site) part =
          onePacketPrescribed setup leaks bounds horizon scheduler sequence inputs.scale
            inputs.scale_pos inputs.scale_le_one n ((onePacketN).agentAt site) := by
        obtain ⟨identify, componentEq⟩ := freeKeyedComponent_of_not_free
          (key := agentLateKey setup leaks bounds (initialLaw setup) horizon scheduler)
          (onePacketUnforced setup leaks bounds horizon scheduler inputs.scale inputs.scale_pos
            inputs.scale_le_one n)
          (onePacketPrescribed setup leaks bounds horizon scheduler sequence inputs.scale
            inputs.scale_pos inputs.scale_le_one n)
          (onePacketLate setup leaks bounds horizon scheduler sequence inputs.scale
            inputs.scale_pos inputs.scale_le_one (slots := slots) n) forced
        rw [componentEq]
        exact keyedComponent_of_not_keyed _ _ keyedSite _
      refine ⟨PMF.pure part, ?_⟩
      rw [PMF.pure_bind, componentEq]
      have dominated := unintendedCommitment_gain_le setup leaks bounds horizon scheduler
        parameter utility excludedPayoff wellFormed contract.completes (targetSequence n) site
        atSite turn choice chosen sends packet debtFree intended
        (onePacketPrescribed setup leaks bounds horizon scheduler sequence inputs.scale
          inputs.scale_pos inputs.scale_le_one n ((onePacketN).agentAt site)) low
        prescribedNear
      have := le_abs_self (otherError n)
      have := abs_nonneg (valueError n)
      have := abs_nonneg (lateError n)
      change onePacketSiteGain setup leaks bounds horizon scheduler parameter utility
          excludedPayoff (targetSequence n) site (PMF.pure choice) ≤
        onePacketSiteGain setup leaks bounds horizon scheduler parameter utility excludedPayoff
          (targetSequence n) site (onePacketPrescribed setup leaks bounds horizon scheduler
            sequence inputs.scale inputs.scale_pos inputs.scale_le_one n
            ((onePacketN).agentAt site)) + _
      linarith
    have changing : ValueChangingSite setup leaks bounds horizon scheduler site :=
      ⟨forced, unkeyed, debtFree, choice, unmarked, atTurn, intended⟩
    obtain ⟨policy, close, bounded⟩ := transport n who site choice forced unkeyed atTurn
      debtFree intended (decided changing)
      (changingInput_decision setup leaks bounds horizon scheduler changing)
    have siteLe : distance n site changing ≤ ∑ agent, agentDistance n agent := by
      have single := Finset.single_le_sum (fun agent _ => distanceNonneg n agent)
        (Finset.mem_univ ((onePacketN).agentAt site))
      have atSite : agentDistance n ((onePacketN).agentAt site) = distance n site changing := by
        have present : ∃ decision : (onePacketN).IsDecisionInfo who site.1,
            ValueChangingSite setup leaks bounds horizon scheduler
              (⟨site.1, decision⟩ : (onePacketN).InformationSite who) := ⟨site.2, changing⟩
        simp only [agentDistance, present, ↓reduceDIte]
        rfl
      rw [atSite] at single
      exact single
    have irregularLe : expect ((targetSequence n).belief who site) (fun history =>
        if RegularTrace setup leaks bounds horizon scheduler (sequence n) who history.1.trace
        then (0 : ℝ) else 1) ≤ ∑ agent, agentIrregular n agent := by
      have single := Finset.single_le_sum (fun agent _ => irregularNonneg n agent)
        (Finset.mem_univ ((onePacketN).agentAt site))
      have atSite : agentIrregular n ((onePacketN).agentAt site) =
          expect ((targetSequence n).belief who site) (fun history =>
            if RegularTrace setup leaks bounds horizon scheduler (sequence n) who
              history.1.trace then (0 : ℝ) else 1) := by
        have present : ∃ decision : (onePacketN).IsDecisionInfo who site.1,
            ValueChangingSite setup leaks bounds horizon scheduler
              (⟨site.1, decision⟩ : (onePacketN).InformationSite who) := ⟨site.2, changing⟩
        simp only [agentIrregular, present, ↓reduceDIte]
        rfl
      rw [atSite] at single
      exact single
    have transported := expect_sub_le_of_bounded
      (((targetSequence n).belief who site).map
        (replayProjection setup leaks bounds horizon scheduler
          (projectedSite setup leaks (decided changing)) site
          (changingInput_decision setup leaks bounds horizon scheduler changing) rfl))
      ((sequence n).belief who (projectedSite setup leaks (decided changing)))
      (setup.intendedModel.historyGain
        (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
        (intendedReadoutExclusion setup parameter utility excludedPayoff) (payoffComponent setup)
        (sequence n) (projectedSite setup leaks (decided changing), policy)) bounded
    have sourceEq := setup.intendedModel.gain_eq_expect_historyGain
      (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
      (intendedReadoutExclusion setup parameter utility excludedPayoff) (payoffComponent setup)
      (sequence n) (projectedSite setup leaks (decided changing), policy)
    have scaled := mul_le_mul_of_nonneg_left siteLe boundNonneg
    have irregularScaled := mul_le_mul_of_nonneg_left irregularLe boundNonneg
    right
    right
    refine ⟨PMF.pure (projectedSite setup leaks (decided changing),
      policy), ?_⟩
    have transportedDistance : _ ≤ bound * distance n site changing := transported
    have final : onePacketSiteGain setup leaks bounds horizon scheduler parameter utility
        excludedPayoff (targetSequence n) site (PMF.pure choice) ≤
        expect ((sequence n).belief who (projectedSite setup leaks (decided changing)))
          (setup.intendedModel.historyGain
            (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
            (intendedReadoutExclusion setup parameter utility excludedPayoff)
            (payoffComponent setup) (sequence n)
            (projectedSite setup leaks (decided changing), policy)) +
          (|valueError n| + bound * ∑ agent, agentDistance n agent + |lateError n| +
            2 * |otherError n| + |memberError n| + 2 * |lateValueError n| +
            6 * inputs.scale n * (2 * payoffBound) + bound * ∑ agent, agentIrregular n agent) := by
      linarith [le_abs_self (valueError n), abs_nonneg (lateError n), abs_nonneg (otherError n)]
    rw [expect_pure]
    change _ ≤ (expect _ _ - expect _ _) + _
    rw [sourceEq]
    exact final
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
    (independent : setup.PrivateInputsIndependent)
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
        scheduler parameter utility excludedPayoff wellFormed independent contract timely
        retains mixed bayes

/-- **Sequential equilibrium of the bounded raw runtime from the open inputs.**
Under the hypotheses of
`Vegas.onePacket_intended_sequentialEquilibrium_of_openInputs`, bounds on the
utility, and a count-evidence service with a deposit covering the spread of the
exclusion payoff, there is a sequential equilibrium of the bounded raw runtime
under the exclusion payoff minus the deposit for each collected count charge,
that charges nobody on its paths, whose joint law of typed readout and realized
payoffs is the intended joint law of typed readout and exclusion payoff. -/
theorem onePacket_intended_raw_sequentialEquilibrium_of_openInputs
    (wellFormed : setup.WellFormed)
    (independent : setup.PrivateInputsIndependent) {delay bound : (graph setup).EventId → Nat}
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
        scheduler parameter utility excludedPayoff wellFormed independent contract timely
        retains mixed bayes)
    service observationRate deliveryRate delivery_nonnegative coverage lowerUtility upperUtility
    lower_le le_upper deposit deposit_nonnegative sufficient


end Open

end Vegas
