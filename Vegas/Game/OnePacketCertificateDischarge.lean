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

/-- A forced site outside late deliveries with a choice committing a value at the
player's own turn. -/
def ValueChangingSite {who : Player} (site : (onePacketN).InformationSite who) : Prop :=
  ¬ UnforcedAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) ∧
    ¬ ownedKeyed (UnforcedAgent setup leaks bounds horizon scheduler)
        (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
        ((onePacketN).agentAt site) ∧
    ∃ choice, ¬ onePacketCompared setup leaks bounds horizon scheduler who site choice ∧
      CommitsAtTurn setup leaks bounds horizon scheduler who site choice

omit [Finite setup.intendedProtocol.History] in
theorem valueChangingSite_input {who : Player} {site : (onePacketN).InformationSite who}
    (changing : ValueChangingSite setup leaks bounds horizon scheduler site) :
    ∃ input : List (application setup leaks).PlayerEntry × (application setup leaks).PlayerView,
      site.1 = some input ∧ ∃ event, input.2.application.publicView.ownTurn? who = some event := by
  obtain ⟨_, _, _, _, past, view, _, event, atSite, _, _, turn⟩ := changing
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

open Classical in
/-- **The forced-belief inputs at one own-turn site** along a source sequence
and a target sequence: operational steps for the target profiles, a tremble
scale negligible against a floor to a depth, and at every stage the intended
own completions of regular histories, the common fibers of the replay
projection, and the honest counterparts of irregular histories. -/
structure OnePacketBeliefInputs (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
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

open Classical in
/-- The failure from a history of installing a law at a late delivery, and zero
elsewhere. -/
def lateBlindFailure (assessment : (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who) (law : PMF ((onePacketN).Choice who site.1))
    (history : (onePacketN).InformationHistory who site.1) : ℝ :=
  if LateDelivery setup leaks who site.1 then
    lateHistoryFailure setup leaks bounds horizon scheduler assessment site law history
  else 0

/-- The failure expectation of `fuel` steps of a lumping's image kernel from the
image read off an operational record. -/
def lumpedFailure {assessment : (onePacketN).BehavioralAssessment} {who : Player}
    {LateOption : Type}
    {profileOf : (onePacketN).InformationSite who → LateOption → ∀ player,
      (onePacketN).BehavioralPolicy player}
    {failedState : LateKey setup leaks → (application setup leaks).ProtocolState → Prop}
    {δ : ℝ} {Y : Type} (lumping : PendingLumping assessment who profileOf failedState δ Y)
    (fuel : Nat) (key : LateKey setup leaks) (option : LateOption)
    (record : List (Option (OperationalState setup leaks))) : ℝ :=
  expect ((fun law => law.bind (lumping.kernel key option))^[fuel]
    (PMF.pure (lumping.start key record))) (lumping.failure key)

open Classical in
omit [Finite setup.intendedProtocol.History] in
/-- **Value blindness of late deliveries from lumping.** Given a one-step
lumping of the profiles installing the late options at late-delivery sites,
whose failed states agree with the failure sets on the final histories of play
from forced histories of the belief, a law of operational records at each key
with the keyed belief drift, and the unforced belief drift, the late
deliveries are value blind with path drift `(2 * horizon + 1) * δ`. -/
def lateDeliveryBlindness_ofLumping (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat} (n : ℕ) (assessment : (onePacketN).BehavioralAssessment) (who : Player)
    {failedState : LateKey setup leaks → (application setup leaks).ProtocolState → Prop}
    {δ : ℝ} {Y : Type}
    (lumping : PendingLumping assessment who
      (fun site option => Profile.update (sig := (onePacketN).behavioralSignature)
        assessment.strategy who ((assessment.strategy who).withLaw site.1
          (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one (slots := slots) n ((onePacketN).agentAt site) option)))
      failedState δ Y)
    (δ_nonneg : 0 ≤ δ)
    (agrees : ∀ (site : (onePacketN).InformationSite who) key,
      lateKey setup leaks who site.1 = some key → LateDelivery setup leaks who site.1 →
      ∀ option,
      ∀ history ∈ (assessment.belief who site).support,
        ForcedState setup leaks who history.1.state →
        ∀ final ∈ ((onePacketN).runBehavioralFrom (Profile.update
            (sig := (onePacketN).behavioralSignature) assessment.strategy who
            ((assessment.strategy who).withLaw site.1
              (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
                scale_le_one (slots := slots) n ((onePacketN).agentAt site) option)))
            (2 * horizon + 1) history.1).support,
          (final ∈ onePacketFailed setup leaks bounds horizon scheduler
            ((onePacketN).agentAt site) ↔ failedState key final.state))
    (recordLaw : LateKey setup leaks → PMF (List (Option (OperationalState setup leaks))))
    {unforcedDrift beliefDrift : ℝ} (beliefDrift_nonneg : 0 ≤ beliefDrift)
    (unforced : ∀ (site : (onePacketN).InformationSite who) key,
      lateKey setup leaks who site.1 = some key →
      expect (assessment.belief who site) (fun history =>
        if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1) ≤ unforcedDrift)
    (keyed : ∀ (site : (onePacketN).InformationSite who) key,
      lateKey setup leaks who site.1 = some key → KeyLate setup leaks key → ∀ option,
      |expect ((assessment.belief who site).map fun history =>
          operationalRecord setup leaks bounds horizon scheduler history.1.trace)
          (lumpedFailure setup leaks bounds horizon scheduler lumping (2 * horizon + 1) key
            option) -
        expect (recordLaw key)
          (lumpedFailure setup leaks bounds horizon scheduler lumping (2 * horizon + 1) key
            option)| ≤
        beliefDrift) :
    LateDeliveryBlindness setup leaks bounds horizon scheduler assessment who
      (LateOption := LateOption slots)
      (fun site option history => lateBlindFailure setup leaks bounds horizon scheduler
        assessment site (onePacketLate setup leaks bounds horizon scheduler sequence scale
          scale_pos scale_le_one (slots := slots) n ((onePacketN).agentAt site) option) history)
      ((2 * horizon + 1 : ℕ) * δ) unforcedDrift beliefDrift where
  failureOf key option record := if KeyLate setup leaks key then
    lumpedFailure setup leaks bounds horizon scheduler lumping (2 * horizon + 1) key option record
  else 0
  recordLaw := recordLaw
  historyFailure_unit site option history := by
    unfold lateBlindFailure
    split
    · exact unit_expect _ _ fun final => by split <;> norm_num
    · exact ⟨le_rfl, zero_le_one⟩
  failureOf_unit key option record := by
    split
    · exact unit_expect _ _ (lumping.failure_unit key)
    · exact ⟨le_rfl, zero_le_one⟩
  pathwise site key siteKey option history supported forced := by
    obtain ⟨fullHistory, infoEq⟩ := history
    have lateIff : KeyLate setup leaks key ↔ LateDelivery setup leaks who site.1 := by
      obtain ⟨info, decision⟩ := site
      have observed : (application setup leaks).observe who fullHistory.state = info :=
        ((bounds.onePacketMenu (runtime setup) leaks).info (initialLaw setup) horizon scheduler
          who fullHistory.trace).symm.trans infoEq
      have menuTrace := fullHistory.trace
      generalize fullHistory.state = state at observed menuTrace
      rcases state with _ | ⟨remaining, actor, execution⟩
      · change none = info at observed
        subst observed
        simp [lateKey] at siteKey
      by_cases active : actor = some who
      swap
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at observed
        change none = info at observed
        subst observed
        simp [lateKey] at siteKey
      subst active
      simp only [ReactiveApplication.observe, ↓reduceIte] at observed
      change some _ = info at observed
      subst observed
      exact keyLate_iff_lateDelivery setup leaks horizon scheduler
        ((bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon
          scheduler menuTrace) rfl siteKey
    by_cases late : LateDelivery setup leaks who site.1
    swap
    · unfold lateBlindFailure
      simp only [late, mt lateIff.mp late, ↓reduceIte, sub_zero, abs_zero]
      exact mul_nonneg (Nat.cast_nonneg _) δ_nonneg
    have keyLate := lateIff.mpr late
    unfold lateBlindFailure
    simp only [late, keyLate, ↓reduceIte]
    have near := lumping.pathwise (2 * horizon + 1) site key siteKey option
      ⟨fullHistory, infoEq⟩ supported forced
    have same : lateHistoryFailure setup leaks bounds horizon scheduler assessment site
        (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one (slots := slots) n ((onePacketN).agentAt site) option)
          ⟨fullHistory, infoEq⟩ =
        expect ((onePacketN).runBehavioralFrom (Profile.update
            (sig := (onePacketN).behavioralSignature) assessment.strategy who
            ((assessment.strategy who).withLaw site.1
              (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
                scale_le_one (slots := slots) n ((onePacketN).agentAt site) option)))
            (2 * horizon + 1) fullHistory)
          (fun final => if failedState key final.state then 1 else 0) := by
      unfold lateHistoryFailure localHistoryRun
      refine expect_congr_on_support fun final reached => ?_
      have iff := agrees site key siteKey late option ⟨fullHistory, infoEq⟩ supported forced
        final reached
      by_cases failed : failedState key final.state
      · simp only [iff.mpr failed, failed, ↓reduceIte]
      · simp only [mt iff.mp failed, failed, ↓reduceIte]
    rw [same]
    exact near
  unforced site key siteKey := unforced site key siteKey
  keyed site key siteKey option := by
    by_cases keyLate : KeyLate setup leaks key
    · simp only [keyLate, ↓reduceIte]
      exact keyed site key siteKey keyLate option
    · simp only [keyLate, ↓reduceIte, expect_constant, sub_zero, abs_zero]
      exact beliefDrift_nonneg

omit [Finite setup.intendedProtocol.History] in
/-- **Site commonness from value blindness.** Along a target sequence, if at
every stage each player's late deliveries are value blind for the failure of the
late options with vanishing drifts, and every marked choice at a forced late
delivery fails within a vanishing drift of some late option or surely, then the
late options fail within a vanishing drift of one minus a score of the
late-delivery key, and so does every marked choice or it fails surely. -/
theorem onePacket_siteCommonness (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat} (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (pathDrift unforcedDrift beliefDrift markDrift : ℕ → ℝ)
    (pathLimit : Tendsto pathDrift atTop (nhds 0))
    (unforcedLimit : Tendsto unforcedDrift atTop (nhds 0))
    (beliefLimit : Tendsto beliefDrift atTop (nhds 0))
    (markLimit : Tendsto markDrift atTop (nhds 0))
    (pathNonneg : ∀ n, 0 ≤ pathDrift n) (markNonneg : ∀ n, 0 ≤ markDrift n)
    (blind : ∀ n who, Nonempty (LateDeliveryBlindness setup leaks bounds horizon scheduler
      (targetSequence n) who (LateOption := LateOption slots)
      (fun site option history => lateBlindFailure setup leaks bounds horizon scheduler
        (targetSequence n) site (onePacketLate setup leaks bounds horizon scheduler sequence
          scale scale_pos scale_le_one (slots := slots) n ((onePacketN).agentAt site) option)
        history)
      (pathDrift n) (unforcedDrift n) (beliefDrift n)))
    (marked : ∀ n who (site : (onePacketN).InformationSite who),
      ¬ UnforcedAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
      ownedKeyed (UnforcedAgent setup leaks bounds horizon scheduler)
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
            (PMF.pure choice) = 1 := by
  let witness := fun n who => Classical.choice (blind n who)
  refine ⟨fun n key option => match key with
      | none => 0
      | some key => 1 - expect ((witness n key.owner).recordLaw key)
          ((witness n key.owner).failureOf key option),
    fun n => pathDrift n + |unforcedDrift n| + |beliefDrift n| + markDrift n, ?_,
    fun n => add_nonneg (add_nonneg (add_nonneg (pathNonneg n) (abs_nonneg _)) (abs_nonneg _))
      (markNonneg n), ?_⟩
  · simpa using ((pathLimit.add unforcedLimit.abs).add beliefLimit.abs).add markLimit
  intro n who site _ keyed
  obtain ⟨past, view, event, atSite, _, _⟩ := keyed.1
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
          | some key => 1 - expect ((witness n key.owner).recordLaw key)
              ((witness n key.owner).failureOf key option)))| ≤
        pathDrift n + |unforcedDrift n| + |beliefDrift n| := by
    intro option
    have near := (witness n who).site_failure_near_key (pathNonneg n)
      ⟨some (past, view), decision⟩ _ rfl option
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
    have guarded : expect ((targetSequence n).belief who ⟨some (past, view), decision⟩)
        (fun history => lateBlindFailure setup leaks bounds horizon scheduler (targetSequence n)
          ⟨some (past, view), decision⟩
          (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one (slots := slots) n
            ((onePacketN).agentAt ⟨some (past, view), decision⟩) option) history) =
        expect ((targetSequence n).belief who ⟨some (past, view), decision⟩)
          (fun history => lateHistoryFailure setup leaks bounds horizon scheduler
            (targetSequence n) ⟨some (past, view), decision⟩
            (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
              scale_le_one (slots := slots) n
              ((onePacketN).agentAt ⟨some (past, view), decision⟩) option) history) := by
      refine expect_congr_on_support fun history _ => ?_
      unfold lateBlindFailure
      split
      · rfl
      · rename_i notLate
        exact (notLate keyed.1).elim
    rw [guarded] at near
    rw [bridge]
    change |expect _ _ - (1 - (1 - expect ((witness n who).recordLaw _)
      ((witness n who).failureOf _ option)))| ≤ _
    rw [sub_sub_cancel]
    linarith [le_abs_self (unforcedDrift n), le_abs_self (beliefDrift n)]
  refine ⟨fun option => (optionNear option).trans (by linarith [markNonneg n]),
    fun choice isMarked => ?_⟩
  rcases marked n who ⟨some (past, view), decision⟩ ‹_› keyed choice isMarked with
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
    (isKeyed : ownedKeyed (UnforcedAgent setup leaks bounds horizon scheduler)
      (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler) agent)
    (option : LateOption slots) :
    ∃ part, freeKeyedComponent (free := UnforcedAgent setup leaks bounds horizon scheduler)
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
      (keyed := ownedKeyed (UnforcedAgent setup leaks bounds horizon scheduler)
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
  /-- **Value blindness of late deliveries.** At every stage each player's late
  deliveries are value blind for the failure of the late options, with vanishing
  path, unforced and belief drifts. -/
  lateBlindness : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon
      scheduler slots p)) (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
    OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos scale_le_one
      weights targetSequence →
    (∀ n, (targetSequence n).IsFullyMixed) →
    (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
    ∃ (pathDrift unforcedDrift beliefDrift : ℕ → ℝ),
      Tendsto pathDrift atTop (nhds 0) ∧ Tendsto unforcedDrift atTop (nhds 0) ∧
      Tendsto beliefDrift atTop (nhds 0) ∧ (∀ n, 0 ≤ pathDrift n) ∧
      ∀ n who, Nonempty (LateDeliveryBlindness setup leaks bounds horizon scheduler
        (targetSequence n) who (LateOption := LateOption slots)
        (fun site option history => lateBlindFailure setup leaks bounds horizon scheduler
          (targetSequence n) site (onePacketLate setup leaks bounds horizon scheduler sequence
            scale scale_pos scale_le_one (slots := slots) n ((onePacketN).agentAt site) option)
          history)
        (pathDrift n) (unforcedDrift n) (beliefDrift n))
  /-- **Marked choices fail like late options.** At every forced late delivery,
  every marked choice fails within a vanishing drift of some late option, or
  surely. -/
  markedNearOption : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon
      scheduler slots p)) (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
    OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos scale_le_one
      weights targetSequence →
    (∀ n, (targetSequence n).IsFullyMixed) →
    (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
    ∃ markDrift : ℕ → ℝ, Tendsto markDrift atTop (nhds 0) ∧ (∀ n, 0 ≤ markDrift n) ∧
      ∀ n who (site : (onePacketN).InformationSite who),
        ¬ UnforcedAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ownedKeyed (UnforcedAgent setup leaks bounds horizon scheduler)
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
            (PMF.pure choice) = 1
  /-- **Projected decisions.** At every forced site with a value-changing choice,
  the projected view is a decision site of the intended game. -/
  projectedDecision : ∀ who (site : (onePacketN).InformationSite who),
    ValueChangingSite setup leaks bounds horizon scheduler site →
      setup.intendedModel.IsDecisionInfo who (projectView setup leaks who site.1)
  /-- **The forced-belief inputs** at every forced site with a value-changing
  choice, along every fully mixed Bayes sequence of assembled profiles. -/
  beliefInputs : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon
      scheduler slots p)) (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
    OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos scale_le_one
      weights targetSequence →
    (∀ n, (targetSequence n).IsFullyMixed) →
    (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
    ∀ who (site : (onePacketN).InformationSite who)
      (changing : ValueChangingSite setup leaks bounds horizon scheduler site),
      OnePacketBeliefInputs setup leaks bounds horizon scheduler sequence targetSequence site
        (projectedSite setup leaks (projectedDecision who site changing))
        (changingInput_decision setup leaks bounds horizon scheduler changing)
        rfl
  /-- **The per-history gain transport.** Away from late deliveries, every
  choice committing a value at the player's own turn has an
  intended policy at the intended site whose gain at the image of each history
  of the belief is, up to a vanishing error, at least the gain of the choice at
  that history; the intended history gains are bounded. The native continuation
  from a forced history after committing a value is the intended continuation
  after committing it, up to the error of transport from the boundary after the
  commitment; at a late delivery the commitment succeeds only with some
  probability and otherwise pays the exclusion payoff, which is at most the
  continuation value, so the bound is one-sided. -/
  valueTransport : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon
      scheduler slots p)) (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
    OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos scale_le_one
      weights targetSequence →
    (∀ n, (targetSequence n).IsFullyMixed) →
    (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
    ∃ (valueError : ℕ → ℝ) (bound : ℝ), Tendsto valueError atTop (nhds 0) ∧ 0 ≤ bound ∧
      ∀ n who (site : (onePacketN).InformationSite who) choice
        (forced : ¬ UnforcedAgent setup leaks bounds horizon scheduler
          ((onePacketN).agentAt site))
        (unkeyed : ¬ ownedKeyed (UnforcedAgent setup leaks bounds horizon scheduler)
          (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
          ((onePacketN).agentAt site))
        (unmarked : ¬ onePacketCompared setup leaks bounds horizon scheduler who site choice)
        (atTurn : CommitsAtTurn setup leaks bounds horizon scheduler who site choice),
        ∃ policy : setup.intendedModel.BehavioralPolicy who,
          (∀ history ∈ ((targetSequence n).belief who site).support,
            (onePacketN).historyGain ((onePacketN).truncatedRunner (2 * horizon + 1))
                (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler
                  parameter utility excludedPayoff) (payoffComponent setup) (targetSequence n)
                (site, ((targetSequence n).strategy who).withLaw site.1 (PMF.pure choice))
                history ≤
              setup.intendedModel.historyGain
                (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
                (intendedReadoutExclusion setup parameter utility excludedPayoff)
                (payoffComponent setup) (sequence n)
                (projectedSite setup leaks (projectedDecision who site
                  ⟨forced, unkeyed, choice, unmarked, atTurn⟩), policy)
                (replayProjection setup leaks bounds horizon scheduler
                  (projectedSite setup leaks (projectedDecision who site
                    ⟨forced, unkeyed, choice, unmarked, atTurn⟩)) site
                  (changingInput_decision setup leaks bounds horizon scheduler
                    ⟨forced, unkeyed, choice, unmarked, atTurn⟩)
                  rfl
                  history) +
                valueError n) ∧
          ∀ point, |setup.intendedModel.historyGain
              (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
              (intendedReadoutExclusion setup parameter utility excludedPayoff)
              (payoffComponent setup) (sequence n)
              (projectedSite setup leaks (projectedDecision who site
                ⟨forced, unkeyed, choice, unmarked, atTurn⟩), policy) point| ≤
            bound
  /-- **Late commitments against late options.** At every forced late delivery,
  every choice committing a value at the player's own turn gains at most what
  some late option gains, up to a vanishing error: sending now at a slot fails
  as the late option sending now at that slot does, and the committed value is
  worth at most the site's continuation value. -/
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
        ¬ UnforcedAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ownedKeyed (UnforcedAgent setup leaks bounds horizon scheduler)
          (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
          ((onePacketN).agentAt site) →
        ¬ onePacketCompared setup leaks bounds horizon scheduler who site choice →
        CommitsAtTurn setup leaks bounds horizon scheduler who site choice →
        ∃ option : LateOption slots,
          onePacketSiteGain setup leaks bounds horizon scheduler parameter utility excludedPayoff
              (targetSequence n) site (PMF.pure choice) ≤
            onePacketSiteGain setup leaks bounds horizon scheduler parameter utility
                excludedPayoff (targetSequence n) site
                (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
                  scale_le_one (slots := slots) n ((onePacketN).agentAt site) option) +
              lateError n

omit [Finite setup.intendedProtocol.History] in
/-- Site commonness of the open inputs, from value blindness and marked choices
failing like late options. -/
theorem OnePacketOpenInputs.siteCommonness
    {sequence : ℕ → setup.intendedModel.BehavioralAssessment} {slots : Nat}
    (inputs : OnePacketOpenInputs setup leaks bounds horizon scheduler parameter utility
      excludedPayoff sequence slots)
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
        ¬ UnforcedAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ownedKeyed (UnforcedAgent setup leaks bounds horizon scheduler)
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
  obtain ⟨pathDrift, unforcedDrift, beliefDrift, pathLimit, unforcedLimit, beliefLimit,
    pathNonneg, blind⟩ := inputs.lateBlindness weights targetSequence assembled mixed bayes
  obtain ⟨markDrift, markLimit, markNonneg, marked⟩ :=
    inputs.markedNearOption weights targetSequence assembled mixed bayes
  exact onePacket_siteCommonness setup leaks bounds horizon scheduler sequence inputs.scale
    inputs.scale_pos inputs.scale_le_one targetSequence pathDrift unforcedDrift beliefDrift
    markDrift pathLimit unforcedLimit beliefLimit markLimit pathNonneg markNonneg blind marked

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
  decomposition weights targetSequence assembled mixed bayes := by
    obtain ⟨continuation, error, errorLimit, value⟩ :=
      inputs.lateDecomposition weights targetSequence assembled mixed bayes
    obtain ⟨score, drift, driftLimit, driftNonneg, common⟩ :=
      inputs.siteCommonness setup leaks bounds horizon scheduler parameter utility
        excludedPayoff weights targetSequence assembled mixed bayes
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
      inputs.siteCommonness setup leaks bounds horizon scheduler parameter utility
        excludedPayoff weights targetSequence assembled mixed bayes
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
  otherComparisons weights targetSequence assembled mixed bayes _ := by
    classical
    obtain ⟨valueError, bound, valueLimit, boundNonneg, transport⟩ :=
      inputs.valueTransport weights targetSequence assembled mixed bayes
    obtain ⟨lateError, lateLimit, late⟩ :=
      inputs.lateCommitments weights targetSequence assembled mixed bayes
    let distance := fun (n : ℕ) {who : Player} (site : (onePacketN).InformationSite who)
        (changing : ValueChangingSite setup leaks bounds horizon scheduler site) =>
      ∑' point, |((((targetSequence n).belief who site).map
          (replayProjection setup leaks bounds horizon scheduler
          (projectedSite setup leaks (inputs.projectedDecision who site changing)) site
          (changingInput_decision setup leaks bounds horizon scheduler changing)
          rfl)) point).toReal -
        ((sequence n).belief who
          (projectedSite setup leaks (inputs.projectedDecision who site changing)) point).toReal|
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
          (Classical.not_not.mp present.2.1)
          (changingInput_turn setup leaks bounds horizon scheduler present.2).choose_spec
          (inputs.beliefInputs weights targetSequence assembled mixed bayes agent.1
            ⟨agent.2.1, present.1⟩ present.2)
      · simp only [agentDistance, present, ↓reduceDIte]
        exact tendsto_const_nhds
    refine ⟨fun n => |valueError n| + bound * ∑ agent, agentDistance n agent + |lateError n|,
      by simpa using (valueLimit.abs.add (beliefLimit.const_mul bound)).add lateLimit.abs,
      fun n who site notFree choice unmarked => ?_⟩
    have forced : ¬ UnforcedAgent setup leaks bounds horizon scheduler
        ((onePacketN).agentAt site) := fun unforced =>
      notFree (Finset.mem_filter.mpr ⟨Finset.mem_univ _, unforced⟩)
    have sumNonneg : 0 ≤ bound * ∑ agent, agentDistance n agent :=
      mul_nonneg boundNonneg (Finset.sum_nonneg fun agent _ => distanceNonneg n agent)
    by_cases atTurn : CommitsAtTurn setup leaks bounds horizon scheduler who site choice
    swap
    · left
      obtain ⟨response, chosen, material, sends, committed⟩ : ∃ response, choice.1 = some response ∧
          ∃ material, response.transmission = some material ∧
            ∃ event handle, material.call.packet = .commitment event handle := by
        by_contra none
        apply unmarked
        intro response chosen material sends event handle packet
        exact none ⟨response, chosen, material, sends, event, handle, packet⟩
      obtain ⟨event, handle, packet⟩ := committed
      have submitted : (runtime setup).submittedEvent? leaks response = some event := by
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
      exact add_nonneg (add_nonneg (abs_nonneg _) sumNonneg) (abs_nonneg _)
    by_cases keyedSite : ownedKeyed (UnforcedAgent setup leaks bounds horizon scheduler)
        (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
        ((onePacketN).agentAt site)
    · right
      left
      obtain ⟨option, optionLe⟩ := late n who site choice forced keyedSite unmarked atTurn
      obtain ⟨part, partEq⟩ := exists_part_eq_late setup leaks bounds horizon scheduler
        sequence inputs.scale inputs.scale_pos inputs.scale_le_one n keyedSite option
      refine ⟨PMF.pure part, ?_⟩
      rw [PMF.pure_bind, partEq]
      have := le_abs_self (lateError n)
      have := abs_nonneg (valueError n)
      change onePacketSiteGain setup leaks bounds horizon scheduler parameter utility
          excludedPayoff (targetSequence n) site (PMF.pure choice) ≤
        onePacketSiteGain setup leaks bounds horizon scheduler parameter utility excludedPayoff
          (targetSequence n) site (onePacketLate setup leaks bounds horizon scheduler sequence
            inputs.scale inputs.scale_pos inputs.scale_le_one (slots := slots) n
            ((onePacketN).agentAt site) option) + _
      linarith
    have unkeyed := keyedSite
    have changing : ValueChangingSite setup leaks bounds horizon scheduler site :=
      ⟨forced, unkeyed, choice, unmarked, atTurn⟩
    obtain ⟨policy, close, bounded⟩ := transport n who site choice forced unkeyed unmarked atTurn
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
    let := Fintype.ofFinite (setup.intendedModel.InformationHistory who
      (projectedSite setup leaks (inputs.projectedDecision who site changing)).1)
    have transported := (onePacketN).gain_le_sourceGain_add
      ((onePacketN).truncatedRunner (2 * horizon + 1))
      (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter utility
        excludedPayoff) (payoffComponent setup) (targetSequence n)
      (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
      (intendedReadoutExclusion setup parameter utility excludedPayoff) (payoffComponent setup)
      (sequence n) (site, ((targetSequence n).strategy who).withLaw site.1 (PMF.pure choice))
      (projectedSite setup leaks (inputs.projectedDecision who site changing), policy)
      (replayProjection setup leaks bounds horizon scheduler
          (projectedSite setup leaks (inputs.projectedDecision who site changing)) site
          (changingInput_decision setup leaks bounds horizon scheduler changing)
          rfl)
      (valueError n) bound close bounded
    have finiteDistance : distance n site changing = ∑ point,
        |((((targetSequence n).belief who site).map
          (replayProjection setup leaks bounds horizon scheduler
          (projectedSite setup leaks (inputs.projectedDecision who site changing)) site
          (changingInput_decision setup leaks bounds horizon scheduler changing)
          rfl)) point).toReal -
        ((sequence n).belief who
          (projectedSite setup leaks (inputs.projectedDecision who site changing)) point).toReal| :=
      tsum_fintype _
    have scaled := mul_le_mul_of_nonneg_left (finiteDistance ▸ siteLe) boundNonneg
    right
    right
    refine ⟨PMF.pure (projectedSite setup leaks (inputs.projectedDecision who site changing),
      policy), ?_⟩
    rw [expect_pure]
    linarith [le_abs_self (valueError n), abs_nonneg (lateError n)]
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
        scheduler parameter utility excludedPayoff wellFormed contract timely retains mixed bayes

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
        scheduler parameter utility excludedPayoff wellFormed contract timely retains mixed
          bayes)
    service observationRate deliveryRate delivery_nonnegative coverage lowerUtility upperUtility
    lower_le le_upper deposit deposit_nonnegative sufficient


end Open

end Vegas
