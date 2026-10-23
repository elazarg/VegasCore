/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketCompletionContent
import Vegas.Game.OnePacketSilence
import Vegas.Game.OnePacketReplayInputs
import Vegas.Game.OnePacketForcedPrefix

/-! # Unsettled content along forced histories

Fix an observer `who`. Along a native history of the one-packet game that ends
in a forced state of `who`, every state is forced for `who`, so the other
players transmit only at their own ready event, at most once
(`Vegas.onePacket_named_of_forcedObserver`,
`Vegas.onePacket_silent_of_forcedObserver`). Hence the following hold at every
state of the history (`Vegas.periodInvariant`, `Vegas.PeriodInvariant`):

* every packet of a player other than `who` names a completed or the ready
  event, and no two such packets of one player name the same event;
* while the ready event has an actor other than `who`, the unsettled content is
  one and that actor has sent nothing for the event, or the actor has sent one
  packet for it and the unsettled content is the mass that the intended
  assessment, at the actor's view of the decoded point, gives the content of
  that packet's call at a contract state from which every fixed meaning is kept
  and at which the packet's own handle is fixed (`Vegas.SentContent`);
* otherwise the unsettled content is one.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Keeping fixed meanings is transitive. -/
theorem keepsFixedCandidates_trans {first second third : EventGraphRuntime.State (graph setup)}
    (left : KeepsFixedCandidates first second) (right : KeepsFixedCandidates second third) :
    KeepsFixedCandidates first third := fun handle fixed => by
  rw [right handle (by rw [left handle fixed]; exact fixed), left handle fixed]

/-- A transition from a state with no actor either keeps the execution or is a
scheduler round of the execution. -/
theorem transition_idle_cases (initial : PMF (application setup leaks).State) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler) (control : (application setup leaks).Control)
    (idle : control.actor = none) (joint : Player → Option (application setup leaks).Action)
    {next : (application setup leaks).Control}
    (reached : some next ∈ ((application setup leaks).transition initial horizon scheduler
      (some control) joint).support) :
    next.execution = control.execution ∨ ∃ command,
      next.execution ∈ (control.execution.environmentStep (application setup leaks)
        command).support := by
  rcases control with ⟨remaining, current, execution⟩
  cases idle
  cases remaining with
  | zero =>
      cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp reached)
      exact Or.inl rfl
  | succ remaining =>
      obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨updated, supported, same⟩ := PMF.support_map .. ▸ moved
      cases Option.some.inj same
      exact Or.inr ⟨command, supported⟩

/-- A transition from a state with no actor keeps the network inputs. -/
theorem transition_idle_inputs (initial : PMF (application setup leaks).State) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler) (control : (application setup leaks).Control)
    (idle : control.actor = none) (joint : Player → Option (application setup leaks).Action)
    {next : (application setup leaks).Control}
    (reached : some next ∈ ((application setup leaks).transition initial horizon scheduler
      (some control) joint).support) :
    next.execution.network.inputs = control.execution.network.inputs := by
  rcases transition_idle_cases initial horizon scheduler control idle joint reached with
    same | ⟨command, moved⟩
  · rw [same]
  · exact (application setup leaks).environmentStep_inputs _ _ command moved

variable (setup) in
/-- **Sent content.** The unsettled content is the mass that the intended
assessment, at `sender`'s view of the decoded point of the configuration of
`control`, gives the content of `message`'s call at a contract state `sent`,
from which `control` keeps every fixed meaning, and at which a commitment
handle of `sender` in the call is fixed. -/
def SentContent (assessment : setup.intendedModel.BehavioralAssessment)
    (control : (application setup leaks).Control) (sender : Player)
    (message : Message Player (WitnessedPacket (graph setup))) (unsettled : ℝ) : Prop :=
  ∃ sent : EventGraphRuntime.State (graph setup),
    KeepsFixedCandidates sent control.execution.application ∧
    (∀ named handle, message.payload.call = .commitment named handle → handle.1 = sender →
      sent.candidates.lookup handle ≠ .fresh) ∧
    unsettled = (((assessment.strategy sender (setup.protocolObserve sender
        (decodedPoint setup control.execution.application.config))).map Subtype.val)
      (callContent setup sent message.payload.call)).toReal

variable (setup) in
/-- **The period invariant** of an observer `who` at a native control state,
for an unsettled content. -/
structure PeriodInvariant (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) (control : (application setup leaks).Control) (unsettled : ℝ) : Prop where
  named : ∀ message ∈ control.execution.network.inputs, message.sender ≠ who →
    ∀ event, message.payload.call.event? (graph setup) = some event →
      event ∈ control.execution.application.config.cut.completed ∨
        control.execution.application.config.cut.Ready event
  unique : ∀ first ∈ control.execution.network.inputs,
    ∀ second ∈ control.execution.network.inputs, first.sender ≠ who →
      first.sender = second.sender → ∀ event,
      first.payload.call.event? (graph setup) = some event →
      second.payload.call.event? (graph setup) = some event → first = second
  settled : ∀ event, control.execution.application.config.cut.Ready event →
    ∀ sender, (graph setup).actor? event = some sender → sender ≠ who →
      (unsettled = 1 ∧ ∀ message ∈ control.execution.network.inputs, message.sender = sender →
        message.payload.call.event? (graph setup) ≠ some event) ∨
      ∃ message ∈ control.execution.network.inputs, message.sender = sender ∧
        message.payload.call.event? (graph setup) = some event ∧
        SentContent setup assessment control sender message unsettled
  quiet : (∀ event, control.execution.application.config.cut.Ready event →
    ∀ sender, (graph setup).actor? event = some sender → sender = who) → unsettled = 1

/-- The period invariant transfers to a state with the same inputs and
configuration whose contract state keeps every fixed meaning. -/
theorem PeriodInvariant.transport {assessment : setup.intendedModel.BehavioralAssessment}
    {who : Player} {control next : (application setup leaks).Control} {unsettled : ℝ}
    (invariant : PeriodInvariant setup assessment who control unsettled)
    (inputs : next.execution.network.inputs = control.execution.network.inputs)
    (config : next.execution.application.config = control.execution.application.config)
    (kept : KeepsFixedCandidates control.execution.application next.execution.application) :
    PeriodInvariant setup assessment who next unsettled where
  named message member := by
    rw [inputs] at member
    rw [config]
    exact invariant.named message member
  unique first firstMember second secondMember := by
    rw [inputs] at firstMember secondMember
    exact invariant.unique first firstMember second secondMember
  settled event ready sender acts other := by
    rw [config] at ready
    rcases invariant.settled event ready sender acts other with ⟨one, none⟩ | ⟨message, member,
        sent, named, content⟩
    · exact Or.inl ⟨one, fun message member => by rw [inputs] at member; exact none message member⟩
    · obtain ⟨state, keep, fixed, eq⟩ := content
      refine Or.inr ⟨message, by rw [inputs]; exact member, sent, named, state,
        keepsFixedCandidates_trans keep kept, fixed, ?_⟩
      rw [config]
      exact eq
  quiet only := invariant.quiet fun event ready => only event (by rw [config]; exact ready)

/-- The period invariant survives an emission of `who` itself. -/
theorem PeriodInvariant.emitOwn {assessment : setup.intendedModel.BehavioralAssessment}
    {who : Player} {control next : (application setup leaks).Control} {unsettled : ℝ}
    (invariant : PeriodInvariant setup assessment who control unsettled)
    (envelope : Message Player (application setup leaks).Payload) (own : envelope.sender = who)
    (inputs : next.execution.network.inputs = control.execution.network.inputs ++ [envelope])
    (config : next.execution.application.config = control.execution.application.config)
    (kept : KeepsFixedCandidates control.execution.application next.execution.application) :
    PeriodInvariant setup assessment who next unsettled := by
  have old : ∀ message ∈ next.execution.network.inputs, message.sender ≠ who →
      message ∈ control.execution.network.inputs := fun message member other => by
    rw [inputs, List.mem_append, List.mem_singleton] at member
    rcases member with present | rfl
    · exact present
    · exact (other own).elim
  refine ⟨fun message member other => ?_, fun first firstMember second secondMember other
      same => ?_, fun event ready sender acts different => ?_, fun only => ?_⟩
  · rw [config]
    exact invariant.named message (old message member other) other
  · exact invariant.unique first (old first firstMember other) second
      (old second secondMember (same ▸ other)) other same
  · rw [config] at ready
    rcases invariant.settled event ready sender acts different with ⟨one, none⟩ |
        ⟨message, member, sent, named, content⟩
    · refine Or.inl ⟨one, fun message member from_ => ?_⟩
      exact none message (old message member (from_ ▸ different)) from_
    · obtain ⟨state, keep, fixed, eq⟩ := content
      refine Or.inr ⟨message, by rw [inputs]; exact List.mem_append_left _ member, sent, named,
        state, keepsFixedCandidates_trans keep kept, fixed, ?_⟩
      rw [config]
      exact eq
  · exact invariant.quiet fun event ready => only event (by rw [config]; exact ready)

variable [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- The source view of a player at an initialized state is its view of the
decoded point. -/
theorem sourceViewOf_eq_decodedPoint (who : Player)
    {control : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control)) :
    sourceViewOf setup leaks who (control.execution.observe (application setup leaks) who) =
      setup.protocolObserve who (decodedPoint setup control.execution.application.config) := by
  obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (failureProfile setup.program)
    (bounds.onePacketMenu (runtime setup) leaks) horizon scheduler trace control rfl
  rw [decodedPoint_eq residual]
  exact projectView_observe setup leaks who control.execution rank residual.checkpoint.ordered _
    residual.decode (control.execution.recall who)

/-- **The period invariant** holds at every state of a native history of the
one-packet game ending in a forced state of `who`. -/
theorem periodInvariant (assessment : setup.intendedModel.BehavioralAssessment) (who : Player) :
    ∀ {state} (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state)
      (control : (application setup leaks).Control), state = some control →
      ForcedState setup leaks who (some control) →
      PeriodInvariant setup assessment who control
        (unsettledContent setup leaks bounds horizon scheduler assessment who trace)
  | _, .start, _, current, _ => by cases current
  | _, .extend (source := before) (target := after) prior joint legal realized, control,
      current, forced => by
      have recursive := fun next same forcedNext =>
        periodInvariant assessment who prior next same forcedNext
      subst current
      change some control ∈ ((application setup leaks).transition (initialLaw setup) horizon
        scheduler before joint).support at realized
      have kept := (keepsFixedCandidates_step (runtime setup) leaks).transition (initialLaw setup)
        horizon scheduler
      cases before with
      | none =>
          obtain rfl := trace_eq_start_of_none prior
          change some control ∈ ((initialLaw setup).map fun state => some
            (⟨horizon, none, ReactiveApplication.Execution.initial (application setup leaks)
              state⟩ : (application setup leaks).Control)).support at realized
          obtain ⟨state, _, same⟩ := PMF.support_map .. ▸ realized
          cases Option.some.inj same
          refine ⟨fun _ member => (List.not_mem_nil member).elim,
            fun _ member => (List.not_mem_nil member).elim, fun _ _ _ _ _ => Or.inl ⟨rfl,
              fun _ member => (List.not_mem_nil member).elim⟩, fun _ => rfl⟩
      | some current =>
          have forcedBefore := forcedState_of_transition prior joint realized forced
          have earlier := recursive current rfl forcedBefore
          have keep := kept current control joint realized
          cases acting : current.actor with
          | some actor =>
              rw [transition_respond current acting joint, PMF.mem_support_pure_iff] at realized
              cases Option.some.inj realized
              have localLegal := legal.2 actor
              have active : (application setup leaks).actor (some current) = some actor := acting
              obtain ⟨response, picked⟩ : ∃ response, joint actor = some response := by
                cases chosen : joint actor with
                | none =>
                    rw [chosen] at localLegal
                    exact (localLegal active).elim
                | some response => exact ⟨response, rfl⟩
              rw [picked] at localLegal
              simp only [picked, Option.getD_some] at keep ⊢
              have member : response ∈ bounds.onePacketActions (runtime setup) leaks actor
                  (current.execution.recall actor)
                  (current.execution.observe (application setup leaks) actor) := localLegal.2
              have configEq := ((runtime setup).reactive_respond_application leaks
                current.execution actor response).1
              rcases response with ⟨transmission⟩
              cases transmission with
              | none =>
                  have stepEq : unsettledStep setup leaks assessment who
                      (unsettledContent setup leaks bounds horizon scheduler assessment who prior)
                      (some current) joint (some { current with
                        actor := none
                        execution := current.execution.respond (application setup leaks) actor
                          ((joint actor).getD ⟨none⟩) }) =
                      unsettledContent setup leaks bounds horizon scheduler assessment who
                        prior := by
                    simp only [unsettledStep, acting, picked, Option.getD_some, contentFactor]
                    split_ifs <;> ring
                  change PeriodInvariant setup assessment who _ (unsettledStep setup leaks
                    assessment who _ (some current) joint _)
                  rw [stepEq]
                  exact earlier.transport rfl configEq keep
              | some material =>
                  have inputsEq : (current.execution.respond (application setup leaks) actor
                      ⟨some material⟩).network.inputs = current.execution.network.inputs ++
                        [⟨(actor, current.execution.network.nextSerial actor),
                          (application setup leaks).packet ((application setup leaks).submit
                            current.execution.application actor material) actor
                            (current.execution.network.known actor) material⟩] := rfl
                  by_cases own : actor = who
                  · subst own
                    have stepEq : unsettledStep setup leaks assessment actor
                        (unsettledContent setup leaks bounds horizon scheduler assessment actor
                          prior) (some current) joint (some { current with
                          actor := none
                          execution := current.execution.respond (application setup leaks) actor
                            ((joint actor).getD ⟨none⟩) }) =
                        unsettledContent setup leaks bounds horizon scheduler assessment actor
                          prior := by
                      simp only [unsettledStep, acting, ↓reduceIte]
                    change PeriodInvariant setup assessment actor _ (unsettledStep setup leaks
                      assessment actor _ (some current) joint _)
                    rw [stepEq]
                    exact earlier.emitOwn _ rfl inputsEq configEq keep
                  · obtain ⟨event, ready, named, acts⟩ := onePacket_named_of_forcedObserver bounds
                      horizon scheduler who prior forcedBefore actor own member
                    have rawTrace := (bounds.onePacketMenu (runtime setup) leaks).toRawTrace
                      (initialLaw setup) horizon scheduler prior
                    obtain ⟨inputRecall, _, _⟩ := (runtime setup).countRecall_history leaks
                      rawTrace
                    rcases earlier.settled event ready actor acts own with ⟨one, nothing⟩ |
                        ⟨message, present, sender, messageNamed, _⟩
                    · have stepEq : unsettledStep setup leaks assessment who
                          (unsettledContent setup leaks bounds horizon scheduler assessment who
                            prior) (some current) joint (some { current with
                            actor := none
                            execution := current.execution.respond (application setup leaks)
                              actor ((joint actor).getD ⟨none⟩) }) =
                          contentFactor setup leaks assessment actor current.execution
                            (current.execution.respond (application setup leaks) actor
                              ⟨some material⟩) ⟨some material⟩ := by
                        simp only [unsettledStep, acting, own, ↓reduceIte, picked,
                          Option.getD_some, one, one_mul]
                      change PeriodInvariant setup assessment who _ (unsettledStep setup leaks
                        assessment who _ (some current) joint _)
                      rw [stepEq]
                      set envelope : Message Player (application setup leaks).Payload :=
                        ⟨(actor, current.execution.network.nextSerial actor),
                          (application setup leaks).packet ((application setup leaks).submit
                            current.execution.application actor material) actor
                            (current.execution.network.known actor) material⟩ with envelopeEq
                      have envelopeCall : envelope.payload.call = material.call.packet := rfl
                      have envelopeSender : envelope.sender = actor := rfl
                      have envelopeNamed : envelope.payload.call.event? (graph setup) =
                          some event := by rw [envelopeCall]; exact named
                      have cases_ : ∀ message ∈ (current.execution.respond
                          (application setup leaks) actor ⟨some material⟩).network.inputs,
                          message ∈ current.execution.network.inputs ∨ message = envelope :=
                        fun message member => by
                          rw [inputsEq, List.mem_append, List.mem_singleton] at member
                          exact member
                      refine ⟨fun message member other x messageNamed => ?_,
                        fun first firstMember second secondMember other same x firstNamed
                          secondNamed => ?_, fun event' ready' sender' acts' other' => ?_,
                        fun only => ?_⟩
                      · change _ ∈ (current.execution.respond (application setup leaks) actor
                          ⟨some material⟩).application.config.cut.completed ∨ _
                        rw [configEq]
                        rcases cases_ message member with present | rfl
                        · exact earlier.named message present other x messageNamed
                        · rw [envelopeNamed] at messageNamed
                          cases messageNamed
                          exact Or.inr ready
                      · rcases cases_ first firstMember with firstOld | rfl <;>
                          rcases cases_ second secondMember with secondOld | rfl
                        · exact earlier.unique first firstOld second secondOld other same x
                            firstNamed secondNamed
                        · rw [envelopeNamed] at secondNamed
                          cases secondNamed
                          exact (nothing first firstOld (same.trans envelopeSender)
                            firstNamed).elim
                        · rw [envelopeNamed] at firstNamed
                          cases firstNamed
                          exact (nothing second secondOld (same.symm.trans envelopeSender)
                            secondNamed).elim
                        · rfl
                      · change (current.execution.respond (application setup leaks) actor
                          ⟨some material⟩).application.config.cut.Ready event' at ready'
                        rw [configEq] at ready'
                        have sameEvent := ready_unique (setup := setup) _ ready' ready
                        subst sameEvent
                        have sameSender : sender' = actor :=
                          Option.some.inj (acts'.symm.trans acts)
                        subst sameSender
                        have emitted : envelope ∈ (current.execution.respond
                            (application setup leaks) sender'
                              ⟨some material⟩).network.inputs := by
                          rw [inputsEq]
                          exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
                        refine Or.inr ⟨envelope, emitted, envelopeSender, envelopeNamed,
                          (current.execution.respond (application setup leaks)
                            sender' ⟨some material⟩).application, fun _ _ => rfl, ?_, ?_⟩
                        · intro named' handle call owned
                          rw [envelopeCall] at call
                          obtain ⟨owner, slot⟩ := handle
                          change owner = sender' at owned
                          subst owned
                          change (submitStep (material.call.register current.execution.application
                            owner) owner material.call.packet).candidates.lookup (owner, slot) ≠
                              .fresh
                          rw [call]
                          exact submitStep_commitment_fixed _ owner named' slot
                        · unfold contentFactor
                          change ((((assessment.strategy sender' (sourceViewOf setup leaks sender'
                              (current.execution.observe (application setup leaks) sender'))).map
                                Subtype.val) (sentSourceAction setup leaks
                                  (current.execution.respond (application setup leaks) sender'
                                    ⟨some material⟩) ⟨some material⟩))).toReal = _
                          rw [sourceViewOf_eq_decodedPoint sender' prior,
                            sentSourceAction_eq_callContent]
                          change _ = (((assessment.strategy sender' (setup.protocolObserve sender'
                            (decodedPoint setup (current.execution.respond
                              (application setup leaks) sender'
                                ⟨some material⟩).application.config))).map Subtype.val)
                            (callContent setup _ envelope.payload.call)).toReal
                          rw [configEq, envelopeCall]
                      · exfalso
                        change ∀ event, (current.execution.respond (application setup leaks)
                          actor ⟨some material⟩).application.config.cut.Ready event → _ at only
                        rw [configEq] at only
                        exact own (only event ready actor acts)
                    · exfalso
                      have silent := onePacket_silent_of_forcedObserver bounds horizon scheduler
                        who prior forcedBefore ready actor own (fun _ => ⟨message, by
                          rw [← inputRecall actor]
                          exact List.mem_filter.mpr ⟨present, by simp [sender]⟩,
                          messageNamed⟩) _ member
                      cases silent
          | none =>
              have inputsEq := transition_idle_inputs (initialLaw setup) horizon scheduler current
                acting joint realized
              rcases transition_configStep (initialLaw setup) horizon scheduler current control
                  joint realized with same | ⟨event, ready, action, member⟩
              · have dropped : control.execution.application.config.history.drop
                    current.execution.application.config.history.length = [] := by
                  rw [same, List.drop_length]
                have stepEq : unsettledStep setup leaks assessment who
                    (unsettledContent setup leaks bounds horizon scheduler assessment who prior)
                    (some current) joint (some control) =
                    unsettledContent setup leaks bounds horizon scheduler assessment who prior := by
                  simp only [unsettledStep, acting, dropped]
                change PeriodInvariant setup assessment who _ (unsettledStep setup leaks
                  assessment who _ (some current) joint _)
                rw [stepEq]
                exact earlier.transport inputsEq same keep
              · have dropped : control.execution.application.config.history.drop
                    current.execution.application.config.history.length = [⟨event, action⟩] := by
                  rw [EventGraph.Config.step_history _ event ready action _ member,
                    List.drop_left]
                have one : unsettledStep setup leaks assessment who
                    (unsettledContent setup leaks bounds horizon scheduler assessment who prior)
                    (some current) joint (some control) = 1 := by
                  simp only [unsettledStep, acting, dropped]
                  cases owner : (graph setup).actor? event with
                  | some _ => rfl
                  | none =>
                      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
                      refine earlier.quiet fun other otherReady sender acts => ?_
                      have sameEvent := ready_unique (setup := setup) _ otherReady ready
                      subst sameEvent
                      rw [owner] at acts
                      cases acts
                change PeriodInvariant setup assessment who _ (unsettledStep setup leaks
                  assessment who _ (some current) joint _)
                rw [one]
                have completedNow : ∀ x, x ∈ current.execution.application.config.cut.completed ∨
                    current.execution.application.config.cut.Ready x →
                    x ∈ control.execution.application.config.cut.completed := by
                  intro x status
                  rw [current.execution.application.config.step_cut event ready action _ member,
                    EventOrder.Cut.mem_complete]
                  rcases status with done | otherReady
                  · exact Or.inr done
                  · exact Or.inl (ready_unique (setup := setup) _ otherReady ready)
                have allCompleted : ∀ message ∈ control.execution.network.inputs,
                    message.sender ≠ who → ∀ x, message.payload.call.event? (graph setup) =
                      some x → x ∈ control.execution.application.config.cut.completed :=
                  fun message member other x named => completedNow x
                    (earlier.named message (inputsEq ▸ member) other x named)
                refine ⟨fun message member other x named =>
                    Or.inl (allCompleted message member other x named),
                  fun first firstMember second secondMember =>
                    earlier.unique first (inputsEq ▸ firstMember) second
                      (inputsEq ▸ secondMember),
                  fun event' ready' sender' acts' other' => Or.inl ⟨rfl,
                    fun message member sent named => ready'.1 (allCompleted message member
                      (sent ▸ other') event' named)⟩, fun _ => rfl⟩

end Vegas
