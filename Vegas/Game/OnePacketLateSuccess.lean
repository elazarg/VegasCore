/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AnchoredHonestLaw
import Interaction.ReactiveAnchoredSupport
import Interaction.ReactiveResponseAccounting
import GameTheoryExtensions.Analysis.Protocol.StoppedTerminalBound
import Vegas.Game.OnePacketEventFailure
import Vegas.Game.OnePacketEventSuccess
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # The successful part of a late delivery

**Pending steps.** While the event of rank `rank` is pending, every control
step keeps the completed prefix and the recorded views below the event, or
completes the event at scheduler control, with the recorded views unchanged
(`Vegas.pendingTransition`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

variable (setup leaks) in
/-- The configuration is a prefix of `rank` and the recorded views saw nothing
beyond it. -/
def PendingAt (rank : Nat) (execution : (application setup leaks).Execution) : Prop :=
  execution.application.config.cut.IsPrefix rank ∧ ReadySeen setup leaks rank execution

/-- **Pending steps.** From a state pending at `rank`, every transition keeps it
pending at `rank`, or completes the event of rank `rank` at scheduler control
with the recorded views still seeing nothing beyond `rank`. -/
theorem pendingTransition {initial : PMF (application setup leaks).State} {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {rank remaining : Nat}
    {actor : Option Player} {execution : (application setup leaks).Execution}
    (pending : PendingAt setup leaks rank execution)
    (joint : Player → Option (application setup leaks).Action)
    {after : (application setup leaks).ProtocolState}
    (reached : after ∈ ((application setup leaks).transition initial horizon scheduler
      (some ⟨remaining, actor, execution⟩) joint).support) :
    ∃ control : (application setup leaks).Control, after = some control ∧
      (PendingAt setup leaks rank control.execution ∨
        (control.actor = none ∧ control.execution.application.config.cut.IsPrefix (rank + 1) ∧
          ReadySeen setup leaks rank control.execution)) := by
  let app := application setup leaks
  obtain ⟨ordered, seen⟩ := pending
  cases actor with
  | some who =>
      change after ∈ (PMF.pure _).support at reached
      rw [PMF.mem_support_pure_iff] at reached
      subst reached
      refine ⟨_, rfl, Or.inl ⟨?_, ?_⟩⟩
      · change (execution.respond app who ((joint who).getD ⟨none⟩)).application.config.cut.IsPrefix
          rank
        rw [((runtime setup).reactive_respond_application leaks execution who _).1]
        exact ordered
      · intro observer entry member event readyView
        rcases app.respond_entry_origin execution who observer _ entry member with
          prior | ⟨_, fresh⟩
        · exact seen observer entry prior event readyView
        · rw [fresh] at readyView
          change execution.application.publicView.EventReady event at readyView
          exact ((ready_iff_rank setup _ rank ordered event).mp
            ((State.publicView_eventReady _ event).mp readyView)).le
  | none =>
      cases remaining with
      | zero =>
          change after ∈ (PMF.pure _).support at reached
          rw [PMF.mem_support_pure_iff] at reached
          subst reached
          exact ⟨_, rfl, Or.inl ⟨ordered, seen⟩⟩
      | succ remaining =>
          obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
          obtain ⟨next, stepped, rfl⟩ := PMF.support_map .. ▸ moved
          have recallEq := app.environmentStep_recall execution next command stepped
          have nextSeen : ReadySeen setup leaks rank next := by
            intro observer entry member
            rw [recallEq] at member
            exact seen observer entry member
          refine ⟨_, rfl, ?_⟩
          rcases (environmentStep_configStep setup leaks execution next command stepped).prefix
              rank ordered with same | advanced
          · exact Or.inl ⟨by rw [same]; exact ordered, nextSeen⟩
          · right
            refine ⟨?_, advanced, nextSeen⟩
            cases command with
            | activate who =>
                exfalso
                have sameApp := activation_application setup leaks execution next who stepped
                have inside : rank < (graph setup).order.eventCount := by
                  have := advanced.1
                  omega
                have rankLt := (advanced.2 ⟨rank, inside⟩).mpr (Nat.lt_succ_self _)
                rw [sameApp] at rankLt
                exact Nat.lt_irrefl _ ((ordered.2 _).mp rankLt)
            | wait | «include» _ | application _ => rfl

/-- Every execution of a legal history of the default runtime is pending at
some rank: its configuration is a prefix, and its recorded views saw nothing
beyond it. -/
theorem pendingAt_serviceInvariant (scheduler : (application setup leaks).Scheduler) :
    (application setup leaks).ServiceInvariant scheduler
      (fun execution => ∃ rank, PendingAt setup leaks rank execution) where
  respond execution who action valid := by
    obtain ⟨rank, ordered, seen⟩ := valid
    refine ⟨rank, ?_, ?_⟩
    · rw [((runtime setup).reactive_respond_application leaks execution who action).1]
      exact ordered
    · intro observer entry member event readyView
      rcases (application setup leaks).respond_entry_origin execution who observer action entry
          member with prior | ⟨_, fresh⟩
      · exact seen observer entry prior event readyView
      · rw [fresh] at readyView
        change execution.application.publicView.EventReady event at readyView
        exact ((ready_iff_rank setup _ rank ordered event).mp
          ((State.publicView_eventReady _ event).mp readyView)).le
  environment execution next command valid _ stepped := by
    obtain ⟨rank, ordered, seen⟩ := valid
    have recallEq := (application setup leaks).environmentStep_recall execution next command
      stepped
    rcases (environmentStep_configStep setup leaks execution next command stepped).prefix rank
        ordered with same | advanced
    · refine ⟨rank, by rw [same]; exact ordered, fun observer entry member => ?_⟩
      rw [recallEq] at member
      exact seen observer entry member
    · refine ⟨rank + 1, advanced, fun observer entry member event readyView => ?_⟩
      rw [recallEq] at member
      exact (seen observer entry member event readyView).trans (Nat.le_succ _)

/-- Every execution reached along a legal history of the default runtime is
pending at some rank. -/
theorem pendingAt_history {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control)) :
    ∃ rank, PendingAt setup leaks rank control.execution :=
  (pendingAt_serviceInvariant scheduler).history (initialLaw setup) horizon
    (fun state supported => by
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact ⟨0, EventOrder.Cut.empty_isPrefix _, fun _ entry member =>
        by simp [ReactiveApplication.Execution.initial] at member⟩) trace

/-- A completed event whose output is not a failure stays so under every
transition. -/
theorem succeeded_transition {initial : PMF (application setup leaks).State} {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} (event : (graph setup).EventId)
    {control : (application setup leaks).Control}
    (completed : event ∈ control.execution.application.config.cut.completed)
    (succeeded : ¬ StoreEventFailed control.execution.application.config.store event)
    (joint : Player → Option (application setup leaks).Action)
    {after : (application setup leaks).ProtocolState}
    (reached : after ∈ ((application setup leaks).transition initial horizon scheduler
      (some control) joint).support) :
    ∃ next : (application setup leaks).Control, after = some next ∧
      event ∈ next.execution.application.config.cut.completed ∧
      ¬ StoreEventFailed next.execution.application.config.store event := by
  let app := application setup leaks
  rcases control with ⟨remaining, actor, execution⟩
  cases actor with
  | some who =>
      change after ∈ (PMF.pure _).support at reached
      rw [PMF.mem_support_pure_iff] at reached
      subst reached
      have configEq := ((runtime setup).reactive_respond_application leaks execution who
        ((joint who).getD ⟨none⟩)).1
      refine ⟨_, rfl, ?_, ?_⟩
      · change event ∈ (execution.respond app who _).application.config.cut.completed
        rw [configEq]
        exact completed
      · change ¬ StoreEventFailed (execution.respond app who _).application.config.store event
        rw [configEq]
        exact succeeded
  | none =>
      cases remaining with
      | zero =>
          change after ∈ (PMF.pure _).support at reached
          rw [PMF.mem_support_pure_iff] at reached
          subst reached
          exact ⟨_, rfl, completed, succeeded⟩
      | succ remaining =>
          obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
          obtain ⟨next, stepped, rfl⟩ := PMF.support_map .. ▸ moved
          refine ⟨_, rfl, ?_⟩
          rcases environmentStep_configStep setup leaks execution next command stepped with
            same | ⟨other, ready, action, member⟩
          · change event ∈ next.application.config.cut.completed ∧
              ¬ StoreEventFailed next.application.config.store event
            rw [same]
            exact ⟨completed, succeeded⟩
          · have different : event ≠ other := fun equal => ready.1 (equal ▸ completed)
            obtain ⟨value, valueEq⟩ := step_complete_of_mem member
            change event ∈ next.application.config.cut.completed ∧
              ¬ StoreEventFailed next.application.config.store event
            rw [valueEq]
            refine ⟨?_, ?_⟩
            · change event ∈ (execution.application.config.cut.complete other ready).completed
              exact (EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inr completed)
            · rintro ⟨stored, read, failure⟩
              apply succeeded
              refine ⟨stored, ?_, failure⟩
              change execution.application.config.outputs event = some stored
              rw [← EventGraph.Config.complete_output_of_ne _ _ _ ready action value different]
              exact read

/-- **A successful output keeps play off the event's failure.** From a history
of the one-packet game whose configuration has completed an event without
recording a failure of it, terminal play under any profile never reaches an
event-level failed history of any player for that event. -/
theorem not_eventFailedHistory_of_succeeded (bounds : MessageBounds (graph setup))
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler} [Fintype Player]
    (profile : ∀ who,
      (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).BehavioralPolicy who)
    (certificate : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (event : (graph setup).EventId)
    (stop : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History) {control : (application setup leaks).Control}
    (state : stop.state = some control)
    (completed : event ∈ control.execution.application.config.cut.completed)
    (succeeded : ¬ StoreEventFailed control.execution.application.config.store event)
    (player : Player) :
    ∀ final ∈ ((onePacketModel setup leaks bounds (initialLaw setup) horizon
        scheduler).runBehavioralTerminalFrom certificate profile stop).support,
      final ∉ EventFailedHistory setup leaks bounds horizon scheduler player event := by
  intro final member
  obtain ⟨last, lastState, _, lastSucceeded⟩ :=
    (onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).runBehavioralTerminalFrom_support_closed certificate profile
      (fun current => ∃ next : (application setup leaks).Control, current = some next ∧
        event ∈ next.execution.application.config.cut.completed ∧
        ¬ StoreEventFailed next.execution.application.config.store event)
      (fun current joint _ target ⟨now, nowState, nowCompleted, nowSucceeded⟩ realized => by
        subst nowState
        exact succeeded_transition (initial := initialLaw setup) (horizon := horizon) event
          nowCompleted nowSucceeded joint realized)
      stop ⟨control, state, completed, succeeded⟩ final member
  change sourceReadout setup leaks final.state ∉ EventFailedReadout setup player event
  rw [lastState]
  exact not_mem_eventFailedReadout_of_store setup leaks last player event lastSucceeded

/-- Complete rounds only extend a completed prefix. -/
theorem runRounds_isPrefix (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy) :
    ∀ (count : Nat) (execution next : (application setup leaks).Execution) (rank : Nat),
      execution.application.config.cut.IsPrefix rank →
      next ∈ ((application setup leaks).runRounds scheduler players count execution).support →
      ∃ later, rank ≤ later ∧ next.application.config.cut.IsPrefix later := by
  intro count
  induction count with
  | zero =>
      intro execution next rank ordered reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨rank, le_rfl, ordered⟩
  | succ count ih =>
      intro execution next rank ordered reached
      obtain ⟨middle, moved, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      rcases (round_configStep setup leaks scheduler players execution middle moved).prefix rank
          ordered with same | advanced
      · obtain ⟨later, grows, holds⟩ := ih middle next rank (by rw [same]; exact ordered) rest
        exact ⟨later, grows, holds⟩
      · obtain ⟨later, grows, holds⟩ := ih middle next (rank + 1) advanced rest
        exact ⟨later, by omega, holds⟩

/-- States reached by rounds from an anchor only extend its completed prefix. -/
theorem runRoundsSupported_isPrefix {scheduler : (application setup leaks).Scheduler}
    {players : Player → (application setup leaks).Policy}
    {anchor : (application setup leaks).Execution} {rank : Nat}
    (ordered : anchor.application.config.cut.IsPrefix rank)
    {state : (application setup leaks).ProtocolState}
    (supported : (application setup leaks).RunRoundsSupported scheduler players anchor state)
    {control : (application setup leaks).Control} (current : state = some control) :
    ∃ later, rank ≤ later ∧ control.execution.application.config.cut.IsPrefix later := by
  subst current
  rcases control with ⟨remaining, actor, execution⟩
  cases actor with
  | none =>
      obtain ⟨count, reached⟩ := supported
      exact runRounds_isPrefix scheduler players count anchor execution rank ordered reached
  | some who =>
      obtain ⟨count, prior, command, priorMem, _, _, stepped⟩ := supported
      obtain ⟨middle, grows, holds⟩ :=
        runRounds_isPrefix scheduler players count anchor prior rank ordered priorMem
      rcases (environmentStep_configStep setup leaks prior execution command stepped).prefix
          middle holds with same | advanced
      · exact ⟨middle, grows, by rw [same]; exact holds⟩
      · exact ⟨middle + 1, by omega, advanced⟩

section Success

variable [Fintype Player] (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

variable (setup leaks) in
/-- The event of rank `rank` has completed: the configuration is a prefix of
`rank + 1`. -/
def LateStopped (rank : Nat) (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol
    (initialLaw setup) horizon scheduler).History) : Prop :=
  ∃ control : (application setup leaks).Control, history.state = some control ∧
    control.execution.application.config.cut.IsPrefix (rank + 1)

variable (setup) in
/-- The source continuation value of a profile at a point: the expected
exclusion payoff of `who` under the typed readout of its continuation. -/
def sourcePointValue (profile : BehavioralProfile setup.program) (who : Player)
    (point : ProtocolState setup.program) : ℝ :=
  expect ((ProtocolState.continuationLaw setup.program profile point).map some)
    (fun readout => exclusionReadoutUtility setup parameter utility excludedPayoff readout who)

open Classical in
variable (setup leaks) in
/-- **The value after a completion.** At a history whose configuration decodes,
after `rank + 1` events, to a point of the intended game, and whose control
satisfies `fresh`, the source continuation value of `profile` there; elsewhere
the fallback. -/
def completionValue (profile : BehavioralProfile setup.program) (rank : Nat)
    (fresh : (application setup leaks).Control → Prop) (who : Player)
    (fallback : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History → ℝ)
    (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History) : ℝ :=
  match history.state with
  | none => fallback history
  | some control =>
      match sourceServicePrefix? setup (rank + 1) control.execution.application.config with
      | none => fallback history
      | some point =>
          if ProtocolState.Intended setup.program point ∧ fresh control then
            sourcePointValue setup parameter utility excludedPayoff profile who point
          else fallback history

end Success

section Transport

variable [Fintype Player] (bounds : MessageBounds (graph setup)) {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

/-- One step of play in the one-packet game follows a transition of the
runtime. -/
theorem onePacket_step_transition
    (profile : ∀ who,
      (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).BehavioralPolicy who)
    {history next : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History}
    (running : ¬ ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).terminal history.state)
    (member : next ∈ ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).runBehavioralFrom profile 1 history).support) :
    ∃ joint : Player → Option (application setup leaks).Action,
      next.state ∈ ((application setup leaks).transition (initialLaw setup) horizon scheduler
        history.state joint).support := by
  obtain ⟨⟨joint, _, realized⟩, _⟩ :=
    (onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).mem_support_runBehavioralFrom_one profile running member
  exact ⟨joint, realized⟩

end Transport

end Vegas
