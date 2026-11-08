/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketLateCompletion
import Vegas.Game.OnePacketCompletionLaw
import Vegas.Game.OnePacketDecodedActor
import GameTheoryExtensions.Analysis.Protocol.StoppedExitBound
import Interaction.ReactiveStoppedState
import Vegas.Game.OnePacketLateSending

/-! # The completion-point law at a late binding

At a late delivery of `who` for its binding `event`, with the configuration
decoding at the event's rank to a point of the intended game, play until the
event completes leaves the configuration unchanged while `who` has not sent:
steps of the others and of the environment keep `who` unsent or fail the event
(`Vegas.lateUnsent_transition_other`). When `who` commits an as-if-honest source
choice at a slot, the event completes at the source step of that choice or
fails (`Vegas.expect_centeredCompletion_of_openableCommitment`); if the
completion mass after the commitment depends on the slot alone up to `η`, the
value of the commitment is drawn independently of its success, and the
as-if-honest step is the step of the intended effective opening
(`Vegas.asIfHonest_bind_step_eq_behavioralStateStep`). In general, a payoff of
stops vanishing while `who` is unsent and at failures, and after each permitted
commitment a slot factor times a centered function of the choice up to `ε`, has
expectation at most the cube of the scale times its bound plus `ε` per step of
the horizon (`Vegas.lateBinding_exitBound`). So, when `who` plays at
each of its decisions since the history, at the history itself and after its
response there, a slot-trembled mixture of late options or silence
(`Vegas.LateOwnerShapeFrom`, implied by `Vegas.LateOwnerShape`), the
completion-point law from the history is the completion mass times the step of
the intended effective opening at the decoded point, up to twice the cube of the
scale plus `η`, per step of the horizon
(`Vegas.lateBinding_completionPointLaw`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

open Classical in
/-- A history whose configuration is a prefix of `rank` events has no
completion point at `rank`. -/
theorem completionPoint_eq_none_of_isPrefix {rank : Nat}
    {fresh : (application setup timeouts leaks).Control → Prop}
    {history : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup)
      horizon scheduler).History} {control : (application setup timeouts leaks).Control}
    (state : history.state = some control)
    (ordered : control.execution.application.config.cut.IsPrefix rank) :
    completionPoint setup timeouts leaks bounds horizon scheduler rank fresh history = none := by
  classical
  unfold completionPoint
  rw [state]
  dsimp only
  rw [ite_eq_right_iff.mpr fun ⟨other, otherState, event, completed, rankEq⟩ => by
    rw [state] at otherState
    cases Option.some.inj otherState
    have earlier := (ordered.2 event).mp completed
    omega]

open Classical in
/-- A history whose control is not fresh has no completion point. -/
theorem completionPoint_eq_none_of_not_fresh {rank : Nat}
    {fresh : (application setup timeouts leaks).Control → Prop}
    {history : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup)
      horizon scheduler).History} {control : (application setup timeouts leaks).Control}
    (state : history.state = some control) (stale : ¬ fresh control) :
    completionPoint setup timeouts leaks bounds horizon scheduler rank fresh history = none := by
  classical
  unfold completionPoint
  rw [state]
  dsimp only
  split
  · split
    · rw [ite_eq_right_iff.mpr fun good => (stale good.2).elim]
    · rfl
  · rfl

variable (setup timeouts leaks bounds horizon scheduler) in
/-- The shape of the owner's laws at its decisions while it has sent nothing for
the event: a slot-trembled mixture of late options, or silence. -/
def LateOwnerShape (assessment : setup.intendedModel.BehavioralAssessment) {scale : ℝ}
    (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) (slots : Nat)
    (installed : ∀ player, (onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
      scheduler).BehavioralPolicy player) (who : Player) (event : (graph setup).EventId)
    (sent : (graph setup).Config) (past : List (application setup timeouts leaks).PlayerEntry) :
      Prop :=
  ∀ (history : ((bounds.onePacketMenu timeouts leaks).protocol
      (initialLaw setup) horizon scheduler).History) (later : Nat)
      (reached : (application setup timeouts leaks).Execution),
    history.state = some ⟨later, some who, reached⟩ →
    LateUnsent setup timeouts leaks who event sent past history.state →
    (∃ options : PMF (LateOption slots),
      installed who (some (reached.logs who, reached.observe (application setup timeouts leaks)
        who)) =
        slotTrembledChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler scale
          nonnegative le_one who
          (some (reached.logs who, reached.observe (application setup timeouts leaks) who))
          (options.bind (lateChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler
            assessment who
            (some (reached.logs who, reached.observe (application setup timeouts leaks) who))))
          (PMF.pure (silenceChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler
            who
            (some (reached.logs who, reached.observe (application setup timeouts leaks) who))))
          (slotChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler
            assessment who
            (some (reached.logs who, reached.observe (application setup timeouts leaks) who)))) ∨
    installed who (some (reached.logs who, reached.observe (application setup timeouts leaks)
      who)) =
      PMF.pure (silenceChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler who
        (some (reached.logs who, reached.observe (application setup timeouts leaks) who)))

variable (setup timeouts leaks bounds horizon scheduler) in
/-- **The late owner shape from a decision.** The shape of the owner's laws at
its decisions while it has sent nothing for the event since the decision
`start`: at the decision itself, identified by its view, and at decisions whose
recall extends the start's by the entry of a response there. -/
def LateOwnerShapeFrom (assessment : setup.intendedModel.BehavioralAssessment) {scale : ℝ}
    (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) (slots : Nat)
    (installed : ∀ player, (onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
      scheduler).BehavioralPolicy player) (who : Player) (event : (graph setup).EventId)
    (start : (application setup timeouts leaks).Execution) : Prop :=
  ∀ (history : ((bounds.onePacketMenu timeouts leaks).protocol
      (initialLaw setup) horizon scheduler).History) (later : Nat)
      (reached : (application setup timeouts leaks).Execution),
    history.state = some ⟨later, some who, reached⟩ →
    LateUnsent setup timeouts leaks who event start.application.config (start.logs who)
      history.state →
    (reached.logs who = start.logs who →
      reached.observe (application setup timeouts leaks) who =
        start.observe (application setup timeouts leaks) who) →
    (reached.logs who ≠ start.logs who → ∃ response,
      start.logs who ++ [respondEntry setup timeouts leaks start who response] <+:
        reached.logs who) →
    (∃ options : PMF (LateOption slots),
      installed who (some (reached.logs who, reached.observe (application setup timeouts leaks)
        who)) =
        slotTrembledChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler scale
          nonnegative le_one who
          (some (reached.logs who, reached.observe (application setup timeouts leaks) who))
          (options.bind (lateChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler
            assessment who
            (some (reached.logs who, reached.observe (application setup timeouts leaks) who))))
          (PMF.pure (silenceChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler
            who
            (some (reached.logs who, reached.observe (application setup timeouts leaks) who))))
          (slotChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler
            assessment who
            (some (reached.logs who, reached.observe (application setup timeouts leaks) who)))) ∨
    installed who (some (reached.logs who, reached.observe (application setup timeouts leaks)
      who)) =
      PMF.pure (silenceChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler who
        (some (reached.logs who, reached.observe (application setup timeouts leaks) who)))

/-- The late owner shape since a decision's recall is the late owner shape from
the decision. -/
theorem LateOwnerShape.from {assessment : setup.intendedModel.BehavioralAssessment}
    {scale : ℝ} {nonnegative : 0 ≤ scale} {le_one : scale ≤ 1} {slots : Nat}
    {installed : ∀ player, (onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
      scheduler).BehavioralPolicy player} {who : Player} {event : (graph setup).EventId}
    {start : (application setup timeouts leaks).Execution}
    (shape : LateOwnerShape setup timeouts leaks bounds horizon scheduler assessment nonnegative
      le_one
      slots installed who event start.application.config (start.logs who)) :
    LateOwnerShapeFrom setup timeouts leaks bounds horizon scheduler assessment nonnegative le_one
      slots installed who event start :=
  fun history later reached state holds _ _ => shape history later reached state holds

omit [Fintype Player] in
/-- At a decision of the owner while it has sent nothing, the configuration is
the one it decodes at, and the event is ready and the owner's turn there. -/
theorem lateUnsent_facts {who : Player} {event : (graph setup).EventId}
    {execution : (application setup timeouts leaks).Execution}
    (turn : execution.application.publicView.ownTurn? who = some event)
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    {later : Nat} {actor : Option Player} {reached : (application setup timeouts leaks).Execution}
    (holds : LateUnsent setup timeouts leaks who event execution.application.config
      (execution.logs who) (some ⟨later, actor, reached⟩)) :
    reached.application.config.cut.Ready event ∧
      reached.application.config.cut.IsPrefix rank ∧
      sourceServicePrefix? setup rank reached.application.config = some point ∧
      reached.application.publicView.ownTurn? who = some event := by
  obtain ⟨atSent, _, _⟩ := holds
  have readySent : execution.application.config.cut.Ready event :=
    (execution.application.publicView_eventReady event).mp
      (PublicView.ownTurn?_spec _ who event turn).1
  refine ⟨by rw [atSent]; exact readySent, by rw [atSent]; exact ordered,
    by rw [atSent]; exact decoded, ?_⟩
  rw [ownTurn?_eq_of_eventReady_iff (second := execution.application.publicView)
    (fun other => by
      rw [State.publicView_eventReady, State.publicView_eventReady, atSent]) who]
  exact turn

open Classical in
/-- **Exit errors at a late binding.** Let `who` be at a decision at a history
whose configuration is a prefix of `rank` events, with its binding `event` its
turn and nothing sent for it, and let `installed` play the late owner shape.
Let a payoff of stops, bounded by `bound` and reading only states, vanish while
`who` has sent nothing and at failed completions of the event. Suppose that
after committing an as-if-honest source choice at a permitted slot within the
capacity, the payoff of play until the event completes is, up to `ε`, a factor
of the slot times `centered` of the choice, where `centered` is bounded by
`bound` and has mean zero under the as-if-honest law. Then the payoff of play
until the event completes from the history is at most the cube of the scale
times `bound` plus `ε`, per step of the horizon. -/
theorem lateBinding_exitBound
    [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
    (covers : bounds.CoversOutputValues) (capacity : 1 ≤ bounds.candidateCount)
    (assessment : setup.intendedModel.BehavioralAssessment) {scale : ℝ} (positive : 0 < scale)
    (le_one : scale ≤ 1) {slots : Nat} (slotsLe : slots ≤ bounds.candidateCount)
    (installed : ∀ player, (onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
      scheduler).BehavioralPolicy player)
    (start : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    {remaining : Nat} {who : Player} {execution : (application setup timeouts leaks).Execution}
    (current : start.state = some ⟨remaining, some who, execution⟩)
    {event : (graph setup).EventId} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (unrecorded : (eventRecorded timeouts) leaks (execution.logs who) event = false)
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    (shape : LateOwnerShapeFrom setup timeouts leaks bounds horizon scheduler assessment positive.le
      le_one slots installed who event execution)
    (payoff : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup)
      horizon scheduler).History → ℝ) {bound ε : ℝ}
    (payoffBounded : ∀ stop, |payoff stop| ≤ bound)
    (payoffState : ∀ first second : ((bounds.onePacketMenu timeouts leaks).protocol
        (initialLaw setup) horizon scheduler).History,
      first.state = second.state → payoff first = payoff second)
    (unsentZero : ∀ (stop : ((bounds.onePacketMenu timeouts leaks).protocol
        (initialLaw setup) horizon scheduler).History)
        (control : (application setup timeouts leaks).Control),
      stop.state = some control →
      control.execution.application.config = execution.application.config → payoff stop = 0)
    (failedZero : ∀ (stop : ((bounds.onePacketMenu timeouts leaks).protocol
        (initialLaw setup) horizon scheduler).History)
        (control : (application setup timeouts leaks).Control),
      stop.state = some control → event ∈ control.execution.application.config.cut.completed →
      StoreEventFailed control.execution.application.config.store event → payoff stop = 0)
    (centered : Option (OwnAction Player L) → ℝ)
    (centeredBounded : ∀ choice, |centered choice| ≤ bound) (ε_nonneg : 0 ≤ ε)
    (mean : ∀ (history : ((bounds.onePacketMenu timeouts leaks).protocol
        (initialLaw setup) horizon scheduler).History) (later : Nat)
        (reached : (application setup timeouts leaks).Execution),
      history.state = some ⟨later, some who, reached⟩ →
      LateUnsent setup timeouts leaks who event execution.application.config (execution.logs who)
        history.state →
      expect (asIfHonestProfile setup timeouts leaks assessment who
        (some (reached.logs who, reached.observe (application setup timeouts leaks) who)))
          centered = 0)
    (committed : ∀ (history : ((bounds.onePacketMenu timeouts leaks).protocol
        (initialLaw setup) horizon scheduler).History) (later : Nat)
        (reached : (application setup timeouts leaks).Execution),
      history.state = some ⟨later, some who, reached⟩ →
      LateUnsent setup timeouts leaks who event execution.application.config (execution.logs who)
        history.state →
      (reached.logs who = execution.logs who →
        reached.observe (application setup timeouts leaks) who =
          execution.observe (application setup timeouts leaks) who) →
      (reached.logs who ≠ execution.logs who → ∃ response,
        execution.logs who ++ [respondEntry setup timeouts leaks execution who response] <+:
          reached.logs who) →
      ∀ slot < bounds.candidateCount,
        countPermits ((application setup timeouts leaks).outputs (reached.logs who))
          (slotEnvelope setup timeouts leaks who (reached.logs who)
            (reached.observe (application setup timeouts leaks) who) event slot) = true →
        ∃ factor : ℝ, ∀ choice ∈ (asIfHonestProfile setup timeouts leaks assessment who
            (some (reached.logs who, reached.observe (application setup timeouts leaks)
              who))).support,
          ∀ next : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup)
              horizon scheduler).History,
            next.state = some ⟨later, none, reached.respond (application setup timeouts leaks) who
              (slotResponse setup timeouts leaks who (reached.logs who)
                (reached.observe (application setup timeouts leaks) who) event slot choice)⟩ →
            |expect ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
                scheduler).runBehavioralUntil
                ((bounds.onePacketMenu timeouts leaks).bounded (initialLaw setup) horizon
                  scheduler).wellFoundedHistories installed
                (LateStopped setup timeouts leaks bounds horizon scheduler rank) next) payoff -
              factor * centered choice| ≤ ε) :
    |expect ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
        scheduler).runBehavioralUntil
        ((bounds.onePacketMenu timeouts leaks).bounded (initialLaw setup) horizon
          scheduler).wellFoundedHistories installed
        (LateStopped setup timeouts leaks bounds horizon scheduler rank) start) payoff| ≤
      (scale ^ 3 * bound + ε) * (2 * horizon + 1) := by
  let menu := bounds.onePacketMenu timeouts leaks
  let model := onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon scheduler
  let certificate := (menu.bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
  let sent := execution.application.config
  let past := execution.logs who
  let stopped := LateStopped setup timeouts leaks bounds horizon scheduler rank
  -- Before the owner's response at the start the state is the start's; after it the
  -- recall extends the start's by the entry of that response.
  let through : (application setup timeouts leaks).ProtocolState → Prop := fun state =>
    ∀ control : (application setup timeouts leaks).Control, state = some control →
      (control.execution.logs who = past → state = start.state) ∧
      (control.execution.logs who ≠ past → ∃ response,
        past ++ [respondEntry setup timeouts leaks execution who response] <+:
          control.execution.logs who)
  let inside : (menu.protocol (initialLaw setup) horizon scheduler).History → Prop :=
    fun history => LateUnsent setup timeouts leaks who event sent past history.state ∧
      through history.state
  have boundNonneg : 0 ≤ bound := (abs_nonneg _).trans (payoffBounded start)
  have κNonneg : 0 ≤ scale ^ 3 * bound + ε :=
    add_nonneg (mul_nonneg (pow_nonneg positive.le 3) boundNonneg) ε_nonneg
  have horizonBound := menu.bounded (initialLaw setup) horizon scheduler
  have atEnd : ∀ history, inside history → (stopped history ∨
      (menu.protocol (initialLaw setup) horizon scheduler).terminal history.state) →
      payoff history = 0 := by
    intro history holds _
    have unsent := holds.1
    cases state : history.state with
    | none =>
        rw [state] at unsent
        exact unsent.elim
    | some control =>
        rw [state] at unsent
        exact unsentZero history control state unsent.1
  have descends : ∀ history next, inside history → ¬ stopped history →
      ¬ (menu.protocol (initialLaw setup) horizon scheduler).terminal history.state →
      next ∈ (model.runBehavioralFrom installed 1 history).support →
      ((2 * horizon + 1) - next.trace.length) + 1 ≤ (2 * horizon + 1) - history.trace.length := by
    intro history next _ _ running member
    have lengthEq := model.length_of_mem_support_runBehavioralFrom_one installed running member
    have short : history.trace.length < 2 * horizon + 1 := by
      by_contra long
      exact running (horizonBound history.state history.trace (by omega))
    omega
  have exits : ∀ history, inside history → ¬ stopped history →
      ¬ (menu.protocol (initialLaw setup) horizon scheduler).terminal history.state →
      |expect (model.runBehavioralFrom installed 1 history) (fun next => if inside next then 0
        else expect (model.runBehavioralUntil certificate installed stopped next) payoff)| ≤
        scale ^ 3 * bound + ε := by
    intro history holds going running
    obtain ⟨control, state⟩ : ∃ control, history.state = some control := by
      have unsent := holds.1
      cases historyState : history.state with
      | none =>
          rw [historyState] at unsent
          exact unsent.elim
      | some control => exact ⟨control, rfl⟩
    have holdsHere := holds.1
    simp only [state] at holdsHere
    obtain ⟨atSent, extends_, unrecordedHere⟩ := holdsHere
    have throughHere := holds.2 control state
    rcases control with ⟨later, actor, reached⟩
    have readySent : sent.cut.Ready event :=
      (execution.application.publicView_eventReady event).mp
        (PublicView.ownTurn?_spec _ who event turn).1
    have rawAfter : ∀ next : (menu.protocol (initialLaw setup) horizon scheduler).History,
        ((application setup timeouts leaks).protocol (initialLaw setup) horizon scheduler).Trace
          next.state := fun next =>
      menu.toRawTrace (initialLaw setup) horizon scheduler next.trace
    let later' := fun next : (menu.protocol (initialLaw setup) horizon scheduler).History =>
      expect (model.runBehavioralUntil certificate installed stopped next) payoff
    have laterBounded : ∀ next, |later' next| ≤ bound := fun next =>
      expect_abs_le_of_bounded boundNonneg payoffBounded
    by_cases owner : actor = some who
    · subst owner
      have traceHere : (menu.protocol (initialLaw setup) horizon scheduler).Trace
          (some ⟨later, some who, reached⟩) := state ▸ history.trace
      have turnHere : reached.application.publicView.ownTurn? who = some event := by
        rw [ownTurn?_eq_of_eventReady_iff (second := execution.application.publicView)
          (fun other => by
            rw [State.publicView_eventReady, State.publicView_eventReady, atSent]) who]
        exact turn
      let info : (application setup timeouts leaks).Info :=
        some (reached.logs who, reached.observe (application setup timeouts leaks) who)
      let respondState := fun response : (application setup timeouts leaks).Action =>
        (some ⟨later, none, reached.respond (application setup timeouts leaks) who response⟩ :
          (application setup timeouts leaks).ProtocolState)
      let step := model.runBehavioralFrom installed 1 history
      let exit := fun next => if inside next then 0 else later' next
      -- The exit value reads only the state.
      let statePayoff : (application setup timeouts leaks).ProtocolState → ℝ := fun reachedState =>
        if found : ∃ other : (menu.protocol (initialLaw setup) horizon scheduler).History,
            other.state = reachedState then payoff found.choose else 0
      have payoffAt : ∀ stop, payoff stop = statePayoff stop.state := by
        intro stop
        have found : ∃ other : (menu.protocol (initialLaw setup) horizon scheduler).History,
            other.state = stop.state := ⟨stop, rfl⟩
        simp only [statePayoff, found, ↓reduceDIte]
        exact payoffState _ _ found.choose_spec.symm
      have statePayoffBounded : ∀ reachedState, |statePayoff reachedState| ≤ bound := by
        intro reachedState
        simp only [statePayoff]
        split
        · exact payoffBounded _
        · rw [abs_zero]
          exact boundNonneg
      have laterState : ∀ first second : (menu.protocol (initialLaw setup) horizon
          scheduler).History, first.state = second.state → later' first = later' second := by
        intro first second same
        simp only [later']
        rw [expect_congr_on_support (g := fun stop => statePayoff stop.state)
            (fun stop _ => payoffAt stop),
          expect_congr_on_support (μ := model.runBehavioralUntil certificate installed stopped
            second) (g := fun stop => statePayoff stop.state) (fun stop _ => payoffAt stop)]
        exact menu.expect_runBehavioralUntil_eq_of_state_eq (initialLaw setup) horizon scheduler
          installed certificate stopped (fun x y same => by
            simp only [stopped, LateStopped, same]) statePayoff statePayoffBounded first second
          same
      have exitState : ∀ first second : (menu.protocol (initialLaw setup) horizon
          scheduler).History, first.state = second.state → exit first = exit second := by
        intro first second same
        simp only [exit, inside, same, laterState first second same]
      let readOff : (application setup timeouts leaks).ProtocolState → ℝ := fun reachedState =>
        if found : ∃ next ∈ step.support, next.state = reachedState then exit found.choose else 0
      have readOffEq : ∀ next ∈ step.support, readOff next.state = exit next := by
        intro next member
        have found : ∃ other ∈ step.support, other.state = next.state := ⟨next, member, rfl⟩
        simp only [readOff, found, ↓reduceDIte]
        exact exitState _ _ found.choose_spec.2
      have exitBounded : ∀ next, |exit next| ≤ bound := by
        intro next
        simp only [exit]
        split
        · rw [abs_zero]
          exact boundNonneg
        · exact laterBounded next
      have readOffBounded : ∀ reachedState, |readOff reachedState| ≤ bound := by
        intro reachedState
        simp only [readOff]
        split
        · exact exitBounded _
        · rw [abs_zero]
          exact boundNonneg
      -- The exit as an expectation over the owner's choices.
      have stepStates := menu.run_one_response (initialLaw setup) horizon scheduler installed
        history who later reached state
      have expectEq : expect step exit = expect (installed who info)
          (fun choice => readOff (respondState (choiceResponse (timeouts := timeouts) choice)))
            := by
        rw [expect_congr_on_support (g := readOff ∘ History.state)
          (fun next member => (readOffEq next member).symm), ← expect_map]
        change expect ((model.runBehavioralFrom installed 1 history).map History.state) readOff = _
        rw [stepStates, expect_map]
        unfold ReactiveApplication.ResponseMenu.decodeProfile ReactiveApplication.decodePolicy
          ReactiveApplication.ResponseMenu.embedPolicy
        rw [PMF.map_comp, expect_map]
        rfl
      -- A choice the owner can draw reaches a successor.
      have drawn : ∀ choice ∈ (installed who info).support, ∃ next ∈ step.support,
          next.state = respondState (choiceResponse (timeouts := timeouts) choice) := by
        intro choice member
        have inStates : respondState (choiceResponse (timeouts := timeouts) choice) ∈
            (step.map History.state).support := by
          change _ ∈ ((model.runBehavioralFrom installed 1 history).map History.state).support
          rw [stepStates]
          unfold ReactiveApplication.ResponseMenu.decodeProfile ReactiveApplication.decodePolicy
            ReactiveApplication.ResponseMenu.embedPolicy
          rw [PMF.map_comp, PMF.map_comp, PMF.mem_support_map_iff]
          exact ⟨choice, member, rfl⟩
        obtain ⟨next, nextMember, nextState⟩ := (PMF.mem_support_map_iff _ _ _).mp inStates
        exact ⟨next, nextMember, nextState⟩
      -- Silence keeps the owner unsent.
      have silentInside : ∀ next : (menu.protocol (initialLaw setup) horizon scheduler).History,
          next.state = respondState ⟨none⟩ → inside next := by
        intro next nextState
        have recallEq : (reached.respond (application setup timeouts leaks) who ⟨none⟩).logs who =
            reached.logs who ++ [respondEntry setup timeouts leaks reached who ⟨none⟩] := by
          rw [(respond_recall timeouts) leaks reached who who ⟨none⟩, ite_eq_left rfl ..]
          rfl
        refine ⟨?_, ?_⟩
        · simp only [nextState, respondState, LateUnsent]
          refine ⟨((reactive_respond_application timeouts) leaks reached who _).1.trans
            atSent, ?_, ?_⟩
          · rw [recallEq]
            exact extends_.trans (List.prefix_append _ _)
          · rw [recallEq]
            unfold EventGraphRuntime.eventRecorded at unrecordedHere ⊢
            rw [List.any_append, unrecordedHere]
            simp [EventGraphRuntime.submittedEvent?, respondEntry]
        · intro nextControl nextEq
          rw [nextState] at nextEq
          cases Option.some.inj nextEq
          have longer : (reached.respond (application setup timeouts leaks) who ⟨none⟩).logs who ≠
              past := by
            intro same
            have lengthEq := congrArg List.length same
            rw [recallEq, List.length_append, List.length_singleton] at lengthEq
            have shorter : past.length ≤ (reached.logs who).length := extends_.length_le
            omega
          refine ⟨fun same => (longer same).elim, fun _ => ?_⟩
          by_cases atStart : reached.logs who = past
          · have startEq := (throughHere.1 atStart).symm
            rw [current, state] at startEq
            cases startEq
            exact ⟨⟨none⟩, by rw [recallEq]⟩
          · obtain ⟨response, prefixed⟩ := throughHere.2 atStart
            exact ⟨response, by rw [recallEq]; exact prefixed.trans (List.prefix_append _ _)⟩
      have silentZero : ∀ next : (menu.protocol (initialLaw setup) horizon scheduler).History,
          next.state = respondState ⟨none⟩ → exit next = 0 := by
        intro next nextState
        simp only [exit, silentInside next nextState, ↓reduceIte]
      have silenceAction : choiceResponse (timeouts := timeouts) (silenceChoice setup timeouts leaks
        bounds (initialLaw setup)
          horizon scheduler who info) = ⟨none⟩ := by
        simp only [choiceResponse, silenceChoice, responseChoice, info,
          bounds.silence_onePacket timeouts leaks who, ↓reduceDIte, Option.getD_some]
      rw [expectEq]
      have holdsState : LateUnsent setup timeouts leaks who event execution.application.config
          (execution.logs who) history.state := holds.1
      have sameView : reached.logs who = execution.logs who →
          reached.observe (application setup timeouts leaks) who =
            execution.observe (application setup timeouts leaks) who := by
        intro atStart
        have startEq := (throughHere.1 atStart).symm
        rw [current, state] at startEq
        cases startEq
        rfl
      rcases shape history later reached state holdsState sameView throughHere.2 with
        ⟨options, lawEq⟩ | silenceEq
      · -- A slot-trembled mixture of late options.
        rw [lawEq]
        have fullSupport := slotTrembledChoice_fullSupport setup timeouts leaks bounds (initialLaw
          setup)
          horizon scheduler positive le_one who info
          (options.bind (lateChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler
            assessment who info))
          (PMF.pure (silenceChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler
            who
            info))
          (slotChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler assessment
            who info)
        have reachable : ∀ choice, ∃ next ∈ step.support,
            next.state = respondState (choiceResponse (timeouts := timeouts) choice) := fun
              choice =>
          drawn choice (by rw [lawEq]; exact fullSupport choice)
        have silent : readOff (respondState ⟨none⟩) = 0 := by
          obtain ⟨next, member, nextState⟩ := reachable (silenceChoice setup timeouts leaks bounds
            (initialLaw setup) horizon scheduler who info)
          rw [silenceAction] at nextState
          rw [← nextState, readOffEq next member]
          exact silentZero next nextState
        have capacityEq : max 1 bounds.candidateCount = bounds.candidateCount :=
          max_eq_right capacity
        have tierBelow : ∀ slot ∈ trembleSlots setup bounds, slot < bounds.candidateCount := by
          intro slot member
          have := Finset.mem_range.mp member
          rw [capacityEq] at this
          exact this
        have optionsBelow : ∀ slot : Fin slots, some slot ∈ options.support →
            slot.val < bounds.candidateCount := fun slot _ => lt_of_lt_of_le slot.isLt slotsLe
        have sending : ∀ slot < bounds.candidateCount, ∃ factor : ℝ,
            ∀ choice ∈ (asIfHonestProfile setup timeouts leaks assessment who info).support,
              |readOff (respondState (choiceResponse (timeouts := timeouts) (responseChoice setup
                timeouts leaks bounds
                  (initialLaw setup) horizon scheduler who info
                  (slotResponse setup timeouts leaks who (reached.logs who)
                    (reached.observe (application setup timeouts leaks) who) event slot choice)))) -
                factor * centered choice| ≤ ε := by
          intro slot below
          by_cases permitted : countPermits ((application setup timeouts leaks).outputs
              (reached.logs who)) (slotEnvelope setup timeouts leaks who (reached.logs who)
                (reached.observe (application setup timeouts leaks) who) event slot) = true
          · obtain ⟨factor, near⟩ := committed history later reached state holdsState
              sameView throughHere.2 slot below permitted
            refine ⟨factor, fun choice member => ?_⟩
            have covered := onePacket_honest_covered (timeouts := timeouts) assessment covers
              traceHere who event
              turnHere choice member
            have inMenu := (slotResponse_mem_onePacket_iff setup timeouts leaks bounds who
              (reached.logs who) (reached.observe (application setup timeouts leaks) who) event
                node
              slot below choice covered).mpr permitted
            have responded : choiceResponse (timeouts := timeouts) (responseChoice setup timeouts
              leaks bounds (initialLaw setup)
                horizon scheduler who info (slotResponse setup timeouts leaks who (reached.logs
                  who)
                  (reached.observe (application setup timeouts leaks) who) event slot choice)) =
                slotResponse setup timeouts leaks who (reached.logs who)
                  (reached.observe (application setup timeouts leaks) who) event slot choice := by
              simp only [choiceResponse, responseChoice, info, inMenu, ↓reduceDIte,
                Option.getD_some]
            obtain ⟨next, nextMember, nextState⟩ := reachable (responseChoice setup timeouts leaks
              bounds
              (initialLaw setup) horizon scheduler who info (slotResponse setup timeouts leaks who
                (reached.logs who) (reached.observe (application setup timeouts leaks) who) event
                  slot
                choice))
            rw [responded] at nextState
            rw [responded, ← nextState, readOffEq next nextMember]
            obtain ⟨action, encoded, values⟩ := covered
            obtain ⟨value, successful, _⟩ := values who payload outputEq codeEq node
            obtain ⟨material, transmits, envelope⟩ := slotResponse_transmission setup timeouts
              leaks who
              (reached.logs who) (reached.observe (application setup timeouts leaks) who) event
                node
              slot choice action encoded (by rw [successful]; rfl)
            have named : (submittedEvent? timeouts) leaks (slotResponse setup timeouts leaks who
                (reached.logs who) (reached.observe (application setup timeouts leaks) who) event
                  slot
                choice) = some event := by
              have call : material.call.packet = .commitment event (who, .prepared slot) :=
                congrArg (fun message : Message Player (WitnessedPacket (graph setup)) =>
                  message.payload.call) envelope
              unfold EventGraphRuntime.submittedEvent?
              rw [transmits]
              dsimp only
              rw [call]
              rfl
            have recordedNext : ¬ inside next := by
              simp only [inside, nextState, respondState, LateUnsent]
              rintro ⟨⟨_, _, unrecordedNext⟩, _⟩
              rw [(respond_recall timeouts) leaks reached who who, ite_eq_left rfl ..]
                at unrecordedNext
              unfold EventGraphRuntime.eventRecorded at unrecordedNext
              rw [List.any_append] at unrecordedNext
              simp [named] at unrecordedNext
            simp only [exit, recordedNext, ↓reduceIte]
            exact near choice member next nextState
          · refine ⟨0, fun choice member => ?_⟩
            have covered := onePacket_honest_covered (timeouts := timeouts) assessment covers
              traceHere who event
              turnHere choice member
            have notMenu : slotResponse setup timeouts leaks who (reached.logs who)
                (reached.observe (application setup timeouts leaks) who) event slot choice ∉
                bounds.onePacketActions timeouts leaks who (reached.logs who)
                  (reached.observe (application setup timeouts leaks) who) := fun inMenu =>
              permitted ((slotResponse_mem_onePacket_iff setup timeouts leaks bounds who
                (reached.logs who) (reached.observe (application setup timeouts leaks) who) event
                  node
                slot below choice covered).mp inMenu)
            have responded : choiceResponse (timeouts := timeouts) (responseChoice setup timeouts
              leaks bounds (initialLaw setup)
                horizon scheduler who info (slotResponse setup timeouts leaks who (reached.logs
                  who)
                  (reached.observe (application setup timeouts leaks) who) event slot choice)) =
                ⟨none⟩ := by
              simp only [choiceResponse, responseChoice, info, notMenu, ↓reduceDIte,
                Option.getD_some]
            rw [responded, silent, zero_mul, sub_zero, abs_zero]
            exact ε_nonneg
        exact abs_expect_slotTrembled_lateChoice_le (timeouts := timeouts) assessment positive.le
          le_one
          options who (reached.logs who) (reached.observe (application setup timeouts leaks) who)
            event
          turnHere (fun response => readOff (respondState response)) centered
          (fun response => readOffBounded _) centeredBounded
          (mean history later reached state holdsState) silent bounds.candidateCount tierBelow
          optionsBelow sending
      · -- Silence.
        rw [silenceEq, expect_pure, silenceAction]
        obtain ⟨next, member, nextState⟩ := drawn (silenceChoice setup timeouts leaks bounds
          (initialLaw setup) horizon scheduler who info) (by
            rw [silenceEq]
            exact (PMF.mem_support_pure_iff _ _).mpr rfl)
        rw [silenceAction] at nextState
        rw [← nextState, readOffEq next member, silentZero next nextState, abs_zero]
        exact κNonneg
    · -- Steps of others keep the owner unsent or fail the event.
      have zero : ∀ next ∈ (model.runBehavioralFrom installed 1 history).support,
          (if inside next then 0 else later' next) = 0 := by
        intro next member
        obtain ⟨⟨joint, legal, realized⟩, _⟩ :=
          model.mem_support_runBehavioralFrom_one installed running member
        have realized' : next.state ∈ ((application setup timeouts leaks).transition (initialLaw
          setup)
            horizon scheduler history.state joint).support := realized
        rw [state] at realized'
        rcases lateUnsent_transition_other (timeouts := timeouts) readySent outputEq
            ⟨later, actor, reached⟩ ⟨atSent, extends_, unrecordedHere⟩ owner joint realized'
            (rawAfter next) with unsent | ⟨after, afterState, completed, failed⟩
        · have throughNext : through next.state := by
            intro nextControl nextEq
            have recallEq := recall_eq_of_transition (timeouts := timeouts) (initial := initialLaw
              setup)
              (horizon := horizon) (scheduler := scheduler) who ⟨later, actor, reached⟩ owner
              joint (nextEq ▸ realized')
            have notStart : reached.logs who ≠ past := by
              intro atStart
              have startEq := (throughHere.1 atStart).symm
              rw [current, state] at startEq
              cases startEq
              exact owner rfl
            rw [recallEq]
            exact ⟨fun atStart => (notStart atStart).elim, fun _ => throughHere.2 notStart⟩
          simp only [show inside next from ⟨unsent, throughNext⟩, ↓reduceIte]
        · split
          · rfl
          · have halted : stopped next :=
              ⟨after, afterState, event, completed,
                (ready_iff_rank setup execution.application.config rank ordered event).mp readySent⟩
            simp only [later', model.runBehavioralUntil_of_stopped certificate installed halted,
              expect_pure]
            exact failedZero next after afterState completed failed
      rw [expect_congr_on_support (g := fun _ => 0) zero, expect_constant, abs_zero]
      exact κNonneg
  have startInside : inside start := by
    refine ⟨?_, fun control startEq => ⟨fun _ => rfl, fun different => ?_⟩⟩
    · simp only [current]
      exact ⟨rfl, List.prefix_refl _, unrecorded⟩
    · rw [current] at startEq
      cases Option.some.inj startEq
      exact (different rfl).elim
  have main := model.abs_expect_runBehavioralUntil_le_of_exits certificate installed stopped
    inside payoff payoffBounded κNonneg (fun history => (2 * horizon + 1) - history.trace.length)
    atEnd descends exits start startInside
  refine main.trans ?_
  have depthLe : (((2 * horizon + 1) - start.trace.length : ℕ) : ℝ) ≤ 2 * horizon + 1 := by
    have : (2 * horizon + 1) - start.trace.length ≤ 2 * horizon + 1 := Nat.sub_le _ _
    exact_mod_cast this
  exact mul_le_mul_of_nonneg_left depthLe κNonneg

open Classical in
/-- **The completion-point law at a late binding.** Under a scheduler completing
play, with every binding value bounded and a positive candidate capacity, let
`who` be at a decision at a history whose configuration is a prefix of `rank`
events decoding to a point of the intended game, with its binding `event` its
turn and nothing sent for it. Suppose that `installed` plays the late owner
shape, and that the completion mass after committing at a permitted slot
depends, up to `η`, on the slot alone and not on the committed as-if-honest
choice (successFree). Then the completion-point law from the history, for every
property `fresh` of controls failing at a failed event, is the completion mass
times the step of the intended effective opening of `assessment` at the decoded
point, up to twice the cube of the scale plus `η` per step of the horizon. -/
theorem lateBinding_completionPointLaw
    [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
    (covers : bounds.CoversOutputValues) (capacity : 1 ≤ bounds.candidateCount)
    (assessment : setup.intendedModel.BehavioralAssessment) {scale : ℝ} (positive : 0 < scale)
    (le_one : scale ≤ 1) {slots : Nat} (slotsLe : slots ≤ bounds.candidateCount)
    (installed : ∀ player, (onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
      scheduler).BehavioralPolicy player)
    (start : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    {remaining : Nat} {who : Player} {execution : (application setup timeouts leaks).Execution}
    (current : start.state = some ⟨remaining, some who, execution⟩)
    {event : (graph setup).EventId} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (unrecorded : (eventRecorded timeouts) leaks (execution.logs who) event = false)
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (terminalCompleted : ∀ (final : (application setup timeouts leaks).Control),
      ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
        scheduler).Trace (some final) →
      (application setup timeouts leaks).terminal (some final) →
      final.execution.application.config = execution.application.config →
      event ∈ final.execution.application.config.cut.completed)
    (intendedPoint : ProtocolState.Intended setup.program point)
    {fresh : (application setup timeouts leaks).Control → Prop}
    (failedStale : ∀ control, StoreEventFailed control.execution.application.config.store event →
      ¬ fresh control)
    (shape : LateOwnerShapeFrom setup timeouts leaks bounds horizon scheduler assessment positive.le
      le_one slots installed who event execution)
    {η : ℝ} (η_nonneg : 0 ≤ η)
    (successFree : ∀ (history : ((bounds.onePacketMenu timeouts leaks).protocol
        (initialLaw setup) horizon scheduler).History) (later : Nat)
        (reached : (application setup timeouts leaks).Execution),
      history.state = some ⟨later, some who, reached⟩ →
      LateUnsent setup timeouts leaks who event execution.application.config (execution.logs who)
        history.state →
      (reached.logs who = execution.logs who →
        reached.observe (application setup timeouts leaks) who =
          execution.observe (application setup timeouts leaks) who) →
      (reached.logs who ≠ execution.logs who → ∃ response,
        execution.logs who ++ [respondEntry setup timeouts leaks execution who response] <+:
          reached.logs who) →
      ∀ slot < bounds.candidateCount,
        countPermits ((application setup timeouts leaks).outputs (reached.logs who))
          (slotEnvelope setup timeouts leaks who (reached.logs who)
            (reached.observe (application setup timeouts leaks) who) event slot) = true →
        ∃ factor : ℝ, ∀ choice ∈ (asIfHonestProfile setup timeouts leaks assessment who
            (some (reached.logs who, reached.observe (application setup timeouts leaks)
              who))).support,
          ∀ next : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup)
              horizon scheduler).History,
            next.state = some ⟨later, none, reached.respond (application setup timeouts leaks) who
              (slotResponse setup timeouts leaks who (reached.logs who)
                (reached.observe (application setup timeouts leaks) who) event slot choice)⟩ →
            |expect ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
                scheduler).runBehavioralUntil
                ((bounds.onePacketMenu timeouts leaks).bounded (initialLaw setup) horizon
                  scheduler).wellFoundedHistories installed
                (LateStopped setup timeouts leaks bounds horizon scheduler rank) next)
                (completionIndicator setup timeouts leaks bounds horizon scheduler rank fresh) -
              factor| ≤ η) :
    CompletionPointLaw setup timeouts leaks bounds horizon scheduler installed rank fresh start
      (expect ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
          scheduler).runBehavioralUntil
          ((bounds.onePacketMenu timeouts leaks).bounded (initialLaw setup) horizon
            scheduler).wellFoundedHistories installed
          (LateStopped setup timeouts leaks bounds horizon scheduler rank) start)
        (completionIndicator setup timeouts leaks bounds horizon scheduler rank fresh))
      (ProtocolState.behavioralStateStep setup.program
        (setup.intendedOpeningProfile assessment.strategy) point)
      (2 * (scale ^ 3 + η) * (2 * horizon + 1)) := by
  intro value bound valueBounded
  let menu := bounds.onePacketMenu timeouts leaks
  let model := onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon scheduler
  let certificate := (menu.bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
  let center := expect (ProtocolState.behavioralStateStep setup.program
    (setup.intendedOpeningProfile assessment.strategy) point) value
  let stopped := LateStopped setup timeouts leaks bounds horizon scheduler rank
  let payoff := centeredCompletion setup timeouts leaks bounds horizon scheduler rank fresh value
    center
  have boundNonneg : 0 ≤ bound := (abs_nonneg _).trans (valueBounded point)
  have centerBounded : |center| ≤ bound := expect_abs_le_of_bounded boundNonneg valueBounded
  have payoffBounded : ∀ stop, |payoff stop| ≤ 2 * bound := by
    intro stop
    simp only [payoff, centeredCompletion]
    cases completionPoint setup timeouts leaks bounds horizon scheduler rank fresh stop with
    | none =>
        rw [Option.elim_none, abs_zero]
        linarith
    | some target =>
        rw [Option.elim_some]
        calc |value target - center| ≤ |value target| + |center| := abs_sub _ _
          _ ≤ 2 * bound := by linarith [valueBounded target]
  let centered := fun choice : Option (OwnAction Player L) =>
    expect (ProtocolState.step setup.program point (fun _ => choice)) value - center
  have centeredBounded : ∀ choice, |centered choice| ≤ 2 * bound := by
    intro choice
    have inner := expect_abs_le_of_bounded (μ := ProtocolState.step setup.program point
      (fun _ => choice)) boundNonneg valueBounded
    calc |centered choice| ≤ |expect (ProtocolState.step setup.program point
          (fun _ => choice)) value| + |center| := abs_sub _ _
      _ ≤ 2 * bound := by linarith
  have mean : ∀ (history : (menu.protocol (initialLaw setup) horizon scheduler).History)
      (later : Nat) (reached : (application setup timeouts leaks).Execution),
      history.state = some ⟨later, some who, reached⟩ →
      LateUnsent setup timeouts leaks who event execution.application.config (execution.logs who)
        history.state →
      expect (asIfHonestProfile setup timeouts leaks assessment who
        (some (reached.logs who, reached.observe (application setup timeouts leaks) who)))
          centered =
        0 := by
    intro history later reached state holds
    obtain ⟨_, orderedHere, decodedHere, turnHere⟩ := lateUnsent_facts (timeouts := timeouts) turn
      ordered decoded
      (by simpa only [state] using holds)
    have stepLaw := asIfHonest_bind_step_eq_behavioralStateStep (timeouts := timeouts) assessment
      who reached
      orderedHere decodedHere intendedPoint turnHere (by
        rw [defaulted_eq_empty_of_decodedIntended
          ((decodedPoint_eq_of_isPrefix orderedHere).trans decodedHere) intendedPoint]
        exact Finset.notMem_empty _) (reached.logs who)
    have firstIntegrable : PayoffIntegrable (asIfHonestProfile setup timeouts leaks assessment who
        (some (reached.logs who, reached.observe (application setup timeouts leaks) who)))
        (fun choice => expect (ProtocolState.step setup.program point
          (fun _ => choice)) value) :=
      payoffIntegrable_of_bounded _ _ (C := bound) fun choice =>
        expect_abs_le_of_bounded boundNonneg valueBounded
    simp only [centered]
    rw [expect_sub firstIntegrable (payoffIntegrable_constant _ center), expect_constant,
      ← expect_bind_tower_bounded _ _ _ valueBounded, stepLaw, sub_self]
  have committed : ∀ (history : (menu.protocol (initialLaw setup) horizon scheduler).History)
      (later : Nat) (reached : (application setup timeouts leaks).Execution),
      history.state = some ⟨later, some who, reached⟩ →
      LateUnsent setup timeouts leaks who event execution.application.config (execution.logs who)
        history.state →
      (reached.logs who = execution.logs who →
        reached.observe (application setup timeouts leaks) who =
          execution.observe (application setup timeouts leaks) who) →
      (reached.logs who ≠ execution.logs who → ∃ response,
        execution.logs who ++ [respondEntry setup timeouts leaks execution who response] <+:
          reached.logs who) →
      ∀ slot < bounds.candidateCount,
        countPermits ((application setup timeouts leaks).outputs (reached.logs who))
          (slotEnvelope setup timeouts leaks who (reached.logs who)
            (reached.observe (application setup timeouts leaks) who) event slot) = true →
        ∃ factor : ℝ, ∀ choice ∈ (asIfHonestProfile setup timeouts leaks assessment who
            (some (reached.logs who, reached.observe (application setup timeouts leaks)
              who))).support,
          ∀ next : (menu.protocol (initialLaw setup) horizon scheduler).History,
            next.state = some ⟨later, none, reached.respond (application setup timeouts leaks) who
              (slotResponse setup timeouts leaks who (reached.logs who)
                (reached.observe (application setup timeouts leaks) who) event slot choice)⟩ →
            |expect (model.runBehavioralUntil certificate installed stopped next) payoff -
              factor * centered choice| ≤ 2 * bound * η := by
    intro history later reached state holds sameView extended slot below permitted
    have sameConfig : reached.application.config = execution.application.config := by
      have unsent := holds
      rw [state] at unsent
      exact unsent.1
    obtain ⟨factor, near⟩ := successFree history later reached state holds sameView extended slot
      below permitted
    refine ⟨factor, fun choice member next nextState => ?_⟩
    have traceHere : (menu.protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨later, some who, reached⟩) := state ▸ history.trace
    obtain ⟨readyHere, orderedHere, decodedHere, turnHere⟩ := lateUnsent_facts (timeouts :=
      timeouts) turn ordered
      decoded (by simpa only [state] using holds)
    obtain ⟨action, encoded, values⟩ := onePacket_honest_covered (timeouts := timeouts) assessment
      covers traceHere who
      event turnHere choice member
    obtain ⟨committedValue, successful, _⟩ := values who payload outputEq codeEq node
    obtain ⟨entry, message, invariant⟩ := openableCommitmentInvariant_slot (timeouts := timeouts)
      bounds horizon
      scheduler traceHere node readyHere slot choice action encoded successful permitted
      (nextState ▸ next.trace)
    obtain ⟨found, ⟨residualFound⟩⟩ := protocol_sourceResidual (timeouts := timeouts)
      (failureProfile setup.program) menu horizon scheduler traceHere _ rfl
    have foundEq : found = rank :=
      EventOrder.Cut.IsPrefix.unique residualFound.checkpoint.ordered orderedHere
    have residual := foundEq ▸ residualFound
    cases choice with
    | none => simp at encoded
    | some source =>
    have encodedSource : encodeEventAction? setup.program event source = some action := encoded
    have decodeEq := decodeEventAction_encodeEventAction?_eq_some setup.program event source
      action encodedSource
    have owned : (graph setup).actor? event = some who := nodeView_bind_actor outputEq codeEq
    have pointDecoded : decodedPoint setup reached.application.config = some point :=
      (decodedPoint_eq residual).trans (residual.decode.symm.trans decodedHere)
    have acts := (decodedPoint_actor_of_history who
      (menu.toRawTrace (initialLaw setup) horizon scheduler traceHere) readyHere pointDecoded).trans
        owned
    obtain ⟨target, stepEq⟩ := ProtocolState.step_eq_pure_of_actor who who setup.program point
      (fun _ => some source) acts
    have stepEq' : ProtocolState.step setup.program point
        (fun _ => decodeEventAction setup.program event action) = PMF.pure target := by
      rw [decodeEq]
      exact stepEq
    have valueAt := expect_centeredCompletion_of_openableCommitment (timeouts := timeouts)
      certificate
      installed codeEq successful residual decodedHere
      (fun final trace ended same => terminalCompleted final trace ended
        (same.trans sameConfig)) stepEq' failedStale next
      (by rw [nextState]; exact invariant) value center
    have centeredEq : centered (some source) = value target - center := by
      simp only [centered, stepEq, expect_pure]
    simp only [payoff]
    rw [valueAt, centeredEq]
    have closeness := near (some source) member next nextState
    have targetBounded : |value target - center| ≤ 2 * bound := by
      calc |value target - center| ≤ |value target| + |center| := abs_sub _ _
        _ ≤ 2 * bound := by linarith [valueBounded target]
    rw [show (value target - center) * expect (model.runBehavioralUntil certificate installed
        stopped next) (completionIndicator setup timeouts leaks bounds horizon scheduler rank
          fresh) -
        factor * (value target - center) = (value target - center) *
        (expect (model.runBehavioralUntil certificate installed stopped next)
          (completionIndicator setup timeouts leaks bounds horizon scheduler rank fresh) - factor)
            by ring,
      abs_mul]
    exact mul_le_mul targetBounded closeness (abs_nonneg _) (by linarith)
  have main := lateBinding_exitBound (timeouts := timeouts) covers capacity assessment positive
    le_one slotsLe installed
    start current node turn unrecorded ordered shape payoff payoffBounded
    (fun first second same => by
      simp only [payoff, centeredCompletion, completionPoint_congr_state (timeouts := timeouts)
        same])
    (fun stop control state atSent => by
      change (completionPoint setup timeouts leaks bounds horizon scheduler rank fresh stop).elim 0
        (fun target => value target - center) = 0
      rw [completionPoint_eq_none_of_isPrefix (timeouts := timeouts) state (by rw [atSent]; exact
        ordered)]
      rfl)
    (fun stop control state _ failed => by
      change (completionPoint setup timeouts leaks bounds horizon scheduler rank fresh stop).elim 0
        (fun target => value target - center) = 0
      rw [completionPoint_eq_none_of_not_fresh (timeouts := timeouts) state (failedStale control
        failed)]
      rfl)
    centered centeredBounded (mul_nonneg (by linarith) η_nonneg) mean committed
  have rewriteEq : expect (model.runBehavioralUntil certificate installed stopped start)
        (fun stop => (completionPoint setup timeouts leaks bounds horizon scheduler rank fresh
          stop).elim
          0 value) -
      expect (model.runBehavioralUntil certificate installed stopped start)
        (completionIndicator setup timeouts leaks bounds horizon scheduler rank fresh) * center =
      expect (model.runBehavioralUntil certificate installed stopped start) payoff := by
    have firstIntegrable : PayoffIntegrable (model.runBehavioralUntil certificate installed
        stopped start) (fun stop => (completionPoint setup timeouts leaks bounds horizon scheduler
          rank
          fresh stop).elim 0 value) :=
      payoffIntegrable_of_bounded _ _ (C := bound) fun stop => by
        cases completionPoint setup timeouts leaks bounds horizon scheduler rank fresh stop with
        | none => simpa using boundNonneg
        | some target => exact valueBounded target
    have secondIntegrable : PayoffIntegrable (model.runBehavioralUntil certificate installed
        stopped start) (fun stop => center *
          completionIndicator setup timeouts leaks bounds horizon scheduler rank fresh stop) :=
      payoffIntegrable_of_bounded _ _ (C := |center|) fun stop => by
        simp only [completionIndicator]
        cases completionPoint setup timeouts leaks bounds horizon scheduler rank fresh stop with
        | none => simp
        | some target => simp
    rw [mul_comm, ← expect_const_mul, ← expect_sub firstIntegrable secondIntegrable]
    apply expect_congr_on_support
    intro stop _
    simp only [payoff, centeredCompletion, completionIndicator]
    cases completionPoint setup timeouts leaks bounds horizon scheduler rank fresh stop with
    | none => simp
    | some target => simp
  change |expect (model.runBehavioralUntil certificate installed stopped start)
      (fun stop => (completionPoint setup timeouts leaks bounds horizon scheduler rank fresh
        stop).elim
        0 value) -
    expect (model.runBehavioralUntil certificate installed stopped start)
      (completionIndicator setup timeouts leaks bounds horizon scheduler rank fresh) * center| ≤ _
  rw [rewriteEq]
  refine main.trans (le_of_eq ?_)
  ring

end Vegas
