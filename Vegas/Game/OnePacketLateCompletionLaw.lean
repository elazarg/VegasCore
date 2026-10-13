/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketLateCompletion
import Vegas.Game.OnePacketOwnerLaws

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
(`Vegas.asIfHonest_bind_step_eq_behavioralStateStep`). So, when `who` plays at
each of its decisions a slot-trembled mixture of late options or silence, the
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
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

open Classical in
/-- A history whose configuration is a prefix of `rank` events has no
completion point at `rank`. -/
theorem completionPoint_eq_none_of_isPrefix {rank : Nat}
    {fresh : (application setup leaks).Control → Prop}
    {history : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History} {control : (application setup leaks).Control}
    (state : history.state = some control)
    (ordered : control.execution.application.config.cut.IsPrefix rank) :
    completionPoint setup leaks bounds horizon scheduler rank fresh history = none := by
  classical
  unfold completionPoint
  rw [state]
  dsimp only
  rw [ite_eq_right_iff.mpr fun prefixed =>
    (Nat.succ_ne_self rank (isPrefix_unique prefixed ordered)).elim]

open Classical in
/-- A history whose control is not fresh has no completion point. -/
theorem completionPoint_eq_none_of_not_fresh {rank : Nat}
    {fresh : (application setup leaks).Control → Prop}
    {history : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History} {control : (application setup leaks).Control}
    (state : history.state = some control) (stale : ¬ fresh control) :
    completionPoint setup leaks bounds horizon scheduler rank fresh history = none := by
  classical
  unfold completionPoint
  rw [state]
  dsimp only
  split
  · split
    · rw [ite_eq_right_iff.mpr fun good => (stale good.2).elim]
    · rfl
  · rfl

open Classical in
/-- **The completion-point law at a late binding.** Under a scheduler completing
play, with every binding value bounded and a positive candidate capacity, let
`who` be at a decision at a history whose configuration is a prefix of `rank`
events decoding to a point of the intended game, with its binding `event` its
turn and nothing sent for it. Suppose that, at each of its decisions while it
has sent nothing for the event, `installed` plays a slot-trembled mixture of
late options over slots within the capacity, or silence (shape), and that the
completion mass after committing at a permitted slot depends, up to `η`, on the
slot alone and not on the committed as-if-honest choice (successFree). Then the
completion-point law from the history, for every property `fresh` of controls
failing at a failed event, is the completion mass times the step of the
intended effective opening of `assessment` at the decoded point, up to twice
the cube of the scale plus `η` per step of the horizon. -/
theorem lateBinding_completionPointLaw
    [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (covers : bounds.CoversOutputValues) (capacity : 1 ≤ bounds.candidateCount)
    (assessment : setup.intendedModel.BehavioralAssessment) {scale : ℝ} (positive : 0 < scale)
    (le_one : scale ≤ 1) {slots : Nat} (slotsLe : slots ≤ bounds.candidateCount)
    (installed : ∀ player, (onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).BehavioralPolicy player)
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (current : start.state = some ⟨remaining, some who, execution⟩)
    {event : (graph setup).EventId} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (unrecorded : (runtime setup).eventRecorded leaks (execution.recall who) event = false)
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    {fresh : (application setup leaks).Control → Prop}
    (failedStale : ∀ control, StoreEventFailed control.execution.application.config.store event →
      ¬ fresh control)
    (shape : ∀ (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol
        (initialLaw setup) horizon scheduler).History) (later : Nat)
        (reached : (application setup leaks).Execution),
      history.state = some ⟨later, some who, reached⟩ →
      LateUnsent setup leaks who event execution.application.config (execution.recall who)
        history.state →
      (∃ options : PMF (LateOption slots),
        installed who (some (reached.recall who, reached.observe (application setup leaks) who)) =
          slotTrembledChoice setup leaks bounds (initialLaw setup) horizon scheduler scale
            positive.le le_one who
            (some (reached.recall who, reached.observe (application setup leaks) who))
            (options.bind (lateChoice setup leaks bounds (initialLaw setup) horizon scheduler
              assessment who
              (some (reached.recall who, reached.observe (application setup leaks) who))))
            (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who
              (some (reached.recall who, reached.observe (application setup leaks) who))))
            (slotChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment who
              (some (reached.recall who, reached.observe (application setup leaks) who)))) ∨
      installed who (some (reached.recall who, reached.observe (application setup leaks) who)) =
        PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who
          (some (reached.recall who, reached.observe (application setup leaks) who))))
    {η : ℝ} (η_nonneg : 0 ≤ η)
    (successFree : ∀ (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol
        (initialLaw setup) horizon scheduler).History) (later : Nat)
        (reached : (application setup leaks).Execution),
      history.state = some ⟨later, some who, reached⟩ →
      LateUnsent setup leaks who event execution.application.config (execution.recall who)
        history.state →
      ∀ slot < bounds.candidateCount,
        countPermits ((application setup leaks).outputs (reached.recall who))
          (slotEnvelope setup leaks who (reached.recall who)
            (reached.observe (application setup leaks) who) event slot) = true →
        ∃ factor : ℝ, ∀ choice ∈ (asIfHonestProfile setup leaks assessment who
            (some (reached.recall who, reached.observe (application setup leaks) who))).support,
          ∀ next : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
              horizon scheduler).History,
            next.state = some ⟨later, none, reached.respond (application setup leaks) who
              (slotResponse setup leaks who (reached.recall who)
                (reached.observe (application setup leaks) who) event slot choice)⟩ →
            |expect ((onePacketModel setup leaks bounds (initialLaw setup) horizon
                scheduler).runBehavioralUntil
                ((bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup) horizon
                  scheduler).wellFoundedHistories installed
                (LateStopped setup leaks bounds horizon scheduler rank) next)
                (completionIndicator setup leaks bounds horizon scheduler rank fresh) -
              factor| ≤ η) :
    CompletionPointLaw setup leaks bounds horizon scheduler installed rank fresh start
      (expect ((onePacketModel setup leaks bounds (initialLaw setup) horizon
          scheduler).runBehavioralUntil
          ((bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup) horizon
            scheduler).wellFoundedHistories installed
          (LateStopped setup leaks bounds horizon scheduler rank) start)
        (completionIndicator setup leaks bounds horizon scheduler rank fresh))
      (ProtocolState.behavioralStateStep setup.program
        (setup.intendedOpeningProfile assessment.strategy) point)
      (2 * (scale ^ 3 + η) * (2 * horizon + 1)) := by
  intro value bound valueBounded
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler
  let certificate := (menu.bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
  let sent := execution.application.config
  let past := execution.recall who
  let center := expect (ProtocolState.behavioralStateStep setup.program
    (setup.intendedOpeningProfile assessment.strategy) point) value
  let stopped := LateStopped setup leaks bounds horizon scheduler rank
  let payoff := centeredCompletion setup leaks bounds horizon scheduler rank fresh value center
  let inside : (menu.protocol (initialLaw setup) horizon scheduler).History → Prop :=
    fun history => LateUnsent setup leaks who event sent past history.state
  have boundNonneg : 0 ≤ bound := (abs_nonneg _).trans (valueBounded point)
  have centerBounded : |center| ≤ bound := expect_abs_le_of_bounded boundNonneg valueBounded
  have payoffBounded : ∀ stop, |payoff stop| ≤ 2 * bound := by
    intro stop
    simp only [payoff, centeredCompletion]
    cases completionPoint setup leaks bounds horizon scheduler rank fresh stop with
    | none =>
        rw [Option.elim_none, abs_zero]
        linarith
    | some target =>
        rw [Option.elim_some]
        calc |value target - center| ≤ |value target| + |center| := abs_sub _ _
          _ ≤ 2 * bound := by linarith [valueBounded target]
  have κNonneg : 0 ≤ 2 * bound * (scale ^ 3 + η) :=
    mul_nonneg (by linarith) (add_nonneg (pow_nonneg positive.le 3) η_nonneg)
  have horizonBound := menu.bounded (initialLaw setup) horizon scheduler
  have atEnd : ∀ history, inside history → (stopped history ∨
      (menu.protocol (initialLaw setup) horizon scheduler).terminal history.state) →
      payoff history = 0 := by
    intro history holds _
    simp only [inside] at holds
    cases state : history.state with
    | none =>
        rw [state] at holds
        exact holds.elim
    | some control =>
        rw [state] at holds
        obtain ⟨atSent, _, _⟩ := holds
        have prefixed : control.execution.application.config.cut.IsPrefix rank := by
          rw [atSent]
          exact ordered
        change (completionPoint setup leaks bounds horizon scheduler rank fresh history).elim 0
          (fun target => value target - center) = 0
        rw [completionPoint_eq_none_of_isPrefix state prefixed]
        rfl
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
        2 * bound * (scale ^ 3 + η) := by
    intro history holds going running
    obtain ⟨control, state⟩ : ∃ control, history.state = some control := by
      simp only [inside] at holds
      cases historyState : history.state with
      | none =>
          rw [historyState] at holds
          exact holds.elim
      | some control => exact ⟨control, rfl⟩
    have holdsHere := holds
    simp only [inside, state] at holdsHere
    obtain ⟨atSent, extends_, unrecordedHere⟩ := holdsHere
    rcases control with ⟨later, actor, reached⟩
    have readySent : sent.cut.Ready event :=
      (execution.application.publicView_eventReady event).mp
        (PublicView.ownTurn?_spec _ who event turn).1
    have rawAfter : ∀ next : (menu.protocol (initialLaw setup) horizon scheduler).History,
        ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
          next.state := fun next =>
      menu.toRawTrace (initialLaw setup) horizon scheduler next.trace
    let later' := fun next : (menu.protocol (initialLaw setup) horizon scheduler).History =>
      expect (model.runBehavioralUntil certificate installed stopped next) payoff
    have laterBounded : ∀ next, |later' next| ≤ 2 * bound := fun next =>
      expect_abs_le_of_bounded (by linarith) payoffBounded
    by_cases owner : actor = some who
    · subst owner
      have traceHere : (menu.protocol (initialLaw setup) horizon scheduler).Trace
          (some ⟨later, some who, reached⟩) := state ▸ history.trace
      have readyHere : reached.application.config.cut.Ready event := by
        rw [atSent]
        exact readySent
      have orderedHere : reached.application.config.cut.IsPrefix rank := by
        rw [atSent]
        exact ordered
      have decodedHere : sourceServicePrefix? setup rank reached.application.config =
          some point := by
        rw [atSent]
        exact decoded
      have turnHere : reached.application.publicView.ownTurn? who = some event := by
        rw [ownTurn?_eq_of_eventReady_iff (second := execution.application.publicView)
          (fun other => by
            rw [State.publicView_eventReady, State.publicView_eventReady, atSent]) who]
        exact turn
      let info : (application setup leaks).Info :=
        some (reached.recall who, reached.observe (application setup leaks) who)
      let respondState := fun response : (application setup leaks).Action =>
        (some ⟨later, none, reached.respond (application setup leaks) who response⟩ :
          (application setup leaks).ProtocolState)
      let step := model.runBehavioralFrom installed 1 history
      let exit := fun next => if inside next then 0 else later' next
      -- The exit value reads only the state.
      let statePayoff : (application setup leaks).ProtocolState → ℝ := fun reachedState =>
        if found : ∃ other : (menu.protocol (initialLaw setup) horizon scheduler).History,
            other.state = reachedState then payoff found.choose else 0
      have payoffState : ∀ stop, payoff stop = statePayoff stop.state := by
        intro stop
        have found : ∃ other : (menu.protocol (initialLaw setup) horizon scheduler).History,
            other.state = stop.state := ⟨stop, rfl⟩
        simp only [statePayoff, found, ↓reduceDIte, payoff, centeredCompletion]
        rw [completionPoint_congr_state found.choose_spec]
      have statePayoffBounded : ∀ reachedState, |statePayoff reachedState| ≤ 2 * bound := by
        intro reachedState
        simp only [statePayoff]
        split
        · exact payoffBounded _
        · rw [abs_zero]
          linarith
      have laterState : ∀ first second : (menu.protocol (initialLaw setup) horizon
          scheduler).History, first.state = second.state → later' first = later' second := by
        intro first second same
        simp only [later']
        rw [expect_congr_on_support (g := fun stop => statePayoff stop.state)
            (fun stop _ => payoffState stop),
          expect_congr_on_support (μ := model.runBehavioralUntil certificate installed stopped
            second) (g := fun stop => statePayoff stop.state) (fun stop _ => payoffState stop)]
        exact menu.expect_runBehavioralUntil_eq_of_state_eq (initialLaw setup) horizon scheduler
          installed certificate stopped (fun x y same => by
            simp only [stopped, LateStopped, same]) statePayoff statePayoffBounded first second
          same
      have exitState : ∀ first second : (menu.protocol (initialLaw setup) horizon
          scheduler).History, first.state = second.state → exit first = exit second := by
        intro first second same
        simp only [exit, inside, same, laterState first second same]
      let readOff : (application setup leaks).ProtocolState → ℝ := fun reachedState =>
        if found : ∃ next ∈ step.support, next.state = reachedState then exit found.choose else 0
      have readOffEq : ∀ next ∈ step.support, readOff next.state = exit next := by
        intro next member
        have found : ∃ other ∈ step.support, other.state = next.state := ⟨next, member, rfl⟩
        simp only [readOff, found, ↓reduceDIte]
        exact exitState _ _ found.choose_spec.2
      have exitBounded : ∀ next, |exit next| ≤ 2 * bound := by
        intro next
        simp only [exit]
        split
        · rw [abs_zero]
          linarith
        · exact laterBounded next
      have readOffBounded : ∀ reachedState, |readOff reachedState| ≤ 2 * bound := by
        intro reachedState
        simp only [readOff]
        split
        · exact exitBounded _
        · rw [abs_zero]
          linarith
      -- The exit as an expectation over the owner's choices.
      have stepStates := menu.run_one_response (initialLaw setup) horizon scheduler installed
        history who later reached state
      have expectEq : expect step exit = expect (installed who info)
          (fun choice => readOff (respondState (choiceResponse choice))) := by
        rw [expect_congr_on_support (g := readOff ∘ History.state)
          (fun next member => (readOffEq next member).symm), ← expect_map]
        change expect ((model.runBehavioralFrom installed 1 history).map History.state) readOff = _
        rw [stepStates, expect_map, decodeProfile_eq_map, expect_map]
        rfl
      -- A choice the owner can draw reaches a successor.
      have drawn : ∀ choice ∈ (installed who info).support, ∃ next ∈ step.support,
          next.state = respondState (choiceResponse choice) := by
        intro choice member
        have inStates : respondState (choiceResponse choice) ∈
            (step.map History.state).support := by
          change _ ∈ ((model.runBehavioralFrom installed 1 history).map History.state).support
          rw [stepStates, decodeProfile_eq_map, PMF.map_comp, PMF.mem_support_map_iff]
          exact ⟨choice, member, rfl⟩
        obtain ⟨next, nextMember, nextState⟩ := (PMF.mem_support_map_iff _ _ _).mp inStates
        exact ⟨next, nextMember, nextState⟩
      -- Silence keeps the owner unsent.
      have silentInside : ∀ next : (menu.protocol (initialLaw setup) horizon scheduler).History,
          next.state = respondState ⟨none⟩ → inside next := by
        intro next nextState
        simp only [inside, nextState, respondState, LateUnsent]
        have recallEq := (runtime setup).respond_recall leaks reached who who ⟨none⟩
        rw [ite_eq_left rfl ..] at recallEq
        refine ⟨((runtime setup).reactive_respond_application leaks reached who _).1.trans
          atSent, ?_, ?_⟩
        · rw [recallEq]
          exact extends_.trans (List.prefix_append _ _)
        · rw [recallEq]
          unfold EventGraphRuntime.eventRecorded at unrecordedHere ⊢
          rw [List.any_append, unrecordedHere]
          simp [EventGraphRuntime.submittedEvent?]
      have silentZero : ∀ next : (menu.protocol (initialLaw setup) horizon scheduler).History,
          next.state = respondState ⟨none⟩ → exit next = 0 := by
        intro next nextState
        simp only [exit, silentInside next nextState, ↓reduceIte]
      have silenceAction : choiceResponse (silenceChoice setup leaks bounds (initialLaw setup)
          horizon scheduler who info) = ⟨none⟩ := by
        simp only [choiceResponse, silenceChoice, responseChoice, info,
          bounds.silence_onePacket (runtime setup) leaks who, ↓reduceDIte, Option.getD_some]
      rw [expectEq]
      have holdsState : LateUnsent setup leaks who event execution.application.config
          (execution.recall who) history.state := holds
      rcases shape history later reached state holdsState with ⟨options, lawEq⟩ | silenceEq
      · -- A slot-trembled mixture of late options.
        rw [lawEq]
        have fullSupport := slotTrembledChoice_fullSupport setup leaks bounds (initialLaw setup)
          horizon scheduler positive le_one who info
          (options.bind (lateChoice setup leaks bounds (initialLaw setup) horizon scheduler
            assessment who info))
          (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who
            info))
          (slotChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment who info)
        have reachable : ∀ choice, ∃ next ∈ step.support,
            next.state = respondState (choiceResponse choice) := fun choice =>
          drawn choice (by rw [lawEq]; exact fullSupport choice)
        let centered := fun choice : Option (OwnAction Player L) =>
          expect (ProtocolState.step setup.program point (fun _ => choice)) value - center
        have centeredBounded : ∀ choice, |centered choice| ≤ 2 * bound := by
          intro choice
          have inner := expect_abs_le_of_bounded (μ := ProtocolState.step setup.program point
            (fun _ => choice)) boundNonneg valueBounded
          calc |centered choice| ≤ |expect (ProtocolState.step setup.program point
                (fun _ => choice)) value| + |center| := abs_sub _ _
            _ ≤ 2 * bound := by linarith
        have stepLaw := asIfHonest_bind_step_eq_behavioralStateStep assessment who reached
          orderedHere decodedHere intendedPoint turnHere (reached.recall who)
        have mean : expect (asIfHonestProfile setup leaks assessment who info) centered = 0 := by
          have firstIntegrable : PayoffIntegrable (asIfHonestProfile setup leaks assessment who
              info) (fun choice => expect (ProtocolState.step setup.program point
                (fun _ => choice)) value) :=
            payoffIntegrable_of_bounded _ _ (C := bound) fun choice =>
              expect_abs_le_of_bounded boundNonneg valueBounded
          simp only [centered]
          rw [expect_sub firstIntegrable (payoffIntegrable_constant _ center), expect_constant,
            ← expect_bind_tower_bounded _ _ _ valueBounded]
          change expect ((asIfHonestProfile setup leaks assessment who
            (some (reached.recall who, reached.observe (application setup leaks) who))).bind
              fun choice => ProtocolState.step setup.program point (fun _ => choice)) value -
            center = 0
          rw [stepLaw, sub_self]
        have silent : readOff (respondState ⟨none⟩) = 0 := by
          obtain ⟨next, member, nextState⟩ := reachable (silenceChoice setup leaks bounds
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
            ∀ choice ∈ (asIfHonestProfile setup leaks assessment who info).support,
              |readOff (respondState (choiceResponse (responseChoice setup leaks bounds
                  (initialLaw setup) horizon scheduler who info
                  (slotResponse setup leaks who (reached.recall who)
                    (reached.observe (application setup leaks) who) event slot choice)))) -
                factor * centered choice| ≤ 2 * bound * η := by
          intro slot below
          by_cases permitted : countPermits ((application setup leaks).outputs
              (reached.recall who)) (slotEnvelope setup leaks who (reached.recall who)
                (reached.observe (application setup leaks) who) event slot) = true
          · obtain ⟨factor, near⟩ := successFree history later reached state holdsState slot
              below permitted
            refine ⟨factor, fun choice member => ?_⟩
            have covered := onePacket_honest_covered assessment covers traceHere who event
              turnHere choice member
            have inMenu := (slotResponse_mem_onePacket_iff setup leaks bounds who
              (reached.recall who) (reached.observe (application setup leaks) who) event node
              slot below choice covered).mpr permitted
            have responded : choiceResponse (responseChoice setup leaks bounds (initialLaw setup)
                horizon scheduler who info (slotResponse setup leaks who (reached.recall who)
                  (reached.observe (application setup leaks) who) event slot choice)) =
                slotResponse setup leaks who (reached.recall who)
                  (reached.observe (application setup leaks) who) event slot choice := by
              simp only [choiceResponse, responseChoice, info, inMenu, ↓reduceDIte,
                Option.getD_some]
            obtain ⟨next, nextMember, nextState⟩ := reachable (responseChoice setup leaks bounds
              (initialLaw setup) horizon scheduler who info (slotResponse setup leaks who
                (reached.recall who) (reached.observe (application setup leaks) who) event slot
                choice))
            rw [responded] at nextState
            rw [responded, ← nextState, readOffEq next nextMember]
            obtain ⟨action, encoded, values⟩ := covered
            obtain ⟨committed, successful, _⟩ := values who payload outputEq codeEq node
            obtain ⟨material, transmits, envelope⟩ := slotResponse_transmission setup leaks who
              (reached.recall who) (reached.observe (application setup leaks) who) event node
              slot choice action encoded
            have named : (runtime setup).submittedEvent? leaks (slotResponse setup leaks who
                (reached.recall who) (reached.observe (application setup leaks) who) event slot
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
              rintro ⟨_, _, unrecordedNext⟩
              rw [(runtime setup).respond_recall leaks reached who who, ite_eq_left rfl ..]
                at unrecordedNext
              unfold EventGraphRuntime.eventRecorded at unrecordedNext
              rw [List.any_append] at unrecordedNext
              simp [named] at unrecordedNext
            simp only [exit, recordedNext, ↓reduceIte]
            have nextState' : next.state = some ⟨later, none, reached.respond
                (application setup leaks) who (slotResponse setup leaks who (reached.recall who)
                  (reached.observe (application setup leaks) who) event slot choice)⟩ := nextState
            obtain ⟨entry, message, invariant⟩ := openableCommitmentInvariant_slot bounds horizon
              scheduler traceHere node readyHere slot choice action encoded successful permitted
              (nextState' ▸ next.trace)
            obtain ⟨found, ⟨residualFound⟩⟩ := protocol_sourceResidual
              (failureProfile setup.program) menu horizon scheduler traceHere _ rfl
            have foundEq : found = rank :=
              isPrefix_unique residualFound.checkpoint.ordered orderedHere
            have residual := foundEq ▸ residualFound
            cases choice with
            | none => simp at encoded
            | some source =>
                have encodedSource : encodeEventAction? setup.program event source =
                    some action := encoded
                have decodeEq := decodeEventAction_encodeEventAction?_eq_some setup.program event
                  source action encodedSource
                have owned : (graph setup).actor? event = some who :=
                  nodeView_bind_actor outputEq codeEq
                have pointDecoded : decodedPoint setup reached.application.config = some point :=
                  (decodedPoint_eq_of_isPrefix orderedHere).trans decodedHere
                have acts := (decodedPoint_actor who readyHere pointDecoded).trans owned
                obtain ⟨target, stepEq⟩ := ProtocolState.step_eq_pure_of_actor who who
                  setup.program point (fun _ => some source) acts
                have stepEq' : ProtocolState.step setup.program point
                    (fun _ => decodeEventAction setup.program event action) = PMF.pure target := by
                  rw [decodeEq]
                  exact stepEq
                have valueAt := expect_centeredCompletion_of_openableCommitment completes
                  certificate installed codeEq successful residual decodedHere stepEq'
                  failedStale next (by rw [nextState']; exact invariant) value center
                have centeredEq : centered (some source) = value target - center := by
                  simp only [centered, stepEq, expect_pure]
                change |expect (model.runBehavioralUntil certificate installed stopped next)
                  payoff - _| ≤ _
                simp only [payoff]
                rw [valueAt, centeredEq]
                have closeness := near (some source) member next nextState
                have targetBounded : |value target - center| ≤ 2 * bound := by
                  calc |value target - center| ≤ |value target| + |center| := abs_sub _ _
                    _ ≤ 2 * bound := by linarith [valueBounded target]
                rw [show (value target - center) * expect (model.runBehavioralUntil certificate
                    installed (LateStopped setup leaks bounds horizon scheduler rank) next)
                    (completionIndicator setup leaks bounds horizon scheduler rank fresh) -
                    factor * (value target - center) = (value target - center) *
                    (expect (model.runBehavioralUntil certificate installed
                      (LateStopped setup leaks bounds horizon scheduler rank) next)
                      (completionIndicator setup leaks bounds horizon scheduler rank fresh) -
                      factor) by ring, abs_mul]
                exact mul_le_mul targetBounded closeness (abs_nonneg _) (by linarith)
          · refine ⟨0, fun choice member => ?_⟩
            have covered := onePacket_honest_covered assessment covers traceHere who event
              turnHere choice member
            have notMenu : slotResponse setup leaks who (reached.recall who)
                (reached.observe (application setup leaks) who) event slot choice ∉
                bounds.onePacketActions (runtime setup) leaks who (reached.recall who)
                  (reached.observe (application setup leaks) who) := fun inMenu =>
              permitted ((slotResponse_mem_onePacket_iff setup leaks bounds who
                (reached.recall who) (reached.observe (application setup leaks) who) event node
                slot below choice covered).mp inMenu)
            have responded : choiceResponse (responseChoice setup leaks bounds (initialLaw setup)
                horizon scheduler who info (slotResponse setup leaks who (reached.recall who)
                  (reached.observe (application setup leaks) who) event slot choice)) =
                ⟨none⟩ := by
              simp only [choiceResponse, responseChoice, info, notMenu, ↓reduceDIte,
                Option.getD_some]
            rw [responded, silent, zero_mul, sub_zero, abs_zero]
            exact mul_nonneg (by linarith) η_nonneg
        have bounded' := abs_expect_slotTrembled_lateChoice_le assessment positive.le le_one
          options who (reached.recall who) (reached.observe (application setup leaks) who) event
          turnHere (fun response => readOff (respondState response)) centered
          (bound := 2 * bound) (ε := 2 * bound * η) (fun response => readOffBounded _)
          centeredBounded mean silent bounds.candidateCount tierBelow optionsBelow sending
        calc _ ≤ scale ^ 3 * (2 * bound) + 2 * bound * η := bounded'
          _ = 2 * bound * (scale ^ 3 + η) := by ring
      · -- Silence.
        rw [silenceEq, expect_pure, silenceAction]
        obtain ⟨next, member, nextState⟩ := drawn (silenceChoice setup leaks bounds
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
        have realized' : next.state ∈ ((application setup leaks).transition (initialLaw setup)
            horizon scheduler history.state joint).support := realized
        rw [state] at realized'
        rcases lateUnsent_transition_other ordered readySent outputEq
            ⟨later, actor, reached⟩ ⟨atSent, extends_, unrecordedHere⟩ owner joint realized'
            (rawAfter next) with unsent | ⟨after, afterState, prefixed, failed⟩
        · simp only [show inside next from unsent, ↓reduceIte]
        · split
          · rfl
          · have halted : stopped next := ⟨after, afterState, prefixed⟩
            simp only [later', model.runBehavioralUntil_of_stopped certificate installed halted,
              expect_pure, payoff, centeredCompletion]
            rw [completionPoint_eq_none_of_not_fresh afterState (failedStale after failed)]
            rfl
      rw [expect_congr_on_support (g := fun _ => 0) zero, expect_constant, abs_zero]
      exact κNonneg
  have startInside : inside start := by
    simp only [inside, current]
    exact ⟨rfl, List.prefix_refl _, unrecorded⟩
  have main := model.abs_expect_runBehavioralUntil_le_of_exits certificate installed stopped
    inside payoff payoffBounded κNonneg (fun history => (2 * horizon + 1) - history.trace.length)
    atEnd descends exits start startInside
  have rewriteEq : expect (model.runBehavioralUntil certificate installed stopped start)
        (fun stop => (completionPoint setup leaks bounds horizon scheduler rank fresh stop).elim
          0 value) -
      expect (model.runBehavioralUntil certificate installed stopped start)
        (completionIndicator setup leaks bounds horizon scheduler rank fresh) * center =
      expect (model.runBehavioralUntil certificate installed stopped start) payoff := by
    have firstIntegrable : PayoffIntegrable (model.runBehavioralUntil certificate installed
        stopped start) (fun stop => (completionPoint setup leaks bounds horizon scheduler rank
          fresh stop).elim 0 value) :=
      payoffIntegrable_of_bounded _ _ (C := bound) fun stop => by
        cases completionPoint setup leaks bounds horizon scheduler rank fresh stop with
        | none => simpa using boundNonneg
        | some target => exact valueBounded target
    have secondIntegrable : PayoffIntegrable (model.runBehavioralUntil certificate installed
        stopped start) (fun stop => center *
          completionIndicator setup leaks bounds horizon scheduler rank fresh stop) :=
      payoffIntegrable_of_bounded _ _ (C := |center|) fun stop => by
        simp only [completionIndicator]
        cases completionPoint setup leaks bounds horizon scheduler rank fresh stop with
        | none => simp
        | some target => simp
    rw [mul_comm, ← expect_const_mul, ← expect_sub firstIntegrable secondIntegrable]
    apply expect_congr_on_support
    intro stop _
    simp only [payoff, centeredCompletion, completionIndicator]
    cases completionPoint setup leaks bounds horizon scheduler rank fresh stop with
    | none => simp
    | some target => simp
  change |expect (model.runBehavioralUntil certificate installed stopped start)
      (fun stop => (completionPoint setup leaks bounds horizon scheduler rank fresh stop).elim
        0 value) -
    expect (model.runBehavioralUntil certificate installed stopped start)
      (completionIndicator setup leaks bounds horizon scheduler rank fresh) * center| ≤ _
  rw [rewriteEq]
  refine main.trans ?_
  have depthLe : (((2 * horizon + 1) - start.trace.length : ℕ) : ℝ) ≤ 2 * horizon + 1 := by
    have : (2 * horizon + 1) - start.trace.length ≤ 2 * horizon + 1 := Nat.sub_le _ _
    exact_mod_cast this
  calc 2 * bound * (scale ^ 3 + η) * (((2 * horizon + 1) - start.trace.length : ℕ) : ℝ)
      ≤ 2 * bound * (scale ^ 3 + η) * (2 * horizon + 1) :=
        mul_le_mul_of_nonneg_left depthLe κNonneg
    _ = 2 * (scale ^ 3 + η) * (2 * horizon + 1) * bound := by ring

end Vegas
