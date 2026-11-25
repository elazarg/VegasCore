module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ReadyRosterService
public import Vegas.Game.SequentialPrior

@[expose] public section

/-! # A single submission opportunity on an event-tagged roster -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability GameTheory.Protocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
  (rosters : setup.informationGraph.EventId → List Player)
  (network : (NetworkPolicy (timeouts setup)) leaks)

local notation "app" => application setup (Vegas.timeouts setup) leaks
local notation "plan" => rosterPlan setup.dataflowGraph rosters
local notation "schedule" => readyRosterScheduler setup.dataflowGraph leaks rosters network

private theorem activation_tag (past : List (app).EnvironmentEntry) (view : (app).EnvironmentView)
    (who : Player) (chosen : .activate who ∈ (schedule past view).support) :
    ∃ tag, plan[past.length]? = some (tag, .player who) ∧ view.application.EventReady tag := by
  classical
  cases found : plan[past.length]? with
  | none => simp [readyRosterScheduler, rosterScheduler, found] at chosen
  | some pair =>
    obtain ⟨tag, instruction⟩ := pair
    cases instruction with
    | player owner =>
      by_cases ready : view.application.EventReady tag
      · simp only [readyRosterScheduler, found, ready, ↓reduceIte, PMF.mem_support_pure_iff,
          ReactiveApplication.Command.activate.injEq] at chosen
        subst owner
        exact ⟨tag, rfl, ready⟩
      · simp [readyRosterScheduler, found, ready] at chosen
    | wire =>
      exact (rosterPlan_no_wire setup.dataflowGraph rosters tag (List.mem_of_getElem? found)).elim
    | tick =>
      simp only [readyRosterScheduler, rosterScheduler, found, PMF.mem_support_pure_iff] at chosen
      split at chosen <;> cases chosen
    | includeLatest event owner =>
      simp only [readyRosterScheduler, rosterScheduler, found, interactionInstruction,
        PMF.mem_support_pure_iff, reactiveLatest] at chosen
      split at chosen <;> cases chosen
    | sample event => simp [readyRosterScheduler, rosterScheduler, found, interactionInstruction]
        at chosen
    | expire event => simp [readyRosterScheduler, rosterScheduler, found, interactionInstruction]
        at chosen

variable (cursor : setup.informationGraph.EventId → Nat)

/-- An owner's earlier callbacks precede the current one in environment time. -/
private def OfferPositions (control : (app).Control) : Prop :=
  (∀ who, control.actor = some who → ∀ event,
    control.execution.application.publicView.ownTurn? who = some event →
    cursor event + 1 = control.execution.environmentRecall.length) ∧
  ∀ who entry, entry ∈ control.execution.logs who → ∀ event,
    entry.beforeView.application.publicView.ownTurn? who = some event →
    cursor event + 1 ≤ control.execution.environmentRecall.length ∧
    (control.actor.isSome → cursor event + 1 < control.execution.environmentRecall.length)

private theorem offerPositions_history
    (unique : ∀ i event who, plan[i]? = some (event, .player who) → i = cursor event) :
    ∀ {state} (_ : ((app).protocol (initialDistribution setup) (plan).length schedule).Trace state),
      state.elim True (OfferPositions setup leaks cursor)
  | _, .start => trivial
  | _, .extend (source := before) prior joint legal reached => by
    have previous := offerPositions_history unique prior
    cases before with
    | none =>
      obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ reached
      exact ⟨by intros; contradiction, by intros; contradiction⟩
    | some control =>
      obtain ⟨remaining, actor, execution⟩ := control
      cases actor with
      | some who =>
        cases (PMF.mem_support_pure_iff _ _).mp reached
        refine ⟨by intros; contradiction, ?_⟩
        intro observer entry member event turn
        rw [(app).respond_environmentRecall]
        rcases (app).respond_entry_origin execution who observer _ entry member with old | fresh
        · exact ⟨(previous.2 observer entry old event turn).1, by simp⟩
        · obtain ⟨rfl, viewed⟩ := fresh
          rw [viewed] at turn
          exact ⟨(previous.1 observer rfl event turn).le, by simp⟩
      | none =>
        cases remaining with
        | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
        | succ remaining =>
          obtain ⟨command, chosen, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
          obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
          have appended := (app).environmentStep_environmentRecall execution next command supported
          have lengthEq : next.environmentRecall.length =
              execution.environmentRecall.length + 1 := by
            rw [appended, List.length_append, List.length_singleton]
          constructor
          · intro who active event turn
            cases command <;> cases active
            obtain ⟨tag, tagged, ready⟩ :=
              activation_tag setup leaks rosters network _ _ who chosen
            have stateEq : next.application = execution.application := by
              obtain ⟨updated, step, rfl⟩ := PMF.support_map .. ▸ supported
              obtain ⟨_, _, rfl⟩ := PMF.support_map .. ▸ step
              rfl
            change next.application.publicView.ownTurn? who = some event at turn
            rw [stateEq] at turn
            have turnReady := (execution.application.publicView.ownTurn?_spec who event turn).1
            have equal := setup.informationGraph.sequentialize_ready_unique _
              ((execution.application.publicView_eventReady event).mp turnReady)
              ((execution.application.publicView_eventReady tag).mp ready)
            subst tag
            change cursor event + 1 = next.environmentRecall.length
            rw [lengthEq, unique _ event who tagged]
          · intro who entry member event turn
            change entry ∈ next.logs who at member
            rw [(app).environmentStep_recall execution next command supported] at member
            have past := (previous.2 who entry member event turn).1
            change cursor event + 1 ≤ next.environmentRecall.length ∧
              (_ → cursor event + 1 < next.environmentRecall.length)
            rw [lengthEq]
            exact ⟨past.step, fun _ => Nat.lt_succ_of_le past⟩

/-- If the public plan has one position for each tagged activation, no legal
one-packet information site offers an owner a second submission for the same event. -/
theorem readyRoster_singleSubmissionOpportunity [Fintype Player]
    (bounds : MessageBounds setup.informationGraph)
    (unique : ∀ i event who, plan[i]? = some (event, .player who) → i = cursor event) :
    SingleSubmissionOpportunity setup (Vegas.timeouts setup) leaks bounds (plan).length
      schedule := by
  intro who site late
  obtain ⟨past, view, event, atSite, pending, entry, recorded, earlier⟩ := late
  rw [atSite] at pending
  have turn := (pendingEvent_spec pending).1
  obtain ⟨⟨history, member⟩, _⟩ := site.2
  rw [onePacket_infoOf, atSite] at member
  cases stateEq : history.state with
  | none => rw [stateEq] at member; cases member
  | some control =>
    have trace := (bounds.onePacketMenu (Vegas.timeouts setup) leaks).toRawTrace
      (initialDistribution setup)
      (plan).length schedule (stateEq ▸ history.trace)
    have facts := offerPositions_history setup leaks rosters network cursor unique trace
    rw [stateEq] at member
    simp only [ReactiveApplication.observe] at member
    split at member
    · rename_i active
      obtain ⟨recallEq, viewEq⟩ := Prod.mk.inj (Option.some.inj member)
      subst past
      subst view
      have lengthEq := facts.1 who active event turn
      have strict := (facts.2 who entry recorded event earlier).2 (by simp [active])
      omega
    · cases member

/-- A ready roster with at most one activation in each event block provides at most
one submission opportunity per event, for every legal one-packet history. -/
theorem readyRoster_singleSubmissionOpportunity_of_length_le_one [Fintype Player]
    (bounds : MessageBounds setup.informationGraph)
    (single : ∀ event, (rosters event).length ≤ 1) :
    SingleSubmissionOpportunity setup (Vegas.timeouts setup) leaks bounds (plan).length
      schedule := by
  apply readyRoster_singleSubmissionOpportunity setup leaks rosters network
    (fun event => (rosterPlanPrefix setup.dataflowGraph rosters event.val).length) bounds
  intro i event who found
  have locate (n : Nat) (bounded : n ≤ setup.informationGraph.order.eventCount)
      (atIndex : (rosterPlanPrefix setup.dataflowGraph rosters n)[i]? = some (event, .player who)) :
      i = (rosterPlanPrefix setup.dataflowGraph rosters event.val).length := by
    induction n with
    | zero =>
        simp only [rosterPlanPrefix, List.take_zero, List.flatMap_nil, List.getElem?_nil] at atIndex
        cases atIndex
    | succ n ih =>
        let tag : setup.informationGraph.EventId := ⟨n, by omega⟩
        rw [rosterPlanPrefix_succ setup.dataflowGraph rosters tag] at atIndex
        by_cases early : i < (rosterPlanPrefix setup.dataflowGraph rosters n).length
        · exact ih (by omega) ((List.getElem?_append_left early).symm.trans atIndex)
        · rw [List.getElem?_append_right (Nat.le_of_not_gt early), List.getElem?_map] at atIndex
          obtain ⟨instruction, chosen, equal⟩ := Option.map_eq_some_iff.mp atIndex
          have tagEq : tag = event := congrArg Prod.fst equal
          have instructionEq : instruction = .player who := congrArg Prod.snd equal
          rw [instructionEq] at chosen
          rw [← tagEq]
          have inside : i - (rosterPlanPrefix setup.dataflowGraph rosters tag.val).length <
              (rosters tag).length := by
            by_contra! beyond
            rw [rosterBlock_eq_ending, List.getElem?_append_right (by simpa using beyond)]
              at chosen
            have member := List.mem_of_getElem? chosen
            unfold rosterPhaseEnding at member
            cases actor : setup.informationGraph.actor? tag <;> simp [actor] at member
          have one := single tag
          change i - (rosterPlanPrefix setup.dataflowGraph rosters n).length < _ at inside
          change i = (rosterPlanPrefix setup.dataflowGraph rosters n).length
          omega
  exact locate _ le_rfl ((rosterPlanPrefix_eventCount setup.dataflowGraph rosters) ▸ found)

end Vegas
