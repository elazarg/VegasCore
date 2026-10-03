/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBindingFirstPacket
import Vegas.Game.SourceServiceFirstTurnMixture
import Vegas.Pending.ReactiveBindingAcceptanceReceipts
import Vegas.Pending.ReactiveBindingOmission
import Interaction.ReactiveOwnPlay

/-! # The actual selected binding input

The selected turn is read chronologically from actual own recall. It retains
the original before-response input, including earlier deferrals. Stopping at
that input or completion does not assume that the scheduler visits the chosen
turn. Before the input is recorded, the selected family has issued no packet
for this event. Completion before that input is therefore a real public miss.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

private def selectedTurn (who : Player) (event : (graph setup).EventId) (selected : Nat)
    (played : (application setup leaks).Info × (application setup leaks).Action) : Bool :=
  match played.1 with
  | none => false
  | some (past, view) => decide (sourceServiceTurn setup leaks who event past view = some selected)

/-- The chronological selected turn's actual before-response input. -/
def sourceServiceSelectedInput? (who : Player) (event : (graph setup).EventId)
    (selected : Nat) (past : List (application setup leaks).PlayerEntry) :
    (application setup leaks).Info :=
  (((application setup leaks).recallOwnPlay past).reverse.find?
    (selectedTurn setup leaks who event selected)).bind Prod.fst

variable {setup leaks}

private theorem selectedFind_none (who : Player) (event : (graph setup).EventId)
    (selected : Nat)
    (played : List ((application setup leaks).Info × (application setup leaks).Action)) :
    ((played.find? (selectedTurn setup leaks who event selected)).bind Prod.fst = none) ↔
      played.find? (selectedTurn setup leaks who event selected) = none := by
  cases found : played.find? (selectedTurn setup leaks who event selected) with
  | none => simp only [Option.bind_none]
  | some chosen =>
      have named := List.find?_some found
      cases info : chosen.1 with
      | none => simp only [selectedTurn, info, Bool.false_eq_true] at named
      | some input => simp only [Option.bind_some, info, Option.some_ne_none]

/-- Later entries preserve the selected input and its original recalled prefix. -/
theorem sourceServiceSelectedInput?_append_present (who : Player)
    (event : (graph setup).EventId) (selected : Nat)
    (past : List (application setup leaks).PlayerEntry)
    (entry : (application setup leaks).PlayerEntry) (input : (application setup leaks).Info)
    (present : sourceServiceSelectedInput? setup leaks who event selected past = input)
    (nonempty : input ≠ none) :
    sourceServiceSelectedInput? setup leaks who event selected (past ++ [entry]) = input := by
  cases input with
  | none => exact (nonempty rfl).elim
  | some input =>
      obtain ⟨played, found, chosen⟩ := Option.bind_eq_some_iff.mp present
      unfold sourceServiceSelectedInput?
      rw [ReactiveApplication.recallOwnPlay_append, List.reverse_cons, List.find?_append, found]
      simpa only [Option.some_or, Option.bind_some] using chosen

/-- Any extension of own recall preserves an already recorded selected input. -/
theorem sourceServiceSelectedInput?_prefix (who : Player) (event : (graph setup).EventId)
    (selected : Nat) (before after : List (application setup leaks).PlayerEntry)
    (retained : before <+: after) (input : (application setup leaks).Info)
    (present : sourceServiceSelectedInput? setup leaks who event selected before = input)
    (nonempty : input ≠ none) :
    sourceServiceSelectedInput? setup leaks who event selected after = input := by
  obtain ⟨suffix, rfl⟩ := retained
  induction suffix using List.reverseRecOn with
  | nil => simpa only [List.append_nil] using present
  | append_singleton suffix entry ih =>
      rw [← List.append_assoc]
      exact sourceServiceSelectedInput?_append_present who event selected _ entry input ih nonempty

/-- Appending a selected response records its real before-response input.
An unselected response cannot create this readout. -/
theorem sourceServiceSelectedInput?_respond (who : Player) (event : (graph setup).EventId)
    (selected : Nat) (execution : (application setup leaks).Execution)
    (absent : sourceServiceSelectedInput? setup leaks who event selected
      (execution.recall who) = none)
    (response : (application setup leaks).Action) :
    sourceServiceSelectedInput? setup leaks who event selected
        ((execution.respond (application setup leaks) who response).recall who) =
      if sourceServiceTurn setup leaks who event (execution.recall who)
          (execution.observe (application setup leaks) who) = some selected
      then some (execution.recall who, execution.observe (application setup leaks) who)
      else none := by
  have found := (selectedFind_none who event selected _).mp absent
  unfold sourceServiceSelectedInput?
  rw [ReactiveApplication.respond_ownPlay, List.reverse_cons, List.find?_append, found]
  by_cases current : sourceServiceTurn setup leaks who event (execution.recall who)
      (execution.observe (application setup leaks) who) = some selected
  · have named : selectedTurn setup leaks who event selected
        (some (execution.recall who, execution.observe (application setup leaks) who), response) =
        true := decide_eq_true current
    simp only [Option.none_or, List.find?_cons_of_pos named, Option.bind_some,
      current, ↓reduceIte]
  · have unnamed : ¬ selectedTurn setup leaks who event selected
        (some (execution.recall who, execution.observe (application setup leaks) who), response) =
        true := by
      simpa only [selectedTurn, decide_eq_true_eq] using current
    simp only [Option.none_or, List.find?_cons_of_neg unnamed, List.find?_nil,
      Option.bind_none, current, ↓reduceIte]

private theorem selectedInput_untouched (owner : Player) (event : (graph setup).EventId)
    (selected : Nat) (execution : (application setup leaks).Execution)
    (untouched : Untouched setup leaks event execution) :
    sourceServiceSelectedInput? setup leaks owner event selected (execution.recall owner) =
      none := by
  have all : ∀ entry ∈ execution.recall owner,
      entry.beforeView.application.publicView.ownTurn? owner ≠ some event :=
    fun entry member turn => untouched owner entry member
      (PublicView.ownTurn?_spec _ owner event turn).1
  generalize execution.recall owner = past at all ⊢
  revert all
  induction past using List.reverseRecOn with
  | nil => intro _all; rfl
  | append_singleton past entry ih =>
      intro all
      have prior := ih (fun other member => all other (List.mem_append_left _ member))
      have found := (selectedFind_none owner event selected _).mp prior
      have notTurn := all entry (List.mem_append_right _ (List.mem_singleton_self _))
      have notSelected := sourceServiceTurn_of_not_turn setup leaks owner event past
        entry.beforeView notTurn
      have unnamed : ¬ selectedTurn setup leaks owner event selected
          (some (past, entry.beforeView), entry.action) = true := by
        change ¬ decide (sourceServiceTurn setup leaks owner event past entry.beforeView =
          some selected) = true
        simp only [decide_eq_true_eq, notSelected, reduceCtorEq, not_false_eq_true]
      unfold sourceServiceSelectedInput?
      rw [ReactiveApplication.recallOwnPlay_append, List.reverse_cons, List.find?_append, found]
      simp only [Option.none_or, List.find?_cons_of_neg unnamed, List.find?_nil, Option.bind_none]

private theorem selectedFamily_no_packet
    (players : Player → (application setup leaks).Policy)
    (bound : (graph setup).EventId → Nat) (profile : BehavioralProfile setup.program)
    (owner : Player) (event : (graph setup).EventId) (turns : Nat) (slot : Fin (turns + 1)) :
    (application setup leaks).PolicyInvariant
      (Function.update players owner
        (sourceServiceTurnFamily setup leaks bound profile owner event turns slot))
      (fun current => sourceServiceSelectedInput? setup leaks owner event slot.val
        (current.recall owner) = none →
          (runtime setup).eventRecorded leaks (current.recall owner) event = false) := by
  let app := application setup leaks
  constructor
  · intro current actor response holds chosen after
    by_cases same : actor = owner
    · subst actor
      have absent : sourceServiceSelectedInput? setup leaks owner event slot.val
          (current.recall owner) = none := by
        by_contra present
        have retained := sourceServiceSelectedInput?_prefix owner event slot.val _ _
          (app.respond_recall_prefix current owner owner response) _ rfl present
        exact present (retained.symm.trans after)
      have unselected : sourceServiceTurn setup leaks owner event (current.recall owner)
          (current.observe app owner) ≠ some slot.val := by
        intro selected
        rw [sourceServiceSelectedInput?_respond owner event slot.val current absent response,
          ite_eq_left selected] at after
        cases after
      rw [Function.update_self] at chosen
      have waits : sourceServiceTurnFamily setup leaks bound profile owner event turns slot
          (current.recall owner) (current.observe app owner) =
          app.silentPolicy (current.recall owner) (current.observe app owner) := by
        apply app.turnScheduledPolicy_unselected
        intro other equal
        cases Option.some.inj equal
        exact unselected
      rw [waits] at chosen
      cases (PMF.mem_support_pure_iff _ _).mp chosen
      have same := (runtime setup).eventRecorded_respond_other leaks current owner owner ⟨none⟩
        event (fun _ impossible => by cases impossible)
      exact same.trans (holds absent)
    · rw [app.respond_recall_other current actor owner (Ne.symm same) response] at after ⊢
      exact holds after
  · intro current next command holds moved after
    rw [app.environmentStep_recall current next command moved] at after ⊢
    exact holds after

private theorem selectedInput_origin
    (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy)
    (owner : Player) (event : (graph setup).EventId) (selected : Nat)
    (count : Nat) (execution : (application setup leaks).Execution)
    (ready : execution.application.config.cut.Ready event)
    (absent : sourceServiceSelectedInput? setup leaks owner event selected
      (execution.recall owner) = none)
    (stopped : (application setup leaks).Execution)
    (hit : sourceServiceSelectedInput? setup leaks owner event selected
      (stopped.recall owner) ≠ none)
    (reached : stopped ∈ ((application setup leaks).runUntil scheduler players
      (fun final => event ∈ final.application.config.cut.completed ∨
        sourceServiceSelectedInput? setup leaks owner event selected (final.recall owner) ≠ none)
      count execution).support) :
    ∃ (used : Nat) (before middle : (application setup leaks).Execution)
      (response : (application setup leaks).Action),
      used < count ∧
      before ∈ ((application setup leaks).runRounds scheduler players used execution).support ∧
      before.application.config = execution.application.config ∧
      sourceServiceSelectedInput? setup leaks owner event selected (before.recall owner) = none ∧
      .activate owner ∈ (scheduler before.environmentRecall
        (before.observeEnvironment (application setup leaks))).support ∧
      middle ∈ (before.environmentStep (application setup leaks) (.activate owner)).support ∧
      sourceServiceTurn setup leaks owner event (middle.recall owner)
        (middle.observe (application setup leaks) owner) = some selected ∧
      response ∈ (players owner (middle.recall owner)
        (middle.observe (application setup leaks) owner)).support ∧
      stopped = middle.respond (application setup leaks) owner response ∧
      sourceServiceSelectedInput? setup leaks owner event selected (stopped.recall owner) =
        some (middle.recall owner, middle.observe (application setup leaks) owner) := by
  classical
  let app := application setup leaks
  let stop := fun final : app.Execution => event ∈ final.application.config.cut.completed ∨
    sourceServiceSelectedInput? setup leaks owner event selected (final.recall owner) ≠ none
  induction count generalizing execution with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact (hit absent).elim
  | succ count ih =>
      have running : ¬ stop execution := by
        intro halted
        rcases halted with completed | seen
        · exact ready.1 completed
        · exact seen absent
      change stopped ∈ (app.runUntil scheduler players stop (count + 1) execution).support
        at reached
      simp only [ReactiveApplication.runUntil, running, ↓reduceIte] at reached
      obtain ⟨next, moved, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      by_cases seen : stop next
      · rw [app.runUntil_of_stop scheduler players stop count next seen,
          PMF.mem_support_pure_iff] at rest
        subst stopped
        obtain ⟨command, chosen, middle, observed, cases⟩ := round_cases setup leaks moved
        have recalls := app.environmentStep_recall execution middle command observed
        have notYet : sourceServiceSelectedInput? setup leaks owner event selected
            (middle.recall owner) = none := by rw [recalls]; exact absent
        rcases cases with ⟨_inactive, rfl⟩ | ⟨actor, active, response, supported, rfl⟩
        · exact (hit notYet).elim
        · by_cases same : actor = owner
          · subst actor
            have current : sourceServiceTurn setup leaks owner event (middle.recall owner)
                (middle.observe app owner) = some selected := by
              by_contra different
              apply hit
              rw [sourceServiceSelectedInput?_respond owner event selected middle notYet response,
                ite_eq_right different]
            have commandEq : command = .activate owner := by
              cases command with
              | activate actor =>
                  exact congrArg ReactiveApplication.Command.activate (Option.some.inj active)
              | wait | «include» _ | application _ => cases active
            subst commandEq
            refine ⟨0, execution, middle, response, by omega, ?_, rfl, absent, chosen,
              observed, current, supported, rfl, ?_⟩
            · simp only [ReactiveApplication.runRounds, PMF.mem_support_pure_iff]
            · rw [sourceServiceSelectedInput?_respond owner event selected middle notYet response,
                ite_eq_left current]
          · apply (hit ?_).elim
            rw [app.respond_recall_other middle actor owner (Ne.symm same) response]
            exact notYet
      · have nextAbsent : sourceServiceSelectedInput? setup leaks owner event selected
            (next.recall owner) = none := by
          by_contra present
          exact seen (Or.inr present)
        have same : next.application.config = execution.application.config := by
          rcases round_configStep setup leaks scheduler players execution next moved with same |
              ⟨target, targetReady, action, stepped⟩
          · exact same
          · have targetEq := setup.eventGraph.sequentialize_ready_unique
              execution.application.config.cut targetReady ready
            subst target
            apply (seen (Or.inl ?_)).elim
            rw [execution.application.config.step_cut event ready action next.application.config
              stepped, EventOrder.Cut.mem_complete]
            exact Or.inl rfl
        obtain ⟨used, before, middle, response, within, actual, configEq, noInput, chosen,
          observed, current, supported, result, readout⟩ :=
          ih next (same ▸ ready) nextAbsent rest
        refine ⟨used + 1, before, middle, response, by omega, ?_, configEq.trans same,
          noInput, chosen, observed, current, supported, result, readout⟩
        rw [Nat.add_comm, ReactiveApplication.runRounds_add, PMF.support_bind]
        exact Set.mem_iUnion₂.mpr ⟨next,
          by simpa only [ReactiveApplication.runRounds, PMF.bind_pure] using moved, actual⟩

/-- The actual selected-family phase reaches either its original selected
input, with the real supported response, or completion before any attempt.
The latter branch has a public miss and typed failure. Foreign players are
arbitrary raw policies; the original prefix follows only the named owner's
turn policy. No visit to the selected turn is assumed. -/
theorem sourceService_binding_selected_stop
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (players : Player → (application setup leaks).Policy)
    (turns : Nat) (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (owner : Player)
    (follows : players owner = sourceServiceTurnPolicy setup leaks bound turns timing profile owner)
    (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (slot : Fin (turns + 1)) (execution : (application setup leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler players event.val execution)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (stopped : (application setup leaks).Execution)
    (reached : stopped ∈ ((application setup leaks).runUntilHorizon scheduler
      (Function.update players owner
        (sourceServiceTurnFamily setup leaks bound profile owner event turns slot))
      (fun final => event ∈ final.application.config.cut.completed ∨
        sourceServiceSelectedInput? setup leaks owner event slot.val (final.recall owner) ≠ none)
      horizon execution).support) :
    let app := application setup leaks
    let familyPlayers := Function.update players owner
      (sourceServiceTurnFamily setup leaks bound profile owner event turns slot)
    (∃ (used : Nat) (before middle : app.Execution) (response : app.Action),
      used < horizon - execution.environmentRecall.length ∧
      before ∈ (app.runRounds scheduler familyPlayers used execution).support ∧
      before.application.config = execution.application.config ∧
      Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨horizon - middle.environmentRecall.length, some owner, middle⟩)) ∧
      .activate owner ∈ (scheduler before.environmentRecall
        (before.observeEnvironment app)).support ∧
      middle ∈ (before.environmentStep app (.activate owner)).support ∧
      sourceServiceTurn setup leaks owner event (middle.recall owner) (middle.observe app owner) =
        some slot.val ∧
      sourceServiceSelectedInput? setup leaks owner event slot.val (middle.recall owner) = none ∧
      (runtime setup).eventRecorded leaks (middle.recall owner) event = false ∧
      response ∈ (sourceServiceCanonicalOpportunity setup leaks bound profile owner event
        (middle.recall owner) (middle.observe app owner)).support ∧
      stopped = middle.respond app owner response ∧
      sourceServiceSelectedInput? setup leaks owner event slot.val (stopped.recall owner) =
        some (middle.recall owner, middle.observe app owner)) ∨
    (event ∈ stopped.application.config.cut.completed ∧
      sourceServiceSelectedInput? setup leaks owner event slot.val (stopped.recall owner) = none ∧
      (runtime setup).eventRecorded leaks (stopped.recall owner) event = false ∧
      stopped.network.Satisfies (fun message => message.sender = owner →
        message.payload.call.event? (graph setup) ≠ some event) ∧
      event ∈ stopped.application.missedEvents ∧
      (⟨.inr event, outputEq⟩ : EventGraph.FieldRef (graph setup).layout
        (.binding owner payload)).get? stopped.application.config.store = some .failure) := by
  classical
  dsimp only
  let app := application setup leaks
  let familyPlayers := Function.update players owner
    (sourceServiceTurnFamily setup leaks bound profile owner event turns slot)
  let stop := fun final : app.Execution => event ∈ final.application.config.cut.completed ∨
    sourceServiceSelectedInput? setup leaks owner event slot.val (final.recall owner) ≠ none
  have ready := (ready_iff_rank setup execution.application.config event.val boundary.ordered
    event).mpr rfl
  have absent := selectedInput_untouched owner event slot.val execution (boundary.untouched event
    rfl)
  have initialUnrecorded : (runtime setup).eventRecorded leaks (execution.recall owner) event =
      false := by
    have atTurn := (canonicalSlots_roundsFrom scheduler players owner timing profile follows
      _ execution boundary.supported).1
    apply Bool.eq_false_iff.mpr
    intro recorded
    obtain ⟨entry, member, submitted⟩ := ((runtime setup).eventRecorded_iff leaks _ event).mp
      recorded
    have turn := atTurn entry member event submitted
    exact boundary.untouched event rfl owner entry member (PublicView.ownTurn?_spec _ owner event
      turn).1
  obtain ⟨startTrace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players
    _ bounded execution boundary.supported
  have invariant := selectedFamily_no_packet players bound profile owner event turns slot
  obtain ⟨used, budget, rounds, length⟩ := app.runUntil_runRounds scheduler familyPlayers stop
    (horizon - execution.environmentRecall.length) execution stopped reached
  have left : horizon - stopped.environmentRecall.length =
      horizon - execution.environmentRecall.length - used := by omega
  obtain ⟨finalTrace⟩ := app.raw_trace_runRounds (initialLaw setup) horizon scheduler familyPlayers
    (horizon - execution.environmentRecall.length - used) used execution stopped
    (by simpa only [Nat.sub_add_cancel budget] using startTrace) rounds
  have finalUnrecorded := invariant.runRounds scheduler used execution stopped
    (fun _ => initialUnrecorded) rounds
  by_cases hit : sourceServiceSelectedInput? setup leaks owner event slot.val
      (stopped.recall owner) ≠ none
  · left
    obtain ⟨used, before, middle, response, within, actual, configEq, noInput, chosen, observed,
      current, supported, result, readout⟩ := selectedInput_origin scheduler familyPlayers owner
        event slot.val (horizon - execution.environmentRecall.length) execution ready absent
          stopped hit reached
    have beforeLength := app.runRounds_environmentRecall_length scheduler familyPlayers used
      execution before actual
    obtain ⟨beforeTrace⟩ := app.raw_trace_runRounds (initialLaw setup) horizon scheduler
      familyPlayers (horizon - execution.environmentRecall.length - used) used execution before
        (by simpa only [Nat.sub_add_cancel (Nat.le_of_lt within)] using startTrace) actual
    have middleLength : middle.environmentRecall.length = before.environmentRecall.length + 1 := by
      rw [(app.activation_visible before middle owner observed).2, List.length_append,
        List.length_singleton]
    obtain ⟨middleTrace⟩ := app.raw_trace_environment (initialLaw setup) horizon scheduler
      (horizon - middle.environmentRecall.length) before middle (.activate owner)
      (by
        have count : horizon - execution.environmentRecall.length - used =
            horizon - middle.environmentRecall.length + 1 := by omega
        rwa [count] at beforeTrace) chosen observed
    have recalls := app.environmentStep_recall before middle (.activate owner) observed
    have middleAbsent : sourceServiceSelectedInput? setup leaks owner event slot.val
        (middle.recall owner) = none := by rw [recalls]; exact noInput
    have beforeUnrecorded := invariant.runRounds scheduler used execution before
      (fun _ => initialUnrecorded) actual noInput
    have middleUnrecorded : (runtime setup).eventRecorded leaks (middle.recall owner) event =
        false := by rw [recalls]; exact beforeUnrecorded
    have canonical : response ∈ (sourceServiceCanonicalOpportunity setup leaks bound profile owner
        event (middle.recall owner) (middle.observe app owner)).support := by
      change response ∈ (familyPlayers owner (middle.recall owner)
        (middle.observe app owner)).support at supported
      dsimp only [familyPlayers] at supported
      rw [Function.update_self] at supported
      unfold sourceServiceTurnFamily at supported
      rw [app.turnScheduledPolicy_selected _ slot _ _ _ _ current] at supported
      exact supported
    exact ⟨used, before, middle, response, within, actual, configEq, ⟨middleTrace⟩, chosen,
      observed, current, middleAbsent, middleUnrecorded, canonical, result, readout⟩
  · right
    have absentFinal : sourceServiceSelectedInput? setup leaks owner event slot.val
        (stopped.recall owner) = none := not_ne_iff.mp hit
    have unrecorded := finalUnrecorded absentFinal
    have completed : event ∈ stopped.application.config.cut.completed := by
      rcases app.runUntilHorizon_stopped scheduler familyPlayers stop horizon
        (horizon - execution.environmentRecall.length) execution stopped (by omega) reached with
        halted | spent
      · exact halted.resolve_right hit
      · rw [← left, spent, Nat.sub_self] at finalTrace
        have complete := contract.completes ⟨0, none, stopped⟩ finalTrace (by
          change 0 = 0 ∧ _
          exact ⟨rfl, rfl⟩)
        rw [complete]
        exact Finset.mem_univ _
    have facts := legalFacts setup leaks horizon scheduler _ finalTrace
    have noPacket := sourceService_unrecorded_event_packets setup leaks stopped owner event
      facts.provenance unrecorded
    have inputTrace := finalTrace
    rw [initialLaw_eq_inputs] at inputTrace
    have absentHandle : stopped.application.accepted (.inr event) = none := by
      cases accepted : stopped.application.accepted (.inr event) with
      | none => rfl
      | some candidate =>
          obtain ⟨kind, typed⟩ := facts.binding.accepted_typed (.inr event) candidate accepted
          change (graph setup).outputLayout event = .binding candidate.1 kind at typed
          have authored : candidate.1 = owner :=
            (EventGraph.EventField.binding.inj (typed.symm.trans outputEq)).1
          obtain ⟨message, published, sender, named, _⟩ := acceptedBindingReceipts_history
            (runtime setup) leaks (setup.initialLaw.map setup.eventInputs) horizon scheduler
            inputTrace event candidate accepted
          exact ((noPacket.ledger message published (sender.trans authored))
            (by rw [named]; rfl)).elim
    have misses := bindingMissesExact_history (runtime setup) leaks
      (setup.initialLaw.map setup.eventInputs) horizon scheduler inputTrace event owner payload
      outputEq
    refine ⟨completed, absentFinal, unrecorded, noPacket,
      misses.mpr ⟨completed, absentHandle⟩, ?_⟩
    let ref : EventGraph.FieldRef (graph setup).layout (.binding owner payload) :=
      ⟨.inr event, outputEq⟩
    have present := ref.get?_isSome stopped.application.config.store
      ((stopped.application.config.output_available event).mpr completed)
    obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp present
    cases value with
    | failure => exact stored
    | success value =>
        obtain ⟨candidate, accepted, _, _⟩ := facts.binding.success_provenance ref value stored
        rw [absentHandle] at accepted
        cases accepted

end Vegas
