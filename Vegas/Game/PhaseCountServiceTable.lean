/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCountServiceTapePolicy
import Vegas.Pending.PhaseBindingMemoryCallback
import Interaction.ReactiveMixtureAtoms

/-! # Original complete timing tables and their conditional remaining coordinates -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks
local notation "graph" => serviceGraph setup mode

variable
  (values : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty),
    (serviceGraph setup mode).outputLayout event = .binding owner payload →
      List (phaseApplication runtime leaks).PlayerEntry →
      (phaseApplication runtime leaks).PlayerView → PMF (L.Val payload))
  (choose : Player → CommitAttemptEvent (serviceGraph setup mode) → List Nat → Bool)
  (failure timing : ℝ)
  (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
  (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
  (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)
  (horizon : Nat)

local notation "Q" => phaseCountServiceTapePolicy setup mode runtime leaks bounds values choose
  failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
  slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon
local notation "P" => phaseCountServicePolicy setup mode runtime leaks bounds values choose
  failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
  slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
local notation "coinLaw" => PhaseCount.bindingServiceCoinLaw failure timing firstNonnegative
  firstBounded timingNonnegative timingBounded rawWeight rawNonnegative rawBounded
local notation "original" => independentProduct (fun _address : PhaseSeedAddress graph =>
  independentProduct (fun index : Fin horizon => coinLaw (Fin.val index)))

/-- Changing an unqueried ordinal of an original address table changes none
of the earlier response laws. Other addresses, openings and inert branches
retain their complete original continuation. -/
theorem phaseCountServiceTapePolicy_update_unread
    (who : Player) (coordinate : PhaseSeedAddress graph) (past : List (app).PlayerEntry)
    (selected : Fin horizon)
    (selectedOrdinal : selected.val =
      (PhaseSeedScheduler.ownerWord runtime leaks coordinate.val who past).length)
    (before : List (app).PlayerEntry) (entry : (app).PlayerEntry)
    (recorded : before ++ [entry] <+: past)
    (tables : PhaseSeedAddress graph → Fin horizon → Bool × Bool) (coin : Bool × Bool) :
    Q (Function.update tables coordinate (Function.update (tables coordinate) selected coin))
        who before entry.beforeView =
      Q tables who before entry.beforeView := by
  classical
  let updated := Function.update tables coordinate
    (Function.update (tables coordinate) selected coin)
  unfold phaseCountServiceTapePolicy
  obtain common | ⟨event, payload, binding, selectedBranch⟩ :=
    phasePolicyDispatch_indexed_cases setup mode runtime leaks
      (fun owner _event _payload _binding => P owner)
      (fun (table : PhaseSeedAddress graph → Fin horizon → Bool × Bool)
          owner event payload binding before view =>
        if bounded : view.application.2.attempt.phase < (serviceGraph setup mode).order.eventCount ∧
            view.application.2.attempt.generation ≤ Fintype.card Player then
          PhaseCount.bindingServiceTapeMember runtime leaks bounds (P owner) owner
            ⟨view.application.2.attempt, event⟩ payload
            (fun before view => (values owner event payload binding before view).map
              PublicationResult.success)
            (choose owner ⟨view.application.2.attempt, event⟩) failure timing firstNonnegative
            firstBounded timingNonnegative timingBounded slotWeight slotNonnegative slotBounded
            rawWeight rawNonnegative rawBounded horizon
            (table ⟨⟨view.application.2.attempt, event⟩, bounded⟩) before view
        else P owner before view)
      who before entry.beforeView
  · obtain ⟨law, same⟩ := common
    exact (same updated).trans (same tables).symm
  · rw [selectedBranch updated, selectedBranch tables]
    split
    · rename_i bounded
      let address : PhaseSeedAddress graph :=
        ⟨⟨entry.beforeView.application.2.attempt, event⟩, bounded⟩
      change PhaseCount.bindingServiceTapeMember runtime leaks bounds (P who) who address.val
        payload _ _ failure timing firstNonnegative firstBounded timingNonnegative timingBounded
        slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon
        (updated address) before entry.beforeView =
          PhaseCount.bindingServiceTapeMember runtime leaks bounds (P who) who address.val
            payload _ _ failure timing firstNonnegative firstBounded timingNonnegative
            timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative
            rawBounded horizon (tables address) before entry.beforeView
      by_cases same : address = coordinate
      · have lookup : updated address = Function.update (tables address) selected coin := by
          simp only [updated, ← same, Function.update_self]
        rw [lookup]
        have selectedAt : selected.val =
            (PhaseSeedScheduler.ownerWord runtime leaks address.val who past).length := by
          simpa only [same] using selectedOrdinal
        by_cases requested : PhaseRuntimeState.requests entry.beforeView.application.2 who
            address.val
        · have earlier := PhaseCount.bindingServiceOrdinal_lt runtime leaks who address.val
            before past entry recorded requested
          by_cases inside :
              (PhaseSeedScheduler.ownerWord runtime leaks address.val who before).length < horizon
          · have different : (⟨(PhaseSeedScheduler.ownerWord runtime leaks address.val who
                before).length, inside⟩ : Fin horizon) ≠ selected := by
              intro equal
              have equalVal :
                  (PhaseSeedScheduler.ownerWord runtime leaks address.val who before).length =
                    selected.val := congrArg Fin.val equal
              omega
            simp only [PhaseCount.bindingServiceTapeMember, ite_eq_left requested,
              dite_eq_left inside,
              Function.update_of_ne different]
          · simp only [PhaseCount.bindingServiceTapeMember, ite_eq_left requested,
              dite_eq_right inside]
        · simp only [PhaseCount.bindingServiceTapeMember, ite_eq_right requested]
      · have unchanged : updated address = tables address := Function.update_of_ne same _ _
        change _ = _
        rw [unchanged]
    · rfl

/-- The current original coin is independent of the updated entire remaining
table after own recall. The two nested splits retain every other address and
ordinal; neither the entry distribution nor the remaining table is refreshed. -/
theorem phaseCountServiceTapePolicy_table_posterior
    (who : Player) (coordinate : PhaseSeedAddress graph) (past : List (app).PlayerEntry)
    (inside : (PhaseSeedScheduler.ownerWord runtime leaks coordinate.val who past).length <
      horizon) :
    let selected : Fin horizon :=
      ⟨(PhaseSeedScheduler.ownerWord runtime leaks coordinate.val who past).length, inside⟩
    ∃ remainder : PMF
        (({index : Fin horizon // index ≠ selected} → Bool × Bool) ×
          ({address : PhaseSeedAddress graph // address ≠ coordinate} →
            Fin horizon → Bool × Bool)),
      (((app).policyMixture original (fun table => Q table who)).posterior past).map
          (fun table => (table coordinate selected,
            ((fun index : {index : Fin horizon // index ≠ selected} =>
                table coordinate index.val),
              (fun address : {address : PhaseSeedAddress graph // address ≠ coordinate} =>
                table address.val)))) =
        (coinLaw selected.val).bind (fun coin => remainder.map (Prod.mk coin)) := by
  classical
  intro selected
  let outer := Equiv.piSplitAt coordinate (fun _ : PhaseSeedAddress graph =>
    Fin horizon → Bool × Bool)
  let inner := Equiv.piSplitAt selected (fun _ : Fin horizon => Bool × Bool)
  let read := fun table : PhaseSeedAddress graph → Fin horizon → Bool × Bool =>
    ((inner (table coordinate)).1, ((inner (table coordinate)).2, (outer table).2))
  let restore := fun pair : (Bool × Bool) ×
      (({index : Fin horizon // index ≠ selected} → Bool × Bool) ×
        ({address : PhaseSeedAddress graph // address ≠ coordinate} →
          Fin horizon → Bool × Bool)) =>
    outer.symm (inner.symm (pair.1, pair.2.1), pair.2.2)
  let restLaw :=
    (independentProduct (fun index : {index : Fin horizon // index ≠ selected} =>
      coinLaw index.val.val)).bind fun rest =>
        (independentProduct (fun _address :
          {address : PhaseSeedAddress graph // address ≠ coordinate} =>
            independentProduct (fun index : Fin horizon => coinLaw (Fin.val index)))).map
              (Prod.mk rest)
  let reference := (coinLaw selected.val).support_nonempty.choose
  let members := fun pair => Q (restore pair) who
  let remaining := fun rest => members (reference, rest)
  have splitLaw : (original).map read =
      (coinLaw selected.val).bind (fun coin => restLaw.map (Prod.mk coin)) := by
    rw [independentProduct_splitAt _ coordinate, PMF.map_bind]
    conv_lhs => arg 1; rw [independentProduct_splitAt _ selected]
    simp only [PMF.bind_bind, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def,
      restLaw]
    apply congrArg (PMF.bind (coinLaw selected.val))
    funext coin
    congr 1
    funext rest
    congr 1
    funext other
    change read (outer.symm (inner.symm (coin, rest), other)) = (coin, (rest, other))
    have atCoordinate := congrArg Prod.fst
      (outer.apply_symm_apply (inner.symm (coin, rest), other))
    change outer.symm (inner.symm (coin, rest), other) coordinate =
      inner.symm (coin, rest) at atCoordinate
    dsimp only [read]
    rw [atCoordinate]
    simp only [Equiv.apply_symm_apply]
  have restored (table : PhaseSeedAddress graph → Fin horizon → Bool × Bool) :
      restore (read table) = table := by
    change outer.symm (inner.symm (inner (table coordinate)), (outer table).2) = table
    rw [inner.symm_apply_apply]
    exact outer.symm_apply_apply table
  have familyEq : (fun table => members (read table)) = fun table => Q table who := by
    funext table
    exact congrArg (fun table => Q table who) (restored table)
  have transported := (app).policyMixture_posterior_map original read members past
  rw [familyEq, splitLaw] at transported
  refine ⟨((app).policyMixture restLaw remaining).posterior past, ?_⟩
  change (((app).policyMixture original (fun table => Q table who)).posterior past).map read = _
  apply transported.trans
  apply (app).policyMixture_posterior_independent_left_atoms (coinLaw selected.val) restLaw
    members remaining past
  intro before entry recorded coin rest
  have updated : restore (coin, rest) =
      Function.update (restore (reference, rest)) coordinate
        (Function.update (restore (reference, rest) coordinate) selected coin) := by
    funext address index
    by_cases sameAddress : address = coordinate
    · subst address
      by_cases sameIndex : index = selected
      · subst index
        simp [restore, outer, inner, Equiv.piSplitAt]
      · simp [restore, outer, inner, Equiv.piSplitAt, sameIndex]
    · simp [restore, outer, inner, Equiv.piSplitAt, sameAddress]
  change Q (restore (coin, rest)) who before entry.beforeView entry.action =
    Q (restore (reference, rest)) who before entry.beforeView entry.action
  rw [updated]
  exact congrArg (fun law => law entry.action)
    (phaseCountServiceTapePolicy_update_unread setup mode runtime leaks bounds values choose
      failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
      slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon who coordinate past
      selected rfl before entry recorded (restore (reference, rest)) coin)

/-- Averaging the complete original table at a genuine binding request gives
the literal normalized prescription. The posterior still retains all earlier
queries and all other original addresses of the same owner. -/
theorem phaseCountServiceTapePolicy_table_binding
    (execution : (app).Execution) {inputs} (valid : execution.application.Invariant inputs)
    (budget : execution.application.SeedBudget)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩) :
    ((app).policyMixture original (fun table => Q table who)).policy
        (execution.recall who) (execution.observe app who) =
      P who (execution.recall who) (execution.observe app who) := by
  classical
  let coordinate : PhaseSeedAddress graph := request.coordinate budget
  let past := execution.recall who
  let view := execution.observe app who
  have requested := (execution.application.requests_publicView valid who
    ⟨execution.application.attempt, event⟩).mpr request
  change PhaseRuntimeState.requests view.application.2 who coordinate.val at requested
  change ((app).policyMixture original (fun table => Q table who)).policy past view =
    P who past view
  have current (table : PhaseSeedAddress graph → Fin horizon → Bool × Bool) :=
    phaseCountServiceTapePolicy_binding setup mode runtime leaks bounds values choose failure
      timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
      slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon table execution valid
      budget who event payload binding request
  have prescribed := phaseCountServicePolicy_binding setup mode runtime leaks bounds values
    choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
    slotNonnegative slotBounded rawWeight rawNonnegative rawBounded execution valid who event
    payload binding request
  by_cases inside :
      (PhaseSeedScheduler.ownerWord runtime leaks coordinate.val who past).length < horizon
  · let selected : Fin horizon :=
      ⟨(PhaseSeedScheduler.ownerWord runtime leaks coordinate.val who past).length, inside⟩
    obtain ⟨remainder, split⟩ := phaseCountServiceTapePolicy_table_posterior setup mode runtime
      leaks bounds values choose failure timing firstNonnegative firstBounded timingNonnegative
      timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
      horizon who coordinate past inside
    have marginal : (((app).policyMixture original (fun table => Q table who)).posterior
        past).map (fun table => table coordinate selected) = coinLaw selected.val := by
      have mapped := congrArg (PMF.map Prod.fst) split
      simp only [PMF.map_comp, PMF.map_bind, Function.comp_def] at mapped
      have constants (coin : Bool × Bool) :
          remainder.map (fun _ => coin) = PMF.pure coin := PMF.map_const remainder coin
      simp_rw [constants] at mapped
      simpa only [PMF.bind_pure, selected] using mapped
    have evaluate (table : PhaseSeedAddress graph → Fin horizon → Bool × Bool) :
        Q table who past view = PhaseCount.bindingServiceCoinResponse runtime leaks bounds who
          coordinate.val payload (fun before observed =>
            (values who event payload binding before observed).map PublicationResult.success)
          (choose who coordinate.val) slotWeight slotNonnegative slotBounded
          (table coordinate selected) past view := by
      rw [current table]
      change PhaseCount.bindingServiceTapeMember runtime leaks bounds (P who) who
        coordinate.val payload _ (choose who coordinate.val) failure timing firstNonnegative
        firstBounded timingNonnegative timingBounded slotWeight slotNonnegative slotBounded
        rawWeight rawNonnegative rawBounded horizon (table coordinate) past view = _
      simp only [PhaseCount.bindingServiceTapeMember, ite_eq_left requested,
        dite_eq_left inside, selected]
    rw [ReactiveApplication.policyMixture_policy]
    simp_rw [evaluate]
    have evaluated := congrArg (fun law => law.bind fun coin =>
      PhaseCount.bindingServiceCoinResponse runtime leaks bounds who coordinate.val payload
        (fun before observed =>
          (values who event payload binding before observed).map PublicationResult.success)
        (choose who coordinate.val) slotWeight slotNonnegative slotBounded coin past view) marginal
    rw [PMF.bind_map] at evaluated
    simp only [Function.comp_def] at evaluated
    apply evaluated.trans
    exact (PhaseCount.bindingServiceCoinResponse_average runtime leaks bounds who coordinate.val
      payload _ (choose who coordinate.val) failure timing firstNonnegative firstBounded
      timingNonnegative timingBounded slotWeight slotNonnegative slotBounded rawWeight
      rawNonnegative rawBounded past view).trans prescribed.symm
  · have same (table : PhaseSeedAddress graph → Fin horizon → Bool × Bool) :
        Q table who past view = P who past view := by
      rw [current table, prescribed]
      change PhaseCount.bindingServiceTapeMember runtime leaks bounds (P who) who
        coordinate.val payload _ (choose who coordinate.val) failure timing firstNonnegative
        firstBounded timingNonnegative timingBounded slotWeight slotNonnegative slotBounded
        rawWeight rawNonnegative rawBounded horizon (table coordinate) past view = _
      simp only [PhaseCount.bindingServiceTapeMember, ite_eq_left requested, dite_eq_right inside]
      rfl
    rw [ReactiveApplication.policyMixture_policy]
    simp_rw [same]
    exact PMF.bind_const _ _

/-- Every actual callback of the original complete-table implementation is
the selected normalized policy, including openings and singleton WAIT menus.
No clear-endpoint or source-consistency assumption is used. -/
theorem phaseCountServiceTapePolicy_table_policy_of_history
    (plan : RuntimePhasePlan graph) (inputs : PMF (serviceGraph setup mode).Inputs)
    (scheduler : (app).Scheduler) (control : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (who : Player) (active : control.actor = some who) :
    ((app).policyMixture original (fun table => Q table who)).policy
        (control.execution.recall who) (control.execution.observe app who) =
      P who (control.execution.recall who) (control.execution.observe app who) := by
  classical
  let past := control.execution.recall who
  let view := control.execution.observe app who
  have insensitive (same : ∀ table, Q table who past view = P who past view) :
      ((app).policyMixture original (fun table => Q table who)).policy past view =
        P who past view := by
    rw [ReactiveApplication.policyMixture_policy]
    simp_rw [same]
    exact PMF.bind_const _ _
  obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ _ _ trace)
  have budget := (phaseApplication_seedBudget runtime leaks).history _ horizon scheduler
    (fun state member => by
      obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ member
      exact PhaseRuntimeState.initial_seedBudget plan draw)
    ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ _ _ trace)
  by_cases usable : ∃ coordinate, control.execution.application.SeedRequest who coordinate ∧
      ∀ message ∈ (app).outputs past, PhaseCount.event? message.payload ≠ some coordinate
  · obtain ⟨⟨attempt, event⟩, request, _unsent⟩ := usable
    have address : attempt = control.execution.application.attempt := request.1
    subst attempt
    cases node : nodeView (serviceGraph setup mode) event with
    | bind owner payload binding code =>
        have ownerEq : owner = who := Option.some.inj
          (((EventCode.actor_cast binding _).symm.trans
            (congrArg EventCode.actor code)).symm.trans request.2.2.2.1)
        subst owner
        exact phaseCountServiceTapePolicy_table_binding setup mode runtime leaks bounds values
          choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded
          slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon
          control.execution valid budget who event payload binding request
    | resolve owner payload field checks outputEq codeEq =>
        have ownerEq : owner = who := Option.some.inj
          (((EventCode.actor_cast outputEq _).symm.trans
            (congrArg EventCode.actor codeEq)).symm.trans request.2.2.2.1)
        subst owner
        apply insensitive
        intro table
        unfold phaseCountServiceTapePolicy
        exact phasePolicyDispatch_opening setup mode runtime leaks _ _ control.execution valid
          who event payload field checks outputEq codeEq request
    | sample payload law outputEq codeEq =>
        have noOwner : (serviceGraph setup mode).actor? event = none :=
          (EventCode.actor_cast outputEq _).symm.trans (congrArg EventCode.actor codeEq)
        have owned := request.2.2.2.1
        rw [noOwner] at owned
        cases owned
  · have controlEq : control = ⟨control.remaining, some who, control.execution⟩ := by
      cases control with
      | mk remaining actor execution => cases active; rfl
    have actual : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
          (some ⟨control.remaining, some who, control.execution⟩) := controlEq ▸ trace
    have singleton := PhaseCount.onePacketActions_eq_singleton_of_no_unsent runtime leaks bounds
      plan (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler control.remaining
      who control.execution actual usable
    have forced (policy : (app).Policy)
        (covered : ∀ action, action ∈ (policy past view).support →
          action ∈ PhaseCount.onePacketActions runtime leaks bounds who past view) :
        policy past view = PMF.pure ⟨none⟩ := by
      apply pmf_eq_pure_of_support_subset_singleton
      intro action supported
      have offered := covered action supported
      rw [singleton] at offered
      exact Finset.mem_singleton.mp offered
    apply insensitive
    intro table
    exact (forced (Q table who) (fun action supported =>
      phaseCountServiceTapePolicy_covered setup mode runtime leaks bounds values choose failure
        timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
        slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon table who past view
        action supported)).trans
      (forced (P who) (fun action supported =>
        phaseCountServicePolicy_covered setup mode runtime leaks bounds values choose failure
          timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
          slotNonnegative slotBounded rawWeight rawNonnegative rawBounded who past view action
          supported)).symm

end Vegas
