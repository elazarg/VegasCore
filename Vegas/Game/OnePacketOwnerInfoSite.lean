/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketOwnerSettled
import Vegas.Game.OnePacketSwapInfo

/-! # The two sites' information states differ exactly by the owner swap

Take two late information sites of a player `who` with the same late-delivery
key, at neither of which `who` owes a failure at the decoded point of any
history. The owner swap between the views `who` has at the two sites sends the
information state of the first site to that of the second
(`Vegas.ownerSwap_info`).

Each history of a site is settled for `who` (`Vegas.ownerSettled_of_trace`),
with the slots named by `who`'s packets, which the key records alike. So the
current views are swapped one into the other
(`Vegas.EventGraphRuntime.HiddenSwap.view_ownerSwap_of_settled`), and so is
each recalled entry: its view was taken at an earlier state of each history
with the same operational part (`Vegas.recallRecord_of_trace`), and its
recorded response is swapped into the response with the same envelope
(`Vegas.EventGraphRuntime.HiddenSwap.action_ownerSwap`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

omit [Fintype Player] in
/-- Recalls emitting the same envelopes have the same outputs. -/
private theorem outputs_eq_of_emitted :
    ∀ {first second : List (application setup leaks).PlayerEntry},
      first.map ReactiveApplication.PlayerEntry.emitted =
        second.map ReactiveApplication.PlayerEntry.emitted →
      (application setup leaks).outputs first = (application setup leaks).outputs second
  | [], [], _ => rfl
  | [], _ :: _, same => by cases same
  | _ :: _, [], same => by cases same
  | head :: tail, other :: rest, same => by
      simp only [List.map_cons, List.cons.injEq] at same
      have rest := outputs_eq_of_emitted same.2
      unfold ReactiveApplication.outputs at rest ⊢
      rw [List.filterMap_cons, List.filterMap_cons, same.1, rest]

/-- **The owner swap between two settled histories.** Two histories of the
one-packet game ending where `who` acts, with the same late-delivery key, at
whose decoded points `who` owes no failure, and at each of which some ready
event is named by none of `who`'s packets: the owner swap between the two views
of `who` sends the first information state to the second. -/
theorem ownerSwap_info_of_traces {first second : (application setup leaks).Control}
    (firstTrace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some first))
    (secondTrace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some second))
    {who : Player}
    (sameKey : lateKey setup leaks who (some (first.execution.recall who,
        first.execution.observe (application setup leaks) who)) =
      lateKey setup leaks who (some (second.execution.recall who,
        second.execution.observe (application setup leaks) who)))
    (firstDebtFree : ∀ point, nativeDecodedState setup leaks (some first) = some point →
      ¬ ProtocolState.OwesFailure who setup.program point)
    (secondDebtFree : ∀ point, nativeDecodedState setup leaks (some second) = some point →
      ¬ ProtocolState.OwesFailure who setup.program point)
    (firstPending : ∃ event, first.execution.application.config.cut.Ready event ∧
      ∀ message ∈ (application setup leaks).outputs (first.execution.recall who),
        message.payload.call.event? (graph setup) ≠ some event)
    (secondPending : ∃ event, second.execution.application.config.cut.Ready event ∧
      ∀ message ∈ (application setup leaks).outputs (second.execution.recall who),
        message.payload.call.event? (graph setup) ≠ some event) :
    (ownerSwap who (first.execution.observe (application setup leaks) who).application
        (second.execution.observe (application setup leaks) who).application).info
        (some (first.execution.recall who,
          first.execution.observe (application setup leaks) who)) =
      some (second.execution.recall who,
        second.execution.observe (application setup leaks) who) := by
  simp only [lateKey, Option.some.injEq, LateKey.mk.injEq, true_and] at sameKey
  obtain ⟨currentEq, recalledEq, _⟩ := sameKey
  have lengthEq : (first.execution.recall who).length = (second.execution.recall who).length := by
    simpa using congrArg List.length recalledEq
  have emittedEq : (first.execution.recall who).map ReactiveApplication.PlayerEntry.emitted =
      (second.execution.recall who).map ReactiveApplication.PlayerEntry.emitted := by
    have mapped := congrArg (List.map Prod.snd) recalledEq
    rw [List.map_map, List.map_map] at mapped
    exact mapped
  have outputsEq := outputs_eq_of_emitted emittedEq
  have firstSettled := ownerSettled_of_trace firstTrace firstDebtFree firstPending
  have secondSettled := ownerSettled_of_trace secondTrace secondDebtFree secondPending
  rw [← outputsEq] at secondSettled
  change some ((first.execution.recall who).map _, _) = _
  congr 2
  · apply List.ext_getElem (by simpa using lengthEq)
    intro k firstInside secondInside
    rw [List.length_map] at firstInside
    rw [List.getElem_map]
    have entryKey := congrArg (fun list => list[k]?) recalledEq
    simp only [List.getElem?_map, List.getElem?_eq_getElem firstInside,
      List.getElem?_eq_getElem secondInside, Option.map_some, Option.some.injEq,
      Prod.mk.injEq] at entryKey
    obtain ⟨operational, emitted⟩ := entryKey
    have takeEq : (application setup leaks).outputs ((first.execution.recall who).take k) =
        (application setup leaks).outputs ((second.execution.recall who).take k) := by
      apply outputs_eq_of_emitted
      rw [List.map_take, List.map_take, emittedEq]
    obtain ⟨firstBefore, firstView, firstGrows, firstFresh, firstInitial, firstRecorded⟩ :=
      recallRecord_of_trace firstTrace first rfl who k firstInside
    obtain ⟨secondBefore, secondView, secondGrows, secondFresh, secondInitial,
      secondRecorded⟩ := recallRecord_of_trace secondTrace second rfl who k secondInside
    rw [← takeEq] at secondFresh
    have knownEq : ReactiveApplication.ResponseMenu.knownPackets
        ((first.execution.recall who).take k) (first.execution.recall who)[k].beforeView =
        ReactiveApplication.ResponseMenu.knownPackets ((second.execution.recall who).take k)
          (second.execution.recall who)[k].beforeView := by
      simp only [operationalView, Prod.mk.injEq] at operational
      unfold ReactiveApplication.ResponseMenu.knownPackets
      rw [takeEq, operational.2.1]
    rw [knownEq] at firstRecorded
    rcases firstEntry : (first.execution.recall who)[k] with
      ⟨firstBeforeView, firstAction, firstEmitted⟩
    rcases secondEntry : (second.execution.recall who)[k] with
      ⟨secondBeforeView, secondAction, secondEmitted⟩
    rw [firstEntry] at firstView firstRecorded operational emitted
    rw [secondEntry] at secondView secondRecorded firstRecorded operational emitted
    change (⟨(ownerSwap who (first.execution.application.playerView who)
        (second.execution.application.playerView who)).view firstBeforeView,
      (ownerSwap who (first.execution.application.playerView who)
        (second.execution.application.playerView who)).action firstAction, firstEmitted⟩ :
          (application setup leaks).PlayerEntry) = ⟨secondBeforeView, secondAction, secondEmitted⟩
    have actionEq := EventGraphRuntime.HiddenSwap.action_ownerSwap who firstSettled
      secondSettled firstRecorded secondRecorded emitted
      (fun message event serial sent call => ⟨message,
        List.mem_filterMap.mpr ⟨(first.execution.recall who)[k], List.getElem_mem firstInside,
          by rw [firstEntry]; exact sent⟩, event, call⟩)
    have viewEq := EventGraphRuntime.HiddenSwap.view_ownerSwap_of_settled who firstSettled
      secondSettled (firstGrows.ownerEarlier who firstFresh firstInitial)
      (secondGrows.ownerEarlier who secondFresh secondInitial) firstView secondView operational
    change firstEmitted = secondEmitted at emitted
    rw [viewEq, actionEq, emitted]
  · exact EventGraphRuntime.HiddenSwap.view_ownerSwap_of_settled who firstSettled
      secondSettled firstSettled.earlier secondSettled.earlier rfl rfl currentEq

/-- A late delivery leaves a ready event named by none of the player's
packets. -/
theorem pending_of_lateDelivery {control : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    {who : Player}
    (late : LateDelivery setup leaks who (some (control.execution.recall who,
      control.execution.observe (application setup leaks) who))) :
    ∃ event, control.execution.application.config.cut.Ready event ∧
      ∀ message ∈ (application setup leaks).outputs (control.execution.recall who),
        message.payload.call.event? (graph setup) ≠ some event := by
  obtain ⟨past, view, event, infoEq, pending, _⟩ := late
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj infoEq)
  obtain ⟨_, ready, _, unrecorded⟩ := pendingEvent_spec pending
  refine ⟨event, (State.publicView_eventReady _ event).mp ready, fun message member named => ?_⟩
  have rawTrace := (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup)
    horizon scheduler trace
  have recorded := (history_eventRecorded_iff rawTrace who event).mpr ⟨message, member, named⟩
  rw [unrecorded] at recorded
  cases recorded

/-- A site of `who` is reached at a history ending where `who` acts with the
site's recall and view. -/
private theorem site_realized {who : Player}
    (site : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    (debtFree : ∀ history : (onePacketInformation setup leaks bounds horizon
        scheduler).InformationHistory who site.1, ∀ point,
      nativeDecodedState setup leaks history.1.state = some point →
        ¬ ProtocolState.OwesFailure who setup.program point) :
    ∃ control : (application setup leaks).Control,
      Nonempty ((onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control)) ∧
      control.execution.recall who = past ∧
      control.execution.observe (application setup leaks) who = view ∧
      ∀ point, nativeDecodedState setup leaks (some control) = some point →
        ¬ ProtocolState.OwesFailure who setup.program point := by
  obtain ⟨⟨history, member⟩, -⟩ := site.2
  have info := member
  rw [onePacket_infoOf, atSite] at info
  cases stateEq : history.state with
  | none =>
      rw [stateEq] at info
      cases info
  | some control =>
      have trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace
          (some control) := stateEq ▸ history.trace
      rw [stateEq] at info
      simp only [ReactiveApplication.observe] at info
      split at info
      · obtain ⟨recallEq, viewEq⟩ := Prod.mk.inj (Option.some.inj info)
        exact ⟨control, ⟨trace⟩, recallEq, viewEq, fun point decoded =>
          debtFree ⟨history, member⟩ point (by rw [stateEq]; exact decoded)⟩
      · cases info

/-- **The two sites' information states differ exactly by the owner swap.**
Take two late-delivery information sites of `who` with the same late-delivery
key, at neither of which `who` owes a failure at the decoded point of any
history (the negation of `Vegas.OwingAgent` at the site's agent). The owner
swap between the views of `who` at the two sites sends the information state of
the first site to that of the second. -/
theorem ownerSwap_info {who : Player}
    {site₁ site₂ : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who}
    {past₁ past₂ : List (application setup leaks).PlayerEntry}
    {view₁ view₂ : (application setup leaks).PlayerView}
    (firstSite : site₁.1 = some (past₁, view₁)) (secondSite : site₂.1 = some (past₂, view₂))
    (sameKey : lateKey setup leaks who site₁.1 = lateKey setup leaks who site₂.1)
    (firstDebtFree : ∀ history : (onePacketInformation setup leaks bounds horizon
        scheduler).InformationHistory who site₁.1, ∀ point,
      nativeDecodedState setup leaks history.1.state = some point →
        ¬ ProtocolState.OwesFailure who setup.program point)
    (secondDebtFree : ∀ history : (onePacketInformation setup leaks bounds horizon
        scheduler).InformationHistory who site₂.1, ∀ point,
      nativeDecodedState setup leaks history.1.state = some point →
        ¬ ProtocolState.OwesFailure who setup.program point)
    (firstLate : LateDelivery setup leaks who site₁.1)
    (secondLate : LateDelivery setup leaks who site₂.1) :
    (ownerSwap who view₁.application view₂.application).info site₁.1 = site₂.1 := by
  obtain ⟨first, ⟨firstTrace⟩, rfl, rfl, firstDebt⟩ := site_realized site₁ firstSite firstDebtFree
  obtain ⟨second, ⟨secondTrace⟩, rfl, rfl, secondDebt⟩ :=
    site_realized site₂ secondSite secondDebtFree
  rw [firstSite] at sameKey firstLate
  rw [secondSite] at sameKey secondLate
  rw [firstSite, secondSite]
  exact ownerSwap_info_of_traces firstTrace secondTrace sameKey firstDebt secondDebt
    (pending_of_lateDelivery firstTrace firstLate) (pending_of_lateDelivery secondTrace secondLate)

end Vegas
