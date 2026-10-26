/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketRecallPrefix
import Vegas.Game.OnePacketDirectedRepairPrefix

/-! # Unfinished foreign events have no earlier activation at an own source turn -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  Interaction EventGraphRuntime

private theorem mem_ownPlayFrom {Principal : Type} (app : ReactiveApplication Principal)
    (seen prior : List app.PlayerEntry) (entry : app.PlayerEntry) (later : List app.PlayerEntry) :
    (some (seen ++ prior, entry.beforeView), entry.action) ∈
      app.ownPlayFrom seen (prior ++ entry :: later) := by
  induction prior generalizing seen with
  | nil =>
      simp only [List.append_nil, List.nil_append, ReactiveApplication.ownPlayFrom]
      exact List.mem_append_right _ (List.mem_singleton_self _)
  | cons head prior ih =>
      simp only [List.cons_append, ReactiveApplication.ownPlayFrom]
      exact List.mem_append_left _ (by simpa [List.append_assoc] using ih (seen ++ [head]))


private theorem prefixes_comparable {Principal : Type} {protocol : ExecutionProtocol Principal}
    {first second final : protocol.State} {left : protocol.Trace first}
    {right : protocol.Trace second} {trace : protocol.Trace final}
    (leftPrefix : TracePrefix left trace) (rightPrefix : TracePrefix right trace) :
    TracePrefix left right ∨ TracePrefix right left := by
  induction trace with
  | start =>
      cases leftPrefix
      cases rightPrefix
      exact Or.inl .refl
  | extend earlier joint legal realized ih =>
      cases leftPrefix with
      | refl => exact Or.inr rightPrefix
      | extend leftEarlier _ _ _ =>
          cases rightPrefix with
          | refl => exact Or.inl (.extend leftEarlier joint legal realized)
          | extend rightEarlier _ _ _ => exact ih leftEarlier rightEarlier

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

/-- Every actual ready prefix of an unfinished foreign event lies after a
focal own source turn on the same trace. Sequential readiness prevents an
unaccounted earlier readiness episode. -/
theorem foreign_ready_prefix_after_ownTurn
    {start before : (application setup runtime leaks).Control}
    (startTrace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some
      start))
    (beforeTrace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some
      before))
    {state : (application setup runtime leaks).ProtocolState}
    {trace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace state}
    (startPrefix : TracePrefix startTrace trace)
    (beforePrefix : TracePrefix beforeTrace trace)
    (focal owner : Player) (different : owner ≠ focal)
    (current event : (graph setup).EventId)
    (turn : start.execution.application.publicView.ownTurn? focal = some current)
    (owned : (graph setup).actor? event = some owner)
    (unfinished : event ∉ start.execution.application.config.cut.completed)
    (ready : before.execution.application.config.cut.Ready event) :
    TracePrefix startTrace beforeTrace := by
  rcases prefixes_comparable startPrefix beforePrefix with forward | backward
  · exact forward
  · obtain ⟨after, same, preserved⟩ :=
      readyOrCompleted_of_tracePrefix (runtime := runtime) beforeTrace backward (Or.inl ready)
    cases Option.some.inj same
    rcases preserved with readyNow | completed
    · have focalFacts := PublicView.ownTurn?_spec _ focal current turn
      have focalReady := (start.execution.application.publicView_eventReady current).mp focalFacts.1
      have sameEvent := ready_unique (setup := setup) _ focalReady readyNow
      rw [← sameEvent] at owned
      exact (different (Option.some.inj (owned.symm.trans focalFacts.2))).elim
    · exact (unfinished completed).elim

omit [Fintype Player] in
private theorem first_activated_recall_split (owner : Player) (event : (graph setup).EventId)
    (past : List (application setup runtime leaks).PlayerEntry)
    (occurs : ∃ entry ∈ past, ActivatedAt setup runtime leaks owner event entry) :
    ∃ earlier entry later, past = earlier ++ entry :: later ∧
      ActivatedAt setup runtime leaks owner event entry ∧
      ∀ previous ∈ earlier, ¬ ActivatedAt setup runtime leaks owner event previous := by
  classical
  let matching := fun entry : (application setup runtime leaks).PlayerEntry =>
    decide (ActivatedAt setup runtime leaks owner event entry)
  have found : ∃ entry, past.find? matching = some entry := by
    cases selected : past.find? matching with
    | none =>
        obtain ⟨entry, recalled, activated⟩ := occurs
        have quiet := List.find?_eq_none.mp selected entry recalled
        simp [matching, activated] at quiet
    | some entry => exact ⟨entry, rfl⟩
  obtain ⟨entry, selected⟩ := found
  obtain ⟨activated, earlier, later, split, quiet⟩ := List.find?_eq_some_iff_append.mp selected
  refine ⟨earlier, entry, later, split, ?_, ?_⟩
  · simpa [matching] using activated
  · simpa [matching] using quiet

/-- A recorded ready owner activation has an actual first-response prefix, with
its supported transition and full private recall. Intended submission provenance
makes that earliest ready activation genuinely pending. -/
theorem firstActivation_response_prefix_of_recall
    {control : (application setup runtime leaks).Control}
    (trace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control))
    (owner : Player) (event : (graph setup).EventId)
    (occurs : ∃ entry ∈ control.execution.recall owner, ActivatedAt setup runtime leaks owner
      event entry)
    (submissions : OwnSubmissionsAtTurn setup leaks control.execution owner) :
    ∃ (before : (application setup runtime leaks).Control)
      (prior : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some before))
      (response : (application setup runtime leaks).Action)
      (joint : Player → Option (application setup runtime leaks).Action)
      (legal : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Legal (some
        before) joint)
      (realized : some ⟨before.remaining, none,
        before.execution.respond (application setup runtime leaks) owner response⟩ ∈
        ((onePacketProtocol setup runtime leaks bounds horizon scheduler).step (some before)
          ⟨joint, legal⟩).support),
      TracePrefix (prior.extend joint legal realized) trace ∧
      before.actor = some owner ∧ joint owner = some response ∧
      pendingEvent setup runtime leaks owner (some (before.execution.recall owner,
        before.execution.observe (application setup runtime leaks) owner)) = some event ∧
      ∀ previous ∈ before.execution.recall owner,
        ¬ ActivatedAt setup runtime leaks owner event previous := by
  obtain ⟨earlier, entry, later, split, activated, quiet⟩ :=
    first_activated_recall_split (runtime := runtime) owner event (control.execution.recall owner)
      occurs
  have unrecorded : runtime.eventRecorded leaks earlier event = false := by
    cases recorded : runtime.eventRecorded leaks earlier event with
    | false => rfl
    | true =>
        obtain ⟨previous, recalled, submitted⟩ :=
          (runtime.eventRecorded_iff leaks _ event).mp recorded
        have finalMember : previous ∈ control.execution.recall owner := by
          rw [split]
          exact List.mem_append_left _ recalled
        exact (quiet previous recalled (submissions previous finalMember event submitted)).elim
  have remembered : (some (earlier, entry.beforeView), entry.action) ∈
      (onePacketInformation setup runtime leaks bounds horizon scheduler).ownPlay owner trace := by
    rw [onePacket_ownPlay_recall]
    change (some (earlier, entry.beforeView), entry.action) ∈
      (application setup runtime leaks).recallOwnPlay (control.execution.recall owner)
    rw [split]
    simpa only [ReactiveApplication.recallOwnPlay, List.nil_append] using
      mem_ownPlayFrom (application setup runtime leaks) [] earlier entry later
  obtain ⟨before, after, prior, joint, legal, realized, isPrefix, observed, chosen⟩ :=
    InformationModel.exists_tracePrefix_of_mem_ownPlay trace remembered
  have localLegal := (onePacketProtocol setup runtime leaks bounds horizon
    scheduler).legalOption_of_legal
    legal owner
  rw [chosen] at localLegal
  have acting := localLegal.1
  cases before with
  | none =>
      change (application setup runtime leaks).actor none = some owner at acting
      simp only [ReactiveApplication.actor, Option.bind_none] at acting
      cases acting
  | some before =>
      have active : before.actor = some owner := acting
      rw [onePacket_infoOf] at observed
      simp only [ReactiveApplication.observe, active, ↓reduceIte] at observed
      have sameRecall : before.execution.recall owner = earlier :=
        congrArg Prod.fst (Option.some.inj observed)
      have sameView : before.execution.observe (application setup runtime leaks) owner =
        entry.beforeView :=
        congrArg Prod.snd (Option.some.inj observed)
      have pending := pendingEvent_of_spec (runtime := runtime) (setup := setup) (leaks := leaks)
        activated unrecorded
      have pendingBefore : pendingEvent setup runtime leaks owner
          (some (before.execution.recall owner,
            before.execution.observe (application setup runtime leaks) owner)) = some event := by
        simpa only [sameRecall, sameView] using pending
      have quietBefore : ∀ previous ∈ before.execution.recall owner,
          ¬ ActivatedAt setup runtime leaks owner event previous := by
        simpa only [sameRecall] using quiet
      have afterEq : after = some ⟨before.remaining, none,
          before.execution.respond (application setup runtime leaks) owner entry.action⟩ := by
        change after ∈ ((application setup runtime leaks).transition (initialLaw setup) horizon
          scheduler
          (some before) joint).support at realized
        rw [transition_respond (runtime := runtime) before acting joint, chosen, Option.getD_some,
          PMF.mem_support_pure_iff] at realized
        exact realized
      subst after
      exact ⟨before, prior, entry.action, joint, legal, realized, isPrefix, acting, chosen,
        pendingBefore, quietBefore⟩

end Vegas
