/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketUnpendingSites
import Vegas.Game.OnePacketComponents
import Vegas.Game.OnePacketHonestForced
import Vegas.Game.OnePacketOwnSubmissions
import Vegas.Game.OnePacketSilenceMasses
import Vegas.Game.OnePacketSureFailure

/-! # Legal response choices at debt-free native decision inputs -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}
  [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler

section MenuChoices

variable (setup runtime leaks bounds horizon scheduler)

omit [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)] in
/-- At a decision input, every choice is some response of the one-packet menu. -/
theorem choice_response {who : Player} (site : (N).InformationSite who)
    {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView} (atSite : site.1 = some (past, view))
    (choice : (N).Choice who site.1) :
    ∃ response, choice.1 = some response ∧
      response ∈ bounds.onePacketActions runtime leaks who past view := by
  obtain ⟨info, decision⟩ := site
  change info = some (past, view) at atSite
  subst atSite
  obtain ⟨action, member, actionEq⟩ := choice.2
  exact ⟨action, actionEq, member⟩

omit [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)] in
/-- A transmitting response of the one-packet menu names an event. -/
theorem submittedEvent_of_transmits {who : Player}
    {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView} {response : (application setup runtime
      leaks).Action}
    (member : response ∈ bounds.onePacketActions runtime leaks who past view)
    {material : (application setup runtime leaks).Submission}
    (sends : response.transmission = some material) :
    ∃ event, runtime.submittedEvent? leaks response = some event := by
  unfold EventGraphRuntime.submittedEvent?
  rw [sends]
  cases packet : material.call.packet with
  | commitment event _ => exact ⟨event, by simp only [packet, Payload.event?]⟩
  | opening event _ _ => exact ⟨event, by simp only [packet, Payload.event?]⟩
  | malformed raw => exact (onePacket_not_malformed (runtime := runtime) bounds member sends raw
    packet).elim

/-- A choice at a site transmits a packet for the event at the player's own
turn. -/
def CommitsAtTurn (who : Player) (site : (N).InformationSite who)
    (choice : (N).Choice who site.1) : Prop :=
  ∃ past view response event, site.1 = some (past, view) ∧ choice.1 = some response ∧
    runtime.submittedEvent? leaks response = some event ∧
    view.application.publicView.ownTurn? who = some event

omit [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)] in
/-- **Commitments away from the turn are owed failures.** For a well-formed
setup, at every history of a site, a choice transmitting a packet for an event
that is not the player's own turn leaves the player owing a failure at the
decoded point: a readiness token is issued only once all earlier events have
completed. -/
theorem owes_of_not_commitsAtTurn (wellFormed : setup.WellFormed)
    (profile : BehavioralProfile setup.program) {who : Player}
    (site : (N).InformationSite who) (choice : (N).Choice who site.1)
    (offTurn : ¬ CommitsAtTurn setup runtime leaks bounds horizon scheduler who site choice)
    {response : (application setup runtime leaks).Action} (chosen : choice.1 = some response)
    {event : (graph setup).EventId}
    (submitted : runtime.submittedEvent? leaks response = some event)
    (history : (N).InformationHistory who site.1) :
    DecodedState setup runtime leaks profile (ProtocolState.OwesFailure who setup.program)
      history.1.state := by
  let app := application setup runtime leaks
  let menu := bounds.onePacketMenu runtime leaks
  obtain ⟨fullHistory, infoEq⟩ := history
  have observed : app.observe who fullHistory.state = site.1 :=
    (menu.info (initialLaw setup) horizon scheduler who fullHistory.trace).symm.trans infoEq
  have menuTrace := fullHistory.trace
  change DecodedState setup runtime leaks profile _ fullHistory.state
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
  obtain ⟨rank, ⟨residual⟩, _⟩ := decodedState_intended_or_owes (runtime := runtime) wellFormed
    profile menu horizon
    scheduler menuTrace _ rfl
  have legal := choice.2
  obtain ⟨info, decision⟩ := site
  change info = _ at atSite
  subst atSite
  obtain ⟨action, member, actionEq⟩ := legal
  rw [chosen] at actionEq
  cases Option.some.inj actionEq
  rcases onePacket_submission_atTurn (runtime := runtime) bounds profile
      (menu.toRawTrace (initialLaw setup) horizon scheduler menuTrace) residual response member
      event submitted with turn | owes
  · exact (offTurn ⟨_, _, response, event, rfl, chosen, submitted, turn⟩).elim
  · exact ⟨rank, ⟨residual⟩, owes⟩

end MenuChoices

/-- At a decision input owing no failure, every legal transmitted packet names
the event at its author's current source turn. No continuation contract is used. -/
theorem commitsAtTurn_of_notOwing (wellFormed : setup.WellFormed)
    {who : Player} (site : (N).InformationSite who)
    (notOwing : ¬ OwingAgent setup runtime leaks bounds (initialLaw setup) horizon scheduler
      ((N).agentAt site))
    (choice : (N).Choice who site.1) {response : (application setup runtime leaks).Action}
    (chosen : choice.1 = some response) {event : (graph setup).EventId}
    (submitted : runtime.submittedEvent? leaks response = some event) :
    CommitsAtTurn setup runtime leaks bounds horizon scheduler who site choice := by
  classical
  by_contra offTurn
  obtain ⟨history, _running, _action⟩ := site.2
  have debt := owes_of_not_commitsAtTurn setup runtime leaks bounds horizon scheduler wellFormed
    (failureProfile setup.program) site choice offTurn chosen submitted history
  cases state : history.1.state with
  | none =>
      rw [state] at debt
      exact debt.elim
  | some control =>
      rw [state] at debt
      obtain ⟨rank, ⟨residual⟩, holds⟩ := debt
      let point := residual.lift (ProtocolState.entry residual.program residual.source)
      have decoded : nativeDecodedState setup runtime leaks history.1.state = some point := by
        rw [state]
        exact decodedPoint_eq residual
      exact notOwing ⟨history, point, decoded, holds point residual.decode⟩

/-- An unpending debt-free decision offers only silence. This includes a
foreign current event and a packet already recorded for the player's event. -/
theorem choice_eq_silence_of_unpending_notOwing (wellFormed : setup.WellFormed)
    {who : Player} (site : (N).InformationSite who)
    (notOwing : ¬ OwingAgent setup runtime leaks bounds (initialLaw setup) horizon scheduler
      ((N).agentAt site))
    {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView} (atSite : site.1 = some (past, view))
    (unpending : pendingEvent setup runtime leaks who site.1 = none)
    (choice : (N).Choice who site.1) :
    choice.1 = some ⟨none⟩ := by
  classical
  obtain ⟨history, _running, _action⟩ := site.2
  obtain ⟨control, state, pastEq, viewEq, cases⟩ := unpending_cases (runtime := runtime) atSite
    unpending history
  obtain ⟨response, chosen, member⟩ := choice_response setup runtime leaks bounds horizon
    scheduler site
    atSite choice
  rw [chosen]
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some material =>
      exfalso
      obtain ⟨event, submitted⟩ := submittedEvent_of_transmits setup runtime leaks bounds member
        (material := material) rfl
      obtain ⟨otherPast, otherView, otherResponse, otherEvent, otherAt, otherChosen,
        otherSubmitted, turn⟩ :=
        commitsAtTurn_of_notOwing (runtime := runtime) wellFormed site notOwing choice chosen
          submitted
      obtain ⟨_pastSame, viewSame⟩ := Prod.mk.inj (Option.some.inj (atSite.symm.trans otherAt))
      subst otherView
      have responseSame := Option.some.inj (chosen.symm.trans otherChosen)
      subst otherResponse
      have eventSame := Option.some.inj (submitted.symm.trans otherSubmitted)
      subst otherEvent
      rcases cases with noTurn | ⟨named, atTurn, recorded⟩
      · rw [noTurn] at turn
        cases turn
      · have eventSame := Option.some.inj (turn.symm.trans atTurn)
        subst named
        have trace := state ▸ history.1.trace
        subst pastEq viewEq
        exact onePacket_recorded_not_offered (runtime := runtime) trace who event recorded _
          submitted member

/-- At an unpending debt-free input every local probability law is the same
point mass; no random or pure local replacement changes the policy. -/
theorem withLaw_eq_self_of_unpending_notOwing (wellFormed : setup.WellFormed)
    {who : Player} (site : (N).InformationSite who)
    (notOwing : ¬ OwingAgent setup runtime leaks bounds (initialLaw setup) horizon scheduler
      ((N).agentAt site))
    {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView} (atSite : site.1 = some (past, view))
    (unpending : pendingEvent setup runtime leaks who site.1 = none)
    (policy : (N).BehavioralPolicy who) (law : PMF ((N).Choice who site.1)) :
    policy.withLaw site.1 law = policy := by
  classical
  obtain ⟨choice, _⟩ := law.support_nonempty
  have unique : ∀ other : (N).Choice who site.1, other = choice := fun other => Subtype.ext
    ((choice_eq_silence_of_unpending_notOwing (runtime := runtime) wellFormed site notOwing atSite
      unpending other).trans
      (choice_eq_silence_of_unpending_notOwing (runtime := runtime) wellFormed site notOwing
        atSite unpending
        choice).symm)
  have oneLaw : ∀ measure : PMF ((N).Choice who site.1), measure = PMF.pure choice := by
    intro measure
    calc
      measure = measure.map id := (PMF.map_id measure).symm
      _ = measure.map (fun _ => choice) := congrArg (fun f => measure.map f) (funext unique)
      _ = PMF.pure choice := PMF.map_const _ _
  rw [(oneLaw law).trans (oneLaw (policy site.1)).symm]
  exact BehavioralPolicy.withLaw_eq_self _ _
end Vegas
