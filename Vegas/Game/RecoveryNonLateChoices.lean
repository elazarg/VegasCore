/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketUnpendingSites

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

/-- At a decision input owing no failure, every legal transmitted packet names
the event at its author's current source turn. No continuation contract is used. -/
theorem commitsAtTurn_of_notOwing (wellFormed : setup.WellFormed)
    {who : Player} (site : (N).InformationSite who)
    (notOwing : ¬ OwingAgent setup runtime leaks bounds horizon scheduler ((N).agentAt site))
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
    (notOwing : ¬ OwingAgent setup runtime leaks bounds horizon scheduler ((N).agentAt site))
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
    (notOwing : ¬ OwingAgent setup runtime leaks bounds horizon scheduler ((N).agentAt site))
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
