module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketOffTurnPackets
public import Vegas.Game.OnePacketDirectedRepairPrefix

@[expose] public section

/-! # Prefix responses occur at their own turn in a forced information history -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

private theorem recall_subset_at_tracePrefix {before : (application setup timeouts leaks).Control}
    (prior : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace (some before))
    {state : (application setup timeouts leaks).ProtocolState}
    {top : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace state}
    (isPrefix : TracePrefix prior top) (after : (application setup timeouts leaks).Control)
    (current : state = some after) (who : Player) :
    before.execution.logs who ⊆ after.execution.logs who := by
  have carry : ∀ {first last : (onePacketProtocol setup timeouts leaks bounds horizon
    scheduler).State}
      (firstTrace : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace first)
      (lastTrace : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace last),
      TracePrefix firstTrace lastTrace → ∀ control,
      first = some control → ∃ next, last = some next ∧
        ∀ actor, control.execution.logs actor ⊆ next.execution.logs actor := by
    intro first last firstTrace lastTrace
    induction lastTrace with
    | start =>
        intro found control same
        cases found
        exact ⟨control, same, fun _ => List.Subset.refl _⟩
    | @extend source target earlier joint legal realized ih =>
        intro found control same
        cases found with
        | refl => exact ⟨control, same, fun _ => List.Subset.refl _⟩
        | extend isEarlier _ _ _ =>
            obtain ⟨middle, sourceEq, subsets⟩ := ih isEarlier control same
            subst sourceEq
            obtain ⟨next, targetEq, retained⟩ := (application setup timeouts
              leaks).transition_recall_prefix
              (initialLaw setup) horizon scheduler middle target joint realized
            exact ⟨next, targetEq, fun actor entry member =>
              (retained actor).subset (subsets actor member)⟩
  obtain ⟨next, nextEq, subsets⟩ := carry prior top isPrefix before rfl
  cases Option.some.inj (nextEq.symm.trans current)
  exact subsets who

/-- A response already present in an actual prefix of a forced focal
information history names the current turn of every other responder. -/
theorem response_atTurn_of_forced_prefix {focal : Player}
    {info : (onePacketInformation setup timeouts leaks bounds horizon scheduler).InfoState focal}
    (forced : forcedAgent (timeouts := timeouts) (bounds.onePacketMenu timeouts leaks) (initialLaw
      setup) horizon
      scheduler focal info)
    {past : List (application setup timeouts leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView} (decision : info = some (past, view))
    (history : (onePacketInformation setup timeouts leaks bounds horizon
      scheduler).InformationHistory focal
      info)
    {final : (application setup timeouts leaks).Control} (current : history.1.state = some final)
    (remaining : Nat) (owner : Player) (other : owner ≠ focal)
    (original : (application setup timeouts leaks).Execution) (response : (application setup
      timeouts leaks).Action)
    (afterTrace : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace
      (some ⟨remaining, none, original.respond (application setup timeouts leaks) owner response⟩))
    (isPrefix : TracePrefix afterTrace history.1.trace)
    (event : (graph setup).EventId)
    (submitted : (submittedEvent? timeouts) leaks response = some event) :
    original.application.publicView.ownTurn? owner = some event := by
  let app := application setup timeouts leaks
  let entry : app.PlayerEntry := ⟨original.observe app owner, response,
    response.transmission.map fun material =>
      ⟨(owner, original.network.nextSerial owner),
        app.packet (app.submit original.application owner material) owner
          (original.network.known owner) material⟩⟩
  have recalled : entry ∈ (original.respond app owner response).logs owner := by
    rw [(respond_recall timeouts) leaks]
    simp only [↓reduceIte, List.mem_append, List.mem_singleton]
    exact Or.inr rfl
  have retained := recall_subset_at_tracePrefix (timeouts := timeouts) afterTrace isPrefix final
    current owner recalled
  exact submittedAtTurn_of_forcedSite (timeouts := timeouts) forced decision history current other
    entry retained event
    submitted

end Vegas
