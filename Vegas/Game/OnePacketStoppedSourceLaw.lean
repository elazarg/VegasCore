/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketStoppedAcceptance
import Vegas.Game.SourceServiceCheckpoint
import Vegas.Compile.EventGraphLaw

/-! # Source continuation law at counted packet boundaries

A supported packet-completion stop retains the full ordinary graph continuation
of its typed accepted action. The compiler's suffix law then identifies the complete
source execution, including failed publication, public defaults and actual own choices.
The suffix and checkpoint are typed compiler certificates; no successful-guard condition
is required.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
variable [Fintype Player]
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : Interaction.MessageNetwork.ObservationRule Player
    (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}
  {bound : (graph setup).EventId → Nat}

local notation "menu" => bounds.onePacketMenu runtime leaks
local notation "protocol" => Interaction.ReactiveApplication.ResponseMenu.protocol menu
  (initialLaw setup) horizon scheduler
local notation "model" => Interaction.ReactiveApplication.ResponseMenu.information menu
  (initialLaw setup) horizon scheduler
local notation "Clear" => Interaction.ReactiveApplication.stateInvariant
  (app := application setup runtime leaks)
    (fun state : EventGraphRuntime.State (graph setup) =>
      EventGraph.Config.defaulted (EventGraphRuntime.State.config state) = ∅)

/-- Completing the ordinary graph from a supported counted acceptance stop and
reading the certified source suffix gives exactly that suffix's full source run.
The checkpoint includes actual own choices and public default history. -/
theorem counted_accepted_stop_runFrom
    (inclusion : ∀ control : (application setup runtime leaks).Control,
      (protocol).Trace (some control) → control.execution.application.config.defaulted = ∅ →
      ProtectedInclusionAt runtime leaks control.execution bound)
    (completes : ∀ control : (application setup runtime leaks).Control,
      (protocol).Trace (some control) → control.execution.application.config.defaulted = ∅ →
      (application setup runtime leaks).terminal (some control) →
      control.execution.application.config.cut.Terminal)
    (wholeProfile : BehavioralProfile setup.program)
    (certificate : (protocol).WellFoundedHistories)
    (players : ∀ player, (model).BehavioralPolicy player)
    {who : Player} {entry : (application setup runtime leaks).PlayerEntry}
    {message : Interaction.Message Player (WitnessedPacket (graph setup))}
    {event : (graph setup).EventId} {sent : (graph setup).Config}
    {action : (graph setup).Action event} {output : ((graph setup).outputLayout event).Value}
    (ready : sent.cut.Ready event)
    (start : (protocol).History) {control : (application setup runtime leaks).Control}
    (current : start.state = some control)
    (clear : control.execution.application.config.defaulted = ∅)
    (invariant : AcceptanceInvariant setup runtime leaks bounds horizon scheduler who entry
      message event sent action output (some control))
    (atSent : control.execution.application.config = sent)
    (owned : (graph setup).actor? event = some who)
    (fresh : FreshCall setup leaks who event bound entry message)
    {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names) (profile : BehavioralProfile program)
    (refs : ContextRefs (graph setup).layout Γ) (source : SourceProgram.Config Player L Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
    (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
    (aligned : CompiledPolicySuffix setup.program wholeProfile program profile refs
      source.revelations source.registry embedding refsBefore offset)
    (checkpoint : SourceCheckpoint setup source refs offset
      (sent.complete event ready action output)) :
    let plan := (graph setup).policyPlan (compileEventProfile setup.program wholeProfile)
      (graph setup).canonicalScheduler
    let read := fun final : (graph setup).Config =>
      decodeConfig? setup.program program refs source.revelations source.registry embedding
        final.store final.history
    (((model).runBehavioralUntil certificate players
      (fun history => (∃ final, history.state = some final ∧
        event ∈ final.execution.application.config.cut.completed) ∨ ¬ Clear history.state)
      start).bind fun history =>
        match history.state with
        | none => PMF.pure none
        | some final => ((graph setup).runPlan plan final.execution.application.config.remaining
            final.execution.application.config).map read) =
      (SourceProgram.runFrom program profile source).map some := by
  dsimp only
  have stopped := counted_accepted_stop_continuation (runtime := runtime) inclusion completes
    (compileEventProfile setup.program wholeProfile) certificate players start current clear
    invariant atSent owned fresh
  have historyEq := checkpoint.history
  have completionId : setup.eventGraph.fromModeCompletion .sequential = id := rfl
  rw [completionId, List.map_id] at historyEq
  have sourceLaw := CompiledPolicySuffix.runFrom_remaining_law setup.program wholeProfile
    program profile refs source
    embedding refsBefore offset aligned (sent.complete event ready action output)
    checkpoint.ordered checkpoint.agrees historyEq checkpoint.defaults
  calc
    _ = (((model).runBehavioralUntil certificate players
      (fun history => (∃ final, history.state = some final ∧
        event ∈ final.execution.application.config.cut.completed) ∨ ¬ Clear history.state)
      start).bind fun _ => (SourceProgram.runFrom program profile source).map some) := by
        apply bind_congr_on_support _
        intro history supported
        obtain ⟨final, ready', state, _done, _actual, law⟩ := stopped history supported
        rw [state]
        dsimp only
        rw [law]
        exact sourceLaw
    _ = _ := PMF.bind_const _ _

end Vegas
