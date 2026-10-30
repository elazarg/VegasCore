/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/
import Vegas.Game.OnePacketStoppedSourceLaw
import Vegas.Game.SourceServiceContinuation
import Vegas.EventGraph.OwnedStep
/-! # Source continuation kernels of prescribed packets

A transmitting canonical packet at a genuine first callback is a supported owned
graph action. Counted native service and the compiler suffix correspondence identify
the entire terminal source continuation after the actual completion stop. Binding
and disclosure share the same typed acceptance and ordinary graph continuation laws.
-/

noncomputable section
namespace Vegas
open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime
variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}
  {delay bound : (graph setup).EventId → Nat}
local notation "menu" => bounds.onePacketMenu runtime leaks
local notation "N" => ReactiveApplication.ResponseMenu.information menu (initialLaw setup)
  horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol menu (initialLaw setup)
  horizon scheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup runtime leaks)
    (fun native : EventGraphRuntime.State (graph setup) =>
      EventGraph.Config.defaulted (EventGraphRuntime.State.config native) = ∅)

/-- A canonical action followed by the compiled source continuation has the
full terminal source law at every counted completion stop. Authentic failed
publication retains its actual action and public default history. -/
theorem counted_canonical_source_continuation
    (opportunity : ∀ control : (application setup runtime leaks).Control,
      (E).Trace (some control) → control.execution.application.config.defaulted = ∅ →
      OpportunityAt runtime leaks control.execution delay)
    (inclusion : ∀ control : (application setup runtime leaks).Control,
      (E).Trace (some control) → control.execution.application.config.defaulted = ∅ →
      ProtectedInclusionAt runtime leaks control.execution bound)
    (timely : runtime.AsyncTimely delay bound)
    (completes : ∀ control : (application setup runtime leaks).Control,
      (E).Trace (some control) → control.execution.application.config.defaulted = ∅ →
      (application setup runtime leaks).terminal (some control) →
      control.execution.application.config.cut.Terminal)
    (source : BehavioralProfile setup.program)
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (N).BehavioralPolicy player)
    {remaining : Nat} {who : Player} {execution : (application setup runtime leaks).Execution}
    (trace : (E).Trace (some ⟨remaining, some who, execution⟩))
    (clear : execution.application.config.defaulted = ∅)
    (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (never : ∀ entry ∈ execution.recall who, ¬ ActivatedAt setup runtime leaks who event entry)
    (action : (graph setup).Action event) (material : (application setup runtime leaks).Submission)
    (submits : (runtime.canonicalServiceDecision leaks who (execution.recall who)
      (execution.observe (application setup runtime leaks) who) event action).transmission =
        some material)
    {rank : Nat} (residual : SourceResidual setup source rank execution.application.config)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (start : (E).History)
    (current : start.state = some ⟨remaining, none,
      execution.respond (application setup runtime leaks) who
        (runtime.canonicalServiceDecision leaks who (execution.recall who)
          (execution.observe (application setup runtime leaks) who) event action)⟩) :
    let plan := (graph setup).policyPlan (compileEventProfile setup.program source)
      (graph setup).canonicalScheduler
    let read := fun final : (graph setup).Config => decodeConfig? setup.program setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (Revelations.initial setup.context) [] (outputEmbedding setup.program)
      final.store final.history
    (((N).runBehavioralUntil certificate players
      (fun history => (∃ final, history.state = some final ∧
        event ∈ final.execution.application.config.cut.completed) ∨ ¬ Clear history.state)
      start).bind fun history => match history.state with
        | none => PMF.pure none
        | some final => ((graph setup).runPlan plan final.execution.application.config.remaining
            final.execution.application.config).map read) =
      (ProtocolState.step setup.program point
        (fun _ => decodeEventAction setup.program event action)).bind fun target =>
          (ProtocolState.continuationLaw setup.program source target).map some := by
  let response := runtime.canonicalServiceDecision leaks who (execution.recall who)
    (execution.observe (application setup runtime leaks) who) event action
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  have ready := (execution.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec _ who event turn).1
  have active : who ∉ execution.application.config.defaulted := by
    rw [clear]
    exact Finset.notMem_empty _
  have fits := firstActivation_inclusionFits_of_counted_opportunity setup runtime leaks bounds
    horizon scheduler delay bound opportunity timely trace rfl clear event turn never
  have rawTrace := (menu).toRawTrace (initialLaw setup) horizon scheduler trace
  have fresh := canonical_freshCall rawTrace bound who event turn fits action material submits
  have afterTrace := current ▸ start.trace
  obtain ⟨output, invariant⟩ := acceptanceInvariant_respond (runtime := runtime) bounds horizon
    scheduler trace event turn action material submits afterTrace
  have sameConfig := (runtime.reactive_respond_application leaks execution who response).1
  have supported := AcceptanceWitness.complete_mem_step invariant.2.2.2.2.1 sameConfig
    ready who owned active
  let after := execution.application.config.complete event ready action output
  obtain ⟨successor, _stepped, mass⟩ := residual.step_mass event ready action after supported
  have pointEq := Option.some.inj (residual.decode.symm.trans decoded)
  rw [pointEq] at mass
  obtain ⟨next, pureEq⟩ := execution.application.config.step_eq_pure_of_actor event ready action
    who owned
  have afterEq : after = next := (PMF.mem_support_pure_iff _ _).mp (pureEq ▸ supported)
  have one : (ProtocolState.step setup.program point
      (fun _ => decodeEventAction setup.program event action))
      (successor.lift (ProtocolState.entry successor.program successor.source)) = 1 := by
    simpa only [pureEq, afterEq, PMF.pure_apply_self] using mass
  have sourcePure : ProtocolState.step setup.program point
      (fun _ => decodeEventAction setup.program event action) =
      PMF.pure (successor.lift (ProtocolState.entry successor.program successor.source)) :=
    pmf_eq_pure_of_support_subset_singleton _ _ ((PMF.apply_eq_one_iff _ _).mp one).le
  have responseClear :
    (execution.respond (application setup runtime leaks) who response).application.config.defaulted
        = ∅ := by rw [sameConfig, clear]
  have stopped := counted_accepted_stop_continuation (runtime := runtime) inclusion completes
    (compileEventProfile setup.program source) certificate players start current responseClear
    invariant sameConfig owned (by
      simpa only [respondEntry, submits, Option.map_some, sentEnvelope] using fresh)
  dsimp only
  rw [sourcePure, PMF.pure_bind]
  calc
    _ = (((N).runBehavioralUntil certificate players
      (fun history => (∃ final, history.state = some final ∧
        event ∈ final.execution.application.config.cut.completed) ∨ ¬ Clear history.state)
      start).bind fun _ => sourceContinuation setup source (rank + 1) after) := by
        apply bind_congr_on_support _
        intro history member
        obtain ⟨final, foundReady, state, _done, _actual, law⟩ := stopped history member
        rw [state]
        dsimp only
        rw [law]
        exact successor.runPlan_readout_law
    _ = sourceContinuation setup source (rank + 1) after := PMF.bind_const _ _
    _ = _ := by
      change (setup.continuationLaw source (sourceServicePrefix? setup (rank + 1) after)).map
        some = _
      rw [successor.decode]
      rfl
end Vegas
