/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.SourceSessionPolicy
import Vegas.Examples.LateResolutionService
import Vegas.Source.DisclosureAliases

/-! # Frozen source decisions through the actual pending-message runner

The compiled fixture has two deterministic samples and one Boolean resolution.
These tests use its source graph, not its scheduler. Both successful and failed
initial bindings are supplied to the session initializer. Admission and opening
are exercised with actual response envelopes and inclusion receipts.
-/

namespace VegasTests.SourceSession

open Vegas Interaction GameTheory.Math.Probability

noncomputable section

private abbrev Player := Vegas.LateResolutionService.Player
private abbrev owner : Player := Vegas.LateResolutionService.owner
private abbrev player : Vegas.SourceSession.Principal Player := .player owner
private abbrev watcher : Vegas.SourceSession.Principal Player := .watcher
private abbrev setup := Vegas.LateResolutionService.setup
private abbrev graph := Vegas.LateResolutionService.nativeGraph
private abbrev sample0 := Vegas.LateResolutionService.sample0
private abbrev sample1 := Vegas.LateResolutionService.sample1
private abbrev resolution := Vegas.LateResolutionService.resolution

private def runtime : Vegas.SourceSession.Runtime graph where
  deadline _ := 3

private def leaks : MessageNetwork.ObservationRule (Vegas.SourceSession.Principal Player)
    (Vegas.SourceSession.Packet graph) :=
  fun _ _ => PMF.pure ∅

private abbrev app := Vegas.SourceSession.application runtime leaks

private def initialSource (result : PublicationResult Bool) :
    Vegas.State simpleExpr Vegas.LateResolutionService.initialCtx :=
  Env.cons result (Env.empty _)

private def source0 (result : PublicationResult Bool) : EventGraphRuntime.State graph :=
  EventGraphRuntime.State.initial (setup.eventInputs (initialSource result))

private theorem sample0Ready (result : PublicationResult Bool) :
    (source0 result).config.cut.Ready sample0 := by
  change (EventOrder.Cut.empty graph.order).Ready sample0
  decide

private def source1 (result : PublicationResult Bool) : EventGraphRuntime.State graph :=
  (source0 result).complete sample0 (sample0Ready result) PUnit.unit true

private theorem sample1Ready (result : PublicationResult Bool) :
    (source1 result).config.cut.Ready sample1 := by
  change sample1 ∉ ({sample0} : Finset graph.EventId) ∧
    ∀ predecessor ∈ graph.order.predecessors sample1,
      predecessor ∈ ({sample0} : Finset graph.EventId)
  decide

private def source2 (result : PublicationResult Bool) : EventGraphRuntime.State graph :=
  (source1 result).complete sample1 (sample1Ready result) PUnit.unit true

private def readyState (initial : PublicationResult Bool) : Vegas.SourceSession.State graph :=
  { Vegas.SourceSession.State.initial (graph := graph)
      (setup.eventInputs (initialSource initial)) with
    source := source2 initial }

private def start (initial : PublicationResult Bool) : app.Execution :=
  ReactiveApplication.Execution.initial app (readyState initial)

private abbrev admissionPhase : Vegas.SourceSession.PhaseKey graph :=
  .source resolution .admission

private abbrev openingPhase : Vegas.SourceSession.PhaseKey graph :=
  .source resolution .opening

private abbrev decisionHandle : Vegas.SourceSession.DecisionHandle graph := (owner, resolution)

private abbrev originalHandle : EventGraphRuntime.Handle graph :=
  (owner, .initial ⟨0, by decide⟩)

private def decisionRaw (result : PublicationResult Bool) : EventGraphRuntime.Raw simpleExpr :=
  Vegas.SourceSession.encodeDecision .bool result

private def admission (result : PublicationResult Bool) (intent : Option Bool := none) :
    app.Action :=
  ⟨some (.gameplay {
    call := .admission resolution decisionHandle
    material := some (decisionRaw result)
    certificates := []
    resolutionIntent := intent })⟩

private def opening (result : PublicationResult Bool) : app.Action :=
  ⟨some (.gameplay {
    call := .opening resolution decisionHandle (decisionRaw result)
    material := none
    certificates := [.owned (.decision ⟨decisionHandle, decisionRaw result⟩)] ++
      match result with
      | .failure => []
      | .success value => [.owned (.source ⟨originalHandle, ⟨.bool, value⟩⟩)] })⟩

private def admitted (initial result : PublicationResult Bool) : app.Execution :=
  ((start initial).respond app player (admission result)).includePending app (player, 0)

private def opened (initial result : PublicationResult Bool) : app.Execution :=
  ((admitted initial result).respond app player (opening result)).includePending app (player, 1)

private def binding : EventGraph.FieldRef graph.layout (.binding owner .bool) :=
  ⟨.inl ⟨0, by decide⟩, rfl⟩

private def compiledAdmission (initial : PublicationResult Bool) (intention : Bool) : app.Action :=
  ⟨some (.gameplay (Vegas.SourceSession.resolutionAdmission owner resolution .bool binding []
    intention (graph.playerObserve owner (readyState initial).source.config)))⟩

private def compiledAdmitted (initial : PublicationResult Bool) (intention : Bool) :
    app.Execution :=
  ((start initial).respond app player (compiledAdmission initial intention)).includePending
    app (player, 0)

private def compiledOpening (initial : PublicationResult Bool) (intention : Bool) : app.Action :=
  let state := (compiledAdmitted initial intention).application
  ⟨(Vegas.SourceSession.frozenResolutionOpening owner resolution .bool binding state.source.accepted
    (fun event => state.decisions.lookup (owner, event))).map
      Vegas.SourceSession.Submission.gameplay⟩

private def compiledOpened (initial : PublicationResult Bool) (intention : Bool) : app.Execution :=
  ((compiledAdmitted initial intention).respond app player
    (compiledOpening initial intention)).includePending app (player, 1)

/-- The production constructors normalize a failed original TRUE to helper
FALSE and accept its opening through the actual pending-message runner. -/
example : compiledAdmission .failure true = admission .failure (some true) := by
  rfl

example : (compiledOpened .failure true).receipts = [((player, 0), true), ((player, 1), true)] := by
  rfl

example : (compiledOpened .failure true).application.source.config.outputs resolution =
    some PublicationResult.failure := by
  rfl

/-- The admitted private TRUE survives its public FALSE opening and restores
the original source action from actual private recall. -/
example :
    Vegas.SourceSession.recalledResolutionIntent runtime leaks
      ((compiledOpened .failure true).recall player) resolution (player, 0) = some true := by
  rfl

example :
    (Vegas.SourceSession.restoreResolutionCompletion runtime leaks owner
      ((compiledOpened .failure true).recall player)
      (compiledOpened .failure true).application.receipts ⟨resolution, false⟩) =
        ⟨resolution, true⟩ := by
  rfl

example : (compiledOpened (.success true) true).application.source.config.outputs resolution =
    some (PublicationResult.success true) := by
  rfl

/-- A bare admission freezes the helper value without completing the source resolution. -/
example :
    (admitted (.success true) .failure).application.source.config =
      (readyState (.success true)).source.config := by
  rfl

example :
    (admitted (.success true) .failure).application.admissions resolution =
      some ⟨decisionHandle, 0⟩ := by
  rfl

example : (admitted (.success true) .failure).receipts = [((player, 0), true)] := by
  rfl

/-- FALSE is an openable helper value; it uses one helper certificate, not a give-up call. -/
example :
    (opened (.success true) .failure).application.source.config.outputs resolution =
      some PublicationResult.failure := by
  rfl

example : (opened (.success true) .failure).application.status = .completed := by
  decide

example : (opened (.success true) .failure).application.outcome?.isSome = true := by
  decide

example :
    (decodeState? (terminalRefs setup.program)
      (opened (.success true) .failure).application.source.config.store).map
        (fun source => source.get HasVar.here) = some PublicationResult.failure := by
  rfl

/-- TRUE needs both the immutable helper opening and the authentic original opening. -/
example :
    (opened (.success true) (.success true)).application.source.config.outputs resolution =
      some (PublicationResult.success true) := by
  rfl

example :
    (opened (.success true) (.success true)).receipts =
      [((player, 0), true), ((player, 1), true)] := by
  rfl

example : (opened (.success true) (.success true)).application.outcome?.isSome = true := by
  decide

example :
    (decodeState? (terminalRefs setup.program)
      (opened (.success true) (.success true)).application.source.config.store).map
        (fun source => source.get HasVar.here) = some (PublicationResult.success true) := by
  rfl

/-- OPEN sent before admission has no OPEN authorization, even though the source event is ready. -/
private def premature : app.Execution :=
  ((start (.success true)).respond app player (opening .failure)).includePending app (player, 0)

example : premature.receipts = [((player, 0), false)] := by
  rfl

example : premature.application.source.config = (readyState (.success true)).source.config := by
  rfl

/-- A valid original certificate does not replace the missing helper certificate. -/
private def missingHelper : app.Action :=
  ⟨some (.gameplay {
    call := .opening resolution decisionHandle (decisionRaw (.success true))
    material := none
    certificates := [.owned (.source ⟨originalHandle, ⟨.bool, true⟩⟩)] })⟩

example :
    (((admitted (.success true) (.success true)).respond app player missingHelper).includePending
      app (player, 1)).receipts = [((player, 0), true), ((player, 1), false)] := by
  rfl

/-- A valid helper certificate does not replace the missing original certificate. -/
private def missingOriginal : app.Action :=
  ⟨some (.gameplay {
    call := .opening resolution decisionHandle (decisionRaw (.success true))
    material := none
    certificates := [.owned (.decision ⟨decisionHandle, decisionRaw (.success true)⟩)] })⟩

example :
    (((admitted (.success true) (.success true)).respond app player missingOriginal).includePending
      app (player, 1)).receipts = [((player, 0), true), ((player, 1), false)] := by
  rfl

/-- Authentic certificates must also match the frozen helper value and requested opening. -/
private def differentDecision : app.Action :=
  ⟨some (.gameplay {
    call := .opening resolution decisionHandle (decisionRaw (.success true))
    material := none
    certificates := [.owned (.decision ⟨decisionHandle, decisionRaw .failure⟩),
      .owned (.source ⟨originalHandle, ⟨.bool, true⟩⟩)] })⟩

example :
    (((admitted (.success true) .failure).respond app player differentDecision).includePending
      app (player, 1)).receipts = [((player, 0), true), ((player, 1), false)] := by
  rfl

private def lateStart : app.Execution :=
  { start (.success true) with application :=
    { readyState (.success true) with source := { source2 (.success true) with clock := 2 } } }

private def lateAdmitted : app.Execution :=
  (lateStart.respond app player (admission .failure)).includePending app (player, 0)

/-- Admission at the last admissible clock starts a new full opening budget. -/
example : lateAdmitted.application.enteredAt? openingPhase = some 2 := by
  rfl

example :
    ({ lateAdmitted.application with source :=
      { lateAdmitted.application.source with clock := 4 } }).timely runtime openingPhase =
      true := by
  decide

example :
    ({ lateAdmitted.application with source :=
      { lateAdmitted.application.source with clock := 4 } }).timely runtime admissionPhase =
      false := by
  decide

private def lateOpening : app.Execution :=
  { lateAdmitted with application := { lateAdmitted.application with source :=
    { lateAdmitted.application.source with clock := 4 } } }

example :
    ((lateOpening.respond app player (opening .failure)).includePending app (player, 1)).receipts =
      [((player, 0), true), ((player, 1), true)] := by
  rfl

private def overdue : Vegas.SourceSession.State graph :=
  { (admitted (.success true) .failure).application with source :=
    { (admitted (.success true) .failure).application.source with clock := 3 } }

/-- Timeout cancels instead of inventing a completed source failure. -/
example :
    Vegas.SourceSession.environment runtime overdue (.expire openingPhase) =
      PMF.pure (overdue.cancel openingPhase) := by
  rfl

example : (overdue.cancel openingPhase).outcome? = none := by
  simp

example :
    (overdue.cancel openingPhase).source.config.outputs resolution = none := by
  rfl

/-- Cancellation blocks every chance command, independently of the source cut. -/
example (state : Vegas.SourceSession.State graph) (phase : Vegas.SourceSession.PhaseKey graph)
    (event : graph.EventId) :
    (Vegas.SourceSession.environment runtime (state.cancel phase) (.executeSample event)).map
      (fun next => (next.status, next.source.config)) =
        PMF.pure ((state.cancel phase).status, (state.cancel phase).source.config) := by
  exact Vegas.SourceSession.environment_closed runtime (state.cancel phase)
    (by simp [Vegas.SourceSession.State.cancel]) (.executeSample event)

private def cancelledExecution : app.Execution :=
  { admitted (.success true) .failure with application := overdue.cancel openingPhase }

example :
    ((cancelledExecution.respond app player (opening .failure)).includePending app
      (player, 1)).receipts = [((player, 0), true), ((player, 1), false)] := by
  rfl

private def reportAction : app.Action :=
  ⟨some (.report [(player, 0), (player, 0), (player, 999)])⟩

private def reported : app.Execution :=
  (cancelledExecution.respond app watcher reportAction).includePending app (watcher, 0)

/-- Reporting selects authentic known envelopes, removes duplicates and ignores unknown IDs. -/
example :
    ((cancelledExecution.respond app watcher reportAction).network.inputs[1]?).map Message.payload =
      some (.report [⟨(player, 0), .gameplay
        ⟨.admission resolution decisionHandle, [], some admissionPhase⟩⟩]
        (some .reporting)) := by
  rfl

example : reported.receipts = [((player, 0), true), ((watcher, 0), true)] := by
  rfl

example : reported.application.report = some [(player, 0)] := by
  rfl

example : reported.application.source.config = cancelledExecution.application.source.config := by
  rfl

example : reported.application.status = .cancelled openingPhase := by
  rfl

example : reported.application.outcome? = none := by
  rfl

private def playerReport : app.Execution :=
  ((admitted (.success true) .failure).respond app player reportAction).includePending
    app (player, 1)

private def cancelledPlayerReport : app.Execution :=
  { playerReport with application := overdue.cancel openingPhase }

private def reportPlayerReport : app.Action :=
  ⟨some (.report [(player, 1)])⟩

private def reportedPlayerReport : app.Execution :=
  (cancelledPlayerReport.respond app watcher reportPlayerReport).includePending app (watcher, 0)

/-- A rejected source-player report remains a signed report envelope in watcher evidence. -/
example :
    playerReport.receipts = [((player, 0), true), ((player, 1), false)] ∧
    playerReport.application = (admitted (.success true) .failure).application ∧
    (reportedPlayerReport.network.inputs[2]?).map Message.payload =
      some (.report [⟨(player, 1), .report
        [⟨(player, 0), .gameplay
          ⟨.admission resolution decisionHandle, [], some admissionPhase⟩⟩] none⟩]
        (some .reporting)) ∧
    reportedPlayerReport.receipts =
      [((player, 0), true), ((player, 1), false), ((watcher, 0), true)] ∧
    reportedPlayerReport.application.report = some [(player, 1)] ∧
    reportedPlayerReport.application.source.config = playerReport.application.source.config ∧
    reportedPlayerReport.application.status = .cancelled openingPhase ∧
    reportedPlayerReport.application.outcome? = none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private def logicalBefore (initial : PublicationResult Bool) :
    SourceProgram.Config Player simpleExpr
      [(2, .publicData .bool), (1, .publicData .bool), (0, .commitment owner .bool)] :=
  SourceProgram.sampleSuccessor 2 (payload := BaseTy.bool)
    (SourceProgram.sampleSuccessor 1 (payload := BaseTy.bool)
      (⟨initialSource initial, [], Revelations.initial _, fun _ => []⟩ :
        SourceProgram.Config Player simpleExpr Vegas.LateResolutionService.initialCtx) true) true

/-- The source semantics itself normalizes TRUE to FALSE for the failed initial binding. -/
example :
    SourceProgram.effectiveDisclosure 3 (.there (.there .here)) (logicalBefore .failure) true =
      false := by
  rfl

/-- Original TRUE emits the same effective FALSE packet, without original evidence. -/
example :
    ((start .failure).respond app player (admission .failure (some true))).network =
      ((start .failure).respond app player (admission .failure (some false))).network := by
  rfl

example :
    (((start .failure).respond app player
      (admission .failure (some true))).network.inputs.head?).map Message.payload =
      some (.gameplay ⟨.admission resolution decisionHandle, [],
        some admissionPhase⟩) := by
  rfl

private def recalledIntents (execution : app.Execution) : List (Option Bool) :=
  (execution.recall player).map fun entry => entry.action.transmission.bind fun
    | .gameplay submission => submission.resolutionIntent
    | .report _ => none

example :
    recalledIntents ((start .failure).respond app player (admission .failure (some true))) =
      [some true] := by
  rfl

example :
    recalledIntents ((start .failure).respond app player (admission .failure (some false))) =
      [some false] := by
  rfl

example :
    (opened .failure .failure).application.source.config.outputs resolution =
      some PublicationResult.failure := by
  rfl

end

end VegasTests.SourceSession
