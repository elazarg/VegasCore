/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphAssembly
import Vegas.Compile.EventGraphHistory
import Vegas.Compile.EventGraphIndependence
import Vegas.Compile.EventGraphObservation
import Vegas.Compile.EventGraphScheduling
import Vegas.EventGraph.BarrierInformation
import Vegas.Game.EventScheduling
import Vegas.Game.EventCompilation
import Vegas.Pending.EventApplication
import VegasTests.SourceSemantics

/-! # Source-to-event compilation regressions

Compiler-generated dependencies permit distinct players' bindings to complete
in either order while retaining source public-observation barriers. A mixed
source program checks heterogeneous results, initial secrets and public chance.
-/

namespace VegasTests.EventCompilation

open Vegas
open SourceProgram.EventLowering
open GameTheory.Math.Probability

noncomputable section

private def unrestricted {Γ : SourceCtx Bool simpleExpr} (owner : Bool) (name : VarId) :
    SourceGuard simpleExpr Γ owner name .bool where
  schema := []
  schemaNames := by simp
  subjectFresh := by simp
  code := .constBool true
  reads := fun source => nomatch source

private def pairSource : SourceProgram Bool simpleExpr [] ∅ :=
  .commit 0 false (by decide) (unrestricted false 0) <|
  .commit 1 true (by decide) (unrestricted true 1) <|
  .reveal 2 false 0 (by decide) (.there .here) (by decide) <|
  .reveal 3 true 1 (by decide) (.there .here) (by decide) <|
  .ret []

private abbrev pairOrder := Vegas.EventGraph.barrierOrder (outputLayout pairSource)

private def pairGraph := toEventGraph pairSource (by decide)

private def pairConfig : pairGraph.Config := .initial (fun input => nomatch input)

private abbrev first : pairGraph.EventId := ⟨0, by decide⟩
private abbrev second : pairGraph.EventId := ⟨1, by decide⟩

private theorem first_ready : pairConfig.cut.Ready first := by decide

private theorem second_ready : pairConfig.cut.Ready second := by decide

/-- These are the compiler's actual certified nodes, not a hand-built graph. -/
example : pairGraph.InformationDiscipline pairGraph.prefixSchema :=
  toEventGraph_informationDiscipline pairSource (by decide)

private def completedSecond : pairGraph.Config :=
  pairConfig.complete second second_ready (.success true) (.success true)

/-- A real semantic step accepts the second source commitment first. -/
private theorem step_second :
    pairConfig.step second second_ready (.success true) = FinDist.pure completedSecond := by
  change (FinDist.pure (PublicationResult.success true)).map _ = _
  rw [FinDist.map_pure]
  rfl

example : completedSecond.history.map Vegas.EventGraph.Completion.event = [second] := rfl

example : completedSecond.cut.Ready first :=
  first_ready.after_complete second_ready (by decide)

example : completedSecond ∈ (pairConfig.step second second_ready (.success true)).support := by
  rw [step_second]
  exact FinDist.mem_support_pure.mpr rfl

example : eventCount pairSource = 4 := rfl

private def firstRefs : ContextRefs pairGraph.layout
    [(0, CellTy.privateData false simpleExpr.bool)] :=
  ContextRefs.cons (outputRef pairSource first)
    (ContextRefs.initial [] (outputLayout pairSource))

private def firstPublications : PublicationRefs pairGraph.layout
    [(0, CellTy.privateData false simpleExpr.bool)] := initialPublications

private def firstState (choice : Bool) :
    State simpleExpr [(0, CellTy.privateData false simpleExpr.bool)] :=
  Env.cons (BoundValue.value choice, Interaction.Publication.pending)
    (Env.empty (CellVal simpleExpr))

/-- The second player can reconstruct its source decision view before the
foreign commitment has completed. Hidden entries require neither a value nor
a fabricated in-domain default. -/
example (choice : Bool) :
    decodeObservation? true firstRefs firstPublications
        (pairGraph.playerStore true pairConfig.store) =
      some (sourceObserve true (firstState choice)) := by
  apply congrArg some
  apply congrArg SourceObservation.mk
  funext name cell source
  cases source with
  | here => rfl
  | there source => nomatch source

/-- An unavailable own binding is genuinely unavailable, rather than silently
decoded as a payload value. -/
example : decodeObservation? false firstRefs firstPublications
    (pairGraph.playerStore false pairConfig.store) = none := rfl

private def pairProfile : SourceProgram.BehavioralProfile pairSource :=
  fun _ =>
    (fun _ _ => FinDist.pure (BoundValue.value false),
     (fun _ _ => FinDist.pure (BoundValue.value true),
      (fun _ _ => FinDist.pure true,
       (fun _ _ => FinDist.pure true, PUnit.unit))))

private def orderSensitiveFirst : pairGraph.BehavioralPolicy false :=
  fun event actor observation =>
    if same : event = first then by
      subst event
      exact FinDist.pure (.success (decide (second ∈ observation.completionOrder)))
    else compileEventProfile pairSource (by decide) pairProfile false event actor observation

/-- The arbitrary policy class really can use public completion order. -/
example : orderSensitiveFirst first rfl (pairGraph.playerObserve false pairConfig) =
    FinDist.pure (.success false) := by
  simp [orderSensitiveFirst, Vegas.EventGraph.playerObserve, pairConfig,
    Vegas.EventGraph.Config.initial]

example : orderSensitiveFirst first rfl (pairGraph.playerObserve false completedSecond) =
    FinDist.pure (.success true) := by
  simp [orderSensitiveFirst, Vegas.EventGraph.playerObserve, completedSecond,
    Vegas.EventGraph.Config.complete, pairConfig, Vegas.EventGraph.Config.initial]

/-- The actual order-sensitive deviation, not just a compiled source policy,
is covered by the asynchronous graph mixture theorem. -/
example (inputs : FinDist pairGraph.Inputs) (scheduler : pairGraph.PublicScheduler) :
    ∃ mixture : FinDist (pairGraph.BehavioralPolicy false),
      (inputs.bind fun initial => pairGraph.runPolicies scheduler
        (GameTheory.Profile.update (sig := pairGraph.gameSignature)
          (compileEventProfile pairSource (by decide) pairProfile)
          false orderSensitiveFirst) initial).map Vegas.EventGraph.Config.store =
        mixture.bind fun alternative =>
          (inputs.bind fun initial => pairGraph.runPolicies pairGraph.canonicalScheduler
            (GameTheory.Profile.update (sig := pairGraph.gameSignature)
              (compileEventProfile pairSource (by decide) pairProfile)
              false alternative) initial).map Vegas.EventGraph.Config.store := by
  obtain ⟨mixture, law⟩ :=
    (toEventGraph_barrierOrdered pairSource (by decide)).exists_deviation_mixture
      inputs scheduler (compileEventProfile pairSource (by decide) pairProfile)
      false orderSensitiveFirst
  rw [normalizeProfile_compileEventProfile] at law
  exact ⟨mixture, law⟩

private def pairSetup : SourceProgram.Setup (Player := Bool) (L := simpleExpr) where
  context := []
  namesNodup := by decide
  initialLaw := FinDist.pure ⟨Env.empty (CellVal simpleExpr), trivial⟩
  obligations := ∅
  program := pairSource
  accounts := rfl

/-- The order-sensitive asynchronous deviation has a source-policy mixture
for the program whose independent bindings admit both completion orders. -/
example (scheduler : pairSetup.eventGraph.PublicScheduler) :
    ∃ mixture : FinDist (SourceProgram.BehavioralPolicy false pairSource),
      (pairSetup.initialLaw.bind fun initial =>
        (pairSetup.eventGraph.terminalOutcomes scheduler
          (GameTheory.Profile.update (sig := pairSetup.eventGraph.gameSignature)
            (compileEventProfile pairSource pairSetup.namesNodup pairProfile)
            false orderSensitiveFirst)
          (pairSetup.eventInputs initial.1)).map
            (terminalState pairSource pairSetup.namesNodup)) =
        mixture.bind fun alternative =>
          pairSetup.run (GameTheory.Profile.update
            (sig := SourceProgram.gameSignature pairSource) pairProfile false alternative) :=
  scheduled_setup_deviation_law pairSetup scheduler pairProfile false orderSensitiveFirst

/-- The actual compiled second-player policy can act first. It does not wait
for the foreign binding merely to reconstruct its source observation. -/
example : compileEventProfile pairSource (by decide) pairProfile true second rfl
      (pairGraph.playerObserve true pairConfig) =
    FinDist.pure (PublicationResult.success true) := by
  change (FinDist.pure (BoundValue.value true)).map (BoundValue.resultEquiv _) = _
  rw [FinDist.map_pure]
  rfl

/-- Publicly completing the other hidden commitment first does not alter the
first player's prescribed decision. Arbitrary policies may still use that
completion-order signal. -/
example : compileEventProfile pairSource (by decide) pairProfile false first rfl
      (pairGraph.playerObserve false completedSecond) =
    compileEventProfile pairSource (by decide) pairProfile false first rfl
      (pairGraph.playerObserve false pairConfig) := by
  exact compileEventPolicy_complete_hidden pairSource (by decide) false
    (pairProfile false) pairConfig second first second_ready
    (.success true) (.success true) (by decide) (by decide) rfl

/-- Compilation creates two initially enabled bindings, not a global cursor. -/
example : (EventOrder.Cut.empty pairOrder).enabled =
    {⟨0, by decide⟩, ⟨1, by decide⟩} := by decide

private def secondBound : pairOrder.Cut :=
  (EventOrder.Cut.empty pairOrder).complete ⟨1, by decide⟩ (by decide)

example : ⟨1, by decide⟩ ∈ secondBound.completed ∧
    ⟨0, by decide⟩ ∉ secondBound.completed := by decide

/-- Neither public result is enabled until both earlier bindings are complete. -/
example : ¬ secondBound.Ready ⟨2, by decide⟩ ∧
    ¬ secondBound.Ready ⟨3, by decide⟩ := by decide

example : (secondBound.complete ⟨0, by decide⟩ (by decide)).Ready ⟨2, by decide⟩ := by decide

example : ¬ (secondBound.complete ⟨0, by decide⟩ (by decide)).Ready ⟨3, by decide⟩ := by decide

/-- The typed catalog retains the original optional payload separately from
the failure-aware publication result. -/
example : outputLayout SourceSemantics.mixedProgram ⟨0, by decide⟩ =
    .binding SourceSemantics.Player.alice (.option .bool) := rfl

example : outputLayout SourceSemantics.mixedProgram ⟨1, by decide⟩ =
    .publication (.option .bool) := rfl

example : outputLayout SourceSemantics.mixedProgram ⟨2, by decide⟩ = .publication .bool := rfl

example : outputLayout SourceSemantics.mixedProgram ⟨3, by decide⟩ = .publicData .bool := rfl

/-- The complete mixed source compiles with its initial private input and
deferred guard; no sample-free or homogeneous-payload restriction is needed. -/
example : SourceSemantics.mixedInitial.eventGraph.InformationDiscipline
    SourceSemantics.mixedInitial.eventGraph.prefixSchema :=
  toEventGraph_informationDiscipline SourceSemantics.mixedInitial.program
    SourceSemantics.mixedInitial.namesNodup

example : SourceSemantics.mixedInitial.eventGraph.order.eventCount = 4 := rfl

/-- Private initial values are graph inputs rather than another player move. -/
example : inputLayout SourceSemantics.mixedInitial.context ⟨0, by decide⟩ =
    .binding SourceSemantics.Player.alice .bool := rfl

example : encodeInputs SourceSemantics.mixedInitial.state ⟨0, by decide⟩ =
    PublicationResult.success true := rfl

/-- The complete mixed program has its source law under every adaptive public
scheduler, not just under the canonical schedule. -/
example (scheduler : SourceSemantics.mixedInitial.eventGraph.PublicScheduler)
    (profile : SourceProgram.BehavioralProfile SourceSemantics.mixedInitial.program) :
    (SourceSemantics.mixedInitial.eventGraph.terminalOutcomes scheduler
      (compileEventProfile SourceSemantics.mixedInitial.program
        SourceSemantics.mixedInitial.namesNodup profile)
      (encodeInputs SourceSemantics.mixedInitial.state)).map
        (terminalState SourceSemantics.mixedInitial.program
          SourceSemantics.mixedInitial.namesNodup) =
      SourceSemantics.mixedInitial.run profile :=
  scheduled_terminalState_law SourceSemantics.mixedInitial.program
    SourceSemantics.mixedInitial.namesNodup scheduler profile
    SourceSemantics.mixedInitial.state SourceSemantics.mixedInitial.privatePending

private def rejectingGraph := toEventGraph SourceSemantics.falseGuardProgram (by decide)

private abbrev rejectingBind : rejectingGraph.EventId := ⟨0, by decide⟩
private abbrev rejectingReveal : rejectingGraph.EventId := ⟨1, by decide⟩

private def rejectingInitial : rejectingGraph.Config :=
  .initial (fun input => nomatch input)

private def rejectingBound : rejectingGraph.Config :=
  rejectingInitial.complete rejectingBind (by decide)
    (PublicationResult.success true) (PublicationResult.success true)

/-- An unsatisfiable guard compiles, and its reveal computes failure. It is not
silently replaced by an unrestricted commitment or a valid in-domain value. -/
example : (rejectingGraph.nodes rejectingReveal).eval? true rejectingBound.store =
    some (FinDist.pure (PublicationResult.failure : PublicationResult Bool)) := rfl

private def rejected : rejectingGraph.Config :=
  rejectingBound.complete rejectingReveal (by decide) true PublicationResult.failure

/-- Public rejection does not erase the player's original disclosure choice
from its own recall. -/
example : decodeHistory SourceSemantics.falseGuardProgram (by decide)
      rejected.history SourceSemantics.Player.alice =
    [SourceProgram.OwnAction.commit (L := simpleExpr) SourceSemantics.Player.alice 20 .bool
      (BoundValue.value true),
     SourceProgram.OwnAction.reveal SourceSemantics.Player.alice 20 true] := by
  rfl

private def pairRuntime : EventGraphRuntime pairGraph := ⟨fun _ => 3⟩

private def pendingInitial : EventGraphRuntime.State pairGraph :=
  EventGraphRuntime.State.initial (fun input => nomatch input)

private def preparedSecond : EventGraphRuntime.State pairGraph :=
  EventGraphRuntime.privateStep pendingInitial true (.prepare 0 ⟨.bool, true⟩)

private def pendingSecond : Interaction.Message Bool (EventGraphRuntime.Payload pairGraph) :=
  ⟨(true, 0), .commitment second (true, .prepared 0)⟩

/-- Private preparation does not publish the selected binding's meaning. -/
example : preparedSecond.publicView = pendingInitial.publicView := rfl

/-- Independent initially ready events get independent activation entries. -/
example : pendingInitial.activatedAt first = some 0 ∧
    pendingInitial.activatedAt second = some 0 := by decide

/-- The second source commitment has a live native inclusion window before
the first source commitment is included. -/
example : preparedSecond.WithinDeadline pairRuntime second := by
  change 0 < 3
  decide

/-- The boundary belongs to expiry, not to packet acceptance. -/
example : ¬ ({ preparedSecond with clock := 3 }).WithinDeadline pairRuntime second := by
  change ¬ 3 < 3
  decide

example : EventGraphRuntime.handle pairRuntime { preparedSecond with clock := 3 }
    pendingSecond = none := by
  have ready : preparedSecond.config.cut.Ready second := second_ready
  have late : ¬ ({ preparedSecond with clock := 3 }).WithinDeadline pairRuntime second := by
    change ¬ 3 < 3
    decide
  simp only [EventGraphRuntime.handle, pendingSecond, dif_pos ready, dif_neg late]

/-- A completed event cannot be accepted again, independently of its clock. -/
example : EventGraphRuntime.handle pairRuntime
    { preparedSecond with config := completedSecond } pendingSecond = none := by
  have finished : ¬ completedSecond.cut.Ready second := by decide
  simp only [EventGraphRuntime.handle, pendingSecond, dif_neg finished]

example : EventGraphRuntime.handle pairRuntime pendingInitial
    ⟨(true, 0), .malformed ⟨.bool, true⟩⟩ = none := rfl

/-- A real event-addressed handler accepts the second source binding first. -/
example : (EventGraphRuntime.handle pairRuntime preparedSecond pendingSecond).isSome = true := by
  have ready : preparedSecond.config.cut.Ready second := second_ready
  have timely : preparedSecond.WithinDeadline pairRuntime second := by
    change 0 < 3
    decide
  have vacant : preparedSecond.accepted (.inr second) = none := rfl
  have unused : preparedSecond.HandleUnused (true, .prepared 0) := by
    intro field
    cases field with
    | inl input => nomatch input
    | inr event =>
        change (none : Option (EventGraphRuntime.Handle pairGraph)) ≠ some _
        simp
  simp only [EventGraphRuntime.handle, pendingSecond, dif_pos ready, dif_pos timely]
  split
  · rename_i owner payload outputEq _ _
    change Vegas.EventGraph.EventField.binding true simpleExpr.bool =
      .binding owner payload at outputEq
    cases outputEq
    simpa [Interaction.Message.sender, unused] using vacant
  · rename_i owner payload binding checks outputEq _ _
    change Vegas.EventGraph.EventField.binding true simpleExpr.bool =
      .publication payload at outputEq
    cases outputEq
  · rename_i payload law outputEq _ _
    change Vegas.EventGraph.EventField.binding true simpleExpr.bool =
      .publicData payload at outputEq
    cases outputEq

end

end VegasTests.EventCompilation
