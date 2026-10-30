/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.EventGraphAssembly
import Vegas.Compile.EventGraphDeviation
import Vegas.Compile.EventGraphHistory
import Vegas.Compile.EventGraphObservation
import Vegas.Game.EventCompilation
import Vegas.Pending.EventApplication
import Vegas.Pending.ExclusionPolicyLaw
import VegasTests.SourceSemantics

/-! # Source-ranked compiler regressions

Generated dependencies retain source order, public default timing and actual
choices. Arbitrary schedulers and deviations use exact full-configuration laws.
Heterogeneous values, correlated initial inputs and public chance stay supported.
-/

namespace VegasTests.EventCompilation

open Vegas GameTheory.Math.Probability

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

private def pairGraph := toEventGraph pairSource
private def pairConfig : pairGraph.Config := .initial (fun input => nomatch input)
private abbrev first : pairGraph.EventId := ⟨0, by decide⟩
private abbrev second : pairGraph.EventId := ⟨1, by decide⟩
private theorem first_ready : pairConfig.cut.Ready first := by decide

example : pairGraph.InformationDiscipline pairGraph.prefixSchema :=
  toEventGraph_informationDiscipline pairSource

/-- Full source ranking makes only the first binding initially ready. -/
example : pairConfig.cut.enabled = {first} := by decide
example : ¬ pairConfig.cut.Ready second := by decide

private def completedFirst : pairGraph.Config :=
  pairConfig.complete first first_ready (some (.success false)) (.success false)

private theorem step_first :
    pairConfig.step first first_ready (some (.success false)) = PMF.pure completedFirst := by
  rw [pairConfig.step_eq_map_of_eval first first_ready (some (.success false))
    (PMF.pure (PublicationResult.success false)) (by rfl)]
  exact PMF.pure_map _ _

example : completedFirst.history.map Vegas.EventGraph.Completion.event = [first] := rfl
example : completedFirst.cut.Ready second := by decide
example : completedFirst.defaults = ⟨[none]⟩ := rfl

example : completedFirst ∈
    (pairConfig.step first first_ready (some (.success false))).support := by
  rw [step_first]
  exact (PMF.mem_support_pure_iff _ _).mpr rfl

private def firstRefs : ContextRefs pairGraph.layout
    [(0, CellTy.commitment false simpleExpr.bool)] :=
  ContextRefs.cons (outputRef pairSource first)
    (ContextRefs.initial [] (outputLayout pairSource))

private def firstState (choice : Bool) :
    State simpleExpr [(0, CellTy.commitment false simpleExpr.bool)] :=
  Env.cons (PublicationResult.success choice) (Env.empty (CellVal simpleExpr))

/-- Hidden cells require neither a fabricated value nor an in-domain default. -/
example (choice : Bool) :
    decodeObservation? true firstRefs (pairGraph.playerStore true pairConfig.store) =
      some (sourceObserve true (firstState choice)) := by
  apply congrArg some
  apply congrArg SourceObservation.mk
  funext name cell source
  cases source with
  | here => rfl
  | there source => nomatch source

example : decodeObservation? (Γ := [(0, CellTy.commitment false simpleExpr.bool)])
    false firstRefs (pairGraph.playerStore false pairConfig.store) = none := rfl

private def pairProfile : SourceProgram.BehavioralProfile pairSource :=
  fun _ =>
    (fun _ _ _ => PMF.pure (some (.success false)),
     (fun _ _ _ => PMF.pure (some (.success true)),
      (fun _ _ _ => PMF.pure true,
       (fun _ _ _ => PMF.pure true, PUnit.unit))))

/-- Every graph profile, including arbitrary deviations, has one scheduler law. -/
example (scheduler : pairGraph.PublicScheduler) (profile : pairGraph.BehavioralProfile) :
    pairGraph.runPolicies scheduler profile pairConfig.inputs =
      pairGraph.runPolicies pairGraph.canonicalScheduler profile pairConfig.inputs :=
  toEventGraph_runPolicies_eq pairSource profile scheduler pairGraph.canonicalScheduler _

private def pairSetup : SourceProgram.Setup (Player := Bool) (L := simpleExpr) where
  context := []
  namesNodup := by decide
  initialLaw := PMF.pure (Env.empty (CellVal simpleExpr))
  obligations := ∅
  program := pairSource
  accounts := rfl
  exitTransfers := fun _ => 0

/-- One replacement source policy works before private setup is sampled.
The exact configuration law requires neither a mixture nor finite payloads. -/
example (scheduler : pairSetup.eventGraph.PublicScheduler)
    (replacement : pairSetup.eventGraph.BehavioralPolicy false) :
    (pairSetup.initialLaw.bind fun initial =>
      (pairSetup.eventGraph.terminalOutcomes scheduler
        (GameTheory.Profile.update (sig := pairSetup.eventGraph.gameSignature)
          (compileEventProfile pairSource pairProfile) false replacement)
        (pairSetup.eventInputs initial)).map (terminalConfig pairSource)) =
      pairSetup.run (GameTheory.Profile.update
        (sig := SourceProgram.gameSignature pairSource) pairProfile false
        (backtranslateEventPolicy pairSource false replacement)) :=
  scheduled_setup_deviation_law pairSetup scheduler pairProfile false replacement

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
example : SourceSemantics.mixedSetup.eventGraph.InformationDiscipline
    SourceSemantics.mixedSetup.eventGraph.prefixSchema :=
  toEventGraph_informationDiscipline SourceSemantics.mixedSetup.program


example : SourceSemantics.mixedSetup.eventGraph.order.eventCount = 4 := rfl

/-- Private initial values are graph inputs rather than another player move. -/
example : inputLayout SourceSemantics.mixedSetup.context ⟨0, by decide⟩ =
    .binding SourceSemantics.Player.alice .bool := rfl

example : encodeInputs SourceSemantics.mixedState ⟨0, by decide⟩ =
    PublicationResult.success true := rfl

/-- The complete mixed program has its source law under every adaptive public
scheduler, not just under the canonical schedule. -/
example (scheduler : SourceSemantics.mixedSetup.eventGraph.PublicScheduler)
    (profile : SourceProgram.BehavioralProfile SourceSemantics.mixedSetup.program) :
    (SourceSemantics.mixedSetup.eventGraph.terminalOutcomes scheduler
      (compileEventProfile SourceSemantics.mixedSetup.program profile)
      (encodeInputs SourceSemantics.mixedState)).map
        (terminalState SourceSemantics.mixedSetup.program) =
      (SourceProgram.run SourceSemantics.mixedSetup.program profile
        SourceSemantics.mixedState).map SourceProgram.Config.state :=
  scheduled_terminalState_law SourceSemantics.mixedSetup.program scheduler profile
    SourceSemantics.mixedState

private def rejectingGraph := toEventGraph SourceSemantics.falseGuardProgram

private abbrev rejectingBind : rejectingGraph.EventId := ⟨0, by decide⟩
private abbrev rejectingReveal : rejectingGraph.EventId := ⟨1, by decide⟩

private def rejectingInitial : rejectingGraph.Config :=
  .initial (fun input => nomatch input)

private def rejectingBound : rejectingGraph.Config :=
  rejectingInitial.complete rejectingBind (by decide)
    (some (PublicationResult.success true)) (PublicationResult.success true)

/-- An unsatisfiable guard compiles, and its reveal computes failure. It is not
silently replaced by an unrestricted commitment or a valid in-domain value. -/
example : (rejectingGraph.nodes rejectingReveal).eval? true rejectingBound.store =
    some (PMF.pure (PublicationResult.failure : PublicationResult Bool)) := rfl

private def rejected : rejectingGraph.Config :=
  rejectingBound.complete rejectingReveal (by decide) true PublicationResult.failure

/-- Public rejection does not erase the player's original disclosure choice
from its own recall. -/
example : decodeHistory SourceSemantics.falseGuardProgram
      rejected.history SourceSemantics.Player.alice =
    [SourceProgram.OwnAction.commit (L := simpleExpr) SourceSemantics.Player.alice 20 .bool
      (some (PublicationResult.success true)),
     SourceProgram.OwnAction.reveal SourceSemantics.Player.alice 20 true] := by
  rfl

private def defaultChain : SourceProgram Bool simpleExpr [] ∅ :=
  .commit 0 false (by decide) (unrestricted false 0) <|
  .reveal 1 false 0 (by decide) .here (by decide) <|
  .commit 2 false (by decide) (unrestricted false 2) <|
  .reveal 3 false 2 (by decide) .here (by decide) <| .ret []

private abbrev defaultGraph := (toEventGraph defaultChain).sequentialize

private def defaultInitial : EventGraphRuntime.State defaultGraph :=
  .initial (encodeInputs (Env.empty (CellVal simpleExpr)))

private def omitted : EventGraphRuntime.State defaultGraph :=
  defaultInitial.completeFailure ⟨0, by decide⟩ (by decide)

private theorem firstAutomatic : omitted.AutomaticReady ⟨1, by decide⟩ := by
  constructor
  · decide
  · change false ∈ omitted.config.defaulted
    decide

private def afterFirstAutomatic := omitted.completeAutomatic ⟨1, by decide⟩ firstAutomatic

private theorem secondAutomatic : afterFirstAutomatic.AutomaticReady ⟨2, by decide⟩ := by
  constructor
  · decide
  · change false ∈ afterFirstAutomatic.config.defaulted
    decide

private def afterSecondAutomatic :=
  afterFirstAutomatic.completeAutomatic ⟨2, by decide⟩ secondAutomatic

private theorem thirdAutomatic : afterSecondAutomatic.AutomaticReady ⟨3, by decide⟩ := by
  constructor
  · decide
  · change false ∈ afterSecondAutomatic.config.defaulted
    decide

private def afterThirdAutomatic :=
  afterSecondAutomatic.completeAutomatic ⟨3, by decide⟩ thirdAutomatic

/-- Three automatic instructions retain their own public completion positions. -/
example : afterThirdAutomatic.config.defaults.events = [none, none, none, some false] := rfl

/-- Mechanical work records no further strategic decision. -/
example : afterThirdAutomatic.config.history.map (fun completion => completion.decision.isSome) =
    [true, false, false, false] := rfl

/-- Every continuation profile has the same complete endpoint after these
automatic instructions, including profiles that request different actions. -/
example (profile : defaultGraph.BehavioralProfile) :
    defaultGraph.runPlan (defaultGraph.policyPlan profile defaultGraph.canonicalScheduler)
      omitted.config.remaining omitted.config = PMF.pure afterThirdAutomatic.config := by
  calc
    _ = defaultGraph.runPlan (defaultGraph.policyPlan profile defaultGraph.canonicalScheduler)
          afterFirstAutomatic.config.remaining afterFirstAutomatic.config :=
      EventGraphRuntime.State.completeAutomatic_runPlan_canonical _ profile omitted
        ⟨1, by decide⟩ firstAutomatic
    _ = defaultGraph.runPlan (defaultGraph.policyPlan profile defaultGraph.canonicalScheduler)
          afterSecondAutomatic.config.remaining afterSecondAutomatic.config :=
      EventGraphRuntime.State.completeAutomatic_runPlan_canonical _ profile afterFirstAutomatic
        ⟨2, by decide⟩ secondAutomatic
    _ = defaultGraph.runPlan (defaultGraph.policyPlan profile defaultGraph.canonicalScheduler)
          afterThirdAutomatic.config.remaining afterThirdAutomatic.config :=
      EventGraphRuntime.State.completeAutomatic_runPlan_canonical _ profile afterSecondAutomatic
        ⟨3, by decide⟩ thirdAutomatic
    _ = _ := by
      have finished : afterThirdAutomatic.config.remaining = 0 := by decide
      rw [finished]
      rfl

end

end VegasTests.EventCompilation
