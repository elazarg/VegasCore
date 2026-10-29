/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Expr.Simple
import Vegas.Source.Semantics
import Vegas.Compile.EventGraphScheduling

/-! # Whole-run absorbing failure and hidden unopenable bindings -/

noncomputable section

namespace VegasTests

open Vegas Vegas.SourceProgram GameTheory.Math.Probability

private abbrev sourceBindings : SourceCtx Unit simpleExpr :=
  [(1, .commitment () .bool), (0, .commitment () .bool)]

private def openGuard {Γ : SourceCtx Unit simpleExpr} (bindingName : VarId) :
    SourceGuard simpleExpr Γ () bindingName .bool where
  schema := []
  schemaNames := by decide
  subjectFresh := by simp
  code := .constBool true
  reads := fun member => nomatch member

private def twoOpenings : SourceProgram Unit simpleExpr sourceBindings {0, 1} :=
  .reveal 2 () 0 (by decide) (.there .here) (by decide) <|
  .reveal 3 () 1 (by decide) (.there .here) (by decide) <|
  .ret []

private def withholdThenOpen : BehavioralProfile twoOpenings :=
  fun _ => (fun _ _ _ => PMF.pure false, fun _ _ _ => PMF.pure true, PUnit.unit)

private def initialBindings : State simpleExpr sourceBindings :=
  Env.cons (.success true) (Env.cons (.success false) (Env.empty (CellVal simpleExpr)))

private def openingSummary (final : Config Unit simpleExpr twoOpenings.terminalCtx) :=
  (final.state.get (.there .here), final.state.get .here, final.defaulted, final.history ())

/-- A second prescribed disclosure never runs after the first public failure. -/
private theorem withholding_run :
    (twoOpenings.run withholdThenOpen initialBindings).map openingSummary =
    PMF.pure (PublicationResult.failure, PublicationResult.failure, ({()} : Finset Unit),
      [OwnAction.reveal () 0 false]) := by
  simp only [SourceProgram.run, runFrom, twoOpenings, withholdThenOpen, afterReveal,
    revealKernel, Config.initial, Config.view, revealSuccessor,
    Registry.completedBy, Registry.weaken, PublicationResult.isFailure,
    Config.defaulted, DecisionView.defaulted, DefaultHistory.defaulted, DefaultHistory.record]
  simp [PMF.pure_map, openingSummary, Config.defaulted, DefaultHistory.defaulted]

private def twoBindings : SourceProgram Unit simpleExpr [] ∅ :=
  .commit 0 () (by decide) (openGuard 0) <|
  .commit 1 () (by decide) (openGuard 1) <|
  .reveal 2 () 0 (by decide) (.there .here) (by decide) <|
  .reveal 3 () 1 (by decide) (.there .here) (by decide) <|
  .ret []

private def omitThenBind : BehavioralProfile twoBindings :=
  fun _ => (fun _ _ _ => PMF.pure none,
    fun _ _ _ => PMF.pure (some (.success true)),
    fun _ _ _ => PMF.pure true, fun _ _ _ => PMF.pure true, PUnit.unit)

private def bindingSummary (final : Config Unit simpleExpr twoBindings.terminalCtx) :=
  (final.state.get (.there (.there (.there .here))),
    final.state.get (.there (.there .here)), final.state.get (.there .here),
    final.state.get .here, final.defaulted, final.history ())

/-- Binding omission suppresses every later own binding and opening callback. -/
private theorem omission_run :
    (twoBindings.run omitThenBind (Env.empty (CellVal simpleExpr))).map bindingSummary =
    PMF.pure (PublicationResult.failure, PublicationResult.failure,
      PublicationResult.failure, PublicationResult.failure, ({()} : Finset Unit),
      [OwnAction.commit (L := simpleExpr) () 0 .bool none]) := by
  simp only [SourceProgram.run, runFrom, twoBindings, omitThenBind, afterCommit, afterReveal,
    commitKernel, revealKernel, Config.initial, Config.view, commitSuccessor, revealSuccessor,
    Registry.completedBy, Registry.weaken, PublicationResult.isFailure,
    Config.defaulted, DecisionView.defaulted, DefaultHistory.defaulted, DefaultHistory.record]
  simp [PMF.pure_map, bindingSummary, Config.defaulted, DefaultHistory.defaulted]

private def unusableThenBind : BehavioralProfile twoBindings :=
  fun _ => (fun _ _ _ => PMF.pure (some .failure),
    fun _ _ _ => PMF.pure (some (.success true)),
    fun _ _ _ => PMF.pure true, fun _ _ _ => PMF.pure true, PUnit.unit)

/-- An accepted unusable binding permits a later binding before its failed opening. -/
private theorem unusable_run :
    (twoBindings.run unusableThenBind (Env.empty (CellVal simpleExpr))).map bindingSummary =
    PMF.pure (PublicationResult.failure, PublicationResult.success true,
      PublicationResult.failure, PublicationResult.failure, ({()} : Finset Unit),
      [OwnAction.commit (L := simpleExpr) () 0 .bool (some .failure),
        OwnAction.commit (L := simpleExpr) () 1 .bool (some (.success true)),
        OwnAction.reveal () 0 true]) := by
  simp only [SourceProgram.run, runFrom, twoBindings, unusableThenBind, afterCommit, afterReveal,
    commitKernel, revealKernel, Config.initial, Config.view, commitSuccessor, revealSuccessor,
    Registry.completedBy, Obligation.accepts, openGuard,
    SourceGuard.accepts, Registry.weaken, PublicationResult.isFailure,
    Config.defaulted, DecisionView.defaulted, DefaultHistory.defaulted, DefaultHistory.record]
  simp [PMF.pure_map, bindingSummary, Config.defaulted, DefaultHistory.defaulted]

/-- Hidden setup bindings do not publish an initial default. -/
example : (Config.initial (Env.cons (.success true)
      (Env.cons (PublicationResult.failure : PublicationResult Bool)
        (Env.empty (CellVal simpleExpr))) : State simpleExpr sourceBindings)).defaulted = ∅ :=
  rfl

/-- Admitting an unusable binding has no immediate public default effect. -/
example : (commitSuccessor 0 (openGuard 0)
      (Config.initial (Env.empty (CellVal simpleExpr))) (some .failure)).defaulted = ∅ := by
  exact commitSuccessor_unopenable_opaque 0 (openGuard 0) _

/-- Every public schedule of the compiled program suppresses the later opening
after public withholding, with exactly the source's actual-choice history. -/
example (scheduler : (toEventGraph twoOpenings).PublicScheduler) :
    ((toEventGraph twoOpenings).terminalOutcomes scheduler
      (compileEventProfile twoOpenings withholdThenOpen) (encodeInputs initialBindings)).map
        (openingSummary ∘ terminalConfig twoOpenings) =
      PMF.pure (PublicationResult.failure, PublicationResult.failure, ({()} : Finset Unit),
        [OwnAction.reveal () 0 false]) := by
  calc
    _ = (twoOpenings.run withholdThenOpen initialBindings).map openingSummary := by
      rw [← PMF.map_comp, scheduled_terminalConfig_law]
    _ = _ := withholding_run

/-- Binding omission is compiled to public default and later automatic failure,
under every public scheduler. -/
example (scheduler : (toEventGraph twoBindings).PublicScheduler) :
    ((toEventGraph twoBindings).terminalOutcomes scheduler
      (compileEventProfile twoBindings omitThenBind)
      (encodeInputs (Env.empty (CellVal simpleExpr)))).map
        (bindingSummary ∘ terminalConfig twoBindings) =
      PMF.pure (PublicationResult.failure, PublicationResult.failure,
        PublicationResult.failure, PublicationResult.failure, ({()} : Finset Unit),
        [OwnAction.commit (L := simpleExpr) () 0 .bool none]) := by
  calc
    _ = (twoBindings.run omitThenBind (Env.empty (CellVal simpleExpr))).map bindingSummary := by
      rw [← PMF.map_comp, scheduled_terminalConfig_law]
    _ = _ := omission_run

/-- An accepted unopenable binding remains active through the next compiled
binding, and defaults only at its failed opening. -/
example (scheduler : (toEventGraph twoBindings).PublicScheduler) :
    ((toEventGraph twoBindings).terminalOutcomes scheduler
      (compileEventProfile twoBindings unusableThenBind)
      (encodeInputs (Env.empty (CellVal simpleExpr)))).map
        (bindingSummary ∘ terminalConfig twoBindings) =
      PMF.pure (PublicationResult.failure, PublicationResult.success true,
        PublicationResult.failure, PublicationResult.failure, ({()} : Finset Unit),
        [OwnAction.commit (L := simpleExpr) () 0 .bool (some .failure),
          OwnAction.commit (L := simpleExpr) () 1 .bool (some (.success true)),
          OwnAction.reveal () 0 true]) := by
  calc
    _ = (twoBindings.run unusableThenBind (Env.empty (CellVal simpleExpr))).map
        bindingSummary := by
      rw [← PMF.map_comp, scheduled_terminalConfig_law]
    _ = _ := unusable_run

end VegasTests

namespace VegasTests

open Vegas Vegas.SourceProgram

private def acceptGuard {Γ : SourceCtx Bool simpleExpr} (owner : Bool) (binding : VarId) :
    SourceGuard simpleExpr Γ owner binding .bool where
  schema := []
  schemaNames := by decide
  subjectFresh := by simp
  code := .constBool true
  reads := fun member => nomatch member

private abbrev AliceCtx : SourceCtx Bool simpleExpr := [(0, .commitment false .bool)]
private abbrev BobCtx : SourceCtx Bool simpleExpr :=
  [(1, .commitment true .bool), (0, .commitment false .bool)]
private abbrev OpenCtx : SourceCtx Bool simpleExpr :=
  [(2, .publication .bool), (1, .commitment true .bool), (0, .commitment false .bool)]

private def aliceBinding (choice : Option (PublicationResult Bool)) :
    Config Bool simpleExpr AliceCtx :=
  commitSuccessor 0 (acceptGuard false 0)
    (Config.initial (Env.empty (CellVal simpleExpr))) choice

private def bobBinding (choice : Option (PublicationResult Bool)) :
    Config Bool simpleExpr BobCtx :=
  commitSuccessor 1 (acceptGuard true 1) (aliceBinding choice) (some (.success false))

private def bobAfterOpening (choice : Option (PublicationResult Bool)) :
    DecisionView true OpenCtx :=
  (revealSuccessor 2 (.there .here) (bobBinding choice) true).view true

/-- Bob observes whether Alice defaulted before his binding. -/
example : (aliceBinding none).view true ≠ (aliceBinding (some .failure)).view true := by
  intro same
  have status := congrArg DecisionView.defaulted same
  change ({false} : Finset Bool) = ∅ at status
  have contains : false ∈ ({false} : Finset Bool) := by simp
  rw [status] at contains
  exact Finset.notMem_empty false contains

/-- Alice's failed opening eventually gives the two histories the same current status. -/
example : (bobAfterOpening none).defaulted = (bobAfterOpening (some .failure)).defaulted := rfl

/-- Bob's current typed observation and own chosen action list can also coincide. -/
example : (bobAfterOpening none).observation = (bobAfterOpening (some .failure)).observation ∧
    (bobAfterOpening none).history = (bobAfterOpening (some .failure)).history := by
  constructor <;> rfl

/-- The public history keeps the earlier omission distinct from the later failed opening. -/
example : (bobAfterOpening none).defaults.events = [none, none, some false] ∧
    (bobAfterOpening (some .failure)).defaults.events = [some false, none, none] := by
  constructor <;> rfl

/-- Retaining public timing prevents the two later views from merging. -/
example : bobAfterOpening none ≠ bobAfterOpening (some .failure) := by
  intro same
  have record := congrArg (fun view : DecisionView true OpenCtx => view.defaults.events) same
  change [none, none, some false] = [some false, none, none] at record
  cases record

end VegasTests

namespace VegasTests

open Vegas Vegas.SourceProgram GameTheory.Math.Probability

private def observedDefaultGuard {Γ : SourceCtx Bool simpleExpr}
    (owner : Bool) (binding : VarId) : SourceGuard simpleExpr Γ owner binding .bool where
  schema := []
  schemaNames := by decide
  subjectFresh := by simp
  code := .constBool true
  reads := fun member => nomatch member

private def foreignOmission : SourceProgram Bool simpleExpr [] ∅ :=
  .commit 0 false (by decide) (observedDefaultGuard false 0) <|
  .commit 1 true (by decide) (observedDefaultGuard true 1) <|
  .reveal 2 false 0 (by decide) (.there .here) (by decide) <|
  .reveal 3 true 1 (by decide) (.there .here) (by decide) <|
  .ret []

private def respondToOmission : BehavioralProfile foreignOmission :=
  fun _ => (fun _ _ _ => PMF.pure none,
    fun _ view _ => PMF.pure (some (.success (decide (false ∈ view.defaulted)))),
    fun _ _ _ => PMF.pure true, fun _ _ _ => PMF.pure true, PUnit.unit)

private def bobChosenBinding (final : Config Bool simpleExpr foreignOmission.terminalCtx) :
    PublicationResult Bool :=
  final.state.get (.there (.there .here))

/-- Bob's binding records Alice's earlier public omission. -/
private theorem source_bob_observes_omission :
    (foreignOmission.run respondToOmission (Env.empty (CellVal simpleExpr))).map
      bobChosenBinding = PMF.pure (.success true) := by
  simp only [SourceProgram.run, runFrom, foreignOmission, respondToOmission,
    afterCommit, afterReveal, commitKernel, revealKernel, Config.initial, Config.view,
    commitSuccessor, revealSuccessor, Registry.completedBy, Registry.weaken,
    PublicationResult.isFailure, Config.defaulted, DecisionView.defaulted,
    DefaultHistory.defaulted, DefaultHistory.record]
  simp [PMF.pure_map, bobChosenBinding]

/-- Even the greatest-enabled scheduler preserves Bob's reaction to a foreign
binding omission, because compiled dependencies retain its public observation. -/
example :
    ((toEventGraph foreignOmission).terminalOutcomes
        (toEventGraph foreignOmission).greatestScheduler
        (compileEventProfile foreignOmission respondToOmission)
        (encodeInputs (Env.empty (CellVal simpleExpr)))).map
      (bobChosenBinding ∘ terminalConfig foreignOmission) =
      PMF.pure (.success true) := by
  rw [← PMF.map_comp, scheduled_terminalConfig_law]
  exact source_bob_observes_omission

end VegasTests
