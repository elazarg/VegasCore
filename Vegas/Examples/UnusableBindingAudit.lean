/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.PendingMenusSource
import Vegas.Pending.ReactiveBinding

/-! # A hidden unusable binding and a lawful withholding transcript

The existing two-event native graph binds an integer and then reveals it.
An unusable commitment and a valid commitment followed by withholding have
the same public traffic and observations. This tests audit identifiability;
it does not assert that the unusable choice is profitable or obstructs SE.
-/

noncomputable section

namespace Vegas.Examples.UnusableBindingAudit

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

abbrev graph := PendingMenus.graph
abbrev runtime := PendingMenus.runtime

def leaks : MessageNetwork.ObservationRule Unit (WitnessedPacket graph) :=
  fun _ _ => PMF.pure ∅

abbrev app := runtime.reactiveApplication leaks
abbrev candidate : Handle graph := ((), .prepared 0)

def initial : app.Execution :=
  .initial app (State.initial PendingMenus.input)

def submitted (choice : PublicationResult Int) : app.Execution :=
  initial.respond app () (runtime.reactiveBinding leaks () 0 .int choice 0)

theorem submitted_meaning (choice : PublicationResult Int) :
    (submitted choice).application.bindingResult candidate .int = choice :=
  runtime.reactiveBinding_result leaks () 0 .int choice 0 initial rfl

theorem submitted_observation (first second : PublicationResult Int) :
    (submitted first).observeEnvironment app = (submitted second).observeEnvironment app :=
  runtime.reactiveBinding_observation leaks () 0 .int first second 0 initial

private theorem binding_ready (choice : PublicationResult Int) :
    (submitted choice).application.config.cut.Ready 0 := by
  cases choice <;>
    change (EventGraph.Config.initial (graph := graph) PendingMenus.input).cut.Ready 0
  all_goals decide

def boundState (choice : PublicationResult Int) : EventGraphRuntime.State graph :=
  { ((submitted choice).application.complete 0 (binding_ready choice) choice choice) with
    accepted := Function.update (submitted choice).application.accepted (.inr 0) (some candidate)
    candidates := (submitted choice).application.candidates.freeze candidate }

def bound (choice : PublicationResult Int) : app.Execution :=
  (submitted choice).includePending app ((), 0)

private theorem binding_accepted (choice : PublicationResult Int) :
    handle runtime (submitted choice).application
      ⟨((), 0), .commitment 0 candidate⟩ = some (boundState choice) := by
  have accepted := runtime.handle_commitment_eq (submitted choice).application ((), 0) 0
    candidate () .int rfl rfl rfl (binding_ready choice)
    (by cases choice <;> change 0 < 2 <;> decide) rfl rfl
    (by cases choice <;> rfl) (by
      intro field
      cases field with
      | inl input => exact Fin.elim0 input
      | inr event =>
          cases choice <;> change (none : Option (Handle graph)) ≠ some candidate
          all_goals simp)
  rw [submitted_meaning] at accepted
  exact accepted

private theorem submitted_lookup (choice : PublicationResult Int) :
    (submitted choice).network.lookup ((), 0) =
      some ⟨((), 0), ⟨.commitment 0 candidate, none⟩⟩ := by cases choice <;> rfl

theorem bound_state (choice : PublicationResult Int) :
    (bound choice).application = boundState choice := by
  have found : (submitted choice).network.lookup ((), 0) =
      some ⟨((), 0), ⟨.commitment 0 candidate, none⟩⟩ := by cases choice <;> rfl
  change ((submitted choice).includePending app ((), 0)).application = _
  simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    found, app, reactiveApplication]
  rw [binding_accepted]
  rfl

theorem bound_receipts (choice : PublicationResult Int) :
    (bound choice).receipts = [⟨((), 0), true⟩] := by
  have found := submitted_lookup choice
  have accepted := binding_accepted choice
  simp only [bound, ReactiveApplication.Execution.includePending,
    MessageNetwork.includePending, found, app, reactiveApplication, accepted]
  cases choice <;> rfl

theorem bound_observation (first second : PublicationResult Int) :
    (bound first).observeEnvironment app = (bound second).observeEnvironment app := by
  have publicEq : (boundState first).publicView = (boundState second).publicView := by
    cases first <;> cases second
    all_goals unfold State.publicView
    all_goals congr 1
    all_goals apply EventGraph.PublicObservation.ext
    all_goals first | rfl | funext field
    all_goals
      cases field with
      | inl input => exact Fin.elim0 input
      | inr event => fin_cases event <;> rfl
  change ReactiveApplication.EnvironmentView.mk (app := app) _
      (bound first).application.publicView _ =
    ReactiveApplication.EnvironmentView.mk (app := app) _ (bound second).application.publicView _
  rw [bound_state, bound_state, publicEq, bound_receipts, bound_receipts]
  congr 1

def withholding : app.Action :=
  ⟨some (.submit ⟨⟨.withhold 1, none⟩, .none⟩)⟩

def revealState (choice : PublicationResult Int) : EventGraphRuntime.State graph :=
  boundState choice

def withheld (choice : PublicationResult Int) : app.Execution :=
  (bound choice).respond app () withholding

private theorem withheld_state (choice : PublicationResult Int) :
    (withheld choice).application = revealState choice := by
  change (bound choice).application = _
  rw [bound_state]
  rfl

private theorem disclosure_ready (choice : PublicationResult Int) :
    (boundState choice).config.cut.Ready 1 := by
  cases choice <;>
    change (1 : Fin 2) ∉ ({0} : Finset (Fin 2)) ∧
      graph.order.predecessors 1 ⊆ {0}
  all_goals decide

def finalState (choice : PublicationResult Int) : EventGraphRuntime.State graph :=
  (revealState choice).complete 1 (disclosure_ready choice) false .failure

def finished (choice : PublicationResult Int) : app.Execution :=
  (withheld choice).includePending app ((), 1)

private theorem withholding_accepted (choice : PublicationResult Int) :
    handle runtime (withheld choice).application ⟨((), 1), .withhold 1⟩ =
      some (finalState choice) := by
  rw [withheld_state]
  exact runtime.handle_withhold_unremembered_eq (revealState choice) ((), 1) 1 () .int
    PendingMenus.binding [] rfl rfl rfl (disclosure_ready choice)
    (by cases choice <;> change 0 < 2 <;> decide) rfl (by cases choice <;> rfl)

private theorem withheld_lookup (choice : PublicationResult Int) :
    (withheld choice).network.lookup ((), 1) =
      some ⟨((), 1), ⟨.withhold 1, none⟩⟩ := by
  cases choice <;> rfl

theorem finished_state (choice : PublicationResult Int) :
    (finished choice).application = finalState choice := by
  have found := withheld_lookup choice
  have accepted := withholding_accepted choice
  simp only [finished, ReactiveApplication.Execution.includePending,
    MessageNetwork.includePending, found, app, reactiveApplication, accepted, Option.getD_some]

theorem finished_receipts (choice : PublicationResult Int) :
    (finished choice).receipts = [⟨((), 0), true⟩, ⟨((), 1), true⟩] := by
  have found := withheld_lookup choice
  have accepted := withholding_accepted choice
  simp only [finished, ReactiveApplication.Execution.includePending,
    MessageNetwork.includePending, found, app, reactiveApplication, accepted]
  change (bound choice).receipts ++ [⟨((), 1), true⟩] = _
  rw [bound_receipts]
  rfl

theorem withheld_observation (first second : PublicationResult Int) :
    (withheld first).observeEnvironment app = (withheld second).observeEnvironment app := by
  have publicEq := congrArg ReactiveApplication.EnvironmentView.application
    (bound_observation first second)
  change ReactiveApplication.EnvironmentView.mk (app := app) _
      (withheld first).application.publicView _ =
    ReactiveApplication.EnvironmentView.mk (app := app) _
      (withheld second).application.publicView _
  rw [withheld_state, withheld_state]
  change (bound first).application.publicView = (bound second).application.publicView at publicEq
  rw [bound_state, bound_state] at publicEq
  have revealedEq : (revealState first).publicView = (revealState second).publicView := by
    exact publicEq
  rw [revealedEq]
  congr 1
  change (bound first).receipts = (bound second).receipts
  rw [bound_receipts, bound_receipts]

theorem finished_observation (first second : PublicationResult Int) :
    (finished first).observeEnvironment app = (finished second).observeEnvironment app := by
  have publicEq : (finalState first).publicView = (finalState second).publicView := by
    cases first <;> cases second
    all_goals unfold State.publicView
    all_goals congr 1
    all_goals apply EventGraph.PublicObservation.ext
    all_goals first | rfl | funext field
    all_goals
      cases field with
      | inl input => exact Fin.elim0 input
      | inr event => fin_cases event <;> rfl
  change ReactiveApplication.EnvironmentView.mk (app := app) _
      (finished first).application.publicView _ =
    ReactiveApplication.EnvironmentView.mk (app := app) _
      (finished second).application.publicView _
  rw [finished_state, finished_state, publicEq, finished_receipts, finished_receipts]
  congr 1

/-- These executions keep the different private meanings fixed throughout.
The public equivalence does not rely on late assignment or a mutable binding. -/
theorem finished_meaning (choice : PublicationResult Int) :
    (finished choice).application.bindingResult candidate .int = choice := by
  rw [finished_state]
  cases choice <;> rfl

/-- The terminal disclosed field fails on both executions. -/
theorem finished_publication (choice : PublicationResult Int) :
    (finished choice).application.config.store (.inr 1) = some .failure := by
  rw [finished_state]
  cases choice <;> rfl

/-- Public snapshots at every response/inclusion boundary, including the full
pending pool, ledger, authenticated input authors, receipts and public phase. -/
def auditTrace (choice : PublicationResult Int) : List app.EnvironmentView :=
  [initial.observeEnvironment app, (submitted choice).observeEnvironment app,
    (bound choice).observeEnvironment app, (withheld choice).observeEnvironment app,
    (finished choice).observeEnvironment app]

theorem auditTrace_eq (first second : PublicationResult Int) :
    auditTrace first = auditTrace second := by
  simp only [auditTrace, submitted_observation first second, bound_observation first second,
    withheld_observation first second,
    finished_observation first second]

/-- Even randomized auditing of complete public snapshots cannot charge the
unusable binding while remaining silent on this lawful valid-and-withhold run. -/
theorem no_sound_detection (value : Int)
    (audit : List app.EnvironmentView → PMF Bool)
    (sound : ((audit (auditTrace (.success value))) true).toReal = 0) :
    ((audit (auditTrace .failure)) true).toReal = 0 := by
  rw [auditTrace_eq .failure (.success value)]
  exact sound

/-- Subsequent random sampling or other public postprocessing cannot separate
the two executions either. -/
theorem audit_law_eq {Observation : Type}
    (audit : List app.EnvironmentView → PMF Observation) (value : Int) :
    audit (auditTrace .failure) = audit (auditTrace (.success value)) :=
  congrArg audit (auditTrace_eq .failure (.success value))

/-- Valid binding followed by withholding is admitted by every existing source
commitment interface, including the value-only interface. -/
def lawfulSourcePolicy (value : Int) (who : Unit) :
    SourceProgram.BehavioralPolicy who PendingMenus.sourceProgram :=
  (fun _ _ => PMF.pure (.success value), (fun _ _ => PMF.pure false, PUnit.unit))

theorem lawful_source_admitted (value : Int)
    (admission : SourceProgram.CommitmentInterface PendingMenus.sourceProgram) (who : Unit) :
    (lawfulSourcePolicy value who).Admitted PendingMenus.sourceProgram admission := by
  refine ⟨?_, trivial⟩
  intro _ _ choice reached
  have same := (PMF.mem_support_pure_iff _ _).mp reached
  subst choice
  trivial

/-- At the binding site this is the compiler's actual response. -/
theorem compiled_binding (choice : PublicationResult Int) :
    runtime.reactiveDecision leaks () 0 choice (initial.observe app ()).application =
      runtime.reactiveBinding leaks () 0 .int choice 0 := by
  apply runtime.reactiveDecision_binding_eq leaks () () 0 .int rfl rfl rfl
    choice (initial.observe app ()).application 0
  unfold reactiveFreshSlot
  split
  · congr 1
    exact (Nat.find_eq_zero _).mpr rfl
  · rename_i impossible
    exact False.elim (impossible ⟨0, rfl⟩)

/-- At the reveal site the legal source choice to withhold emits exactly
the packet used in the indistinguishable executions. -/
theorem compiled_withholding (choice : PublicationResult Int) :
    runtime.reactiveDecision leaks () 1 false
      ((bound choice).observe app ()).application = withholding := by
  have node : nodeView graph 1 = .resolve () .int PendingMenus.binding [] rfl rfl := rfl
  simp only [reactiveDecision, node, reactiveResolutionPacket,
    cast_eq, Bool.false_eq_true, ↓reduceIte, disclosureSubmission_normalize_withhold]
  rfl

end Vegas.Examples.UnusableBindingAudit
