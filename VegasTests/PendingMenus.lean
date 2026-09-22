/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Expr.Simple
import Vegas.Pending.NativeProtocolSafety
import Vegas.Pending.EventBindingAction
import GameTheory.Protocol.SubgamePerfect

/-! # Competing pending commitments restrict a native continuation

One player binds an integer and then discloses it. Two valid, immutable
commitments are already pending before the last initial owner invocation.
A fixed public wire policy includes the older packet when a third packet is
authored, and the newer packet otherwise. A fresh candidate remains available,
but no action can make that candidate win this inclusion.

The prefix is reachable in the actual service and starts a proper canonical
subgame. Every action loses access to a third value, even after arbitrary
further native computation and traffic. The final policy-level impossibility
theorem additionally needs native deviation witnesses and a source SPE witness.
-/

noncomputable section

namespace VegasTests.PendingMenus

open GameTheory.Protocol GameTheory.Math.Probability Interaction Vegas Vegas.EventGraphRuntime

private abbrev order : EventOrder where
  eventCount := 2
  predecessors event := if event = 1 then {0} else ∅
  predecessor_lt := by decide

private abbrev inputs : Fin 0 → EventGraph.EventField Unit simpleExpr := Fin.elim0
private abbrev outputs : Fin 2 → EventGraph.EventField Unit simpleExpr :=
  Fin.cases (.binding () .int) (fun _ => .publication .int)
private abbrev layout := EventGraph.fieldLayout inputs outputs
private abbrev binding : EventGraph.FieldRef layout (.binding () .int) := ⟨.inr 0, rfl⟩

private abbrev graph : EventGraph Unit simpleExpr where
  inputCount := 0
  order := order
  inputLayout := inputs
  outputLayout := outputs
  nodes := Fin.cases
    (EventGraph.EventCode.bind (layout := layout) () .int)
    (fun _ => EventGraph.EventCode.resolve (layout := layout) () .int binding [])
  reads_available := by
    intro event field member
    cases field with
    | inl input => exact Fin.elim0 input
    | inr producer =>
        fin_cases event
        · exact False.elim (Finset.notMem_empty _ member)
        · change Sum.inr producer ∈ insert (Sum.inr 0) ∅ at member
          simpa [order] using member
  payoffs := []

private def runtime : EventGraphRuntime graph where
  deadline _ := 2

private abbrev app := runtime.application
private def input : graph.Inputs := fun input => nomatch input
private def setup : NativeExecution runtime :=
  NativeExecution.initial runtime (MessageApplication.State.initial app (State.initial input))

private def initial : NativeExecution runtime :=
  { setup with
    native := { setup.native with application :=
      { setup.native.application with serviceGrant := some 0 } }
    environmentHistory :=
      [⟨MessageApplication.State.environmentView app setup.native, .application (.grant 0)⟩] }

private def first : PlayerAction graph := bindingAction () 0 .int (.success 1) 0
private def second : PlayerAction graph := bindingAction () 0 .int (.success 2) 1
private def contested : NativeExecution runtime :=
  runtime.takeAction () (runtime.takeAction () initial first) second

/-- The wire consults public traffic only, not candidate meanings or witnesses. -/
private def wire : app.WirePolicy := fun _ view =>
  FinDist.pure (.include ((), if (view.pool.lookup ((), 2)).isSome then 0 else 1))

private def afterAction (action : PlayerAction graph) : NativeExecution runtime :=
  runtime.takeAction () contested action

private def selected (action : PlayerAction graph) : Nat :=
  if ((afterAction action).native.pool.lookup ((), 2)).isSome then 0 else 1

private def selectedValue (action : PlayerAction graph) : Int :=
  if ((afterAction action).native.pool.lookup ((), 2)).isSome then 1 else 2

private theorem old_pending (action : PlayerAction graph) :
    (afterAction action).native.pool.lookup ((), 0) =
      some ⟨((), 0), .commitment 0 ((), .prepared 0)⟩ ∧
    (afterAction action).native.pool.lookup ((), 1) =
      some ⟨((), 1), .commitment 0 ((), .prepared 1)⟩ := by
  constructor <;> exact runtime.transmit_lookup () contested.native action.transmission _ _ rfl

private theorem candidates_fixed (action : PlayerAction graph) (serial : Nat)
    (fixed : contested.native.application.candidates.lookup ((), .prepared serial) ≠ .fresh) :
    (afterAction action).native.application.candidates.lookup ((), .prepared serial) =
      contested.native.application.candidates.lookup ((), .prepared serial) := by
  obtain ⟨actions, run⟩ := runtime.transmit_native () contested.native action.transmission
  exact runtime.run_candidate_fixed _ _ actions ((), .prepared serial) fixed
    (by rw [run]; exact FinDist.mem_support_pure.mpr rfl)

private theorem include_value (action : PlayerAction graph) (serial : Nat) (value : Int)
    (pending : (afterAction action).native.pool.lookup ((), serial) =
      some ⟨((), serial), .commitment 0 ((), .prepared serial)⟩)
    (candidate : contested.native.application.candidates.lookup ((), .prepared serial) =
      .openable ⟨.int, value⟩) :
    (app.includePending (afterAction action).native ((), serial)).application.config.outputs 0 =
      some (.success value) := by
  have facts := runtime.transmit_application () contested.native action.transmission
  have configEq : (afterAction action).native.application.config =
      initial.native.application.config :=
    facts.1
  have publicEq : (afterAction action).native.application.publicView =
      initial.native.application.publicView := facts.2.2
  have ready : (afterAction action).native.application.config.cut.Ready 0 := by
    rw [configEq]
    decide
  have timely : (afterAction action).native.application.WithinDeadline runtime 0 := by
    have clockEq := congrArg PublicView.clock publicEq
    have activatedEq := congrArg PublicView.activatedAt publicEq
    change (afterAction action).native.application.clock = 0 at clockEq
    change (afterAction action).native.application.activatedAt = _ at activatedEq
    simp only [State.WithinDeadline, clockEq, activatedEq]
    change 0 < 2
    decide
  have vacant : (afterAction action).native.application.accepted (.inr 0) = none := by
    exact congrArg (fun view : PublicView graph => view.accepted (.inr 0)) publicEq
  have unused : (afterAction action).native.application.HandleUnused ((), .prepared serial) := by
    intro field
    have handles := congrArg (fun view : PublicView graph => view.accepted field) publicEq
    cases field with
    | inl input => exact Fin.elim0 input
    | inr event =>
        change (afterAction action).native.application.accepted (.inr event) = none at handles
        rw [handles]
        intro impossible
        cases impossible
  have meaning := candidates_fixed action serial (by rw [candidate]; intro h; cases h)
  rw [candidate] at meaning
  have valueEq : (afterAction action).native.application.bindingResult
      ((), .prepared serial) .int = .success value := by
    simp only [State.bindingResult, meaning, Raw.as?_mk, Option.elim_some]
  have accepted := handle_commitment_eq runtime (afterAction action).native.application
    ((), serial) 0 ((), .prepared serial) () .int rfl rfl rfl ready timely rfl rfl vacant unused
  rw [app.includePending_accept _ _ _ _ pending accepted]
  change ((afterAction action).native.application.config.complete 0 ready _ _).outputs 0 = _
  rw [EventGraph.Config.complete_output_same, valueEq]
  rfl

/-- Every final player action loses the ability to select any third binding
value. This quantifies over all native actions, including arbitrary replay,
opening data, packet kinds, and private memory. -/
theorem selected_binding (action : PlayerAction graph) :
    (app.includePending (afterAction action).native
      ((), selected action)).application.config.outputs 0 =
      some (.success (selectedValue action)) := by
  unfold selected selectedValue
  split
  · exact include_value action 0 1 (old_pending action).1 rfl
  · exact include_value action 1 2 (old_pending action).2 rfl

theorem wait_selects_two : selectedValue PlayerAction.wait = 2 := rfl

/-- A third valid commitment to zero affects selection, but cannot win it. -/
theorem fresh_commitment_selects_one :
    selectedValue (bindingAction () 0 .int (.success 0) 2) = 1 := rfl

private def ordering : runtime.ServiceOrderPolicy :=
  fun _ _ => FinDist.pure (ServiceOrder.increasing graph)

private abbrev arena := runtime.nativeProtocol (FinDist.pure input) [] 1 wire ordering

private def setupControl : NativeControl runtime := ⟨runtime.serviceEpochs, [], setup⟩

private def orderedControl : NativeControl runtime :=
  ⟨5, epochPlan (ServiceOrder.increasing graph) [] 1, setup⟩

private def grantedControl : NativeControl runtime :=
  ⟨5, orderedControl.plan.drop 1, initial⟩

private def firstControl (action : PlayerAction graph) : NativeControl runtime :=
  ⟨5, orderedControl.plan.drop 2, runtime.takeAction () initial action⟩

private def secondControl (one two : PlayerAction graph) : NativeControl runtime :=
  ⟨5, orderedControl.plan.drop 3,
    runtime.takeAction () (runtime.takeAction () initial one) two⟩

private def extendPure (history : arena.History) (joint : Unit → Option (PlayerAction graph))
    (legal : arena.Legal history.state joint) (target : arena.State)
    (law : arena.step history.state ⟨joint, legal⟩ = FinDist.pure target) : arena.History :=
  history.extend legal (by rw [law]; exact FinDist.mem_support_pure.mpr rfl)

private def setupHistory : arena.History :=
  extendPure arena.initHistory (fun _ => none)
    ⟨by change ¬ False; simp, fun _ => by change ¬ (none : Option Unit) = some _; simp⟩
    (some setupControl) (by
      simp only [arena, nativeProtocol, nativeTransition, FinDist.map_pure]
      rfl)

private def orderedHistory : arena.History :=
  extendPure setupHistory (fun _ => none)
    ⟨by change ¬ (6 = 0 ∧ [] = ([] : List (ServiceInstruction graph))); simp,
      fun _ => by change ¬ (none : Option Unit) = some _; simp⟩
    (some orderedControl) (by
      change runtime.nativeTransition (FinDist.pure input) [] 1 wire ordering
        (some setupControl) (fun _ => none) = _
      change (ordering _ _).map _ = _
      rw [ordering, FinDist.map_pure]
      rfl)

private def grantedHistory : arena.History :=
  extendPure orderedHistory (fun _ => none)
    ⟨by change ¬ (5 = 0 ∧ _); simp,
      fun _ => by change ¬ (none : Option Unit) = some _; simp⟩
    (some grantedControl) (by
      change (runtime.nativeInstructionStep wire (.grant 0) setup _).map _ = _
      simp only [nativeInstructionStep, serviceStep, MessageApplication.environmentPolicyStep,
        MessageApplication.advance, MessageApplication.EnvironmentPolicyCommand.toAction,
        MessageApplication.step, application, environmentStep, FinDist.map_pure,
        FinDist.pure_bind]
      rfl)

private def firstHistory (action : PlayerAction graph) : arena.History :=
  extendPure grantedHistory (fun _ => some action)
    ⟨by change ¬ (5 = 0 ∧ _); simp,
      fun who => by cases who; exact ⟨rfl, Set.mem_univ _⟩⟩
    (some (firstControl action)) (by
      change (runtime.actionStep () initial action).map _ = _
      rw [actionStep, FinDist.map_pure]
      rfl)

private def secondHistory (one two : PlayerAction graph) : arena.History :=
  extendPure (firstHistory one) (fun _ => some two)
    ⟨by change ¬ (5 = 0 ∧ _); simp,
      fun who => by cases who; exact ⟨rfl, Set.mem_univ _⟩⟩
    (some (secondControl one two)) (by
      change (runtime.actionStep () (runtime.takeAction () initial one) two).map _ = _
      rw [actionStep, FinDist.map_pure]
      rfl)

private theorem extendPure_unique (history : arena.History)
    (joint : Unit → Option (PlayerAction graph))
    (legal : arena.Legal history.state joint) (target : arena.State)
    (law : arena.step history.state ⟨joint, legal⟩ = FinDist.pure target)
    (otherLegal : arena.Legal history.state joint) (other : arena.State)
    (supported : other ∈ (arena.step history.state ⟨joint, otherLegal⟩).support) :
    history.extend otherLegal supported = extendPure history joint legal target law := by
  rw [law] at supported
  have same := FinDist.mem_support_pure.mp supported
  subst other
  rfl

private theorem inactive_joint (history : arena.History)
    (joint : Unit → Option (PlayerAction graph))
    (legal : arena.Legal history.state joint)
    (inactive : ∀ who, ¬ arena.active history.state who) : joint = fun _ => none := by
  funext who
  cases choice : joint who with
  | none => rfl
  | some action =>
      have valid := legal.2 who
      rw [choice] at valid
      exact False.elim (inactive who valid.1)

private theorem active_joint (history : arena.History)
    (joint : Unit → Option (PlayerAction graph))
    (legal : arena.Legal history.state joint)
    (active : arena.active history.state ()) :
    ∃ action, joint = fun _ => some action := by
  obtain ⟨action, chosen⟩ := LegalOption.exists_eq_some_of_active (joint ())
    (ExecutionProtocol.legalOption_of_legal legal ()) active
  exact ⟨action, funext fun who => by cases who; exact chosen⟩

/-- Every history either precedes the second invocation, or extends one
particular pair of initial player actions. No hidden scheduler choice occurs
before that pair in this instance. -/
private def Classified (history : arena.History) : Prop :=
  history = arena.initHistory ∨ history = setupHistory ∨ history = orderedHistory ∨
    history = grantedHistory ∨ (∃ action, history = firstHistory action) ∨
      ∃ one two, arena.HistoryReaches (secondHistory one two) history

private theorem classified_step (history : arena.History) (classified : Classified history)
    (joint : Unit → Option (PlayerAction graph)) (legal : arena.Legal history.state joint)
    (target : arena.State)
    (supported : target ∈ (arena.step history.state ⟨joint, legal⟩).support) :
    Classified (history.extend legal supported) := by
  rcases classified with rfl | rfl | rfl | rfl | ⟨action, rfl⟩ | ⟨one, two, reached⟩
  · have same := inactive_joint _ joint legal (fun _ h => by cases h)
    subst joint
    exact Or.inr (Or.inl (extendPure_unique _ _ _ _ _ legal target supported))
  · have same := inactive_joint _ joint legal (fun _ h => by cases h)
    subst joint
    exact Or.inr (Or.inr (Or.inl (extendPure_unique _ _ _ _ _ legal target supported)))
  · have same := inactive_joint _ joint legal (fun _ h => by cases h)
    subst joint
    exact Or.inr (Or.inr (Or.inr (Or.inl
      (extendPure_unique _ _ _ _ _ legal target supported))))
  · obtain ⟨action, rfl⟩ := active_joint _ joint legal rfl
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨action, extendPure_unique _ _ _ _ _ legal target supported⟩))))
  · obtain ⟨next, rfl⟩ := active_joint _ joint legal rfl
    have same : (firstHistory action).extend legal supported = secondHistory action next :=
      extendPure_unique _ _ _ _ _ legal target supported
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨action, next, ?_⟩))))
    rw [same]
    exact ExecutionProtocol.HistoryReaches.refl arena _
  · obtain ⟨fuel, path⟩ := reached
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨one, two, fuel + 1,
      path.trans (.step joint legal supported (.refl 0 _))⟩))))

private theorem classified : ∀ {state} (trace : arena.Trace state), Classified ⟨state, trace⟩
  | _, .start => Or.inl rfl
  | _, .extend prior joint legal supported =>
      classified_step _ (classified prior) joint legal _ supported

private def actionRecall (control : NativeControl runtime) : List (PlayerAction graph) :=
  (control.execution.principalHistory ()).map NativeEntry.action

private theorem initial_actions_recalled (one two : PlayerAction graph)
    (history : arena.History) (control : NativeControl runtime)
    (reached : arena.HistoryReaches (secondHistory one two) history)
    (stateEq : history.state = some control) : [one, two] <+: actionRecall control := by
  obtain ⟨fuel, path⟩ := reached
  have retained := runtime.native_reaches_history_prefix (FinDist.pure input) [] 1 wire
    ordering path (secondControl one two) control rfl stateEq ()
  exact retained.map NativeEntry.action

private theorem recalled_initial_actions_reached (one two : PlayerAction graph)
    (history : arena.History) (control : NativeControl runtime)
    (stateEq : history.state = some control)
    (recalled : [one, two] <+: actionRecall control) :
    arena.HistoryReaches (secondHistory one two) history := by
  have casesHistory : Classified history := classified history.trace
  rcases casesHistory with rfl | rfl | rfl | rfl | ⟨action, rfl⟩ | ⟨a, b, reached⟩
  · cases stateEq
  · cases Option.some.inj stateEq
    have bound := recalled.length_le
    change 2 ≤ 0 at bound
    omega
  · cases Option.some.inj stateEq
    have bound := recalled.length_le
    change 2 ≤ 0 at bound
    omega
  · cases Option.some.inj stateEq
    have bound := recalled.length_le
    change 2 ≤ 0 at bound
    omega
  · cases Option.some.inj stateEq
    have bound := recalled.length_le
    change 2 ≤ 1 at bound
    omega
  · have actual := initial_actions_recalled a b history control reached stateEq
    have same : [one, two] = [a, b] :=
      (List.prefix_iff_eq_take.mp recalled).trans (List.prefix_iff_eq_take.mp actual).symm
    have components := List.cons.inj same
    cases components.1
    cases (List.cons.inj components.2).1
    exact reached

/-- This is a proper canonical native subgame, including all its future
decision information sets. Own recall identifies the first two submissions;
the service prefix before them is deterministic. -/
theorem contested_isSubgameRoot :
    (runtime.nativeInformation (FinDist.pure input) [] 1 wire ordering).IsSubgameRoot
      (secondHistory first second) := by
  intro who inside outside reached _ insideActive _ outsideActive sameInfo
  cases who
  have insideCases : ∃ control, inside.state = some control := by
    cases stateEq : inside.state with
    | none =>
        simp only [nativeProtocol, stateEq, nativeActor] at insideActive
        cases insideActive
    | some control => exact ⟨control, rfl⟩
  have outsideCases : ∃ control, outside.state = some control := by
    cases stateEq : outside.state with
    | none =>
        simp only [nativeProtocol, stateEq, nativeActor] at outsideActive
        cases outsideActive
    | some control => exact ⟨control, rfl⟩
  obtain ⟨insideControl, insideEq⟩ := insideCases
  obtain ⟨outsideControl, outsideEq⟩ := outsideCases
  have infoEq : runtime.nativeObserve () inside.state =
      runtime.nativeObserve () outside.state := by
    simpa only [nativeInformation, runtime.native_info] using sameInfo
  have insideActs : runtime.nativeActor (some insideControl) = some () := insideEq ▸ insideActive
  have outsideActs : runtime.nativeActor (some outsideControl) = some () :=
    outsideEq ▸ outsideActive
  rw [insideEq, outsideEq, nativeObserve, ite_eq_left insideActs, nativeObserve,
    ite_eq_left outsideActs] at infoEq
  have recallEq := congrArg Prod.fst (Option.some.inj infoEq)
  have actionsEq : actionRecall insideControl = actionRecall outsideControl :=
    congrArg (List.map NativeEntry.action) recallEq
  exact recalled_initial_actions_reached first second outside outsideControl outsideEq
    (actionsEq ▸ initial_actions_recalled first second inside insideControl reached insideEq)

/-- The competing-packet state is reached from actual setup and the prescribed
service schedule, including its public grant and environment recall. -/
theorem contested_reachable :
    ∃ history : arena.History, history.state = some (secondControl first second) ∧
      (secondControl first second).execution = contested ∧
      runtime.nativeActor history.state = some () :=
  ⟨secondHistory first second, rfl, rfl, rfl⟩

/-- From this initialized prefix the last owner call is immediately followed
by the fixed wire policy, before the reserved latest-message inclusion. -/
theorem remaining_schedule : (secondControl first second).plan =
    [.player (), .wire, .includeLatest 0 (), .sample 0,
      .grant 1, .player (), .player (), .player (), .wire, .includeLatest 1 (), .sample 1,
      .tick, .expire 0, .expire 1] := rfl

/-- The selection law is the actual wire instruction, with all native actions
allowed in the immediately preceding owner invocation. -/
theorem wire_selects_binding (action : PlayerAction graph)
    (joint : Unit → Option (PlayerAction graph)) :
    (runtime.nativeInstructionStep wire .wire (afterAction action) joint).map
      (fun next => next.native.application.config.outputs 0) =
        FinDist.pure (some (.success (selectedValue action))) := by
  simp only [nativeInstructionStep, serviceStep, MessageApplication.invoke,
    MessageApplication.wireEnvironment, wire, FinDist.map_pure, FinDist.pure_bind,
    WireCommand.toEnvironmentCommand, MessageApplication.environmentPolicyStep,
    MessageApplication.advance, MessageApplication.EnvironmentPolicyCommand.toAction,
    MessageApplication.step]
  exact congrArg FinDist.pure (selected_binding action)

private theorem publication_matches_binding (config : graph.Config)
    (reachable : config.Reachable input) (value : Int)
    (published : config.outputs 1 = some (.success value)) :
    config.outputs 0 = some (.success value) := by
  classical
  induction reachable with
  | initial => cases published
  | @step before prior event ready action next supported ih =>
      fin_cases event
      · rw [EventGraph.Config.step, FinDist.support_map] at supported
        obtain ⟨result, _, rfl⟩ := supported
        have earlier : before.outputs 1 = some (.success value) := by
          change (before.complete 0 ready action result).outputs 1 = _ at published
          rw [EventGraph.Config.complete_output_of_ne _ 0 1 ready action result
            (by decide)] at published
          exact published
        have stored := ih earlier
        have present : 0 ∈ before.cut.completed :=
          (before.output_available 0).mp (by simp only [stored, Option.isSome_some])
        exact False.elim (ready.1 present)
      · have available : (before.outputs 0).isSome :=
          (before.output_available 0).mpr (ready.2 (by simp [order]))
        obtain ⟨bound, boundEq⟩ := Option.isSome_iff_exists.mp available
        have evaluates : (graph.nodes 1).eval? action before.store =
            some (FinDist.pure (if action = true then bound else .failure)) := by
          change (EventGraph.EventCode.resolve (layout := layout) () .int binding []).eval?
            action before.store = _
          cases action <;> cases bound <;>
            simp [EventGraph.EventCode.eval?, EventGraph.EventCode.resolveOutput?,
              EventGraph.FieldRef.get?, EventGraph.Config.store, boundEq,
              EventGraph.GuardCheck.allAccepted?]
        change next ∈ (before.step 1 ready action).support at supported
        rw [before.step_eq_map_of_eval 1 ready action _ evaluates, FinDist.map_pure,
          FinDist.mem_support_pure] at supported
        subst next
        rw [EventGraph.Config.complete_output_same] at published
        by_cases opens : action = true
        · rw [ite_eq_left opens] at published ⊢
          have boundValue := Option.some.inj published
          rw [EventGraph.Config.complete_output_of_ne _ 1 0 ready action bound (by decide),
            boundEq, boundValue]
        · rw [ite_eq_right opens] at published
          cases published

private theorem afterAction_invariant (action : PlayerAction graph) :
    (afterAction action).native.application.Invariant input := by
  have initialInvariant : initial.native.application.Invariant input :=
    (State.initial_invariant input).copy rfl rfl rfl
  have firstInvariant := (runtime.nativeStep_progress input () initial _ first initialInvariant
    (FinDist.mem_support_pure.mpr rfl)).invariant
  have secondInvariant := (runtime.nativeStep_progress input () _ _ second firstInvariant
    (FinDist.mem_support_pure.mpr rfl)).invariant
  exact (runtime.nativeStep_progress input () _ _ action secondInvariant
    (FinDist.mem_support_pure.mpr rfl)).invariant

private def included (action : PlayerAction graph) : app.State :=
  app.includePending (afterAction action).native ((), selected action)

private theorem included_invariant (action : PlayerAction graph) :
    (included action).application.Invariant input :=
  runtime.applicationStep_invariant _ _ (.include ((), selected action))
    (afterAction_invariant action) (FinDist.mem_support_pure.mpr rfl)

/-- Every later native trace can publish only the selected earlier value or
failure. Pending, replayed, fresh, and malformed packets cannot recover zero.
The result also allows an unfinished publication at an intermediate endpoint. -/
theorem public_results_restricted (action : PlayerAction graph)
    (actions : List app.Action) (final : app.State)
    (reached : final ∈ (app.run actions (included action)).support) :
    final.application.config.outputs 1 = none ∨
      final.application.config.outputs 1 = some .failure ∨
      final.application.config.outputs 1 = some (.success 1) ∨
      final.application.config.outputs 1 = some (.success 2) := by
  have invariant := runtime.applicationRun_invariant _ _ actions
    (included_invariant action) reached
  have stored := runtime.applicationRun_store_of_some _ _ actions reached
    (.inr 0) (.success (selectedValue action)) (selected_binding action)
  cases published : final.application.config.outputs 1 with
  | none => exact Or.inl rfl
  | some result =>
      cases result with
      | failure => exact Or.inr (Or.inl rfl)
      | success value =>
          have bindingEq := publication_matches_binding _ invariant.reachable value published
          change final.application.config.outputs 0 =
            some (.success (selectedValue action)) at stored
          have valueEq := PublicationResult.success.inj
            (Option.some.inj (bindingEq.symm.trans stored))
          rw [valueEq]
          unfold selectedValue
          split
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr rfl))

/-- A fresh value is unavailable as a public result throughout the residual
game, not merely at the wire's first inclusion. -/
theorem zero_unreachable (action : PlayerAction graph)
    (actions : List app.Action) (final : app.State)
    (reached : final ∈ (app.run actions (included action)).support) :
    final.application.config.outputs 1 ≠ some (.success 0) := by
  rcases public_results_restricted action actions final reached with
    absent | failure | one | two
  · simp [absent]
  · simp [failure]
  · intro same
    have values : (1 : Int) = 0 :=
      PublicationResult.success.inj (Option.some.inj (one.symm.trans same))
    norm_num at values
  · intro same
    have values : (2 : Int) = 0 :=
      PublicationResult.success.inj (Option.some.inj (two.symm.trans same))
    norm_num at values

private def publicUtility (preferOne : Bool) : Option (PublicationResult Int) → ℝ
  | some (.success value) =>
      if value = 0 then 3 else
        if value = 1 then (if preferOne then 2 else 1) else
          if value = 2 then (if preferOne then 1 else 2) else 0
  | _ => 0

/-- The two tests agree on the missing best public result and disagree on the
remaining successes. Failure earns zero in both. -/
theorem residual_utility_sum_le (action : PlayerAction graph)
    (actions : List app.Action) (final : app.State)
    (reached : final ∈ (app.run actions (included action)).support) :
    publicUtility true (final.application.config.outputs 1) +
      publicUtility false (final.application.config.outputs 1) ≤ 3 := by
  rcases public_results_restricted action actions final reached with
    absent | failure | one | two
  all_goals norm_num [publicUtility, *]

/-- Randomizing the final action and all later behavior cannot supply a law
with value at least two for both public utilities. This is the numerical
obstruction; converting it into a native SPE impossibility also requires
information-local deviations attaining the two benchmarks. -/
theorem no_common_residual_law (law : FinDist app.State)
    (supported : ∀ final ∈ law.support, ∃ action actions,
      final ∈ (app.run actions (included action)).support) :
    ¬ (2 ≤ law.expect (fun final => publicUtility true (final.application.config.outputs 1)) ∧
      2 ≤ law.expect (fun final => publicUtility false (final.application.config.outputs 1))) := by
  intro both
  have sumBound : law.expect (fun final =>
      publicUtility true (final.application.config.outputs 1) +
        publicUtility false (final.application.config.outputs 1)) ≤ 3 := by
    apply FinDist.expect_le_of_forall
    intro final member
    obtain ⟨action, actions, reached⟩ := supported final member
    exact residual_utility_sum_le action actions final reached
  rw [FinDist.expect_add] at sumBound
  linarith [both.1, both.2]

end VegasTests.PendingMenus
