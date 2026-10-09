/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceFirstFiber

/-! # Exact native sender information at the protected callback

Initialization and the first activation fix the entire physical execution.
The sender sees both its bit and its private label. Silence at this callback
passes through the two passive commands to the original first late response,
retaining every later player policy.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceProtectedFiber

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLatePrefix
  LateOpeningRuntimeInitializedPrefix

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

/-- Every legal initial sender activation is an initialized execution. -/
theorem protected_normal_form (execution : app.Execution)
    (trace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨25, some alice, execution⟩)) :
    ∃ bit label, execution = protectedDecision bit label := by
  have reachable := rawMenu.roundSupported_uniform initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) trace
  obtain ⟨accounted, count, prior, command, cursor, reached, selected, _, moved⟩ := reachable
  change execution.environmentRecall.length + 25 = 26 at accounted
  change execution.environmentRecall.length = count + 1 at cursor
  have countEq : count = 0 := by omega
  subst count
  obtain ⟨state, initialized, pureReached⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
  cases (PMF.mem_support_pure_iff _ _).mp pureReached
  change state ∈ (setup.initialLaw.map fun source =>
    State.initial (graph := nativeGraph) (setup.eventInputs source)).support at initialized
  obtain ⟨source, sourceSupported, rfl⟩ := PMF.support_map .. ▸ initialized
  obtain ⟨bit, label, rfl⟩ := (initialLaw_support source).mp sourceSupported
  change command ∈ (PMF.pure (.activate alice : app.Command)).support at selected
  cases (PMF.mem_support_pure_iff _ _).mp selected
  change execution ∈ ((initialExecution bit label).environmentStep app (.activate alice)).support
    at moved
  rw [recorded_activation (initialExecution bit label) alice (by rfl)] at moved
  exact ⟨bit, label, (PMF.mem_support_pure_iff _ _).mp moved⟩

theorem protected_view_injective : Function.Injective
    (fun parameter : Parameter =>
      (protectedDecision parameter.1 parameter.2).observe app alice) := by
  rintro ⟨bit, label⟩ ⟨otherBit, otherLabel⟩ same
  have bits := congrArg (fun view : app.PlayerView =>
    view.application.candidates (.initial LateOpeningRuntimeReadout.aliceInput)) same
  have sameBit : bit = otherBit := by
    change CommitmentCandidate.openable (⟨.bool, bit⟩ : Raw simpleExpr) =
      .openable ⟨.bool, otherBit⟩ at bits
    have raw := CommitmentCandidate.openable.inj bits
    have decoded := congrArg (fun value : Raw simpleExpr => value.as? .bool) raw
    simpa only [Raw.as?_mk, Option.some.injEq] using decoded
  have labels := congrArg (fun view : app.PlayerView =>
    view.application.observation.store (.inl LateOpeningRuntimeReadout.labelInput)) same
  have sameLabel : label = otherLabel := by
    change some (labelValue label) = some (labelValue otherLabel) at labels
    have values := congrArg (fun value : Label => value.val) (Option.some.inj labels)
    apply Fin.ext
    change (label.val : Int) = (otherLabel.val : Int) at values
    exact_mod_cast values
  exact Prod.ext sameBit sameLabel

private theorem protected_cursor (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (active : control.actor = some alice) (clock : control.execution.application.clock = 0) :
    control.remaining = 25 := by
  have cursor := active_cursor weight nonnegative control trace alice active
  have displayed := clock_history weight nonnegative control trace
  rw [clock] at displayed
  rcases cursor with ⟨_, positions⟩ | ⟨impossible, _⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at positions
    rcases positions with position | position | position
    · have accounted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) trace
      change control.execution.environmentRecall.length + control.remaining = 26 at accounted
      omega
    · rw [position] at displayed
      exact ((by decide : (0 : Nat) ≠ LateOpeningRuntimeService.clockAt 4) displayed).elim
    · rw [position] at displayed
      exact ((by decide : (0 : Nat) ≠ LateOpeningRuntimeService.clockAt 8) displayed).elim
  · cases impossible

/-- The protected information class has no hidden physical or setup state
uncertainty, including when it is unreached in the assessed strategy. -/
theorem information_history_state
    (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice)
    (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      alice site.1) (bit : Bool) (label : Fin 3)
    (current : representative.1.state = some ⟨25, some alice, protectedDecision bit label⟩)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory alice site.1) :
    history.1.state = some ⟨25, some alice, protectedDecision bit label⟩ := by
  have active := InformationModel.InformationSite.active _ site history
  obtain ⟨control, stateEq, actor⟩ := app.control_of_active initial
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      (rawMenu.toRawHistory _ _ _ history.1) alice active
  change history.1.state = some control at stateEq
  have rawTrace := stateEq ▸ rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) history.1.trace
  have information := representative.2.trans history.2.symm
  change (rawMenu.signals _ _ _).infoOf alice representative.1.trace =
    (rawMenu.signals _ _ _).infoOf alice history.1.trace at information
  rw [rawMenu.info, rawMenu.info] at information
  change app.observe alice representative.1.state = app.observe alice history.1.state at information
  rw [current, stateEq] at information
  simp only [ReactiveApplication.observe, actor, ↓reduceIte] at information
  have sameView := congrArg Prod.snd (Option.some.inj information)
  change (protectedDecision bit label).observe app alice = control.execution.observe app alice
    at sameView
  have clock : control.execution.application.clock = 0 := by
    have sameClock := congrArg (fun view : app.PlayerView =>
      view.application.publicView.clock) sameView
    exact sameClock.symm
  have remaining := protected_cursor weight nonnegative control rawTrace actor clock
  have sameControl : control = ⟨25, some alice, control.execution⟩ := by
    cases control
    simp only [ReactiveApplication.Control.mk.injEq] at actor remaining ⊢
    exact ⟨remaining, actor, trivial⟩
  have trace := stateEq ▸ history.1.trace
  obtain ⟨otherBit, otherLabel, normal⟩ := protected_normal_form weight nonnegative
    control.execution (sameControl ▸ trace)
  rw [normal] at sameView
  have parameters := @protected_view_injective (bit, label) (otherBit, otherLabel) sameView
  cases parameters
  exact stateEq.trans (congrArg some (sameControl.trans
    (congrArg (fun execution => (⟨25, some alice, execution⟩ : app.Control)) normal)))

/-- Protected silence retains the original first late response and its
whole continuation; neither player's future policy is replaced. -/
theorem protected_none_suffix (players : Player → app.Policy) (bit : Bool) (label : Fin 3) :
    app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 25
      ((protectedDecision bit label).respond app alice ⟨none⟩) =
      (players alice ((firstLateDecision bit label).recall alice)
        ((firstLateDecision bit label).observe app alice)).bind fun response =>
          app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 22
            ((firstLateDecision bit label).respond app alice response) := by
  let silent := protectedSilent bit label
  let waited := recorded silent .wait silent.application
  let ticked := recorded waited (.application .advanceClock)
    { waited.application with clock := waited.application.clock + 1 }
  have first : app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      players silent = PMF.pure waited := by
    rw [fixed_round weight nonnegative players silent waited 1 .wait rfl rfl
      (recorded_wait silent)]
    rfl
  have second : app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      players waited = PMF.pure ticked := by
    rw [fixed_round weight nonnegative players waited ticked 2
      (.application .advanceClock) rfl rfl (recorded_clock waited)]
    rfl
  have third : app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      players ticked = app.invoke players alice (firstLateDecision bit label) := by
    rw [fixed_round weight nonnegative players ticked (firstLateDecision bit label) 3
      (.activate alice) rfl rfl (recorded_activation ticked alice (by rfl))]
    rfl
  change app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 25
    silent = _
  rw [ReactiveApplication.runRounds, first, PMF.pure_bind,
    ReactiveApplication.runRounds, second, PMF.pure_bind,
    ReactiveApplication.runRounds, third, ReactiveApplication.invoke, PMF.bind_map]
  rfl

end Vegas.Examples.LateOpeningRuntimeAliceProtectedFiber
