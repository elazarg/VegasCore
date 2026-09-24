/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SequentialValidationEvidence
import Vegas.Pending.ReactiveFiniteResponses
import Interaction.ReactiveCalendar

/-! # A finite native service for the disclosure witness

Each of the four events has a grant, one owner response and an authorized
uniform inclusion opportunity. All four windows precede clock advancement.
A final sequence of ten ticks and expiry for each event supplies timeouts.
The wire bounds retain every packet form, wrong-typed data and known replays.
-/

noncomputable section

namespace VegasTests.SequentialValidation

open Vegas Vegas.EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

def nativeLeaks : MessageNetwork.ObservationRule Bool (Payload nativeGraph) :=
  fun _ _ => FinDist.pure ∅

abbrev nativeApp := nativeRuntime.reactiveApplication nativeLeaks

def nativeBounds : MessageBounds nativeGraph := by
  classical
  exact ⟨56, {⟨.bool, false⟩, ⟨.bool, true⟩, ⟨.int, 0⟩, ⟨.int, 1⟩}⟩

abbrev nativeMenu := nativeBounds.menu nativeRuntime nativeLeaks

def nativeCalendar : Nat → nativeApp.UniformInstruction
  | 0 => .application (.grant bindingEvent)
  | 1 => .activate false
  | 2 => .select (eventProposal bindingEvent false)
  | 3 => .application (.grant dummyEvent)
  | 4 => .activate false
  | 5 => .select (eventProposal dummyEvent false)
  | 6 => .application (.grant secretEvent)
  | 7 => .activate false
  | 8 => .select (eventProposal secretEvent false)
  | 9 => .application (.grant guessEvent)
  | 10 => .activate true
  | 11 => .select (eventProposal guessEvent true)
  | 22 => .application (.expire bindingEvent)
  | 33 => .application (.expire dummyEvent)
  | 44 => .application (.expire secretEvent)
  | 55 => .application (.expire guessEvent)
  | index => if index < 56 then .application .advanceClock else .wait

def nativeScheduler : nativeApp.Scheduler :=
  nativeRuntime.dependencyUniformScheduler nativeLeaks nativeCalendar

abbrev nativeArena := nativeMenu.protocol nativeInitialLaw 56 nativeScheduler
abbrev nativeModel := nativeMenu.information nativeInitialLaw 56 nativeScheduler

theorem native_service_authorized :
    nativeRuntime.DependencyAuthorized nativeLeaks nativeInitialLaw 56 nativeScheduler :=
  nativeRuntime.dependencyUniformScheduler_authorized nativeLeaks _ _ nativeCalendar

theorem native_service_once : nativeApp.AtMostOnce nativeScheduler :=
  nativeRuntime.dependencyUniformScheduler_atMostOnce nativeLeaks nativeCalendar

theorem native_unique_bob_activation (history : List nativeApp.EnvironmentEntry)
    (view : nativeApp.EnvironmentView) (command : nativeApp.Command)
    (supported : command ∈ (nativeScheduler history view).support)
    (active : command.actor? nativeApp = some true) : history.length = 10 := by
  have instruction := nativeApp.uniformInstruction_actor dependencyCondition history view
    (nativeCalendar history.length) command true supported active
  unfold nativeCalendar at instruction
  split at instruction <;> simp_all
  split at instruction <;> cases instruction

theorem native_bob_remaining (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control)) (active : control.actor = some true) :
    control.execution.environmentRecall.length = 11 ∧ control.remaining = 45 := by
  have accounted := nativeApp.remaining_at_activation nativeInitialLaw 56 nativeScheduler true 10
    native_unique_bob_activation control
      (nativeMenu.toRawTrace nativeInitialLaw 56 nativeScheduler trace) active
  exact ⟨accounted.1, by omega⟩

theorem nativeAntichain : nativeModel.DecisionInformationAntichain :=
  nativeMenu.decisionInformationAntichain nativeInitialLaw 56 nativeScheduler

instance : Finite nativeArena.History := inferInstance

end VegasTests.SequentialValidation
