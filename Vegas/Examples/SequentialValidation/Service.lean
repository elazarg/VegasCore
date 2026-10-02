/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.SequentialValidation.Evidence
import Vegas.Pending.ReactiveFiniteResponses
import Interaction.ReactiveCalendar

/-! # A finite native service for the disclosure witness

Each of the four events has one owner response and an authorized uniform
inclusion opportunity. All four windows precede clock advancement.
A final sequence of ten ticks and expiry for each event supplies timeouts.
The wire bounds retain every packet form, wrong-typed data and authentic certificate forwarding.
-/

noncomputable section

namespace Vegas.Examples.SequentialValidation

open Vegas Vegas.EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

def nativeLeaks : MessageNetwork.ObservationRule Bool (WitnessedPacket nativeGraph) :=
  fun _ _ => PMF.pure ∅

abbrev nativeApp := nativeRuntime.reactiveApplication nativeLeaks

def nativeBounds : MessageBounds nativeGraph := by
  classical
  exact ⟨56, {⟨.bool, false⟩, ⟨.bool, true⟩, ⟨.int, 0⟩, ⟨.int, 1⟩}⟩

abbrev nativeMenu := nativeBounds.menu nativeRuntime nativeLeaks

def nativeCalendar : Nat → nativeApp.UniformInstruction
  | 0 => .activate false
  | 1 => .select (eventProposal bindingEvent false)
  | 2 => .activate false
  | 3 => .select (eventProposal dummyEvent false)
  | 4 => .activate false
  | 5 => .select (eventProposal secretEvent false)
  | 6 => .activate true
  | 7 => .select (eventProposal guessEvent true)
  | 18 => .application (.expire bindingEvent)
  | 29 => .application (.expire dummyEvent)
  | 40 => .application (.expire secretEvent)
  | 51 => .application (.expire guessEvent)
  | index => if index < 52 then .application .advanceClock else .wait

def nativeScheduler : nativeApp.Scheduler :=
  nativeRuntime.dependencyUniformScheduler nativeLeaks nativeCalendar

abbrev nativeArena := nativeMenu.protocol nativeInitialLaw 52 nativeScheduler
abbrev nativeModel := nativeMenu.information nativeInitialLaw 52 nativeScheduler

theorem native_service_authorized :
    nativeRuntime.DependencyAuthorized nativeLeaks nativeInitialLaw 52 nativeScheduler :=
  nativeRuntime.dependencyUniformScheduler_authorized nativeLeaks _ _ nativeCalendar

theorem native_service_once : nativeApp.AtMostOnce nativeScheduler :=
  nativeRuntime.dependencyUniformScheduler_atMostOnce nativeLeaks nativeCalendar

theorem native_unique_bob_activation (history : List nativeApp.EnvironmentEntry)
    (view : nativeApp.EnvironmentView) (command : nativeApp.Command)
    (supported : command ∈ (nativeScheduler history view).support)
    (active : command.actor? nativeApp = some true) : history.length = 6 := by
  have instruction := nativeApp.uniformInstruction_actor dependencyCondition history view
    (nativeCalendar history.length) command true supported active
  unfold nativeCalendar at instruction
  split at instruction <;> simp_all
  split at instruction <;> cases instruction

theorem native_bob_remaining (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control)) (active : control.actor = some true) :
    control.execution.environmentRecall.length = 7 ∧ control.remaining = 45 := by
  have accounted := nativeApp.remaining_at_activation nativeInitialLaw 52 nativeScheduler true 6
    native_unique_bob_activation control
      (nativeMenu.toRawTrace nativeInitialLaw 52 nativeScheduler trace) active
  exact ⟨accounted.1, by omega⟩

theorem nativeAntichain : nativeModel.DecisionInformationAntichain :=
  nativeMenu.decisionInformationAntichain nativeInitialLaw 52 nativeScheduler

instance : nativeLeaks.FiniteSupport := ⟨fun _ _ => by simp [nativeLeaks]⟩

instance : nativeApp.FiniteNature nativeInitialLaw nativeScheduler where
  initial_finite := by
    rw [nativeInitialLaw, PMF.support_map]
    exact (Set.toFinite _).image _
  scheduler_finite _ _ := ReactiveApplication.uniformScheduler_support_finite _ _ _ _ _

instance : Finite nativeArena.History := inferInstance

end Vegas.Examples.SequentialValidation
