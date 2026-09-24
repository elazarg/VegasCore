/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SequentialValidationNative
import Vegas.Pending.ReactiveOpeningEvidence
import Vegas.Pending.ReactiveStateInvariant
import Interaction.ReactiveResponseMenu

/-! # An accepted opening identifies the type throughout an information set

The initial law correlates Alice's private input with her initial commitment.
Both remain immutable. A public validated opening therefore identifies that
input at every compatible legal history, for arbitrary scheduling, passive
observations and response menus. No belief-selection assumption is used.
-/

noncomputable section

namespace VegasTests.SequentialValidation

open Vegas Vegas.EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

def typeInput : nativeGraph.InputId := ⟨0, by decide⟩

def nativeInitialLaw : FinDist (State nativeGraph) :=
  (FinDist.uniformOfFintype (α := Bool)).map nativeStart

variable (leaks : MessageNetwork.ObservationRule Bool (Payload nativeGraph))

def nativeTypeEvidence (execution : (nativeRuntime.reactiveApplication leaks).Execution) : Prop :=
  ∃ bit : Bool,
    execution.application.config.store (.inl typeInput) = some bit ∧
    execution.application.candidates.lookup (false, .initial secretInput) =
      .openable ⟨.bool, bit⟩ ∧
    execution.ReceiptsSound (nativeRuntime.reactiveApplication leaks)
      (Payload.Authenticates (false, .initial secretInput) ⟨.bool, bit⟩)

theorem native_type_evidence_invariant
    (scheduler : (nativeRuntime.reactiveApplication leaks).Scheduler) :
    (nativeRuntime.reactiveApplication leaks).ServiceInvariant scheduler
      (nativeTypeEvidence leaks) where
  respond execution who action valid := by
    obtain ⟨bit, stored, fixed, sound⟩ := valid
    have retained := (nativeRuntime.reactiveStoreInvariant leaks (.inl typeInput) bit).respond
      execution who action stored
    have evidence := (nativeRuntime.reactiveOpeningEvidence leaks
      (false, .initial secretInput) ⟨.bool, bit⟩ scheduler).respond
        execution who action ⟨fixed, sound⟩
    exact ⟨bit, retained, evidence⟩
  environment execution next command valid selected reached := by
    obtain ⟨bit, stored, fixed, sound⟩ := valid
    have retained := (nativeRuntime.reactiveStoreInvariant leaks (.inl typeInput) bit)
      |>.environmentStep execution next command stored reached
    have evidence := (nativeRuntime.reactiveOpeningEvidence leaks
      (false, .initial secretInput) ⟨.bool, bit⟩ scheduler).environment
        execution next command ⟨fixed, sound⟩ selected reached
    exact ⟨bit, retained, evidence⟩

theorem native_type_evidence_initial (state : State nativeGraph)
    (supported : state ∈ nativeInitialLaw.support) :
    nativeTypeEvidence leaks
      (.initial (nativeRuntime.reactiveApplication leaks) state) := by
  obtain ⟨bit, _, rfl⟩ := FinDist.support_map .. ▸ supported
  refine ⟨bit, rfl, ?_, List.Forall₂.nil⟩
  change (nativeStart bit).candidates.lookup (false, .initial secretInput) = _
  cases bit <;> rfl

theorem native_type_evidence_history (horizon : Nat)
    (scheduler : (nativeRuntime.reactiveApplication leaks).Scheduler)
    (control : (nativeRuntime.reactiveApplication leaks).Control)
    (trace : ((nativeRuntime.reactiveApplication leaks).protocol
      nativeInitialLaw horizon scheduler).Trace (some control)) :
    nativeTypeEvidence leaks control.execution :=
  (native_type_evidence_invariant leaks scheduler).history nativeInitialLaw horizon
    (native_type_evidence_initial leaks) trace

/-- Knowledge is forced by public evidence, including at off-path histories. -/
theorem native_observed_type (horizon : Nat)
    (scheduler : (nativeRuntime.reactiveApplication leaks).Scheduler)
    (control : (nativeRuntime.reactiveApplication leaks).Control)
    (trace : ((nativeRuntime.reactiveApplication leaks).protocol
      nativeInitialLaw horizon scheduler).Trace (some control))
    (who bit : Bool)
    (observed : nativeRuntime.openingObserved leaks
      (control.execution.observe (nativeRuntime.reactiveApplication leaks) who)
      (false, .initial secretInput) ⟨.bool, bit⟩) :
    control.execution.application.config.store (.inl typeInput) = some bit := by
  obtain ⟨actual, stored, _, sound⟩ :=
    native_type_evidence_history leaks horizon scheduler control trace
  have same := nativeRuntime.observed_opening_eq leaks control.execution who
    (false, .initial secretInput) ⟨.bool, actual⟩ ⟨.bool, bit⟩ sound observed
  have equal := congrArg (fun raw : Raw simpleExpr => raw.as? .bool) same
  simp only [Raw.as?_mk, Option.some.injEq] at equal
  exact equal.symm ▸ stored

def nativeStoredType : (nativeRuntime.reactiveApplication leaks).ProtocolState → Option Bool
  | none => none
  | some control => control.execution.application.config.store (.inl typeInput)

/-- Every history in this information fiber has the disclosed original type.
The finite menu may contain arbitrary malformed and replay responses. -/
theorem native_information_type
    (menu : (nativeRuntime.reactiveApplication leaks).ResponseMenu) (horizon : Nat)
    (scheduler : (nativeRuntime.reactiveApplication leaks).Scheduler)
    (who bit : Bool) (past : List (nativeRuntime.reactiveApplication leaks).PlayerEntry)
    (view : (nativeRuntime.reactiveApplication leaks).PlayerView)
    (observed : nativeRuntime.openingObserved leaks view
      (false, .initial secretInput) ⟨.bool, bit⟩)
    (history : (menu.information nativeInitialLaw horizon scheduler).InformationHistory
      who (some (past, view))) :
    nativeStoredType leaks history.1.state = some bit := by
  rcases history with ⟨⟨state, trace⟩, equal⟩
  change (menu.signals nativeInitialLaw horizon scheduler).infoOf who trace =
    some (past, view) at equal
  rw [ReactiveApplication.ResponseMenu.info] at equal
  cases state with
  | none => cases equal
  | some control =>
      change (if control.actor = some who then
        some (control.execution.recall who,
          control.execution.observe (nativeRuntime.reactiveApplication leaks) who)
        else none) = some (past, view) at equal
      split at equal
      · have sameView := congrArg Prod.snd (Option.some.inj equal)
        change control.execution.observe (nativeRuntime.reactiveApplication leaks) who = view
          at sameView
        apply native_observed_type leaks horizon scheduler control
          (menu.toRawTrace nativeInitialLaw horizon scheduler trace) who bit
        exact sameView.symm ▸ observed
      · cases equal

/-- Even utility-dependent beliefs cannot put weight on another private type. -/
theorem native_belief_type
    (menu : (nativeRuntime.reactiveApplication leaks).ResponseMenu) (horizon : Nat)
    (scheduler : (nativeRuntime.reactiveApplication leaks).Scheduler)
    (who bit : Bool) (past : List (nativeRuntime.reactiveApplication leaks).PlayerEntry)
    (view : (nativeRuntime.reactiveApplication leaks).PlayerView)
    (observed : nativeRuntime.openingObserved leaks view
      (false, .initial secretInput) ⟨.bool, bit⟩)
    (belief : FinDist ((menu.information nativeInitialLaw horizon scheduler).InformationHistory
      who (some (past, view)))) :
    belief.map (fun history => nativeStoredType leaks history.1.state) =
      FinDist.pure (some bit) := by
  calc
    _ = belief.map (fun _ => some bit) := by
      apply FinDist.map_congr_of_eq_on_support
      intro history _
      exact native_information_type leaks menu horizon scheduler who bit past view observed history
    _ = _ := FinDist.map_const _ _

end VegasTests.SequentialValidation
