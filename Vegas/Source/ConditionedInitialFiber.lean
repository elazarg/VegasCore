/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ConditionedInitialHistory
import Vegas.Source.IntendedPlay

/-! # The actual component image of conditioned source histories -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  {Signal : Type*} (signal : State L setup.context → Signal) (value : Signal)

/-- A post-initial source state retains a draw in the specified component.
The unsampled root belongs to every component's history image. -/
def initialComponent : setup.ProtocolState → Prop
  | none => True
  | some point => signal (ProtocolState.base setup.program point) = value

/-- Every initialized intended history retains one of the actual supported
initial draws in its original context cells. -/
theorem intended_trace_initialSupport
    (setup : Setup (Player := Player) (L := L)) :
    ∀ {state : setup.ProtocolState} (_trace : setup.intendedProtocol.Trace state)
      (point : SourceProgram.ProtocolState setup.program), state = some point →
      ProtocolState.base setup.program point ∈ setup.initialLaw.support
  | _, .start, _, same => by cases same
  | _, .extend (source := none) _ joint _ realized, point, same => by
      change _ ∈ (setup.protocolStep none joint).support at realized
      rw [same] at realized
      change some point ∈ (setup.initialLaw.map _).support at realized
      obtain ⟨initial, present, entry⟩ := (PMF.mem_support_map_iff _ _ _).mp realized
      have pointEq := Option.some.inj entry
      rw [← pointEq, ProtocolState.base_entry]
      exact present
  | _, .extend (source := some before) prior joint _ realized, point, same => by
      have present := setup.intended_trace_initialSupport prior before rfl
      change _ ∈ ((ProtocolState.step setup.program before joint).map some).support at realized
      rw [same] at realized
      obtain ⟨after, step, equality⟩ := (PMF.mem_support_map_iff _ _ _).mp realized
      rw [← Option.some.inj equality, ProtocolState.base_step setup.program before joint after step]
      exact present

theorem initialComponent_of_protocolStep
    {before after : setup.ProtocolState} {joint : Player → Option (OwnAction Player L)}
    (reached : after ∈ (setup.protocolStep before joint).support)
    (inside : setup.initialComponent signal value after) :
    setup.initialComponent signal value before := by
  cases before with
  | none => trivial
  | some before =>
      change after ∈ ((ProtocolState.step setup.program before joint).map some).support at reached
      obtain ⟨after, step, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
      change signal (ProtocolState.base setup.program before) = value
      change signal (ProtocolState.base setup.program after) = value at inside
      rw [ProtocolState.base_step setup.program before joint after step] at inside
      exact inside

/-- A genuine source transition ending in the selected component remains
possible after conditioning the initializer. -/
theorem conditionInitial_protocolStep_of_component
    (supported : value ∈ (setup.initialLaw.map signal).support)
    {before after : setup.ProtocolState} {joint : Player → Option (OwnAction Player L)}
    (reached : after ∈ (setup.protocolStep before joint).support)
    (inside : setup.initialComponent signal value after) :
    after ∈ ((setup.conditionInitial signal value).protocolStep before joint).support := by
  cases before with
  | none =>
      change after ∈ (setup.initialLaw.map _).support at reached
      obtain ⟨initial, present, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
      change signal (ProtocolState.base setup.program
        (ProtocolState.entry setup.program (Config.initial initial))) = value at inside
      rw [ProtocolState.base_entry] at inside
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨initial, by
        change initial ∈ (fiberPosterior setup.initialLaw signal value).support
        rw [fiberPosterior_support setup.initialLaw signal value supported]
        exact ⟨inside, present⟩, rfl⟩
  | some before => exact reached

/-- Reconstruct a conditional intended trace from its actual component. -/
def conditionInitial_traceOfComponent
    (setup : Setup (Player := Player) (L := L)) {Signal : Type*}
    (signal : State L setup.context → Signal) (value : Signal)
    (supported : value ∈ (setup.initialLaw.map signal).support) :
    ∀ {state : setup.ProtocolState}, setup.intendedProtocol.Trace state →
      setup.initialComponent signal value state →
        (setup.conditionInitial signal value).intendedProtocol.Trace state
  | _, .start, _ => .start
  | _, .extend prior joint legal realized, inside =>
      .extend (setup.conditionInitial_traceOfComponent signal value supported prior
        (setup.initialComponent_of_protocolStep signal value realized inside)) joint legal
        (setup.conditionInitial_protocolStep_of_component signal value supported realized inside)

@[simp] theorem conditionInitial_trace_traceOfComponent
    (setup : Setup (Player := Player) (L := L)) {Signal : Type*}
    (signal : State L setup.context → Signal) (value : Signal)
    (supported : value ∈ (setup.initialLaw.map signal).support) :
    ∀ {state : setup.ProtocolState} (trace : setup.intendedProtocol.Trace state)
      (inside : setup.initialComponent signal value state),
      setup.conditionInitial_trace signal value supported
        (setup.conditionInitial_traceOfComponent signal value supported trace inside) = trace
  | _, .start, _ => rfl
  | _, .extend prior _ _ _, inside => by
      simp only [conditionInitial_traceOfComponent, conditionInitial_trace]
      rw [setup.conditionInitial_trace_traceOfComponent signal value supported prior]

/-- Reinterpret an actual history in the component under the conditioned law. -/
def conditionInitial_historyOfComponent
    (supported : value ∈ (setup.initialLaw.map signal).support)
    (history : setup.intendedProtocol.History)
    (inside : setup.initialComponent signal value history.state) :
    (setup.conditionInitial signal value).intendedProtocol.History :=
  ⟨history.state, setup.conditionInitial_traceOfComponent signal value supported
    history.trace inside⟩

@[simp] theorem conditionInitial_history_historyOfComponent
    (supported : value ∈ (setup.initialLaw.map signal).support)
    (history : setup.intendedProtocol.History)
    (inside : setup.initialComponent signal value history.state) :
    setup.conditionInitial_history signal value supported
        (setup.conditionInitial_historyOfComponent signal value supported history inside) =
      history := by
  cases history
  exact congrArg (History.mk _) (setup.conditionInitial_trace_traceOfComponent
    signal value supported _ inside)

/-- A conditional information history has the identical original source view. -/
def conditionInitial_informationHistory
    (supported : value ∈ (setup.initialLaw.map signal).support) (who : Player)
    (view : setup.ProtocolView who)
    (history : (setup.conditionInitial signal value).intendedModel.InformationHistory who view) :
    setup.intendedModel.InformationHistory who view :=
  ⟨setup.conditionInitial_history signal value supported history.1,
    (setup.conditionInitial_history_observed signal value supported history.1 who).trans
      history.2⟩

theorem conditionInitial_informationHistory_injective
    (supported : value ∈ (setup.initialLaw.map signal).support) (who : Player)
    (view : setup.ProtocolView who) :
    Function.Injective (setup.conditionInitial_informationHistory signal value supported who
      view) := by
  intro first second same
  apply Subtype.ext
  exact setup.conditionInitial_history_injective signal value supported
    (congrArg Subtype.val same)

/-- If a whole actual information fiber determines this component, its
conditional history map is onto that fiber. This states the exact source
information obligation for a locally recoverable common signal. -/
theorem conditionInitial_informationHistory_surjective
    (supported : value ∈ (setup.initialLaw.map signal).support) (who : Player)
    (view : setup.ProtocolView who)
    (inside : ∀ history : setup.intendedModel.InformationHistory who view,
      setup.initialComponent signal value history.1.state) :
    Function.Surjective (setup.conditionInitial_informationHistory signal value supported who
      view) := by
  intro history
  let restored := setup.conditionInitial_historyOfComponent signal value supported history.1
    (inside history)
  have observed := setup.conditionInitial_history_observed signal value supported restored who
  have mapped : setup.conditionInitial_history signal value supported restored = history.1 :=
    setup.conditionInitial_history_historyOfComponent signal value supported history.1
      (inside history)
  rw [mapped] at observed
  refine ⟨⟨restored, observed.symm.trans history.2⟩, ?_⟩
  exact Subtype.ext mapped

end Vegas.SourceProgram.Setup
