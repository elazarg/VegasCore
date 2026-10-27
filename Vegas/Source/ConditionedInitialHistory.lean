/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ConditionedInitialLaw

/-! # Injectivity of conditional source history transport -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Every source transition leaves the unsampled root permanently. -/
theorem protocolStep_not_none (setup : Setup (Player := Player) (L := L))
    (state : setup.ProtocolState) (joint : Player → Option (OwnAction Player L)) :
    none ∉ (setup.protocolStep state joint).support := by
  cases state <;> simp [protocolStep, PMF.support_map]

theorem intended_trace_none (setup : Setup (Player := Player) (L := L)) :
    ∀ trace : setup.intendedProtocol.Trace none, trace = .start
  | .start => rfl
  | .extend _ joint _ realized =>
      False.elim (setup.protocolStep_not_none _ joint realized)

/-- A source history beyond the unsampled root has positive depth. -/
theorem intended_trace_positive
    (setup : Setup (Player := Player) (L := L)) :
    ∀ {state : setup.ProtocolState} (trace : setup.intendedProtocol.Trace state),
      state ≠ none → 0 < trace.length
  | _, .start, different => False.elim (different rfl)
  | _, .extend prior _ _ _, _ => Nat.zero_lt_succ prior.length

theorem conditionInitial_trace_injective
    (setup : Setup (Player := Player) (L := L)) {Signal : Type*}
    (signal : State L setup.context → Signal) (value : Signal)
    (supported : value ∈ (setup.initialLaw.map signal).support) :
    ∀ {state : setup.ProtocolState}
      (first second : (setup.conditionInitial signal value).intendedProtocol.Trace state),
      setup.conditionInitial_trace signal value supported first =
          setup.conditionInitial_trace signal value supported second → first = second
  | _, .start, .start, _ => rfl
  | _, .start, .extend _ _ _ _, same => nomatch same
  | _, .extend _ _ _ _, .start, same => nomatch same
  | _, .extend prior joint legal realized,
      .extend secondPrior secondJoint secondLegal secondRealized, same => by
      simp only [conditionInitial_trace] at same
      injection same with beforeEq jointEq priorEq
      cases beforeEq
      cases jointEq
      have samePrior := setup.conditionInitial_trace_injective signal value supported
        prior secondPrior (eq_of_heq priorEq)
      cases samePrior
      simp_all

theorem conditionInitial_history_injective
    (setup : Setup (Player := Player) (L := L)) {Signal : Type*}
    (signal : State L setup.context → Signal) (value : Signal)
    (supported : value ∈ (setup.initialLaw.map signal).support) :
    Function.Injective (setup.conditionInitial_history signal value supported) := by
  rintro ⟨firstState, first⟩ ⟨secondState, second⟩ same
  have states : firstState = secondState := congrArg (·.state) same
  cases states
  change History.mk _ (setup.conditionInitial_trace signal value supported first) =
    History.mk _ (setup.conditionInitial_trace signal value supported second) at same
  injection same with _ traces
  have sameTrace := setup.conditionInitial_trace_injective signal value supported first second
    traces
  cases sameTrace
  rfl

end Vegas.SourceProgram.Setup
