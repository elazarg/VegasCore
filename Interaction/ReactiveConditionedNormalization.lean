module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Interaction.ReactiveConditionedMenu
public import Interaction.ReactiveMenuRestriction
public import Interaction.ReactiveNormalHistory

@[expose] public section

/-! # Normalizing menu histories under restriction of initial support -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol.ExecutionProtocol

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  {restricted initial : PMF app.State} {horizon : Nat} {scheduler : app.Scheduler}

namespace SubmissionNormalization

/-- Enlarging the initial support commutes with normalization of a legal trace. -/
theorem traceOfInitialSupportSubset_trace
    (normal : app.SubmissionNormalization) (raw : app.ResponseMenu)
    (stable : ∀ who past view,
      raw.actions who (normal.logs who past) view = raw.actions who past view)
    (included : restricted.support ⊆ initial.support) {state}
    (trace : (raw.protocol restricted horizon scheduler).Trace state) :
    (normal.menu raw).traceOfInitialSupportSubset included
        (normal.trace raw stable restricted horizon scheduler trace) =
      normal.trace raw stable initial horizon scheduler
        (raw.traceOfInitialSupportSubset included trace) := by
  induction trace with
  | start => rfl
  | extend prior joint legal realized ih =>
    simp only [ResponseMenu.traceOfInitialSupportSubset, trace, ih]

end SubmissionNormalization

namespace ResponseMenu.IncludedIn

/-- A trace legal under the smaller menu remains legal under that menu when its
initialization comes from a restricted prior. -/
theorem trace_of_initialSupportSubset
    {smaller larger : app.ResponseMenu} (included : smaller.IncludedIn larger)
    (support : restricted.support ⊆ initial.support) :
    ∀ {state : app.ProtocolState}
      (full : (smaller.protocol initial horizon scheduler).Trace state)
      (part : (larger.protocol restricted horizon scheduler).Trace state),
    larger.traceOfInitialSupportSubset support part =
      included.trace initial horizon scheduler full →
    ∃ localTrace : (smaller.protocol restricted horizon scheduler).Trace state,
      included.trace restricted horizon scheduler localTrace = part
  | _, .start, .start, _ => ⟨.start, rfl⟩
  | _, .start, .extend _ _ _ _, same => by cases same
  | _, .extend _ _ _ _, .start, same => by cases same
  | _, .extend prior joint legal _, .extend prior' joint' legal' realized', same => by
      simp only [ResponseMenu.traceOfInitialSupportSubset, trace, restrictAvailable.trace,
        Trace.extend.injEq] at same
      obtain ⟨rfl, same, actions⟩ := same
      cases actions
      obtain ⟨localTrace, h⟩ := trace_of_initialSupportSubset included support prior prior'
        (eq_of_heq same)
      exact ⟨.extend localTrace joint legal realized', by
        simp only [trace, restrictAvailable.trace, ← h]⟩

end ResponseMenu.IncludedIn

namespace SubmissionNormalization

/-- If a global raw history normalizes to a trace under the smaller menu, its
restriction to any valid initial component has the same smaller-menu representation. -/
theorem history_of_initialSupportSubset
    (normal : app.SubmissionNormalization) (raw smaller : app.ResponseMenu)
    (stable : ∀ who past view,
      raw.actions who (normal.logs who past) view = raw.actions who past view)
    (included : smaller.IncludedIn (normal.menu raw))
    (support : restricted.support ⊆ initial.support)
    (localRaw : (raw.protocol restricted horizon scheduler).History)
    (globalSmall : (smaller.protocol initial horizon scheduler).History)
    (same : normal.history raw stable initial horizon scheduler
      (raw.historyOfInitialSupportSubset support localRaw) =
      included.history initial horizon scheduler globalSmall) :
    ∃ localSmall : (smaller.protocol restricted horizon scheduler).History,
      localSmall.state = globalSmall.state ∧
      normal.history raw stable restricted horizon scheduler localRaw =
        included.history restricted horizon scheduler localSmall := by
  obtain ⟨state, rawTrace⟩ := localRaw
  obtain ⟨smallState, smallTrace⟩ := globalSmall
  have stateEq := congrArg History.state same
  change normal.state state = smallState at stateEq
  subst smallState
  have traceEq := eq_of_heq (History.mk.inj same).2
  have lifted := normal.traceOfInitialSupportSubset_trace raw stable support rawTrace
  obtain ⟨localTrace, matched⟩ :=
    included.trace_of_initialSupportSubset support smallTrace _ (lifted.trans traceEq)
  exact ⟨⟨_, localTrace⟩, rfl, congrArg (History.mk _) matched.symm⟩

end SubmissionNormalization

end Interaction.ReactiveApplication
