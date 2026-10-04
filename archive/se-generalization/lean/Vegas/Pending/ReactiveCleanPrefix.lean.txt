/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveRiskPersistence

/-! # Canonical traces before persistent service risk

A legal risk-menu prefix whose current persistent flags are clear for every
owner is the same full trace in the canonical menu. Backward persistence rules
exclude any earlier expanded response. A current unprotected opportunity need
not be clear: the prefix may stop before the response that records its risk.
This is a structural trace result, not a source or equilibrium embedding.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.MessageBounds

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (bounds : MessageBounds graph) (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (bound : graph.EventId → Nat)
  (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
  (scheduler : (runtime.reactiveApplication leaks).Scheduler)

private theorem risk_step_canonical_of_persistentClear
    (before after : (runtime.reactiveApplication leaks).ProtocolState)
    (joint : Player → Option (runtime.reactiveApplication leaks).Action)
    (legal : ((bounds.riskMenu runtime leaks bound).protocol initial horizon scheduler).Legal
      before joint)
    (realized : after ∈ ((runtime.reactiveApplication leaks).transition initial horizon scheduler
      before joint).support)
    (clear : ∀ control, after = some control → ∀ who,
      runtime.persistentServiceRisk leaks bound who (control.execution.recall who)
        (control.execution.observe (runtime.reactiveApplication leaks) who) = false) :
    (∀ control, before = some control → ∀ who,
      runtime.persistentServiceRisk leaks bound who (control.execution.recall who)
        (control.execution.observe (runtime.reactiveApplication leaks) who) = false) ∧
    ((bounds.canonicalMenu runtime leaks).protocol initial horizon scheduler).Legal
      before joint := by
  let app := runtime.reactiveApplication leaks
  cases before with
  | none =>
      constructor
      · intro _ impossible
        cases impossible
      · refine ⟨legal.1, ?_⟩
        intro who
        have member := legal.2 who
        cases chosen : joint who with
        | none => rw [chosen] at member; exact member
        | some response =>
            rw [chosen] at member
            exact ⟨member.1, member.2⟩
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some owner =>
          have selected := legal.2 owner
          cases chosen : joint owner with
          | none =>
              rw [chosen] at selected
              exact (selected rfl).elim
          | some response =>
              rw [chosen] at selected
              simp only [ReactiveApplication.transition, chosen, Option.getD_some,
                PMF.mem_support_pure_iff] at realized
              cases realized
              have afterClear := clear _ rfl
              have inputClear := runtime.serviceRisk_clear_before_respond leaks bound execution
                owner response (afterClear owner)
              refine ⟨?_, legal.1, ?_⟩
              · intro current same who
                cases Option.some.inj same
                exact runtime.persistentServiceRisk_clear_before_respond leaks bound execution
                  owner who response (afterClear who)
              · intro who
                have member := legal.2 who
                cases choice : joint who with
                | none => rw [choice] at member; exact member
                | some action =>
                    rw [choice] at member
                    have sameOwner : owner = who := Option.some.inj member.1
                    subst who
                    rw [chosen] at choice
                    cases Option.some.inj choice
                    refine ⟨member.1, ?_⟩
                    change response ∈ bounds.canonicalActions runtime leaks owner
                      (execution.recall owner) (execution.observe app owner)
                    have available := selected.2
                    change response ∈ bounds.riskActions runtime leaks bound owner
                      (execution.recall owner) (execution.observe app owner) at available
                    rw [bounds.riskActions_of_clear runtime leaks bound owner _ _ inputClear]
                      at available
                    exact available
      | none =>
          cases remaining with
          | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
          | succ remaining =>
              obtain ⟨command, _chosen, moved⟩ :=
                Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ realized)
              obtain ⟨next, supported, same⟩ := PMF.support_map .. ▸ moved
              cases same
              have beforeClear (who : Player) :=
                runtime.persistentServiceRisk_clear_before_environment leaks bound who
                  (clear _ rfl who) supported
              refine ⟨?_, legal.1, ?_⟩
              · intro current same who
                cases Option.some.inj same
                exact beforeClear who
              · intro who
                have member := legal.2 who
                cases choice : joint who with
                | none => rw [choice] at member; exact member
                | some action =>
                    rw [choice] at member
                    cases member.1

/-- A prefix with all persistent owner flags clear has a canonical trace with
the identical realized action and nature history, not just the same state. -/
theorem riskTrace_canonical_of_persistentClear
    : ∀ {state : (runtime.reactiveApplication leaks).ProtocolState}
      (trace : ((bounds.riskMenu runtime leaks bound).protocol initial horizon scheduler).Trace
        state),
    (∀ control, state = some control → ∀ who,
      runtime.persistentServiceRisk leaks bound who (control.execution.recall who)
        (control.execution.observe (runtime.reactiveApplication leaks) who) = false) →
    ∃ canonical : ((bounds.canonicalMenu runtime leaks).protocol initial horizon scheduler).Trace
        state,
      (bounds.canonicalMenu runtime leaks).toRawTrace initial horizon scheduler canonical =
        (bounds.riskMenu runtime leaks bound).toRawTrace initial horizon scheduler trace
  | _, .start, _ => ⟨.start, rfl⟩
  | _, .extend prior joint legal realized, clear => by
      obtain ⟨beforeClear, canonicalLegal⟩ :=
        bounds.risk_step_canonical_of_persistentClear runtime leaks bound initial horizon scheduler
          _ _ joint legal realized clear
      obtain ⟨canonicalPrior, same⟩ := riskTrace_canonical_of_persistentClear prior beforeClear
      refine ⟨.extend canonicalPrior joint canonicalLegal realized, ?_⟩
      simp only [ReactiveApplication.ResponseMenu.toRawTrace]
      rw [same]

end Vegas.EventGraphRuntime.MessageBounds
