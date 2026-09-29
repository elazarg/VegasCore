/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceStateKernel

/-! # Initialized source prefix laws

The actual source history runner samples its initial configuration once and
then uses the existing source protocol kernel. This equation supplies source
history witnesses without assuming a compiled native profile is fully mixed.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem encoded_prefix_state (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program)
    (profile : BehavioralProfile setup.program)
    (permitted : ∀ who, (profile who).Admitted setup.program admission) (count : Nat) :
    ((setup.informationModel admission).runBehavioral
      (fun who => setup.toProtocolBehavioralPolicy admission who (profile who) (permitted who))
      (count + 1)).map History.state =
    setup.initialLaw.bind fun initial =>
      ((fun law => law.bind (ProtocolState.behavioralStateStep setup.program profile))^[count]
        (PMF.pure (ProtocolState.entry setup.program (setup.initialConfig initial)))).map
          some := by
  rw [InformationModel.runBehavioral, setup.runBehavioralFrom_state]
  change (fun law => law.bind (setup.behavioralStateStep admission
    (fun who => setup.toProtocolBehavioralPolicy admission who (profile who)
      (permitted who))))^[count + 1] (PMF.pure none) = _
  induction count with
  | zero =>
      simp only [Nat.zero_add, Function.iterate_one, PMF.pure_bind,
        setup.behavioralStateStep_none, Function.iterate_zero_apply,
        ← PMF.bind_pure_comp, Function.comp_def]
  | succ count ih =>
      rw [show count + 1 + 1 = (count + 1) + 1 from rfl,
        Function.iterate_succ_apply', ih, PMF.bind_bind]
      apply bind_congr_on_support _
      intro initial _supported
      rw [Function.iterate_succ_apply', PMF.bind_map, PMF.map_bind]
      exact bind_congr_on_support _ fun state _ =>
        setup.behavioralStateStep_encoded_some admission profile permitted state

/-- A source-kernel support witness gives an actual source history at the
same depth, preserving its complete existing protocol state. -/
theorem exists_history_of_prefix_support
    (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program)
    (profile : BehavioralProfile setup.program)
    (permitted : ∀ who, (profile who).Admitted setup.program admission)
    (initial : State L setup.context) (initialSupport : initial ∈ setup.initialLaw.support)
    (count : Nat) (state : SourceProgram.ProtocolState setup.program)
    (supported : state ∈ ((fun law => law.bind
      (ProtocolState.behavioralStateStep setup.program profile))^[count]
        (PMF.pure (ProtocolState.entry setup.program (setup.initialConfig initial)))).support) :
    ∃ history : (setup.executionProtocol admission).History,
      history ∈ ((setup.informationModel admission).runBehavioral
        (fun who => setup.toProtocolBehavioralPolicy admission who (profile who) (permitted who))
        (count + 1)).support ∧ history.state = some state := by
  have member : some state ∈ (((setup.informationModel admission).runBehavioral
      (fun who => setup.toProtocolBehavioralPolicy admission who (profile who) (permitted who))
      (count + 1)).map History.state).support := by
    rw [setup.encoded_prefix_state, PMF.support_bind]
    apply Set.mem_iUnion₂.mpr
    refine ⟨initial, initialSupport, ?_⟩
    rw [PMF.support_map]
    exact ⟨state, supported, rfl⟩
  obtain ⟨history, supported, same⟩ := PMF.support_map .. ▸ member
  exact ⟨history, supported, same⟩

end Vegas.SourceProgram.Setup
