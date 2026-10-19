/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseApplication
import Interaction.ReactiveConsistentHistory
import Interaction.ReactiveEvaluation
import Interaction.ReactiveRounds
import GameTheoryExtensions.Analysis.Protocol.ContinuationOwnPlay
import GameTheoryExtensions.Analysis.Protocol.OwnPlayReach

/-! # Actual consistent phase prefixes retain their whole physical continuations -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [Finite Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- The actual suffix is supported under its consistent prescription. Absorbing
that suffix into the existing finish evaluator retains any subsequent physical
endpoint, with its original network, evidence, resources and complete recalls. -/
theorem phase_finish_supported_of_consistent_prefix
    (initial : PMF (app).State) (horizon : Nat) (scheduler : (app).Scheduler)
    (players : Player → (app).Policy) (before after : (app).Control)
    (prior : ((app).protocol initial horizon scheduler).Trace (some before))
    (trace : ((app).protocol initial horizon scheduler).Trace (some after))
    (kept : TracePrefix prior trace)
    (consistent : ∀ who, (players who).Consistent (after.execution.recall who))
    (final : (app).ProtocolState)
    (reached : final ∈ ((app).finish initial horizon scheduler players (some after)).support) :
    final ∈ ((app).finish initial horizon scheduler players (some before)).support := by
  let := Fintype.ofFinite Player
  let start : ((app).protocol initial horizon scheduler).History := ⟨some before, prior⟩
  let fuel := trace.length - prior.length
  let model := (app).information initial horizon scheduler
  let profile := fun who => (app).encodePolicy (players who)
  have wholeSupported := (app).history_mem_support_runBehavioral_of_consistent
    initial horizon scheduler players trace (fun current same => by
      cases Option.some.inj same
      exact consistent)
  have wholePositive : 0 < (model.historyReachWeight profile ⟨some after, trace⟩).toReal :=
    pmf_toReal_pos_iff.mpr wholeSupported
  obtain ⟨records, recordEq, _provenance, chance, _nonnegative, mass, factor⟩ :=
    model.exists_continuation_ownPlay_factor prior trace kept
  have append (who : Player) (left right : List (model.InfoState who × (app).Action)) :
      model.ownPlayReachProbability (profile who) (left ++ right) =
        model.ownPlayReachProbability (profile who) left *
          model.ownPlayReachProbability (profile who) right := by
    induction left with
    | nil => simp only [List.nil_append, InformationModel.ownPlayReachProbability, one_mul]
    | cons entry rest ih =>
        simp only [List.cons_append, InformationModel.ownPlayReachProbability, ih, mul_assoc]
  have ownPositive (who : Player) :
      0 < model.ownPlayReachProbability (profile who) (records who) := by
    have positive := wholePositive
    rw [model.historyReachProbability_eq_player_mul_counterfactual profile who trace,
      model.playerReachProbability_eq_ownPlayReachProbability, recordEq, append] at positive
    have allPositive := pos_of_mul_pos_left positive
      (model.counterfactualReachProbability_nonneg profile who trace)
    exact pos_of_mul_pos_left allPositive
      (model.ownPlayReachProbability_nonneg (profile who) _)
  have chancePositive : 0 < chance := pos_of_mul_pos_left
    (mass.symm ▸ trace.transitionMass_pos) prior.transitionMass_pos.le
  have historySupported : (⟨some after, trace⟩ :
      ((app).protocol initial horizon scheduler).History) ∈
      (model.runBehavioralFrom profile fuel start).support := by
    apply pmf_toReal_pos_iff.mp
    rw [factor]
    exact mul_pos chancePositive (Finset.prod_pos fun who _ => ownPositive who)
  have stateSupported : some after ∈ ((fun law => law.bind
      ((app).controlStep initial horizon scheduler players))^[fuel]
        (PMF.pure (some before))).support := by
    change some after ∈ ((fun law => law.bind
      ((app).controlStep initial horizon scheduler players))^[fuel]
        (PMF.pure start.state)).support
    rw [← (app).run_map_state initial horizon scheduler players fuel start,
      InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom]
    exact (PMF.mem_support_map_iff _ _ _).mpr
      ⟨⟨some after, trace⟩, historySupported, rfl⟩
  have combined : final ∈ (((fun law => law.bind
      ((app).controlStep initial horizon scheduler players))^[fuel]
        (PMF.pure (some before))).bind
          ((app).finish initial horizon scheduler players)).support :=
    (PMF.mem_support_bind_iff _ _ _).mpr ⟨some after, stateSupported, reached⟩
  rw [(app).finish_after_steps initial horizon scheduler players fuel, PMF.pure_bind] at combined
  exact combined

end Vegas.EventGraphRuntime
