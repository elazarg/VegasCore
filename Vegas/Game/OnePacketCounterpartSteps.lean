/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketSwapRecord

/-! # Chance mass under a hidden swap

A hidden swap fixes every chance draw, so the chance mass of a completion is
that of its swap (`Vegas.completionMass_swap`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}

/-- **A hidden swap fixes chance masses.** -/
theorem completionMass_swap (swap : HiddenSwap (graph setup))
    (before after : EventGraphRuntime.State (graph setup)) :
    completionMass setup (before.swap swap) (after.swap swap) =
      completionMass setup before after := by
  unfold completionMass
  simp only [State.swap_config, EventGraph.Config.swap_history, List.length_map]
  rw [← List.map_drop]
  generalize after.config.history.drop before.config.history.length = completed
  rcases completed with _ | ⟨⟨event, action⟩, _ | ⟨_, _⟩⟩
  · rfl
  · change (match (graph setup).actor? event with
        | none =>
            if ready : (before.config.swap swap.values).cut.Ready event then
              ((before.config.swap swap.values).step event ready
                (swap.values.action event action) (after.config.swap swap.values)).toReal
            else 0
        | some _ => 1) = (match (graph setup).actor? event with
        | none =>
            if ready : before.config.cut.Ready event then
              (before.config.step event ready action after.config).toReal
            else 0
        | some _ => 1)
    cases acts : (graph setup).actor? event with
    | some _ => rfl
    | none =>
        simp only [EventGraph.Config.swap_cut]
        split_ifs with ready
        · have fixed : EventGraph.ResolutionFixed swap.values event := by
            unfold EventGraph.ResolutionFixed
            cases view : nodeView (graph setup) event with
            | bind owner payload outputEq codeEq =>
                rw [nodeView_bind_actor outputEq codeEq] at acts
                cases acts
            | resolve owner payload binding checks outputEq codeEq =>
                rw [nodeView_resolve_actor outputEq codeEq] at acts
                cases acts
            | sample => trivial
          rw [EventGraph.Config.step_swap swap.values before.config event ready action fixed,
            pmf_map_apply_of_injective _ (EventGraph.Config.swap_involutive swap.values).injective]
        · rfl
  · rfl

variable [Fintype Player]
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}
  {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
  {profiles : ℕ → ∀ player,
    (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player}
  {who : Player} {steps : OperationalSteps setup leaks bounds horizon scheduler sequence
    profiles who}
  {allowed : Set (graph setup).Inputs}

end Vegas
