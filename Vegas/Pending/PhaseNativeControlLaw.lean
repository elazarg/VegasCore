/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseNativePairedTransition
import Interaction.ReactiveRoundTrace

/-! # Actual owner policy laws commute with clear physical control steps -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseNativeProjection

open Interaction EventGraph GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (plan : RuntimePhasePlan graph)

local notation "P" => phaseApplication runtime leaks
local notation "N" => runtime.reactiveApplication (nativeLeaks leaks plan)

/-- Couple the actual state kernels of arbitrary globally count-covered owner
policies. The native member uses the very same policies on reconstructed inputs. -/
theorem exists_paired_controlStep (bounds : MessageBounds graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler)
    (players : Player → (P).Policy)
    (covered : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view)
    (current : (P).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (clear : current.execution.application.current.excluded = ∅)
    (running : ¬ (P).terminal (some current)) :
    ∃ paired : PMF ((N).ProtocolState × (P).ProtocolState),
      paired.map Prod.fst = (N).controlStep (inputs.map State.initial) horizon
        (nativeScheduler runtime leaks plan scheduler)
        (fun who => nativePolicy runtime leaks plan (players who))
        (some (control runtime leaks plan current)) ∧
      paired.map Prod.snd = (P).controlStep (inputs.map (PhaseRuntimeState.initial plan)) horizon
        scheduler players (some current) ∧
      ∀ pair ∈ paired.support,
        ((∀ next, pair.2 = some next → next.execution.application.current.excluded = ∅) →
          pair.1 = protocolState runtime leaks plan pair.2) ∧
        PairedPublicRecord runtime leaks plan pair.1 pair.2 := by
  classical
  rcases current with ⟨remaining, actor, current⟩
  cases actor with
  | none =>
      have legal : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
          (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Legal
          (some ⟨remaining, none, current⟩) (fun _ => none) := by
        refine ⟨running, fun who => ?_⟩
        change ¬ (none : Option Player) = some who
        intro impossible
        cases impossible
      exact exists_paired_transition runtime leaks plan bounds ordered maximal inputs horizon
        scheduler ⟨remaining, none, current⟩ trace clear (fun _ => none) legal
  | some who =>
      let draws := players who (current.recall who) (current.observe P who)
      let outcome : (P).Action → (P).ProtocolState := fun response =>
        some ⟨remaining, none, current.respond P who response⟩
      let package := fun response => (protocolState runtime leaks plan (outcome response),
        outcome response)
      refine ⟨draws.map package, ?_, ?_, ?_⟩
      · rw [PMF.map_comp]
        change _ = (nativePolicy runtime leaks plan (players who)
          ((execution runtime leaks plan current).recall who)
          ((execution runtime leaks plan current).observe N who)).bind _
        rw [nativePolicy_at_clear runtime leaks plan bounds inputs horizon scheduler trace clear
          who,
          PMF.bind_map]
        simp only [ReactiveApplication.transition, control, Function.comp_def, ↓reduceIte,
          Option.getD_some]
        rw [pmf_bind_pure_eq_map]
        apply map_congr_on_support
        intro response supported
        have available :=
          covered who (current.recall who) (current.observe P who) response supported
        have same := respond_of_onePacket runtime leaks plan bounds current
          (PhaseCount.countRecall_history runtime leaks
            ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace))
          who response available
        change some (⟨remaining, none, execution runtime leaks plan
            (current.respond P who response)⟩ : (N).Control) = _
        rw [same]
      · rw [PMF.map_comp]
        simp only [ReactiveApplication.controlStep, ReactiveApplication.actor, Option.bind_some,
          ReactiveApplication.transition, ↓reduceIte, Option.getD_some]
        change draws.map outcome = draws.bind fun response => PMF.pure (outcome response)
        exact (pmf_bind_pure_eq_map draws outcome).symm
      · intro pair member
        obtain ⟨response, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
        refine ⟨fun _clear => rfl, ?_⟩
        have available :=
          covered who (current.recall who) (current.observe P who) response supported
        obtain ⟨afterTrace⟩ := (PhaseCount.onePacketMenu runtime leaks bounds).trace_respond
          (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler remaining current who
          response trace available
        have afterClear : (current.respond P who response).application.current.excluded = ∅ := by
          rcases response with ⟨transmission⟩
          cases transmission <;> exact clear
        exact clear_publicRecord runtime leaks plan bounds inputs horizon scheduler afterTrace
          afterClear

end Vegas.EventGraphRuntime.PhaseNativeProjection
