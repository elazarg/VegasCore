/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterPrefixNoise

/-! # Exact source-state posterior after completed roster phases

The traffic law is derived for the whole initialized program. Conditioning on
any positive auxiliary transcript leaves exactly the original source posterior
at the corresponding source view; no full-support assumption is required.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem roster_prefix_state_posterior
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : ∀ event who, (graph setup).actor? event = some who →
      FinDist (Fin ((rosters event).count who)))
    (network : (runtime setup).NetworkPolicy leaks)
    (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (admission : CommitmentInterface setup.program)
    (profile : Profile (setup.informationModel admission).behavioralSignature)
    (focal : Player) (count : Nat) (within : count ≤ eventCount setup.program)
    (observed : setup.ProtocolView focal)
    (extra : (application setup leaks).MessageReadout ×
      List (application setup leaks).PlayerEntry) :
    let executions := (initialLaw setup).bind fun state =>
      (runtime setup).runInteractionPlan leaks
        (rosterPolicy setup leaks rosters timing (setup.decodeBehavioralProfile admission profile))
        network (rosterPlanPrefix setup rosters count)
        (ReactiveApplication.Execution.initial (application setup leaks) state)
    let joint := executions.map fun final => (sourcePrefix? setup count final.application.config,
      ((application setup leaks).messageView final, final.recall focal))
    let information := fun pair => (setup.protocolObserve focal pair.1, pair.2)
    (observed, extra) ∈ (joint.map information).support →
      (joint.condOnFibre information (observed, extra)).map Prod.fst =
        (((setup.informationModel admission).runBehavioral profile (count + 1)).map
          ExecutionProtocol.History.state).condOnFibre (setup.protocolObserve focal) observed := by
  intro executions joint information present
  obtain ⟨noise, factor⟩ := roster_compiled_prefix_noise setup leaks rosters timing network reveals
    openable (setup.decodeBehavioralProfile admission profile) focal count within
  have sourceLaw := roster_compiled_prefix_law setup leaks rosters timing network reveals openable
    admission profile count within
  let prior := executions.map fun final => sourcePrefix? setup count final.application.config
  have factors : joint = prior.bind fun state =>
      (noise (setup.protocolObserve focal state)).map fun signal => (state, signal) := factor
  obtain ⟨pair, pairSupport, equal⟩ := FinDist.support_map .. ▸ present
  rw [factors] at pairSupport
  obtain ⟨state, stateSupport, member⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ pairSupport)
  obtain ⟨signal, signalSupport, pairEq⟩ := FinDist.support_map .. ▸ member
  cases pairEq
  have same : setup.protocolObserve focal state = observed := (Prod.mk.inj equal).1
  have extraEq : signal = extra := (Prod.mk.inj equal).2
  have oldPresent : observed ∈ (prior.map (setup.protocolObserve focal)).support := by
    rw [FinDist.support_map]
    exact ⟨state, stateSupport, same⟩
  have noisePresent : extra ∈ (noise observed).support := by
    simpa only [same, extraEq] using signalSupport
  change (joint.condOnFibre information (observed, extra)).map Prod.fst = _
  rw [factors]
  have posterior := FinDist.conditional_observation_kernel prior (setup.protocolObserve focal)
    noise observed extra oldPresent noisePresent
  exact posterior.trans (congrArg
    (fun law => law.condOnFibre (setup.protocolObserve focal) observed) sourceLaw)

end Vegas.SourceProgram.RevealService
