/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceFirstTurnRanks
import Vegas.Game.DisclosureProfilePrefix

/-! # A common original source carrier at native completion ranks

The actual normalized first-turn policy reaches a decoded effective source
prefix. One composition of the real owner memory kernels restores every
original private intention list together. Its initialized law retains the
same initial parameter and is the original source behavioral prefix law.
This auxiliary carrier is distinct from physical native own recall and does
not assert a native information posterior.
-/

noncomputable section

namespace Vegas

open SourceProgram
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Restore all original source histories from the actual native prefix
decoder. The known original entry supplies the unused `none` branch; no
inhabitant or hidden-history oracle is needed. This is an auxiliary source
carrier, not the physical player's remembered native input. -/
def sourceServiceOriginalPrefixCarrier (profile : BehavioralProfile setup.program)
    (initial : State L setup.context) (rank : Nat)
    (execution : (application setup leaks).Execution) : PMF (ProtocolState setup.program) :=
  match sourceServicePrefix? setup rank execution.application.config with
  | none => PMF.pure (ProtocolState.entry setup.program (setup.initialConfig initial))
  | some before => profile.restoreDisclosureMemory setup.program []
      (Revelations.initial setup.context) before

/-- The actual stopped normalized first-turn law, followed by the same
all-owner restoration kernel, has the complete original source prefix law.
Effectiveness is derived from the source normalizer. -/
theorem sourceServiceFirstTurn_original_prefix_law
    {scheduler : (application setup leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (profile : BehavioralProfile setup.program)
    (initial : State L setup.context) (initialSupport : initial ∈ setup.initialLaw.support)
    (rank : Nat) (within : rank ≤ (graph setup).order.eventCount) :
    ((application setup leaks).runUntilHorizon scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
        (normalizeDisclosureProfile setup.program [] (Revelations.initial setup.context) profile))
      (sourceServiceRankCompleted rank) horizon
      (.initial (application setup leaks)
        (EventGraphRuntime.State.initial (setup.eventInputs initial)))).bind
          (sourceServiceOriginalPrefixCarrier profile initial rank) =
      (fun law => law.bind (ProtocolState.behavioralStateStep setup.program profile))^[rank]
        (PMF.pure (ProtocolState.entry setup.program (setup.initialConfig initial))) := by
  let normalized := normalizeDisclosureProfile setup.program []
    (Revelations.initial setup.context) profile
  have effective (who : Player) : (normalized who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context) :=
    (profile who).normalizeDisclosureFrom_effective setup.program []
      (Revelations.initial setup.context) (fun view => PMF.pure view.2)
  have nativeLaw := (sourceServiceFirstTurn_rank_law (turns := turns) contract timely normalized
    effective initial initialSupport rank within).2
  let restore : setup.ProtocolState → PMF (ProtocolState setup.program) := fun decoded =>
    match decoded with
    | none => PMF.pure (ProtocolState.entry setup.program (setup.initialConfig initial))
    | some before => profile.restoreDisclosureMemory setup.program []
        (Revelations.initial setup.context) before
  calc
    _ = (((application setup leaks).runUntilHorizon scheduler
        (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) normalized)
        (sourceServiceRankCompleted rank) horizon
        (.initial (application setup leaks)
          (EventGraphRuntime.State.initial (setup.eventInputs initial)))).map
            (fun execution => sourceServicePrefix? setup rank execution.application.config)).bind
              restore := by rw [PMF.bind_map]; rfl
    _ = (((fun law => law.bind (ProtocolState.behavioralStateStep setup.program normalized))^[rank]
        (PMF.pure (ProtocolState.entry setup.program (setup.initialConfig initial)))).map some).bind
          restore := by rw [nativeLaw]
    _ = ((fun law => law.bind (ProtocolState.behavioralStateStep setup.program normalized))^[rank]
        (PMF.pure (ProtocolState.entry setup.program (setup.initialConfig initial)))).bind
          (profile.restoreDisclosureMemory setup.program []
            (Revelations.initial setup.context)) := by rw [PMF.bind_map]; rfl
    _ = _ := (normalizeDisclosureProfile_prefix_disintegration setup.program profile
      (setup.initialConfig initial) rank).symm

/-- One common restoration draw preserves all original private histories
jointly with any reading of the same correlated initial source draw. -/
theorem sourceServiceFirstTurn_original_prefix_joint_law {Parameter : Type}
    {scheduler : (application setup leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (profile : BehavioralProfile setup.program)
    (parameter : State L setup.context → Parameter)
    (rank : Nat) (within : rank ≤ (graph setup).order.eventCount) :
    (setup.initialLaw.bind fun initial =>
      (((application setup leaks).runUntilHorizon scheduler
        (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
          (normalizeDisclosureProfile setup.program []
            (Revelations.initial setup.context) profile))
        (sourceServiceRankCompleted rank) horizon
        (.initial (application setup leaks)
          (EventGraphRuntime.State.initial (setup.eventInputs initial)))).bind
            (sourceServiceOriginalPrefixCarrier profile initial rank)).map
              (fun original => (parameter initial, original))) =
      setup.initialLaw.bind fun initial =>
        ((fun law => law.bind (ProtocolState.behavioralStateStep setup.program profile))^[rank]
          (PMF.pure (ProtocolState.entry setup.program (setup.initialConfig initial)))).map
            (fun original => (parameter initial, original)) := by
  apply bind_congr_on_support _
  intro initial supported
  exact congrArg (PMF.map (fun original => (parameter initial, original)))
    (sourceServiceFirstTurn_original_prefix_law contract timely profile initial supported
      rank within)

end Vegas
