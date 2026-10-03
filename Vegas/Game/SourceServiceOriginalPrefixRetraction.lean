/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceOriginalPrefix
import Vegas.Game.DisclosureProfileRetraction
import Vegas.Pending.ReactiveBindingLikelihood

/-! # Actual native inputs retained by the common original carrier

At an initialized completion rank, every sampled original source carrier
compresses to the actual decoded effective prefix. Compression leaves the
same sampled execution, complete traffic, and physical own recall/input in
the joint law. This supplies a retraction for an eventual source-view channel
induction; it neither asserts that the channel factors nor identifies a native
Bayesian posterior.
-/

noncomputable section

namespace Vegas

open SourceProgram
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Every supported common original carrier compresses to this execution's
actual decoder. The effective source support is derived from the stopped
rank law rather than supplied as an information-fiber premise. -/
theorem sourceServiceFirstTurn_original_prefix_retracts
    {scheduler : (application setup leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (profile : BehavioralProfile setup.program)
    (initial : State L setup.context) (initialSupport : initial ∈ setup.initialLaw.support)
    (rank : Nat) (within : rank ≤ (graph setup).order.eventCount)
    (execution : (application setup leaks).Execution)
    (reached : execution ∈ ((application setup leaks).runUntilHorizon scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
        (normalizeDisclosureProfile setup.program [] (Revelations.initial setup.context) profile))
      (sourceServiceRankCompleted rank) horizon
      (.initial (application setup leaks)
        (EventGraphRuntime.State.initial (setup.eventInputs initial)))).support)
    (original : ProtocolState setup.program)
    (restored : original ∈
      (sourceServiceOriginalPrefixCarrier profile initial rank execution).support) :
    some (ProtocolState.normalizeDisclosureProfileRecall setup.program original) =
      sourceServicePrefix? setup rank execution.application.config := by
  let normalized := normalizeDisclosureProfile setup.program []
    (Revelations.initial setup.context) profile
  have effective (who : Player) : (normalized who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context) :=
    (profile who).normalizeDisclosureFrom_effective setup.program []
      (Revelations.initial setup.context) (fun view => PMF.pure view.2)
  have law := (sourceServiceFirstTurn_rank_law (turns := turns) contract timely normalized
    effective initial initialSupport rank within).2
  have decoded : sourceServicePrefix? setup rank execution.application.config ∈
      (((fun law => law.bind (ProtocolState.behavioralStateStep setup.program normalized))^[rank]
        (PMF.pure (ProtocolState.entry setup.program (setup.initialConfig initial)))).map
          some).support := by
    rw [← law, PMF.support_map]
    exact ⟨execution, reached, rfl⟩
  obtain ⟨before, beforeSupport, decoderEq⟩ := PMF.support_map .. ▸ decoded
  unfold sourceServiceOriginalPrefixCarrier at restored
  rw [← decoderEq] at restored
  have retract := normalizeDisclosureProfile_prefix_retracts setup.program profile
    (setup.initialConfig initial) rank before beforeSupport original restored
  rw [retract]
  exact decoderEq

private theorem actual_restoration_readout_joint {Extra : Type}
    {scheduler : (application setup leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (profile : BehavioralProfile setup.program)
    (initial : State L setup.context) (initialSupport : initial ∈ setup.initialLaw.support)
    (rank : Nat) (within : rank ≤ (graph setup).order.eventCount)
    (readout : (application setup leaks).Execution → Extra) :
    let stopped := (application setup leaks).runUntilHorizon scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
        (normalizeDisclosureProfile setup.program [] (Revelations.initial setup.context) profile))
      (sourceServiceRankCompleted rank) horizon
      (.initial (application setup leaks)
        (EventGraphRuntime.State.initial (setup.eventInputs initial)))
    (stopped.bind fun execution =>
      (sourceServiceOriginalPrefixCarrier profile initial rank execution).map fun original =>
        (some (ProtocolState.normalizeDisclosureProfileRecall setup.program original),
          readout execution)) =
      stopped.map (fun execution =>
        (sourceServicePrefix? setup rank execution.application.config, readout execution)) := by
  intro stopped
  calc
    _ = stopped.bind fun execution => PMF.pure
        (sourceServicePrefix? setup rank execution.application.config, readout execution) := by
      apply bind_congr_on_support _
      intro execution reached
      calc
        (sourceServiceOriginalPrefixCarrier profile initial rank execution).map
            (fun original =>
              (some (ProtocolState.normalizeDisclosureProfileRecall setup.program original),
                readout execution)) =
            (sourceServiceOriginalPrefixCarrier profile initial rank execution).map
            (fun _ => (sourceServicePrefix? setup rank execution.application.config,
              readout execution)) :=
          map_congr_on_support _
            (f := fun original =>
              (some (ProtocolState.normalizeDisclosureProfileRecall setup.program original),
                readout execution))
            (g := fun _ => (sourceServicePrefix? setup rank execution.application.config,
              readout execution)) fun original restored => Prod.ext
                (sourceServiceFirstTurn_original_prefix_retracts contract timely profile initial
                  initialSupport rank within execution reached original restored) rfl
        _ = _ := PMF.map_const _ _
    _ = _ := PMF.bind_pure_comp _ _

/-- Compressing the common original carrier retains the same actual full
traffic draw, including scheduler recall and the focal player's private input. -/
theorem sourceServiceFirstTurn_original_prefix_traffic_retraction
    {scheduler : (application setup leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (profile : BehavioralProfile setup.program)
    (initial : State L setup.context) (initialSupport : initial ∈ setup.initialLaw.support)
    (rank : Nat) (within : rank ≤ (graph setup).order.eventCount) (focal : Player) :
    let stopped := (application setup leaks).runUntilHorizon scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
        (normalizeDisclosureProfile setup.program [] (Revelations.initial setup.context) profile))
      (sourceServiceRankCompleted rank) horizon
      (.initial (application setup leaks)
        (EventGraphRuntime.State.initial (setup.eventInputs initial)))
    (stopped.bind fun execution =>
      (sourceServiceOriginalPrefixCarrier profile initial rank execution).map fun original =>
        (some (ProtocolState.normalizeDisclosureProfileRecall setup.program original),
          (runtime setup).bindingTraffic leaks focal execution)) =
      stopped.map (fun execution =>
        (sourceServicePrefix? setup rank execution.application.config,
          (runtime setup).bindingTraffic leaks focal execution)) :=
  actual_restoration_readout_joint contract timely profile initial initialSupport rank within _

/-- The restored carrier and the physical own recall/input use the same
execution. Compression recovers the actual decoder without replacing native
recall by an original intention list. -/
theorem sourceServiceFirstTurn_original_prefix_input_retraction
    {scheduler : (application setup leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (profile : BehavioralProfile setup.program)
    (initial : State L setup.context) (initialSupport : initial ∈ setup.initialLaw.support)
    (rank : Nat) (within : rank ≤ (graph setup).order.eventCount) (focal : Player) :
    let stopped := (application setup leaks).runUntilHorizon scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
        (normalizeDisclosureProfile setup.program [] (Revelations.initial setup.context) profile))
      (sourceServiceRankCompleted rank) horizon
      (.initial (application setup leaks)
        (EventGraphRuntime.State.initial (setup.eventInputs initial)))
    (stopped.bind fun execution =>
      (sourceServiceOriginalPrefixCarrier profile initial rank execution).map fun original =>
        (some (ProtocolState.normalizeDisclosureProfileRecall setup.program original),
          execution.recall focal, execution.observe (application setup leaks) focal)) =
      stopped.map (fun execution =>
        (sourceServicePrefix? setup rank execution.application.config,
          execution.recall focal, execution.observe (application setup leaks) focal)) :=
  actual_restoration_readout_joint contract timely profile initial initialSupport rank within _

end Vegas
