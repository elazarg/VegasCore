/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceOriginalFirstInputPosterior
import Vegas.Game.SourceServiceInitialReadout
import Vegas.Game.SourceServiceFirstInputPassage

/-! # Same-draw source restoration at actual first-input stops

The first-response stop has the unchanged typed configuration of its genuine
completion-rank seed. Its persistent inputs identify the same initialization,
and its actual prefix decoder supplies one common all-owner memory lottery.
Integrating this physical stopped readout gives the true original carrier and
first input jointly. The restoration is auxiliary source data, not native recall.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Decode the actual persistent initialization and completed source prefix,
then restore every owner's original private source history in one common draw.
A failed physical decoder remains explicit in the analysis readout. -/
def sourceServiceRestoredPrefixReadout {Parameter : Type}
    (profile : BehavioralProfile setup.program)
    (parameter : State L setup.context → Parameter) (rank : Nat)
    (config : (graph setup).Config) : PMF (Option (Parameter × ProtocolState setup.program)) :=
  match sourceInitialReadout setup config, sourceServicePrefix? setup rank config with
  | some initial, some before =>
      (profile.restoreDisclosureMemory setup.program [] (Revelations.initial setup.context)
        before).map fun original => some (parameter initial, original)
  | _, _ => PMF.pure none

omit [Fintype Player] in
/-- The real first-response stopping point has the exact rank-seed typed
configuration; submitting its packet changes no graph configuration field. -/
theorem sourceServiceFirstActivation_config
    {scheduler : (application setup leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (players : Player → (application setup leaks).Policy) (who : Player)
    (profile : BehavioralProfile setup.program)
    (follows : players who = sourceServiceTurnPolicy setup leaks bound turns
      (firstTurnTiming setup turns) profile who)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some who)
    (execution : (application setup leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler players event.val execution)
    (within : execution.environmentRecall.length ≤ horizon)
    (stopped : (application setup leaks).Execution)
    (reached : stopped ∈ ((application setup leaks).runUntilHorizon scheduler players
      (fun final => sourceServiceTurnInput? setup leaks who event (final.recall who) ≠ none)
      horizon execution).support) :
    stopped.application.config = execution.application.config := by
  obtain ⟨middle, response, _actual, configEq, _first, _fits, _chosen, after, _inputEq⟩ :=
    sourceServiceFirstActivation_input contract timely players who turns profile follows event
      owned execution boundary within stopped reached
  rw [after]
  exact ((runtime setup).reactive_respond_application leaks middle who response).1.trans configEq

/-- At an actual initialized rank seed and real first-activation stop, both
physical decoders succeed. The stopped restoration kernel is the same kernel
as the seed's all-owner carrier, with its actual correlated initial parameter. -/
theorem sourceServiceFirstTurn_first_input_readout {Parameter : Type}
    {scheduler : (application setup leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (profile : BehavioralProfile setup.program)
    (parameter : State L setup.context → Parameter)
    (who : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some who)
    (initial : State L setup.context) (initialSupport : initial ∈ setup.initialLaw.support)
    (execution : (application setup leaks).Execution) :
    let normalized := normalizeDisclosureProfile setup.program []
      (Revelations.initial setup.context) profile
    let players := sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
      normalized
    execution ∈ ((application setup leaks).runUntilHorizon scheduler players
      (sourceServiceRankCompleted event.val) horizon
      (.initial (application setup leaks)
        (EventGraphRuntime.State.initial (setup.eventInputs initial)))).support →
    ∀ stopped ∈ ((application setup leaks).runUntilHorizon scheduler players
        (fun final => sourceServiceTurnInput? setup leaks who event (final.recall who) ≠ none)
        horizon execution).support,
      sourceServiceRestoredPrefixReadout profile parameter event.val stopped.application.config =
        (sourceServiceOriginalPrefixCarrier profile initial event.val execution).map
          fun original => some (parameter initial, original) := by
  classical
  intro normalized players actual stopped reached
  let app := application setup leaks
  let start := ReactiveApplication.Execution.initial app
    (EventGraphRuntime.State.initial (setup.eventInputs initial))
  have effective (owner : Player) : (normalized owner).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context) :=
    (profile owner).normalizeDisclosureFrom_effective setup.program []
      (Revelations.initial setup.context) (fun view => PMF.pure view.2)
  obtain ⟨bounded, boundary⟩ :=
    (sourceServiceFirstTurn_rank_law (turns := turns) contract timely normalized effective initial
      initialSupport event.val (Nat.le_of_lt event.isLt)).1 execution actual
  have same := sourceServiceFirstActivation_config contract timely players who normalized rfl
    event owned execution boundary bounded stopped reached
  obtain ⟨used, _within, rounds, _length⟩ := app.runUntil_runRounds scheduler players
    (sourceServiceRankCompleted event.val) _ start execution actual
  have initialized := sourceInitialReadout_runRounds setup leaks initial players scheduler used
    execution rounds
  have prefixSupport : sourceServicePrefix? setup event.val execution.application.config ∈
      (((app.runUntilHorizon scheduler players (sourceServiceRankCompleted event.val) horizon
        start).map fun current => sourceServicePrefix? setup event.val
          current.application.config)).support := PMF.support_map .. ▸ ⟨execution, actual, rfl⟩
  rw [(sourceServiceFirstTurn_rank_law (turns := turns) contract timely normalized effective initial
    initialSupport event.val (Nat.le_of_lt event.isLt)).2, PMF.support_map] at prefixSupport
  obtain ⟨before, _sourceSupport, decoded⟩ := prefixSupport
  unfold sourceServiceRestoredPrefixReadout sourceServiceOriginalPrefixCarrier
  rw [same, initialized, ← decoded]

/-- The actual stopped configuration's common restoration draw and actual
first input have the same joint law as the original rank carrier followed by
that real first-input stop. No virtual initialization is selected at the stop. -/
theorem sourceServiceFirstTurn_first_input_joint_readout {Parameter : Type}
    {scheduler : (application setup leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (profile : BehavioralProfile setup.program)
    (parameter : State L setup.context → Parameter)
    (who : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some who) :
    let normalized := normalizeDisclosureProfile setup.program []
      (Revelations.initial setup.context) profile
    let players := sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
      normalized
    let rank := fun initial => (application setup leaks).runUntilHorizon scheduler players
      (sourceServiceRankCompleted event.val) horizon
      (.initial (application setup leaks)
        (EventGraphRuntime.State.initial (setup.eventInputs initial)))
    let first := fun execution => (application setup leaks).runUntilHorizon scheduler players
      (fun final => sourceServiceTurnInput? setup leaks who event (final.recall who) ≠ none)
      horizon execution
    (setup.initialLaw.bind fun initial => (rank initial).bind fun execution =>
      (first execution).bind fun stopped =>
        (sourceServiceRestoredPrefixReadout profile parameter event.val
          stopped.application.config).map fun original =>
            (original, sourceServiceTurnInput? setup leaks who event (stopped.recall who))) =
    ((setup.initialLaw.bind fun initial => (rank initial).bind fun execution =>
      (sourceServiceOriginalPrefixCarrier profile initial event.val execution).bind fun original =>
        (first execution).map fun stopped => ((parameter initial, original),
          sourceServiceTurnInput? setup leaks who event (stopped.recall who))).map
            fun selected => (some selected.1, selected.2)) := by
  classical
  intro normalized players rank first
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply bind_congr_on_support setup.initialLaw
  intro initial initialSupport
  apply bind_congr_on_support (rank initial)
  intro execution actual
  calc
    _ = (first execution).bind (fun stopped =>
        (sourceServiceOriginalPrefixCarrier profile initial event.val execution).map
          fun original => (some (parameter initial, original),
            sourceServiceTurnInput? setup leaks who event (stopped.recall who))) := by
      apply bind_congr_on_support (first execution)
      intro stopped reached
      rw [sourceServiceFirstTurn_first_input_readout contract timely profile parameter who event
        owned initial initialSupport execution actual stopped reached, PMF.map_comp]
      rfl
    _ = _ := PMF.bind_comm _ _ _

end Vegas
