/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceFirstTurnPrefix
import Vegas.Game.SourceServiceRetainedPolicy
import Interaction.ReactiveStopping
import Vegas.Source.InitialState

/-! # Source continuation after an actual canonical prefix

A legal canonical prefix may include delayed accepted decisions and persistent
private opportunity risk. Its future first-turn continuation uses the existing
scheduler runner and the actual retained recall. The decoded terminal law is
the continuation of that same source prefix. This does not select a rational
free continuation or identify native conditional beliefs.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

private theorem canonicalHistory_boundary
    (bounds : MessageBounds (graph setup))
    {scheduler : (application setup leaks).Scheduler} {horizon remaining rank : Nat}
    (execution : (application setup leaks).Execution)
    (trace : ((bounds.canonicalMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, none, execution⟩))
    (ordered : execution.application.config.cut.IsPrefix rank)
    (untouched : ∀ event : (graph setup).EventId, event.val = rank →
      Untouched setup leaks event execution) :
    execution.environmentRecall.length ≤ horizon ∧
      CompletionBoundary setup leaks scheduler
        (bounds.canonicalMenu (runtime setup) leaks).uniformResponses rank execution ∧
      SubmissionsAtTurn setup leaks execution := by
  have reached := (bounds.canonicalMenu (runtime setup) leaks).roundSupported_uniform
    (initialLaw setup) horizon scheduler trace
  refine ⟨by
    have accounted := reached.1
    change execution.environmentRecall.length + remaining = horizon at accounted
    omega,
    ⟨reached.2, ordered, untouched⟩, ?_⟩
  intro who
  exact (retainedCanonicalSlots_history bounds ⟨remaining, none, execution⟩ trace who).1

/-- At every actual canonical completion boundary, including one reached after
an accepted delayed decision, the existing first-turn runner has the decoded
source continuation law. Persistent private opportunity risk need not be clear.
The admitted profile supplies future canonical packet choices on legal traces;
no initialized support under that future profile is required. -/
theorem sourceServiceCanonicalHistory_firstTurn_continuation
    (bounds : MessageBounds (graph setup)) (covered : bounds.CoversBindingValues)
    (initialCovered : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    {scheduler : (application setup leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (profile : BehavioralProfile setup.program)
    (permitted : ∀ who, (profile who).Admitted setup.program (CommitmentInterface.values _))
    (effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (rank remaining : Nat) (execution : (application setup leaks).Execution)
    (trace : ((bounds.canonicalMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, none, execution⟩))
    (ordered : execution.application.config.cut.IsPrefix rank)
    (untouched : ∀ event : (graph setup).EventId, event.val = rank →
      Untouched setup leaks event execution) :
    ((application setup leaks).runToHorizon scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
      horizon execution).map
        (fun final => sourceReadout setup leaks ((application setup leaks).finished final)) =
      sourceContinuation setup profile rank execution.application.config := by
  classical
  let app := application setup leaks
  let menu := bounds.canonicalMenu (runtime setup) leaks
  let players := sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
    profile
  let readout := fun final : app.Execution => sourceReadout setup leaks (app.finished final)
  have admitted : ∀ who, menu.Admissible (initialLaw setup) horizon scheduler who
      (players who) := by
    intro who control current _ response chosen
    exact sourceServiceTurnPolicy_retained bounds covered initialCovered capacity bound turns
      (firstTurnTiming setup turns) profile who (permitted who) control current response chosen
  suffices continuation : ∀ gap rank remaining (execution : app.Execution),
      (graph setup).order.eventCount - rank = gap →
      (menu.protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨remaining, none, execution⟩) →
      execution.application.config.cut.IsPrefix rank →
      (∀ event : (graph setup).EventId, event.val = rank →
        Untouched setup leaks event execution) →
      (app.runToHorizon scheduler players horizon execution).map readout =
        sourceContinuation setup profile rank execution.application.config by
    exact continuation _ rank remaining execution rfl trace ordered untouched
  intro gap
  induction gap with
  | zero =>
      intro rank remaining execution gapEq trace ordered untouched
      obtain ⟨_bounded, boundary, _submissions⟩ :=
        canonicalHistory_boundary bounds execution trace ordered untouched
      have rankEq : rank = (graph setup).order.eventCount := by
        have within := ordered.1
        omega
      subst rankEq
      rw [boundary.terminal_continuation (profile := profile)]
      unfold ReactiveApplication.runToHorizon
      rw [map_congr_on_support _ (g := fun _ => readout execution) (fun next reached => by
        have same := runRounds_config_terminal scheduler players _ execution next ordered reached
        change sourceReadout setup leaks (some ⟨0, none, next⟩) =
          sourceReadout setup leaks (some ⟨0, none, execution⟩)
        simp only [sourceReadout, Option.bind_some, same])]
      exact PMF.map_const _ _
  | succ gap ih =>
      intro rank remaining execution gapEq trace ordered untouched
      obtain ⟨bounded, boundary, submissions⟩ :=
        canonicalHistory_boundary bounds execution trace ordered untouched
      have inside : rank < (graph setup).order.eventCount := by omega
      let event : (graph setup).EventId := ⟨rank, inside⟩
      let stop := fun final : app.Execution => event ∈ final.application.config.cut.completed
      have rawTrace := menu.toRawTrace (initialLaw setup) horizon scheduler trace
      have accounted := app.raw_trace_accounted (initialLaw setup) horizon scheduler rawTrace
      change execution.environmentRecall.length + remaining = horizon at accounted
      obtain ⟨oldRank, oldOrdered, seen⟩ := roundsFrom_ranked setup leaks scheduler
        menu.uniformResponses _ execution boundary.supported
      have seen : ReadySeen setup leaks rank execution := by
        have sameRank := isPrefix_unique oldOrdered ordered
        rw [sameRank] at seen
        exact seen
      have nextResources (stopped : app.Execution)
          (reached : stopped ∈ (app.runUntilHorizon scheduler players stop horizon
            execution).support) :
          Nonempty ((menu.protocol (initialLaw setup) horizon scheduler).Trace
            (some ⟨horizon - stopped.environmentRecall.length, none, stopped⟩)) ∧
          stopped.application.config.cut.IsPrefix (rank + 1) ∧
          (∀ next : (graph setup).EventId, next.val = rank + 1 →
            Untouched setup leaks next stopped) := by
        obtain ⟨_stoppedBounded, nextTrace⟩ := menu.trace_runUntilHorizon
          (initialLaw setup) horizon scheduler players admitted stop remaining execution stopped
          accounted trace reached
        have adjusted : remaining = horizon - execution.environmentRecall.length := by omega
        rw [adjusted] at rawTrace
        have completed := runUntilHorizon_completes contract.completes bounded rawTrace
          stopped reached
        obtain ⟨nextSeen, nextConfig⟩ := runUntil_completion_prefix setup leaks scheduler players
          event _ execution stopped ordered seen reached
        refine ⟨nextTrace, ?_, ?_⟩
        · rcases nextConfig with unchanged | advanced
          · exact (Nat.lt_irrefl _ ((unchanged.2 event).mp completed)).elim
          · exact advanced
        · intro next nextRank observer entry member readyView
          have lower := nextSeen observer entry member next readyView
          change next.val ≤ rank at lower
          omega
      rw [app.runToHorizon_eq_runUntilHorizon_bind scheduler players stop horizon execution,
        PMF.map_bind]
      calc
        _ = (app.runUntilHorizon scheduler players stop horizon execution).bind
            (fun stopped => sourceContinuation setup profile (rank + 1)
              stopped.application.config) := by
          apply bind_congr_on_support _
          intro stopped reached
          obtain ⟨⟨nextTrace⟩, nextOrdered, nextUntouched⟩ := nextResources stopped reached
          exact ih (rank + 1) _ stopped (by omega) nextTrace nextOrdered nextUntouched
        _ = sourceContinuation setup profile rank execution.application.config := by
          obtain ⟨before, decoded, law⟩ := sourceServiceTurnPolicy_firstTurn_prefix_law
            (turns := turns) contract timely profile effective event execution boundary
            submissions bounded
          change sourceServicePrefix? setup rank execution.application.config = some before
            at decoded
          let continuation := fun state : Option (ProtocolState setup.program) =>
            (setup.continuationLaw profile state).map some
          have composed := congrArg (fun distribution => distribution.bind continuation) law
          rw [PMF.bind_map, PMF.bind_map] at composed
          change _ = (ProtocolState.behavioralStateStep setup.program profile before).bind
            (fun state => (ProtocolState.continuationLaw setup.program profile state).map some)
            at composed
          rw [← PMF.map_bind, sourceStep_continuation] at composed
          simpa only [stop, sourceContinuation, decoded, Setup.continuationLaw, continuation,
            Function.comp_def] using composed


/-- A real stopped completion supplies the untouched next boundary. The earlier
players use canonical responses, but may have delayed the completed event.
Their actual stop and retained recall are used directly for the restart. -/
theorem sourceServiceCanonicalHistory_stopped_firstTurn_continuation
    (bounds : MessageBounds (graph setup)) (covered : bounds.CoversBindingValues)
    (initialCovered : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    {scheduler : (application setup leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (profile : BehavioralProfile setup.program)
    (permitted : ∀ who, (profile who).Admitted setup.program (CommitmentInterface.values _))
    (effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (players : Player → (application setup leaks).Policy)
    (admitted : ∀ who, (bounds.canonicalMenu (runtime setup) leaks).Admissible
      (initialLaw setup) horizon scheduler who (players who))
    (event : (graph setup).EventId) (remaining : Nat)
    (execution stopped : (application setup leaks).Execution)
    (trace : ((bounds.canonicalMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, none, execution⟩))
    (ordered : execution.application.config.cut.IsPrefix event.val)
    (reached : stopped ∈ ((application setup leaks).runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon execution).support) :
    ((application setup leaks).runToHorizon scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
      horizon stopped).map
        (fun final => sourceReadout setup leaks ((application setup leaks).finished final)) =
      sourceContinuation setup profile (event.val + 1) stopped.application.config := by
  let app := application setup leaks
  let menu := bounds.canonicalMenu (runtime setup) leaks
  have actual := menu.roundSupported_uniform (initialLaw setup) horizon scheduler trace
  have accounted := actual.1
  change execution.environmentRecall.length + remaining = horizon at accounted
  have bounded : execution.environmentRecall.length ≤ horizon := by omega
  obtain ⟨rank, ranked, seen⟩ := roundsFrom_ranked setup leaks scheduler menu.uniformResponses
    _ execution actual.2
  have sameRank := isPrefix_unique ranked ordered
  rw [sameRank] at seen
  obtain ⟨_, ⟨stoppedTrace⟩⟩ := menu.trace_runUntilHorizon (initialLaw setup) horizon scheduler
    players admitted (fun final => event ∈ final.application.config.cut.completed) remaining
    execution stopped accounted trace reached
  have rawTrace := menu.toRawTrace (initialLaw setup) horizon scheduler trace
  have sameRemaining : remaining = horizon - execution.environmentRecall.length := by omega
  rw [sameRemaining] at rawTrace
  have completed := runUntilHorizon_completes contract.completes bounded rawTrace stopped reached
  obtain ⟨stoppedSeen, progressed⟩ := runUntil_completion_prefix setup leaks scheduler players
    event _ execution stopped ordered seen reached
  have stoppedOrdered : stopped.application.config.cut.IsPrefix (event.val + 1) := by
    rcases progressed with same | advanced
    · exact (Nat.lt_irrefl _ ((same.2 event).mp completed)).elim
    · exact advanced
  have untouched : ∀ next : (graph setup).EventId, next.val = event.val + 1 →
      Untouched setup leaks next stopped := by
    intro next rankNext who entry member readyView
    have lower := stoppedSeen who entry member next readyView
    omega
  exact sourceServiceCanonicalHistory_firstTurn_continuation bounds covered initialCovered
    capacity contract timely profile permitted effective (event.val + 1) _ stopped stoppedTrace
    stoppedOrdered untouched

/-- Initial parameters and public outcomes are read from the same terminal
source state. Their continuation payoff law is therefore preserved jointly,
including after accepted delayed prefixes with private opportunity risk. This
is the base payoff law before any retained audit deduction. -/
theorem sourceServiceCanonicalHistory_firstTurn_public_payoff {Parameter : Type}
    (bounds : MessageBounds (graph setup)) (covered : bounds.CoversBindingValues)
    (initialCovered : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    {scheduler : (application setup leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (profile : BehavioralProfile setup.program)
    (permitted : ∀ who, (profile who).Admitted setup.program (CommitmentInterface.values _))
    (effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (rank remaining : Nat) (execution : (application setup leaks).Execution)
    (trace : ((bounds.canonicalMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, none, execution⟩))
    (ordered : execution.application.config.cut.IsPrefix rank)
    (untouched : ∀ event : (graph setup).EventId, event.val = rank →
      Untouched setup leaks event execution)
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) :
    ((application setup leaks).runToHorizon scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
      horizon execution).map
        (fun final => baseUtility setup leaks
          (fun state => utility (setup.parameterOutcome parameter state))
          ((application setup leaks).finished final)) =
      (setup.continuationLaw profile
        (sourceServicePrefix? setup rank execution.application.config)).map
          (fun state => utility (setup.parameterOutcome parameter state)) := by
  have law := sourceServiceCanonicalHistory_firstTurn_continuation bounds covered initialCovered
    capacity (turns := turns) contract timely profile permitted effective rank remaining execution
    trace ordered untouched
  have mapped := congrArg (PMF.map fun source : Option (State L setup.program.terminalCtx) =>
    fun who => source.elim 0 (fun state => utility (setup.parameterOutcome parameter state) who))
    law
  rw [sourceContinuation, PMF.map_comp, PMF.map_comp] at mapped
  exact mapped

end Vegas
