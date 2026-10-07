/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceTimedMixture
import Vegas.Game.SourceServiceDecidedCompletion
import Vegas.Game.ServiceChancePhase
import Vegas.Game.SourceServiceSiteBridge

/-! # Timing changes the source law only through expiry

Timed canonical clients (`Vegas.timedCanonicalPolicy`) follow the compiled
decisions of a source profile and choose freely when to submit them. Under
complete play, from every completion boundary, their run reads out the source
continuation up to the probability that some remaining event is completed by
expiry (`Vegas.timedCanonical_boundaryContinuationWithin`), for every timing,
every scheduler and every disclosing source profile with effective
disclosures. From initialization this is the source law
(`Vegas.timedCanonical_readout_within`).

The proof couples each event's phase with its source step. An owned phase is
the mixture over the head source action of runs that decide that action with
the given timing (`Vegas.timedCanonical_runUntil_mixture`), and each of those
completes the event with that action or by expiry
(`Vegas.timed_completion_of_follows`). So the phase's successful outcomes are
dominated by the source step, the source continuation coincides with the run
after every successful outcome up to the later expiry probability, and
`PMF.WithinTV.bind_of_dominated` adds the phase's own expiry probability. An
expiry stays in the completion history, so the per-phase errors add up to the
probability of an expiry in the final configuration.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A timed canonical client submits only at its own turns. -/
theorem timedCanonicalPolicy_submitsAtTurn (timing : Player → ResponseTiming setup leaks)
    (profile : BehavioralProfile setup.program) (who : Player) :
    SubmitsAtTurn setup leaks (timedCanonicalPolicy setup leaks timing profile who) who := by
  intro past view response chosen other submitted
  unfold timedCanonicalPolicy at chosen
  split at chosen
  · exact silentPolicy_submitsAtTurn setup leaks who past view response chosen other submitted
  · split at chosen
    · obtain ⟨act, _, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp chosen
      cases act with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at member
          exact silentPolicy_submitsAtTurn setup leaks who past view response member other
            submitted
      | true =>
          simp only [↓reduceIte] at member
          exact sourceServiceCanonicalPolicy_submitsAtTurn setup leaks profile who past view
            response member other submitted
    · exact silentPolicy_submitsAtTurn setup leaks who past view response chosen other submitted

/-- Some event of rank at least `rank` was completed by expiry. -/
def ExpiredFrom (rank : Nat) (config : (graph setup).Config) : Prop :=
  ∃ completion ∈ config.history, rank ≤ completion.event.val ∧
    ExpiryAction completion.event completion.action

/-- An expiry from a later rank is an expiry from an earlier one. -/
theorem ExpiredFrom.mono {rank later : Nat} {config : (graph setup).Config}
    (expired : ExpiredFrom later config) (le : rank ≤ later) : ExpiredFrom rank config := by
  obtain ⟨completion, member, above, expiring⟩ := expired
  exact ⟨completion, member, le.trans above, expiring⟩

/-- Scheduler rounds only extend the completion history. -/
theorem runRounds_history_prefix (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy) :
    ∀ (count : Nat) (execution final : (application setup leaks).Execution),
      final ∈ ((application setup leaks).runRounds scheduler players count execution).support →
      execution.application.config.history <+: final.application.config.history := by
  intro count
  induction count with
  | zero =>
      intro execution final reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact List.prefix_refl _
  | succ count ih =>
      intro execution final reached
      obtain ⟨middle, moved, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      refine List.IsPrefix.trans ?_ (ih middle final rest)
      rcases round_configStep setup leaks scheduler players execution middle moved with
        same | ⟨event, ready, action, member⟩
      · rw [same]
      · rw [execution.application.config.step_history event ready action _ member]
        exact List.prefix_append _ _

/-- The probability, under the run to the horizon, that some event of rank at
least `rank` is completed by expiry. -/
def expiryMass (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy) (horizon rank : Nat)
    (execution : (application setup leaks).Execution) : ℝ :=
  (((application setup leaks).runToHorizon scheduler players horizon execution).toOuterMeasure
    {final | ExpiredFrom rank final.application.config}).toReal

theorem expiryMass_nonneg (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy) (horizon rank : Nat)
    (execution : (application setup leaks).Execution) :
    0 ≤ expiryMass scheduler players horizon rank execution :=
  ENNReal.toReal_nonneg

theorem expiryMass_le_one (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy) (horizon rank : Nat)
    (execution : (application setup leaks).Execution) :
    expiryMass scheduler players horizon rank execution ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by
    simpa using outerMeasure_le_one
      ((application setup leaks).runToHorizon scheduler players horizon execution) _)

/-- **Timing changes the source continuation only through expiry.** Under
complete play, for every timing and every disclosing source profile with
effective disclosures, from every completion boundary of the timed canonical
clients within the horizon, their readout law is within the probability of a
later expiry of the source continuation. -/
theorem timedCanonical_boundaryContinuationWithin [Finite Player]
    {scheduler : (application setup leaks).Scheduler} {horizon : Nat}
    (complete : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (timing : Player → ResponseTiming setup leaks) (profile : BehavioralProfile setup.program)
    (effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (disclosing : ∀ who, Disclosing setup.program (profile who)) :
    ∀ rank (execution : (application setup leaks).Execution),
      CompletionBoundary setup leaks scheduler
        (timedCanonicalPolicy setup leaks timing profile) rank execution →
      execution.environmentRecall.length ≤ horizon →
      PMF.WithinTV
        (expiryMass scheduler (timedCanonicalPolicy setup leaks timing profile) horizon rank
          execution)
        (((application setup leaks).runToHorizon scheduler
            (timedCanonicalPolicy setup leaks timing profile) horizon execution).map
          fun final => sourceReadout setup leaks ((application setup leaks).finished final))
        (sourceContinuation setup profile rank execution.application.config) := by
  classical
  let app := application setup leaks
  let players := timedCanonicalPolicy setup leaks timing profile
  let readout := fun final : app.Execution => sourceReadout setup leaks (app.finished final)
  let mass := expiryMass scheduler players horizon
  suffices remaining : ∀ gap rank (execution : app.Execution),
      (graph setup).order.eventCount - rank = gap →
      CompletionBoundary setup leaks scheduler players rank execution →
      execution.environmentRecall.length ≤ horizon →
      PMF.WithinTV (mass rank execution)
        ((app.runToHorizon scheduler players horizon execution).map readout)
        (sourceContinuation setup profile rank execution.application.config) by
    intro rank execution boundary bounded
    exact remaining _ rank execution rfl boundary bounded
  intro gap
  induction gap with
  | zero =>
      intro rank execution gapEq boundary bounded
      have within : rank ≤ (graph setup).order.eventCount := boundary.ordered.1
      have rankEq : rank = (graph setup).order.eventCount := by omega
      subst rankEq
      rw [boundary.terminal_continuation (profile := profile)]
      have frozen : (app.runToHorizon scheduler players horizon execution).map readout =
          PMF.pure (readout execution) := by
        unfold ReactiveApplication.runToHorizon
        rw [map_congr_on_support _ (g := fun _ => readout execution) (fun next reached => by
          have same := runRounds_config_terminal scheduler players _ execution next
            boundary.ordered reached
          change sourceReadout setup leaks (some ⟨0, none, next⟩) =
            sourceReadout setup leaks (some ⟨0, none, execution⟩)
          simp only [sourceReadout, serviceSourceReadout, Option.bind_some, same])]
        exact PMF.map_const _ _
      rw [frozen]
      exact (PMF.WithinTV.refl _).mono (expiryMass_nonneg _ _ _ _ _)
  | succ gap ih =>
      intro rank execution gapEq boundary bounded
      have inside : rank < (graph setup).order.eventCount := by omega
      let event : (graph setup).EventId := ⟨rank, inside⟩
      let stop := fun final : app.Execution => event ∈ final.application.config.cut.completed
      have ready : execution.application.config.cut.Ready event :=
        (ready_iff_rank setup _ rank boundary.ordered event).mpr rfl
      obtain ⟨residual⟩ := boundary.sourceResidual (profile := profile)
      obtain ⟨law, continuation, policy, effectiveLaw, loudLaw⟩ :=
        SourceResidual.head_law leaks residual event rfl ready
      let phase := app.runUntilHorizon scheduler players stop horizon execution
      let PhaseExpired := fun stopped : app.Execution => ∃ expired, ExpiryAction event expired ∧
        stopped.application.config ∈ (execution.application.config.step event ready expired).support
      let decode := fun stopped : app.Execution =>
        if PhaseExpired stopped then none else some stopped.application.config
      let sourceStep := law.bind fun action => execution.application.config.step event ready action
      obtain ⟨startTrace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler
        players _ bounded execution boundary.supported
      have finishes (stopped : app.Execution) (reached : stopped ∈ phase.support) :
          event ∈ stopped.application.config.cut.completed :=
        completionRun_completes complete event execution boundary bounded stopped reached
      -- After a successful phase the run continues from the next boundary.
      have close : ∀ stopped ∈ phase.support, ∀ next, decode stopped = some next →
          PMF.WithinTV (mass (rank + 1) stopped)
            ((app.runToHorizon scheduler players horizon stopped).map readout)
            (sourceContinuation setup profile (rank + 1) next) := by
        intro stopped reached next decoded
        have nextEq : next = stopped.application.config := by
          simp only [decode] at decoded
          split at decoded
          · cases decoded
          · exact (Option.some.inj decoded).symm
        subst nextEq
        obtain ⟨stoppedBounded, stoppedBoundary⟩ := CompletionBoundary.stopped event execution
          boundary bounded stopped reached (finishes stopped reached)
        exact ih (rank + 1) stopped (by omega) stoppedBoundary stoppedBounded
      -- The successful outcomes of the phase are dominated by the source step.
      have dominated : ∀ next, (phase.map decode) (some next) ≤ sourceStep next := by
        intro next
        cases owned : (graph setup).actor? event with
        | none =>
            have sampled (action : (graph setup).Action event) :
                phase.map (fun stopped => stopped.application.config) =
                  execution.application.config.step event ready action := by
              unfold phase ReactiveApplication.runUntilHorizon
              exact chance_runUntil scheduler players event owned execution.application.config
                (fun cut other eventReady otherReady =>
                  ready_unique (setup := setup) cut otherReady eventReady)
                ready action _ execution rfl finishes
            have notExpired (stopped : app.Execution) : ¬ PhaseExpired stopped := by
              rintro ⟨expired, expiring, _⟩
              revert expiring
              unfold ExpiryAction
              cases node : nodeView (graph setup) event with
              | sample => exact id
              | bind actor payload outputEq codeEq =>
                  have some := nodeView_bind_actor outputEq codeEq
                  rw [owned] at some
                  cases some
              | resolve actor payload binding checks outputEq codeEq =>
                  have some := nodeView_resolve_actor outputEq codeEq
                  rw [owned] at some
                  cases some
            have decoded : phase.map decode =
                (phase.map fun stopped => stopped.application.config).map some := by
              rw [PMF.map_comp]
              exact map_congr_on_support _ fun stopped _ => by
                simp only [decode, notExpired stopped, ↓reduceIte, Function.comp_apply]
            have stepped : sourceStep =
                phase.map fun stopped => stopped.application.config := by
              simp only [sourceStep, ← sampled]
              exact PMF.bind_const _ _
            rw [decoded, stepped, pmf_map_apply_of_injective _ (Option.some_injective _)]
        | some owner =>
            have mixed := timedCanonical_runUntil_mixture event execution boundary owner owned
              timing profile law (policy owner owned) (loudLaw disclosing)
              (effectiveLaw effective) players (horizon - execution.environmentRecall.length) 0
              (by simpa only [Nat.zero_add] using startTrace)
            rw [Function.update_eq_self] at mixed
            have phaseEq : phase = law.bind fun action =>
                app.runUntilHorizon scheduler
                  (Function.update players owner
                    (timedDecidedPolicy setup leaks (timing owner) owner event action))
                  stop horizon execution := mixed
            have ownStart : OwnSubmissionsAtTurn setup leaks execution owner :=
              (roundsFrom_turnFacts setup leaks
                (fun who => timedCanonicalPolicy_submitsAtTurn timing profile who) _ execution
                boundary.supported).1.own owner
            rw [phaseEq, PMF.map_bind, PMF.bind_apply]
            simp only [sourceStep]
            rw [PMF.bind_apply]
            refine ENNReal.tsum_le_tsum fun action => ?_
            by_cases chosen : action ∈ law.support
            swap
            · rw [(PMF.apply_eq_zero_iff _ _).mpr chosen, zero_mul, zero_mul]
            refine mul_le_mul_right ?_ _
            obtain ⟨point, pointMember⟩ :=
              (execution.application.config.step event ready action).support_nonempty
            have pure := execution.application.config.step_eq_pure_of_actor event ready action
              owner owned point pointMember
            rw [pure]
            by_cases same : next = point
            · subst same
              rw [PMF.pure_apply_self]
              exact PMF.coe_le_one _ _
            · have zero : (PMF.map decode (app.runUntilHorizon scheduler
                  (Function.update players owner
                    (timedDecidedPolicy setup leaks (timing owner) owner event action))
                  stop horizon execution)) (some next) = 0 := by
                rw [PMF.apply_eq_zero_iff, PMF.mem_support_map_iff]
                rintro ⟨stopped, reached, decoded⟩
                have outcome := timed_completion_of_follows complete event execution boundary
                  bounded ready owned ownStart action (effectiveLaw effective action chosen)
                  (by
                    simp only [Function.update_self]
                    exact timedDecidedPolicy_decidesWithTiming _ owner event action)
                  stopped reached
                simp only [decode] at decoded
                split at decoded
                · cases decoded
                · rename_i fresh
                  have nextEq := (Option.some.inj decoded).symm
                  rcases outcome with decidedMember | expiredMember
                  · rw [pure, PMF.mem_support_pure_iff] at decidedMember
                    exact same (nextEq.trans decidedMember)
                  · exact fresh expiredMember
              rw [zero]
              exact zero_le
      -- The expiry probabilities add up along the phase.
      have recursion :
          ((phase.map decode) none).toReal +
              expect phase (fun stopped => if (decode stopped).isSome then
                mass (rank + 1) stopped else 0) ≤
            mass rank execution := by
        let failed : app.Execution → ℝ := fun stopped => if PhaseExpired stopped then 1 else 0
        let later : app.Execution → ℝ := fun stopped =>
          if PhaseExpired stopped then 0 else mass (rank + 1) stopped
        have failure : ((phase.map decode) none).toReal = expect phase failed := by
          rw [toReal_map_apply]
          refine expect_congr_on_support fun stopped _ => ?_
          by_cases expiredHere : PhaseExpired stopped <;>
            simp [decode, failed, expiredHere]
        have continued : (expect phase fun stopped => if (decode stopped).isSome then
            mass (rank + 1) stopped else 0) = expect phase later := by
          refine expect_congr_on_support fun stopped _ => ?_
          by_cases expiredHere : PhaseExpired stopped <;>
            simp [decode, later, expiredHere]
        have failedIntegrable : PayoffIntegrable phase failed :=
          payoffIntegrable_of_bounded phase failed (C := 1) fun stopped => by
            by_cases expiredHere : PhaseExpired stopped <;> simp [failed, expiredHere]
        have laterIntegrable : PayoffIntegrable phase later :=
          payoffIntegrable_of_bounded phase later (C := 1) fun stopped => by
            by_cases expiredHere : PhaseExpired stopped
            · simp [later, expiredHere]
            · simp only [later, expiredHere, ↓reduceIte]
              rw [abs_of_nonneg (expiryMass_nonneg _ _ _ _ _)]
              exact expiryMass_le_one _ _ _ _ _
        have whole : mass rank execution = expect phase fun stopped =>
            ((app.runToHorizon scheduler players horizon stopped).toOuterMeasure
              {final | ExpiredFrom rank final.application.config}).toReal := by
          change ((app.runToHorizon scheduler players horizon execution).toOuterMeasure
            {final | ExpiredFrom rank final.application.config}).toReal = _
          rw [app.runToHorizon_eq_runUntilHorizon_bind scheduler players stop horizon execution,
            toReal_toOuterMeasure_bind]
        rw [failure, continued, ← expect_add failedIntegrable laterIntegrable, whole]
        refine expect_mono (fun stopped _ => ?_) (payoffIntegrable_add failedIntegrable
          laterIntegrable) (payoffIntegrable_toReal_toOuterMeasure phase _ _)
        by_cases expiredHere : PhaseExpired stopped
        · have total : failed stopped + later stopped = 1 := by
            simp [failed, later, expiredHere]
          rw [total]
          obtain ⟨expired, expiring, member⟩ := expiredHere
          have certain : (app.runToHorizon scheduler players horizon stopped).toOuterMeasure
              {final | ExpiredFrom rank final.application.config} = 1 := by
            rw [PMF.toOuterMeasure_apply_eq_one_iff]
            intro final reached'
            have extended := runRounds_history_prefix scheduler players _ stopped final reached'
            rw [execution.application.config.step_history event ready expired _
              member] at extended
            exact ⟨⟨event, expired⟩, extended.subset (by simp), le_refl _, expiring⟩
          rw [certain, ENNReal.toReal_one]
        · have total : failed stopped + later stopped = mass (rank + 1) stopped := by
            simp [failed, later, expiredHere]
          rw [total]
          exact ENNReal.toReal_mono (outerMeasure_ne_top _ _)
            (MeasureTheory.measure_mono fun final reachedLater => ExpiredFrom.mono reachedLater
              (Nat.le_succ rank))
      have combined := PMF.WithinTV.bind_of_dominated phase sourceStep decode dominated
        (fun stopped => (app.runToHorizon scheduler players horizon stopped).map readout)
        (sourceContinuation setup profile (rank + 1)) (fun stopped => mass (rank + 1) stopped)
        (fun stopped => expiryMass_nonneg _ _ _ _ _) (fun stopped => expiryMass_le_one _ _ _ _ _)
        close
      have sourceEq : sourceContinuation setup profile rank execution.application.config =
          sourceStep.bind (sourceContinuation setup profile (rank + 1)) := by
        rw [continuation, PMF.bind_bind]
      rw [app.runToHorizon_eq_runUntilHorizon_bind scheduler players stop horizon execution,
        PMF.map_bind, sourceEq]
      exact combined.mono recursion


/-- **Timing changes the source law only through expiry.** Under complete
play, for every timing and every disclosing source profile with effective
disclosures, the typed readout law of the timed canonical clients from
initialization is within the probability that some event is completed by
expiry of the source law. -/
theorem timedCanonical_readout_within [Finite Player]
    {scheduler : (application setup leaks).Scheduler} {horizon : Nat}
    (complete : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (timing : Player → ResponseTiming setup leaks) (profile : BehavioralProfile setup.program)
    (effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (disclosing : ∀ who, Disclosing setup.program (profile who)) :
    PMF.WithinTV
      ((((application setup leaks).roundsFrom (initialLaw setup) scheduler
          (timedCanonicalPolicy setup leaks timing profile) horizon).toOuterMeasure
        {final | ExpiredFrom 0 final.application.config}).toReal)
      (((application setup leaks).roundsFrom (initialLaw setup) scheduler
          (timedCanonicalPolicy setup leaks timing profile) horizon).map
        fun final => sourceReadout setup leaks ((application setup leaks).finished final))
      ((setup.run profile).map some) := by
  let app := application setup leaks
  let players := timedCanonicalPolicy setup leaks timing profile
  have error : (((app.roundsFrom (initialLaw setup) scheduler players horizon).toOuterMeasure
      {final | ExpiredFrom 0 final.application.config}).toReal) =
      expect (initialLaw setup) fun state => expiryMass scheduler players horizon 0
        (ReactiveApplication.Execution.initial app state) := by
    rw [ReactiveApplication.roundsFrom, toReal_toOuterMeasure_bind]
    rfl
  rw [error, ← initialLaw_bind_sourceContinuation setup profile, ReactiveApplication.roundsFrom,
    PMF.map_bind]
  refine PMF.WithinTV.bind_right_expect _ _
    (payoffIntegrable_of_bounded _ _ (C := 1) fun state => by
      rw [abs_of_nonneg (expiryMass_nonneg _ _ _ _ _)]
      exact expiryMass_le_one _ _ _ _ _) fun state supported => ?_
  exact timedCanonical_boundaryContinuationWithin complete timing profile effective disclosing 0
    (ReactiveApplication.Execution.initial app state)
    (initial_completionBoundary setup leaks scheduler players state supported) (Nat.zero_le _)

end Vegas
