/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealServiceHonestLaw
import Vegas.Game.RevealServiceEffectiveTimely
import Vegas.Pending.CanonicalOutcomeAccepted

/-! # The honest outcome law of effective-opening clients

Clients of a reference that opens a publication exactly when the opening would
be accepted keep the outcome law of an always-open twin reference at every
scheduler boundary, under every public scheduler. A round in which every ready
event is a publication preserves the always-open reference's outcome law,
because accepted honest openings stay within their deadline and a rejected
opening's expiry publishes the same failure. A solitary segment preserves the
effective reference's outcome law, which is the always-open twin's.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

section Induction

variable {horizon turns : Nat} {scheduler :
    (serviceApplication setup mode deadline leaks).Scheduler}
  {delay bound : (serviceGraph setup mode).EventId → Nat}

/-- **The honest outcome law from every boundary.** Under the asynchronous
service contract, on a graph where only independent reveals are concurrent and
every other event leads, honest clients of an opening, ready-independent
reference run, from every initialized execution whose responses saw only
completed events or publications ready, to the reference's outcome law. -/
theorem effective_runToHorizon_outcomeLaw
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    (only : (serviceGraph setup mode).RevealsOnlyConcurrent)
    (leading : ∀ event, ¬ ((serviceGraph setup mode).outputLayout event).IsPublication →
      (serviceGraph setup mode).Leading event)
    (effective : (serviceGraph setup mode).BehavioralProfile)
    (effectiveIndependent : ReadyIndependent effective)
    (decides : ∀ (config : (serviceGraph setup mode).Config)
      (event : (serviceGraph setup mode).EventId) (owner : Player) (payload : L.Ty)
      (binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload))
      (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
      (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
        ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks),
      nodeView (serviceGraph setup mode) event =
        .resolve owner payload binding checks outputEq codeEq →
      ∀ (actor : (serviceGraph setup mode).actor? event = some owner)
        (active : owner ∉ ((serviceGraph setup mode).playerObserve owner config).defaulted),
        effective owner event actor ((serviceGraph setup mode).playerObserve owner config)
          active = PMF.pure (cast (congrArg EventField.Action outputEq.symm)
            (openingAccepted event config.store)))
    (reference : (serviceGraph setup mode).BehavioralProfile)
    (independent : ReadyIndependent reference) (opens : OpensPublications reference)
    {Outcome : Type*} (read : (serviceGraph setup mode).Config → Outcome)
    (keyed : ∀ left right : (serviceGraph setup mode).Config, runKey left = runKey right →
      read left = read right)
    (invariant : ∀ config, read config.erase = read config)
    (twins : ∀ config, outcomeLaw effective read config = outcomeLaw reference read config) :
    let players := serviceReferenceTurnPolicy setup mode deadline leaks bound turns
      (firstTurnTiming setup turns mode) effective
    ∀ execution : (serviceApplication setup mode deadline leaks).Execution,
      execution ∈ ((serviceApplication setup mode deadline leaks).roundsFrom
        (serviceInitialLaw setup mode) scheduler players
          execution.environmentRecall.length).support →
      execution.environmentRecall.length ≤ horizon →
      SeenWithin (fun event => ((serviceGraph setup mode).outputLayout event).IsPublication)
        execution →
      ((serviceApplication setup mode deadline leaks).runToHorizon scheduler players horizon
          execution).map (fun final => read final.application.config) =
        outcomeLaw reference read execution.application.config := by
  classical
  intro players
  let app := serviceApplication setup mode deadline leaks
  let publication := fun event : (serviceGraph setup mode).EventId =>
    ((serviceGraph setup mode).outputLayout event).IsPublication
  intro execution
  generalize leftEq : horizon - execution.environmentRecall.length = left
  induction left using Nat.strong_induction_on generalizing execution with
  | h left ih =>
  intro supported bounded seen
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup mode) horizon scheduler
    players execution.environmentRecall.length bounded execution supported
  cases left with
  | zero =>
      rw [leftEq] at trace
      have terminal := contract.completes _ trace ⟨rfl, rfl⟩
      have noRounds : app.runToHorizon scheduler players horizon execution =
          PMF.pure execution := by
        unfold ReactiveApplication.runToHorizon
        rw [leftEq]
        rfl
      have remaining : execution.application.config.remaining = 0 :=
        execution.application.config.terminal_iff_remaining_zero.mp terminal
      rw [noRounds, PMF.pure_map]
      unfold outcomeLaw
      rw [remaining, EventGraph.runPlan, PMF.pure_map]
  | succ left =>
      by_cases allPublications : ∀ event, execution.application.config.cut.Ready event →
          publication event
      · have rounds : app.runToHorizon scheduler players horizon execution =
            (app.round scheduler players execution).bind
              (app.runToHorizon scheduler players horizon) := by
          unfold ReactiveApplication.runToHorizon
          rw [leftEq, ReactiveApplication.runRounds]
          apply bind_congr_on_support _
          intro next reached
          rw [app.round_environmentRecall_length scheduler players execution next reached]
          congr 1
          omega
        rw [rounds, PMF.map_bind]
        calc
          _ = (app.round scheduler players execution).bind
              (fun _ => outcomeLaw reference read execution.application.config) := by
            apply bind_congr_on_support _
            intro next reached
            have lengthNext := app.round_environmentRecall_length scheduler players execution
              next reached
            have supportedNext : next ∈ (app.roundsFrom (serviceInitialLaw setup mode) scheduler
                players next.environmentRecall.length).support := by
              rw [lengthNext, app.roundsFrom_succ]
              exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨execution, supported, reached⟩
            rw [ih left (by omega) next (by omega) supportedNext (by omega)
              (round_seenWithin seen allPublications reached)]
            exact reactive_round_outcomeLaw_of_accepted independent opens read keyed invariant
              (serviceRuntime setup mode deadline) leaks scheduler players execution next
              allPublications (fun event owner ready owned _ accepted =>
                effectivePublication_withinDeadline contract timely players owner effective
                  decides rfl execution.environmentRecall.length bounded execution supported event
                  owned ready (allPublications event ready) accepted) reached
          _ = _ := PMF.bind_const _ _
      · push Not at allPublications
        obtain ⟨event, ready, notPublication⟩ := allPublications
        have solitary := only.solitary notPublication
        let stop := fun final : app.Execution => event ∈ final.application.config.cut.completed
        rw [app.runToHorizon_eq_runUntilHorizon_bind scheduler players stop, PMF.map_bind]
        calc
          _ = (app.runUntilHorizon scheduler players stop horizon execution).bind
              (fun stopped => outcomeLaw reference read stopped.application.config) := by
            apply bind_congr_on_support _
            intro stopped reached
            obtain ⟨used, within, rounds, lengthEq⟩ := app.runUntil_runRounds scheduler players
              stop _ execution stopped reached
            have stoppedSupported := app.roundsFrom_runUntil scheduler players
              (serviceInitialLaw setup mode) stop _ execution stopped supported reached
            have stoppedBounded : stopped.environmentRecall.length ≤ horizon := by omega
            have finished : event ∈ stopped.application.config.cut.completed := by
              rcases app.runUntilHorizon_stopped scheduler players stop horizon (left + 1)
                  execution stopped (by omega) reached with done | spent
              · exact done
              · obtain ⟨stoppedTrace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup mode)
                  horizon scheduler players stopped.environmentRecall.length stoppedBounded
                  stopped stoppedSupported
                rw [spent, Nat.sub_self] at stoppedTrace
                have terminal := contract.completes _ stoppedTrace ⟨rfl, rfl⟩
                rw [EventOrder.Cut.Terminal] at terminal
                rw [terminal]
                exact Finset.mem_univ _
            have progressed : 0 < used := by
              rcases Nat.eq_zero_or_pos used with zero | positive
              · subst zero
                cases (PMF.mem_support_pure_iff _ _).mp rounds
                exact (ready.1 finished).elim
              · exact positive
            have seenEvent := runUntil_seenWithin (allowed := publication) scheduler players event
              solitary _ execution stopped ready
              (fun who entry member other readyView =>
                (seen who entry member other readyView).imp_right Or.inl) reached
            have seenStopped : SeenWithin publication stopped := by
              intro who entry member other readyView
              rcases seenEvent who entry member other readyView with completed | permitted |
                  same
              · exact Or.inl completed
              · exact Or.inr permitted
              · subst same
                exact Or.inl finished
            exact ih (horizon - stopped.environmentRecall.length) (by omega) stopped rfl
              stoppedSupported stoppedBounded seenStopped
          _ = _ := by
            have segment := soleSegment_outcomeLaw (serviceRuntime setup mode deadline) leaks
              scheduler delay bound contract timely effective effectiveIndependent read keyed
              players event (fun _ _ => rfl) solitary (leading event notPublication)
              notPublication execution ready supported (seen.untouched ready.1 notPublication)
              bounded
            simp only [twins] at segment
            exact segment

/-- **The honest outcome law of the run.** Under the hypotheses of
`honest_runToHorizon_outcomeLaw`, the outcome of the honest clients' run to the
horizon has the reference's outcome law from the initial configurations. -/
theorem effective_roundsFrom_outcomeLaw
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    (only : (serviceGraph setup mode).RevealsOnlyConcurrent)
    (leading : ∀ event, ¬ ((serviceGraph setup mode).outputLayout event).IsPublication →
      (serviceGraph setup mode).Leading event)
    (effective : (serviceGraph setup mode).BehavioralProfile)
    (effectiveIndependent : ReadyIndependent effective)
    (decides : ∀ (config : (serviceGraph setup mode).Config)
      (event : (serviceGraph setup mode).EventId) (owner : Player) (payload : L.Ty)
      (binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload))
      (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
      (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
        ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks),
      nodeView (serviceGraph setup mode) event =
        .resolve owner payload binding checks outputEq codeEq →
      ∀ (actor : (serviceGraph setup mode).actor? event = some owner)
        (active : owner ∉ ((serviceGraph setup mode).playerObserve owner config).defaulted),
        effective owner event actor ((serviceGraph setup mode).playerObserve owner config)
          active = PMF.pure (cast (congrArg EventField.Action outputEq.symm)
            (openingAccepted event config.store)))
    (reference : (serviceGraph setup mode).BehavioralProfile)
    (independent : ReadyIndependent reference) (opens : OpensPublications reference)
    {Outcome : Type*} (read : (serviceGraph setup mode).Config → Outcome)
    (keyed : ∀ left right : (serviceGraph setup mode).Config, runKey left = runKey right →
      read left = read right)
    (invariant : ∀ config, read config.erase = read config)
    (twins : ∀ config, outcomeLaw effective read config = outcomeLaw reference read config) :
    ((serviceApplication setup mode deadline leaks).roundsFrom (serviceInitialLaw setup mode)
        scheduler (serviceReferenceTurnPolicy setup mode deadline leaks bound turns
          (firstTurnTiming setup turns mode) effective) horizon).map
        (fun final => read final.application.config) =
      (serviceInitialLaw setup mode).bind
        (fun state => outcomeLaw reference read state.config) := by
  let app := serviceApplication setup mode deadline leaks
  let players := serviceReferenceTurnPolicy setup mode deadline leaks bound turns
    (firstTurnTiming setup turns mode) effective
  unfold ReactiveApplication.roundsFrom
  rw [PMF.map_bind]
  apply bind_congr_on_support _
  intro state member
  let execution := ReactiveApplication.Execution.initial app state
  have supported : execution ∈ (app.roundsFrom (serviceInitialLaw setup mode) scheduler players
      execution.environmentRecall.length).support := by
    change execution ∈ (app.roundsFrom (serviceInitialLaw setup mode) scheduler players 0).support
    rw [ReactiveApplication.roundsFrom, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨_, member, by simp [ReactiveApplication.runRounds, execution]⟩
  have seen : SeenWithin (fun event => ((serviceGraph setup mode).outputLayout event).IsPublication)
      execution := by
    intro who entry present
    cases present
  exact effective_runToHorizon_outcomeLaw (turns := turns) contract timely only leading
    effective effectiveIndependent decides reference independent opens read keyed invariant twins
    execution supported (Nat.zero_le _) seen

end Induction

end Vegas
