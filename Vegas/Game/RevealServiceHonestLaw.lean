/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealServiceSoleSegment
import Vegas.Game.RevealServiceTimely

/-! # The honest outcome law with concurrent reveals

When only independent reveals are concurrent, honest clients of an opening,
ready-independent reference keep the reference's outcome law at every scheduler
boundary, under every public scheduler. A round in which every ready event is a
publication preserves the law, because honest publications stay within their
deadline whenever their binding holds a value. Otherwise a single solitary event
is ready, and the run until it completes preserves the law. Induction on the
rounds left gives the law of the whole run.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- Every event a recorded response saw ready has completed or satisfies
`allowed`. -/
def SeenWithin (allowed : (serviceGraph setup mode).EventId → Prop)
    (execution : (serviceApplication setup mode deadline leaks).Execution) : Prop :=
  ∀ who, ∀ entry ∈ execution.logs who, ∀ event,
    entry.beforeView.application.publicView.EventReady event →
      event ∈ execution.application.config.cut.completed ∨ allowed event

/-- An untouched event: no response saw it ready, when only completed or allowed
events were seen and it is neither. -/
theorem SeenWithin.untouched {allowed : (serviceGraph setup mode).EventId → Prop}
    {execution : (serviceApplication setup mode deadline leaks).Execution}
    (seen : SeenWithin allowed execution) {event : (serviceGraph setup mode).EventId}
    (unfinished : event ∉ execution.application.config.cut.completed)
    (disallowed : ¬ allowed event) : Untouched setup leaks event execution := by
  intro who entry member readyView
  rcases seen who entry member event readyView with completed | permitted
  · exact unfinished completed
  · exact disallowed permitted

/-- A round's configuration is reached from the previous one by graph steps. -/
theorem round_config_path
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {players : Player → (serviceApplication setup mode deadline leaks).Policy}
    {execution next : (serviceApplication setup mode deadline leaks).Execution}
    (reached : next ∈
      ((serviceApplication setup mode deadline leaks).round scheduler players execution).support) :
    Relation.ReflTransGen EventGraph.Config.Step execution.application.config
      next.application.config := by
  obtain ⟨command, _, middle, moved, cases⟩ := round_cases (setup := setup) leaks reached
  have path := ((serviceRuntime setup mode deadline).reactiveApplication_graphSteps
    leaks).environmentStep execution middle command moved
  rcases cases with ⟨_, rfl⟩ | ⟨who, _, response, _, rfl⟩
  · exact path
  · rw [((serviceRuntime setup mode deadline).reactive_respond_application leaks middle who
      response).1]
    exact path

/-- A round keeps the seen-ready bound when every event ready before it is
allowed. -/
theorem round_seenWithin {allowed : (serviceGraph setup mode).EventId → Prop}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {players : Player → (serviceApplication setup mode deadline leaks).Policy}
    {execution next : (serviceApplication setup mode deadline leaks).Execution}
    (seen : SeenWithin allowed execution)
    (readyAllowed : ∀ event, execution.application.config.cut.Ready event → allowed event)
    (reached : next ∈
      ((serviceApplication setup mode deadline leaks).round scheduler players execution).support) :
    SeenWithin allowed next := by
  let app := serviceApplication setup mode deadline leaks
  have grown := EventGraph.Config.Step.path_completed_mono (round_config_path reached)
  obtain ⟨command, _, middle, moved, cases⟩ := round_cases (setup := setup) leaks reached
  have recallEq := app.environmentStep_recall execution middle command moved
  intro who entry member event readyView
  rcases cases with ⟨_, rfl⟩ | ⟨actor, active, response, _, rfl⟩
  · rw [recallEq] at member
    rcases seen who entry member event readyView with completed | permitted
    · exact Or.inl (grown completed)
    · exact Or.inr permitted
  · rcases app.respond_entry_origin middle actor who response entry member with
      prior | ⟨_, fresh⟩
    · rw [recallEq] at prior
      rcases seen who entry prior event readyView with completed | permitted
      · exact Or.inl (grown completed)
      · exact Or.inr permitted
    · have commandEq : command = .activate actor := by
        cases command <;> simp_all [ReactiveApplication.Command.actor?]
      subst command
      have sameApp := activation_application (setup := setup) leaks execution middle actor moved
      rw [fresh] at readyView
      change middle.application.publicView.EventReady event at readyView
      have readyNow := (EventGraphRuntime.State.publicView_eventReady _ event).mp readyView
      rw [sameApp] at readyNow
      exact Or.inr (readyAllowed event readyNow)

/-- While a solitary event is ready, responses see only it, so running until
it completes keeps every seen event completed, allowed or that event. -/
theorem runUntil_seenWithin {allowed : (serviceGraph setup mode).EventId → Prop}
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy)
    (event : (serviceGraph setup mode).EventId)
    (solitary : (serviceGraph setup mode).Solitary event) :
    ∀ (count : Nat) (execution stopped : (serviceApplication setup mode deadline leaks).Execution),
      execution.application.config.cut.Ready event →
      SeenWithin (fun other => allowed other ∨ other = event) execution →
      stopped ∈ ((serviceApplication setup mode deadline leaks).runUntil scheduler players
        (fun final => event ∈ final.application.config.cut.completed) count execution).support →
      SeenWithin (fun other => allowed other ∨ other = event) stopped := by
  classical
  let app := serviceApplication setup mode deadline leaks
  intro count
  induction count with
  | zero =>
      intro execution stopped _ seen reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact seen
  | succ count ih =>
      intro execution stopped ready seen reached
      simp only [ReactiveApplication.runUntil, ready.1, ↓reduceIte] at reached
      obtain ⟨next, moved, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have seenNext := round_seenWithin seen (fun other otherReady =>
        Or.inr (solitary _ otherReady ready)) moved
      by_cases completed : event ∈ next.application.config.cut.completed
      · rw [app.runUntil_of_stop scheduler players _ count next completed,
          PMF.mem_support_pure_iff] at rest
        subst stopped
        exact seenNext
      · have same := EventGraph.Config.Step.path_eq_of_ready_of_not_completed event
          (fun _ otherReady => solitary _ otherReady ready) completed (round_config_path moved)
        exact ih next stopped (same.symm ▸ ready) seenNext rest

section Induction

variable {horizon turns : Nat} {scheduler :
    (serviceApplication setup mode deadline leaks).Scheduler}
  {delay bound : (serviceGraph setup mode).EventId → Nat}

/-- **The honest outcome law from every boundary.** Under the asynchronous
service contract, on a graph where only independent reveals are concurrent and
every other event leads, honest clients of an opening, ready-independent
reference run, from every initialized execution whose responses saw only
completed events or publications ready, to the reference's outcome law. -/
theorem honest_runToHorizon_outcomeLaw
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    (only : (serviceGraph setup mode).RevealsOnlyConcurrent)
    (leading : ∀ event, ¬ ((serviceGraph setup mode).outputLayout event).IsPublication →
      (serviceGraph setup mode).Leading event)
    (reference : (serviceGraph setup mode).BehavioralProfile)
    (independent : ReadyIndependent reference) (opens : OpensPublications reference)
    {Outcome : Type*} (read : (serviceGraph setup mode).Config → Outcome)
    (keyed : ∀ left right : (serviceGraph setup mode).Config, runKey left = runKey right →
      read left = read right)
    (invariant : ∀ config, read config.erase = read config) :
    let players := serviceReferenceTurnPolicy setup mode deadline leaks bound turns
      (firstTurnTiming setup turns mode) reference
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
            exact reactive_round_outcomeLaw_of_publications independent opens read keyed invariant
              (serviceRuntime setup mode deadline) leaks scheduler players execution next
              allPublications (fun event owner ready owned _ holds =>
                honestPublication_withinDeadline contract timely players owner reference opens rfl
                  execution.environmentRecall.length bounded execution supported event owned ready
                  (allPublications event ready) holds) reached
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
          _ = _ := soleSegment_outcomeLaw (serviceRuntime setup mode deadline) leaks scheduler
              delay bound contract timely reference independent read keyed players event
              (fun _ _ => rfl) solitary (leading event notPublication) notPublication execution
              ready supported (seen.untouched ready.1 notPublication) bounded

/-- **The honest outcome law of the run.** Under the hypotheses of
`honest_runToHorizon_outcomeLaw`, the outcome of the honest clients' run to the
horizon has the reference's outcome law from the initial configurations. -/
theorem honest_roundsFrom_outcomeLaw
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    (only : (serviceGraph setup mode).RevealsOnlyConcurrent)
    (leading : ∀ event, ¬ ((serviceGraph setup mode).outputLayout event).IsPublication →
      (serviceGraph setup mode).Leading event)
    (reference : (serviceGraph setup mode).BehavioralProfile)
    (independent : ReadyIndependent reference) (opens : OpensPublications reference)
    {Outcome : Type*} (read : (serviceGraph setup mode).Config → Outcome)
    (keyed : ∀ left right : (serviceGraph setup mode).Config, runKey left = runKey right →
      read left = read right)
    (invariant : ∀ config, read config.erase = read config) :
    ((serviceApplication setup mode deadline leaks).roundsFrom (serviceInitialLaw setup mode)
        scheduler (serviceReferenceTurnPolicy setup mode deadline leaks bound turns
          (firstTurnTiming setup turns mode) reference) horizon).map
        (fun final => read final.application.config) =
      (serviceInitialLaw setup mode).bind
        (fun state => outcomeLaw reference read state.config) := by
  let app := serviceApplication setup mode deadline leaks
  let players := serviceReferenceTurnPolicy setup mode deadline leaks bound turns
    (firstTurnTiming setup turns mode) reference
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
  exact honest_runToHorizon_outcomeLaw (turns := turns) contract timely only leading
    reference independent opens read keyed invariant execution supported (Nat.zero_le _) seen

end Induction

end Vegas
