/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveAnchoredPolicy
import Vegas.Source.DisclosureOpening
import Interaction.ReactiveMixtureRounds
import Vegas.Game.SourceServiceDecidedCompletion
import Vegas.Game.SourceServiceFirstTurnMixture
import Vegas.Game.ServiceChancePhase
import Vegas.Game.SourceServiceSiteBridge
import Vegas.Game.ServiceAssignedPolicy

/-! # First-turn clients from executions reached by any players

The first-turn clients of a source profile that opens effectively, continued
from any completion boundary that any players reached, read out the source
continuation of the boundary's decoded point, under the asynchronous contract
with timely delays (`Vegas.anchored_firstTurn_boundaryContinuation`). The boundary must
leave every later event untouched and every own submission at its author's
turn; it need not be reached by the clients.

The proof runs the anchored profile, which replays the reaching players up to
the anchor and is the clients from there on
(`Interaction.ReactiveApplication.anchoredPolicy`). Its boundaries are
completion boundaries of one fixed profile, so the event-by-event argument of
the timing invariance applies: at each owned event the owner's first-turn
family is the mixture over the head source action of policies deciding that
action (`Vegas.firstTurn_runUntil_mixture_update`), each of which completes the
event with its action (`Vegas.decided_completion_of_follows`).

A source policy that opens effectively has effective disclosures
(`Vegas.SourceProgram.BehavioralPolicy.OpensEffectively.effectiveDisclosures`).
-/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A policy that opens effectively has effective disclosures. -/
theorem BehavioralPolicy.OpensEffectively.effectiveDisclosures {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (registry : Registry Γ) →
    (revelations : Revelations Γ) → (policy : BehavioralPolicy who program) →
    policy.OpensEffectively program registry revelations →
    policy.EffectiveDisclosures program registry revelations
  | _, _, .ret _, _, _, _, _ => trivial
  | _, _, .sample _ _ _ next, _, _, policy, opens =>
      OpensEffectively.effectiveDisclosures next _ _ policy opens
  | _, _, .commit _ _ _ _ next, _, _, policy, opens =>
      OpensEffectively.effectiveDisclosures next _ _ policy.2 opens
  | _, _, .reveal published _ _ _ selected _ next, registry, revelations, policy, opens => by
      refine ⟨fun own view disclose chosen => ?_,
        OpensEffectively.effectiveDisclosures next _ _ policy.2 opens.2⟩
      rw [opens.1 own view, PMF.mem_support_pure_iff] at chosen
      subst chosen
      cases effective : effectiveDisclosureView published selected registry revelations
          (own.symm ▸ view.1) true with
      | true => exact effective
      | false =>
          unfold effectiveDisclosureView
          exact effectiveDisclosure_false _ _ _

end Vegas.SourceProgram

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

variable (setup leaks) in
/-- The first-turn clients of a source profile on the default runtime. -/
abbrev firstTurnClients (bound : (graph setup).EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program) : Player → (application setup leaks).Policy :=
  serviceTurnPolicy setup .sequential (rankDeadline setup .sequential) leaks bound turns
    (firstTurnTiming setup turns .sequential) profile

variable (setup leaks) in
/-- An execution continuing an anchor: every recall extends the anchor's, and
every own submission was made at its author's turn. -/
def ContinuesAnchor (anchor execution : (application setup leaks).Execution) : Prop :=
  (∀ who, anchor.recall who <+: execution.recall who) ∧
    ∀ who, OwnSubmissionsAtTurn setup leaks execution who

/-- A round of the anchored first-turn clients keeps an execution continuing
its anchor. -/
theorem ContinuesAnchor.round {scheduler : (application setup leaks).Scheduler}
    {bound : (graph setup).EventId → Nat} {turns : Nat} {profile : BehavioralProfile setup.program}
    {anchor execution next : (application setup leaks).Execution}
    (holds : ContinuesAnchor setup leaks anchor execution)
    (moved : next ∈ ((application setup leaks).round scheduler
      (ReactiveApplication.anchoredPolicy anchor (firstTurnClients setup leaks bound turns profile))
      execution).support) :
    ContinuesAnchor setup leaks anchor next := by
  let app := application setup leaks
  obtain ⟨command, _, middle, stepped, cases⟩ := round_cases setup leaks moved
  have recallEq := app.environmentStep_recall execution middle command stepped
  rcases cases with ⟨_, rfl⟩ | ⟨responder, _, response, chosen, rfl⟩
  · refine ⟨fun who => ?_, fun who entry member => ?_⟩
    · rw [recallEq]
      exact holds.1 who
    · rw [recallEq] at member
      exact holds.2 who entry member
  · have follows : ReactiveApplication.anchoredPolicy anchor
        (firstTurnClients setup leaks bound turns profile) responder (middle.recall responder)
        (middle.observe app responder) =
        firstTurnClients setup leaks bound turns profile responder (middle.recall responder)
          (middle.observe app responder) :=
      ReactiveApplication.anchoredPolicy_of_extends anchor _ responder _ _
        (by rw [recallEq]; exact holds.1 responder)
    rw [follows] at chosen
    refine ⟨fun who => ?_, fun who entry member event submitted => ?_⟩
    · by_cases same : who = responder
      · subst same
        obtain ⟨emitted, recalled, _⟩ := respond_recall_self setup leaks middle who response
        rw [recalled, recallEq]
        exact (holds.1 who).trans (List.prefix_append _ _)
      · rw [app.respond_recall_other middle responder who same response, recallEq]
        exact holds.1 who
    · by_cases same : who = responder
      · subst same
        obtain ⟨emitted, recalled, _⟩ := respond_recall_self setup leaks middle who response
        rw [recalled] at member
        rcases List.mem_append.mp member with prior | fresh
        · rw [recallEq] at prior
          exact holds.2 who entry prior event submitted
        · rw [List.mem_singleton] at fresh
          subst fresh
          exact sourceServiceTurnPolicy_submitsAtTurn setup leaks bound turns _ profile who _ _
            response chosen event submitted
      · rw [app.respond_recall_other middle responder who same response, recallEq] at member
        exact holds.2 who entry member event submitted

/-- Rounds of the anchored first-turn clients keep an execution continuing its
anchor. -/
theorem ContinuesAnchor.runRounds {scheduler : (application setup leaks).Scheduler}
    {bound : (graph setup).EventId → Nat} {turns : Nat} {profile : BehavioralProfile setup.program}
    {anchor : (application setup leaks).Execution} :
    ∀ (count : Nat) (execution : (application setup leaks).Execution),
      ContinuesAnchor setup leaks anchor execution →
      ∀ final ∈ ((application setup leaks).runRounds scheduler
          (ReactiveApplication.anchoredPolicy anchor
            (firstTurnClients setup leaks bound turns profile)) count execution).support,
        ContinuesAnchor setup leaks anchor final := by
  intro count
  induction count with
  | zero =>
      intro execution holds final reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact holds
  | succ count ih =>
      intro execution holds final reached
      obtain ⟨middle, moved, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      exact ih middle (holds.round moved) final rest

/-- **First-turn clients from any reached boundary.** Under the asynchronous
contract with timely delays, for a source profile opening effectively, from
every completion boundary of the anchored first-turn clients within the horizon
that continues the anchor, their readout law is the source continuation of the
boundary's decoded point. -/
theorem anchored_firstTurn_boundaryContinuation [Finite Player] {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound) (turns : Nat)
    (profile : BehavioralProfile setup.program)
    (opens : ∀ who, (profile who).OpensEffectively setup.program []
      (Revelations.initial setup.context))
    (anchor : (application setup leaks).Execution) :
    ∀ rank (execution : (application setup leaks).Execution),
      CompletionBoundary setup leaks scheduler (ReactiveApplication.anchoredPolicy anchor
        (firstTurnClients setup leaks bound turns profile)) rank execution →
      execution.environmentRecall.length ≤ horizon →
      ContinuesAnchor setup leaks anchor execution →
      ((application setup leaks).runToHorizon scheduler (ReactiveApplication.anchoredPolicy anchor
          (firstTurnClients setup leaks bound turns profile)) horizon execution).map
        (fun final => sourceReadout setup leaks ((application setup leaks).finished final)) =
      sourceContinuation setup profile rank execution.application.config := by
  classical
  let app := application setup leaks
  let clients := firstTurnClients setup leaks bound turns profile
  let players := ReactiveApplication.anchoredPolicy anchor clients
  let readout := fun final : app.Execution => sourceReadout setup leaks (app.finished final)
  have effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context) := fun who =>
    BehavioralPolicy.OpensEffectively.effectiveDisclosures _ _ _ _ (opens who)
  suffices remaining : ∀ gap rank (execution : app.Execution),
      (graph setup).order.eventCount - rank = gap →
      CompletionBoundary setup leaks scheduler players rank execution →
      execution.environmentRecall.length ≤ horizon →
      ContinuesAnchor setup leaks anchor execution →
      (app.runToHorizon scheduler players horizon execution).map readout =
        sourceContinuation setup profile rank execution.application.config by
    intro rank execution boundary bounded continues
    exact remaining _ rank execution rfl boundary bounded continues
  intro gap
  induction gap with
  | zero =>
      intro rank execution gapEq boundary bounded _
      have within : rank ≤ (graph setup).order.eventCount := boundary.ordered.1
      have rankEq : rank = (graph setup).order.eventCount := by omega
      subst rankEq
      rw [boundary.terminal_continuation (profile := profile)]
      unfold ReactiveApplication.runToHorizon
      rw [map_congr_on_support _ (g := fun _ => readout execution) (fun next reached => by
        have same := runRounds_config_terminal scheduler players _ execution next
          boundary.ordered reached
        change sourceReadout setup leaks (some ⟨0, none, next⟩) =
          sourceReadout setup leaks (some ⟨0, none, execution⟩)
        simp only [sourceReadout, serviceSourceReadout, Option.bind_some, same])]
      exact PMF.map_const _ _
  | succ gap ih =>
      intro rank execution gapEq boundary bounded continues
      have inside : rank < (graph setup).order.eventCount := by omega
      let event : (graph setup).EventId := ⟨rank, inside⟩
      let stop := fun final : app.Execution => event ∈ final.application.config.cut.completed
      have ready : execution.application.config.cut.Ready event :=
        (ready_iff_rank setup _ rank boundary.ordered event).mpr rfl
      obtain ⟨residual⟩ := boundary.sourceResidual (profile := profile)
      obtain ⟨law, continuation, policy, effectiveLaw, _⟩ :=
        SourceResidual.head_law leaks residual event rfl ready
      let phase := app.runUntilHorizon scheduler players stop horizon execution
      have finishes (stopped : app.Execution) (reached : stopped ∈ phase.support) :
          event ∈ stopped.application.config.cut.completed :=
        completionRun_completes contract.completes event execution boundary bounded stopped
          reached
      have close : ∀ stopped ∈ phase.support,
          (app.runToHorizon scheduler players horizon stopped).map readout =
            sourceContinuation setup profile (rank + 1) stopped.application.config := by
        intro stopped reached
        obtain ⟨stoppedBounded, stoppedBoundary⟩ := CompletionBoundary.stopped event execution
          boundary bounded stopped reached (finishes stopped reached)
        obtain ⟨used, _, rounds, _⟩ := app.runUntil_runRounds scheduler players stop _ execution
          stopped reached
        exact ih (rank + 1) stopped (by omega) stoppedBoundary stoppedBounded
          (ContinuesAnchor.runRounds used execution continues stopped rounds)
      have alone : ∀ (cut : (graph setup).order.Cut) (other : (graph setup).EventId),
          cut.Ready event → cut.Ready other → other = event :=
        fun cut other eventReady otherReady => ready_unique (setup := setup) cut otherReady
          eventReady
      have phaseConfig : phase.map (fun stopped => stopped.application.config) =
          law.bind fun action => execution.application.config.step event ready action := by
        cases owned : (graph setup).actor? event with
        | none =>
            have sampled (action : (graph setup).Action event) :
                phase.map (fun stopped => stopped.application.config) =
                  execution.application.config.step event ready action := by
              unfold phase ReactiveApplication.runUntilHorizon
              exact chance_runUntil scheduler players event owned execution.application.config
                alone ready action _ execution rfl finishes
            simp only [← sampled]
            exact (PMF.bind_const _ _).symm
        | some owner =>
            let family := sourceServiceTurnFamily setup leaks bound profile owner event turns 0
            let count := horizon - execution.environmentRecall.length
            -- From the boundary on, the owner's anchored client is its first-turn family.
            have agreement : app.runUntil scheduler players stop count execution =
                app.runUntil scheduler (Function.update players owner family) stop count
                  execution := by
              refine app.runUntil_congr_of_agree scheduler players _ stop (fun current =>
                (current.application.config = execution.application.config ∨ stop current) ∧
                  ∀ who, execution.recall who <+: current.recall who) ?_ ?_ count execution
                ⟨Or.inl rfl, fun _ => List.prefix_refl _⟩
              · intro current holds halted command _ middle moved who active
                have sameConfig : current.application.config = execution.application.config :=
                  holds.1.resolve_right halted
                have commandEq : command = .activate who := by
                  cases command with
                  | activate actor =>
                      exact congrArg ReactiveApplication.Command.activate
                        (Option.some.inj active)
                  | wait | «include» _ | application _ => cases active
                subst commandEq
                have appEq := activation_application setup leaks current middle who moved
                have recallEq := app.environmentStep_recall current middle _ moved
                by_cases same : who = owner
                · subst same
                  rw [Function.update_self]
                  have extends_ : anchor.recall who <+: middle.recall who := by
                    rw [recallEq]
                    exact (continues.1 who).trans (holds.2 who)
                  refine (ReactiveApplication.anchoredPolicy_of_extends anchor clients who _ _
                    extends_).trans ?_
                  have middleReady : middle.application.config.cut.Ready event := by
                    rw [appEq, sameConfig]
                    exact ready
                  have turn : (middle.observe app who).application.publicView.ownTurn? who =
                      some event := by
                    refine PublicView.ownTurn?_of_ownTurn _ who event
                      ⟨(middle.application.publicView_eventReady event).mpr middleReady, owned,
                        fun other otherReady _ => ?_⟩
                    have readyOther := (middle.application.publicView_eventReady other).mp
                      otherReady
                    exact alone _ other middleReady readyOther
                  exact firstTurnPolicy_eq_family owned turn
                · rw [Function.update_of_ne same]
              · intro current holds halted next moved
                have sameConfig : current.application.config = execution.application.config :=
                  holds.1.resolve_right halted
                refine ⟨?_, fun who => ?_⟩
                · rcases round_configStep setup leaks scheduler players current next moved with
                    unchanged | ⟨other, otherReady, action, member⟩
                  · left
                    rw [unchanged, sameConfig]
                  · right
                    have otherEq : other = event := alone _ other (by rw [sameConfig]; exact ready)
                      otherReady
                    subst otherEq
                    change event ∈ next.application.config.cut.completed
                    rw [current.application.config.step_cut event otherReady action _ member]
                    exact (EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inl rfl)
                · obtain ⟨command, _, middle, stepped, cases⟩ := round_cases setup leaks moved
                  have recallEq := app.environmentStep_recall current middle command stepped
                  refine (holds.2 who).trans ?_
                  rcases cases with ⟨_, rfl⟩ | ⟨responder, _, response, _, rfl⟩
                  · rw [recallEq]
                  · by_cases same : who = responder
                    · subst same
                      obtain ⟨emitted, recalled, _⟩ :=
                        respond_recall_self setup leaks middle who response
                      rw [recalled, recallEq]
                      exact List.prefix_append _ _
                    · rw [app.respond_recall_other middle responder who same response, recallEq]
            have mixed := firstTurn_runUntil_mixture_update event execution boundary owner owned
              bound turns profile law (policy owner owned) players count
            have decided (action : (graph setup).Action event) (chosen : action ∈ law.support) :
                (app.runUntil scheduler (Function.update players owner
                  (decidedTurnPolicy setup leaks bound owner event action)) stop count
                    execution).map (fun stopped => stopped.application.config) =
                  execution.application.config.step event ready action := by
              obtain ⟨point, pointMember⟩ :=
                (execution.application.config.step event ready action).support_nonempty
              have pure := execution.application.config.step_eq_pure_of_actor event ready action
                owner owned point pointMember
              rw [pure]
              refine (map_congr_on_support _ (g := fun _ => point) fun stopped reached => ?_).trans
                (PMF.map_const _ _)
              have completed := decided_completion_of_follows contract timely event execution
                boundary bounded ready owned alone (continues.2 owner) action
                (effectiveLaw effective action chosen) (Function.update_self ..) stopped reached
              rw [pure, PMF.mem_support_pure_iff] at completed
              exact completed
            change (app.runUntil scheduler players stop count execution).map _ = _
            rw [agreement, mixed, PMF.map_bind]
            exact bind_congr_on_support _ fun action chosen => decided action chosen
      have sourceEq : sourceContinuation setup profile rank execution.application.config =
          (law.bind fun action => execution.application.config.step event ready action).bind
            (sourceContinuation setup profile (rank + 1)) := by
        rw [continuation, PMF.bind_bind]
      rw [app.runToHorizon_eq_runUntilHorizon_bind scheduler players stop horizon execution,
        PMF.map_bind, sourceEq, ← phaseConfig, PMF.bind_map]
      exact bind_congr_on_support _ close

end Vegas
