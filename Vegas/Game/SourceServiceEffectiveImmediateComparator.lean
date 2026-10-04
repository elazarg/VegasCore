/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCompatibleImmediateAudit
import Interaction.ReactiveSupportedMenuPolicy
import GameTheory.Protocol.BehavioralTerminal
import GameTheoryExtensions.Analysis.FinitePayoffBounds

/-! # An immediate comparator in the complete effective menu

Actual source-compatible owner input supplies the prefix resources. Local
canonical-slot and bounded-record facts admit the immediate owner's responses
along its real continuation. Finite restriction therefore has no fallback on
that continuation, including against arbitrary effective opponent policies.
-/

noncomputable section

namespace Vegas.AsyncServiceSpec

open SourceProgram Interaction EventGraphRuntime EventGraph GameTheory GameTheory.Math.Probability
  GameTheory.Enforcement GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (service : AsyncServiceSpec Player L)

local notation "app" => application service.setup service.leaks
local notation "runtime" => runtime service.setup
local notation "menu" => service.bounds.menu (runtime) service.leaks

local instance immediate_history_nonempty : Nonempty (((menu).protocol (initialLaw service.setup)
    service.horizon service.scheduler).History) :=
  ⟨((menu).protocol (initialLaw service.setup) service.horizon service.scheduler).initHistory⟩

/-- Actual owner slot resources suffice for local admission in the full effective
menu. No risk-menu trace or global immediate-policy admission is required. -/
theorem immediatePolicy_effective_of_slots
    (profile : BehavioralProfile service.setup.program) (who : Player)
    (permitted : (profile who).Admitted service.setup.program (CommitmentInterface.values _))
    (control : (app).Control)
    (trace : ((menu).protocol (initialLaw service.setup) service.horizon service.scheduler).Trace
      (some control))
    (atTurn : OwnSubmissionsAtTurn service.setup service.leaks control.execution who)
    (slots : CanonicalSlotsUsed service.setup service.leaks control.execution who)
    (response : (app).Action)
    (chosen : response ∈ (sourceServiceImmediatePolicy service.setup service.leaks service.bound
      profile who (control.execution.recall who) (control.execution.observe (app) who)).support) :
    response ∈ (menu).actions who (control.execution.recall who)
      (control.execution.observe (app) who) := by
  have rawTrace := (menu).toRawTrace (initialLaw service.setup) service.horizon service.scheduler
    trace
  have facts := legalFacts service.setup service.leaks service.horizon service.scheduler control
    rawTrace
  have boundedTrace := (service.bounds.menu_in_raw (runtime) service.leaks).trace
    (initialLaw service.setup) service.horizon service.scheduler trace
  have values := service.bounds.candidateValues_raw_history (runtime) service.leaks
    (initialLaw service.setup) service.horizon service.scheduler service.initialValues boundedTrace
  rw [initialLaw_eq_inputs] at boundedTrace
  have handles := service.bounds.executionHandles_raw_history (runtime) service.leaks
    (service.setup.initialLaw.map service.setup.eventInputs) service.horizon service.scheduler
    boundedTrace
  apply service.bounds.canonicalActions_effective (runtime) service.leaks who _ _
  have silent : response = ⟨none⟩ → response ∈ service.bounds.canonicalActions (runtime)
      service.leaks who (control.execution.recall who) (control.execution.observe (app) who) := by
    rintro rfl
    exact service.bounds.silence_canonical (runtime) service.leaks who _ _
  rcases sourceServiceImmediatePolicy_cases chosen with empty | ⟨event, _, turn, supported⟩
  · exact silent empty
  · unfold sourceServiceCanonicalOpportunity at supported
    split at supported
    · exact silent ((app).silentPolicy_cases _ _ response supported)
    · rename_i unrecorded
      split at supported
      · rename_i fits
        rw [PMF.support_bind] at supported
        obtain ⟨decided, decisionSupported, member⟩ := Set.mem_iUnion₂.mp supported
        split at member
        · exact silent ((app).silentPolicy_cases _ _ response member)
        · cases (PMF.mem_support_pure_iff _ _).mp member
          have unsent : (runtime).eventRecorded service.leaks
              (control.execution.recall who) event = false := by simpa using unrecorded
          have fresh := canonicalSlot_fresh_of_used rawTrace who atTurn slots event turn unsent
          have counted : control.execution.application.publicView.bindingCount who <
              service.bounds.candidateCount := by
            classical
            let history := control.execution.application.config.history.map Completion.event
            have ready := (control.execution.application.publicView_eventReady event).mp
              (PublicView.ownTurn?_spec _ who event turn).1
            have absent : event ∉ history := fun present => ready.1
              ((control.execution.application.config.history_exact event).mp present)
            have distinct : (event :: history).Nodup := List.nodup_cons.mpr
              ⟨absent, control.execution.application.config.history_nodup⟩
            have lengthBound := distinct.length_le_card
            have capacity := service.capacity
            change history.countP _ < service.bounds.candidateCount
            apply lt_of_le_of_lt List.countP_le_length
            simp only [List.length_cons, Fintype.card_fin] at lengthBound
            omega
          exact sourceServiceCanonicalPolicy_retained_of_resources service.bounds service.values
            profile who permitted control.execution facts.binding values handles.1 event turn
            fits.withinDeadline unsent counted (canonicalFreshSlot_canonical who _ fresh)
            response decisionSupported
      · exact silent ((app).silentPolicy_cases _ _ response supported)

private def ownerSlots (who : Player) : (app).ProtocolState → Prop
  | none => True
  | some control => OwnSubmissionsAtTurn service.setup service.leaks control.execution who ∧
      CanonicalSlotsUsed service.setup service.leaks control.execution who

private theorem ownerSlots_controlStep
    (profile : BehavioralProfile service.setup.program) (who : Player)
    (players : Player → (app).Policy)
    (follows : players who = sourceServiceImmediatePolicy service.setup service.leaks service.bound
      profile who)
    (state : (app).ProtocolState)
    (trace : ((menu).protocol (initialLaw service.setup) service.horizon service.scheduler).Trace
      state) (valid : service.ownerSlots who state)
    (next : (app).ProtocolState)
    (reached : next ∈ ((app).controlStep (initialLaw service.setup) service.horizon
      service.scheduler players state).support) : service.ownerSlots who next := by
  cases state with
  | none =>
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ reached
      constructor
      · intro entry member
        cases member
      · intro serial member
        simp only [EventGraphRuntime.submittedCandidateSlots, ReactiveApplication.Execution.initial,
          List.map_nil, List.filterMap_nil, List.not_mem_nil] at member
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      obtain ⟨atTurn, slots⟩ := valid
      cases actor with
      | some responder =>
          obtain ⟨response, chosen, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
          cases (PMF.mem_support_pure_iff _ _).mp moved
          simp only [ownerSlots, ↓reduceIte, Option.getD_some]
          by_cases same : responder = who
          · subst responder
            rw [follows] at chosen
            exact sourceServiceImmediatePolicy_canonicalSlots_respond
              ((menu).toRawTrace (initialLaw service.setup) service.horizon service.scheduler trace)
              atTurn slots chosen
          · refine ⟨?_, canonicalSlotsUsed_respond_other execution (Ne.symm same) response slots⟩
            unfold OwnSubmissionsAtTurn
            rw [(app).respond_recall_other execution responder who (Ne.symm same) response]
            exact atTurn
      | none =>
          cases remaining with
          | zero => cases (PMF.mem_support_pure_iff _ _).mp reached; exact ⟨atTurn, slots⟩
          | succ remaining =>
              obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
              obtain ⟨middle, supported, rfl⟩ := PMF.support_map .. ▸ moved
              refine ⟨?_, canonicalSlotsUsed_environment supported who slots⟩
              unfold OwnSubmissionsAtTurn
              rw [(app).environmentStep_recall execution middle command supported]
              exact atTurn

/-- One implementable finite policy is shared across all hidden histories. -/
def effectiveImmediateComparator
    (profile : BehavioralProfile service.setup.program) (who : Player) :
    ((menu).information (initialLaw service.setup) service.horizon
      service.scheduler).BehavioralPolicy who :=
  (menu).restrictPolicy (initialLaw service.setup) service.horizon service.scheduler who
    (sourceServiceImmediatePolicy service.setup service.leaks service.bound profile who)

/-- At compatible actual information, whole-policy replacement has the full
physical immediate continuation law against arbitrary effective opponents.
The local owner invariants make finite restriction's fallback unreachable. -/
theorem effectiveImmediateComparator_terminal_law
    (profile : BehavioralProfile service.setup.program) (who : Player)
    (permitted : (profile who).Admitted service.setup.program (CommitmentInterface.values _))
    (certificate : ((menu).protocol (initialLaw service.setup) service.horizon
      service.scheduler).WellFoundedHistories)
    (baseline : ∀ player, ((menu).information (initialLaw service.setup) service.horizon
      service.scheduler).BehavioralPolicy player)
    (history : ((menu).protocol (initialLaw service.setup) service.horizon
      service.scheduler).History)
    (remaining : Nat) (execution : (app).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (compatible : service.sourceCompatibleInfo who
      (some (execution.recall who, execution.observe (app) who))) :
    (((menu).information (initialLaw service.setup) service.horizon
      service.scheduler).runBehavioralTerminalFrom certificate
        (GameTheory.Profile.update (sig := ((menu).information (initialLaw service.setup)
          service.horizon service.scheduler).behavioralSignature) baseline who
            (service.effectiveImmediateComparator profile who)) history).map History.state =
      (app).finish (initialLaw service.setup) service.horizon service.scheduler
        (Function.update ((menu).decodeProfile (initialLaw service.setup) service.horizon
          service.scheduler baseline) who (sourceServiceImmediatePolicy service.setup
            service.leaks service.bound profile who)) history.state := by
  let players := Function.update ((menu).decodeProfile (initialLaw service.setup) service.horizon
    service.scheduler baseline) who (sourceServiceImmediatePolicy service.setup service.leaks
      service.bound profile who)
  have follows : players who = sourceServiceImmediatePolicy service.setup service.leaks
      service.bound profile who := Function.update_self ..
  have represented : (fun player => (menu).restrictPolicy (initialLaw service.setup)
      service.horizon service.scheduler player (players player)) = GameTheory.Profile.update
        (sig := ((menu).information (initialLaw service.setup) service.horizon
          service.scheduler).behavioralSignature) baseline who
            (service.effectiveImmediateComparator profile who) := by
    funext player
    by_cases same : player = who
    · subst player
      simp only [players, Function.update_self, GameTheory.Profile.update_same,
        effectiveImmediateComparator]
    · simp only [players, Function.update_of_ne same, GameTheory.Profile.update_of_ne _ _ same,
        ReactiveApplication.ResponseMenu.decodeProfile]
      exact (menu).restrict_decode_embedPolicy (initialLaw service.setup) service.horizon
        service.scheduler player (baseline player)
  have covered : ∀ responder control,
      ((menu).protocol (initialLaw service.setup) service.horizon service.scheduler).Trace
        (some control) → service.ownerSlots who (some control) →
      control.actor = some responder → ∀ response ∈
        (players responder (control.execution.recall responder)
          (control.execution.observe (app) responder)).support,
        response ∈ (menu).actions responder (control.execution.recall responder)
          (control.execution.observe (app) responder) := by
    intro responder control trace valid _ response chosen
    by_cases same : responder = who
    · subst responder
      rw [follows] at chosen
      exact service.immediatePolicy_effective_of_slots profile who permitted control trace
        valid.1 valid.2 response chosen
    · simp only [players, Function.update_of_ne same,
        ReactiveApplication.ResponseMenu.decodeProfile] at chosen
      exact (menu).decode_embedPolicy_covered (initialLaw service.setup) service.horizon
        service.scheduler responder (baseline responder) _ _ response chosen
  have rawTrace := (menu).toRawTrace (initialLaw service.setup) service.horizon service.scheduler
    history.trace
  obtain ⟨_, atTurn, slots, _⟩ := service.sourceCompatibleInfo_raw_prefixFacts
    ⟨remaining, some who, execution⟩ (current ▸ rawTrace) who compatible
  have holds : service.ownerSlots who history.state := by
    rw [current]
    exact ⟨atTurn, slots⟩
  have evaluated := ReactiveApplication.ResponseMenu.run_restrict_supported_controlSteps_from
    («app» := (app)) (initial := initialLaw service.setup) (horizon := service.horizon)
    (scheduler := service.scheduler) (players := players) («menu» := (menu))
    (service.ownerSlots who) covered
    (service.ownerSlots_controlStep profile who players follows) (2 * service.horizon + 1)
    history holds
  rw [InformationModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
    ((menu).information (initialLaw service.setup) service.horizon service.scheduler) certificate
      ((menu).bounded (initialLaw service.setup) service.horizon service.scheduler),
    ← represented, evaluated]
  apply (app).iterate_eq_finish
  have budget := (app).trace_bound (initialLaw service.setup) service.horizon service.scheduler
    rawTrace
  change (app).rank service.horizon history.state ≤ 2 * service.horizon + 1
  omega

/-- Every terminal continuation of this one effective comparator has zero
actual owner collection. Foreign effective policies are arbitrary, and the
sampling backend may remain partial and correlated. -/
theorem effectiveImmediateComparator_terminal_charge_zero
    (profile : BehavioralProfile service.setup.program) (who : Player)
    (permitted : (profile who).Admitted service.setup.program (CommitmentInterface.values _))
    (certificate : ((menu).protocol (initialLaw service.setup) service.horizon
      service.scheduler).WellFoundedHistories)
    (baseline : ∀ player, ((menu).information (initialLaw service.setup) service.horizon
      service.scheduler).BehavioralPolicy player)
    (history : ((menu).protocol (initialLaw service.setup) service.horizon
      service.scheduler).History)
    (remaining : Nat) (execution : (app).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (compatible : service.sourceCompatibleInfo who
      (some (execution.recall who, execution.observe (app) who)))
    (final : ((menu).protocol (initialLaw service.setup) service.horizon
      service.scheduler).History)
    (reached : final ∈ (((menu).information (initialLaw service.setup) service.horizon
      service.scheduler).runBehavioralTerminalFrom certificate
        (GameTheory.Profile.update (sig := ((menu).information (initialLaw service.setup)
          service.horizon service.scheduler).behavioralSignature) baseline who
            (service.effectiveImmediateComparator profile who)) history).support)
    (sample : List (SettledEvidence service.setup) → PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual) :
    TerminalAudit.charge ((runtime).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample) final.state who = 0 := by
  have stateReached : final.state ∈ ((((menu).information (initialLaw service.setup)
      service.horizon service.scheduler).runBehavioralTerminalFrom certificate
        (GameTheory.Profile.update (sig := ((menu).information (initialLaw service.setup)
          service.horizon service.scheduler).behavioralSignature) baseline who
            (service.effectiveImmediateComparator profile who)) history).map
            History.state).support :=
    PMF.support_map .. ▸ ⟨final, reached, rfl⟩
  rw [service.effectiveImmediateComparator_terminal_law profile who permitted certificate baseline
    history remaining execution current compatible, current] at stateReached
  exact service.sourceCompatibleInfo_immediate_finish_charge_zero execution who
    (current ▸ (menu).toRawTrace (initialLaw service.setup) service.horizon service.scheduler
      history.trace) compatible
    ((menu).decodeProfile (initialLaw service.setup) service.horizon service.scheduler baseline)
    profile final.state stateReached sample authentic

/-- The comparator is shared by every hidden history at one actual compatible
information site, with no assumption on the assessment's belief there. -/
theorem effectiveImmediateComparator_charge_zero_at_information
    (profile : BehavioralProfile service.setup.program) (who : Player)
    (permitted : (profile who).Admitted service.setup.program (CommitmentInterface.values _))
    (certificate : ((menu).protocol (initialLaw service.setup) service.horizon
      service.scheduler).WellFoundedHistories)
    (baseline : ∀ player, ((menu).information (initialLaw service.setup) service.horizon
      service.scheduler).BehavioralPolicy player)
    (site : ((menu).information (initialLaw service.setup) service.horizon
      service.scheduler).InformationSite who)
    (compatible : service.sourceCompatibleInfo who site.1)
    (sample : List (SettledEvidence service.setup) → PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual) :
    ∀ history : ((menu).information (initialLaw service.setup) service.horizon
      service.scheduler).InformationHistory who site.1,
    ∀ final ∈ (((menu).information (initialLaw service.setup) service.horizon
      service.scheduler).runBehavioralTerminalFrom certificate
        (GameTheory.Profile.update (sig := ((menu).information (initialLaw service.setup)
          service.horizon service.scheduler).behavioralSignature) baseline who
            (service.effectiveImmediateComparator profile who)) history.1).support,
      TerminalAudit.charge ((runtime).serviceAuditObservation service.leaks)
        (sourceServiceAudit service.setup service.leaks sample) final.state who = 0 := by
  intro history final reached
  have active := InformationModel.InformationSite.active _ site history
  have input := ((menu).info (initialLaw service.setup) service.horizon service.scheduler who
    history.1.trace).symm.trans history.2
  cases current : history.1.state with
  | none =>
      rw [current] at active
      cases active
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      rw [current] at active input
      change actor = some who at active
      subst actor
      have actualCompatible : service.sourceCompatibleInfo who
          (some (execution.recall who, execution.observe (app) who)) := by
        rw [← input] at compatible
        simpa only [ReactiveApplication.observe, ↓reduceIte] using compatible
      exact service.effectiveImmediateComparator_terminal_charge_zero profile who permitted
        certificate baseline history.1 remaining execution current actualCompatible final reached
        sample authentic

open Classical in
/-- Authentic zero collection makes the actual immediate comparator worth at
least the finite base-payoff minimum under every belief on the compatible
information fiber. The opponents and the deposit are arbitrary. -/
theorem effectiveImmediateComparator_expected_utility_lower
    (base : (app).ProtocolState → Player → ℝ)
    (sample : List (SettledEvidence service.setup) → PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ)
    (profile : BehavioralProfile service.setup.program) (who : Player)
    (permitted : (profile who).Admitted service.setup.program (CommitmentInterface.values _))
    (certificate : ((menu).protocol (initialLaw service.setup) service.horizon
      service.scheduler).WellFoundedHistories)
    (baseline : ∀ player, ((menu).information (initialLaw service.setup) service.horizon
      service.scheduler).BehavioralPolicy player)
    (site : ((menu).information (initialLaw service.setup) service.horizon
      service.scheduler).InformationSite who)
    (compatible : service.sourceCompatibleInfo who site.1)
    (belief : PMF (((menu).information (initialLaw service.setup) service.horizon
      service.scheduler).InformationHistory who site.1)) :
    FinitePayoffBounds.lower (fun final : ((menu).protocol (initialLaw service.setup)
      service.horizon service.scheduler).History => base final.state who) ≤
      expect belief (fun history => expect (((menu).information (initialLaw service.setup)
        service.horizon service.scheduler).runBehavioralTerminalFrom certificate
        (GameTheory.Profile.update (sig := ((menu).information (initialLaw service.setup)
          service.horizon service.scheduler).behavioralSignature) baseline who
            (service.effectiveImmediateComparator profile who)) history.1)
        (fun final => TerminalAudit.utility base ((runtime).serviceAuditObservation service.leaks)
          (sourceServiceAudit service.setup service.leaks sample) deposit final.state who)) := by
  let extremum := fun final : ((menu).protocol (initialLaw service.setup) service.horizon
    service.scheduler).History => base final.state who
  have clean := service.effectiveImmediateComparator_charge_zero_at_information profile who
    permitted certificate baseline site compatible sample authentic
  rw [← expect_constant belief (FinitePayoffBounds.lower extremum)]
  apply expect_mono _ (payoffIntegrable_constant _ _) (payoffIntegrable_of_finite _ _)
  intro history _
  let law := ((menu).information (initialLaw service.setup) service.horizon
    service.scheduler).runBehavioralTerminalFrom certificate
      (GameTheory.Profile.update (sig := ((menu).information (initialLaw service.setup)
        service.horizon service.scheduler).behavioralSignature) baseline who
          (service.effectiveImmediateComparator profile who)) history.1
  rw [← expect_constant law (FinitePayoffBounds.lower extremum)]
  apply expect_mono _ (payoffIntegrable_constant _ _) (payoffIntegrable_of_finite _ _)
  intro final supported
  have zero := clean history final supported
  change FinitePayoffBounds.lower extremum ≤ base final.state who -
    TerminalAudit.charge ((runtime).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample) final.state who * deposit who
  rw [zero, zero_mul, sub_zero]
  exact FinitePayoffBounds.lower_le extremum final

end Vegas.AsyncServiceSpec
