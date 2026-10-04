/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRepeatedRepair
import GameTheory.Math.Probability.Conditioning
import Vegas.Game.SourceServiceDuplicatePackets
import Vegas.Game.AsyncServiceDeposit
import Interaction.ReactiveStopping

/-! # Final collection on actual repair exits

The actual classified draw or signed inclusion leaves authentic traffic at
the final endpoint. Coverage bounds the audit's averaged total charge there.
No renewed collection or value comparison for the retained tail is asserted.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

local instance (menu : (application setup leaks).ResponseMenu) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler) :
    Nonempty (menu.protocol (initialLaw setup) horizon scheduler).History :=
  ⟨(menu.protocol (initialLaw setup) horizon scheduler).initHistory⟩

omit [Fintype Player] in
private theorem response_tail_finish
    {horizon budget count : Nat} {scheduler : (application setup leaks).Scheduler}
    (players : Player → (application setup leaks).Policy)
    (before final : (application setup leaks).Execution) (who : Player)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨budget, some who, before⟩))
    (finalTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨0, none, final⟩))
    (response : (application setup leaks).Action)
    (drawn : response ∈ (players who (before.recall who)
      (before.observe (application setup leaks) who)).support)
    (tail : final ∈ ((application setup leaks).runRounds scheduler players count
      (before.respond (application setup leaks) who response)).support) :
    some ⟨0, none, final⟩ ∈ ((application setup leaks).finish (initialLaw setup) horizon
      scheduler players (some ⟨budget, some who, before⟩)).support := by
  let app := application setup leaks
  have beforeBudget := app.raw_trace_accounted (initialLaw setup) horizon scheduler trace
  have afterBudget := app.raw_trace_accounted (initialLaw setup) horizon scheduler finalTrace
  have length := app.runRounds_environmentRecall_length scheduler players count
    (before.respond app who response) final tail
  rw [app.respond_environmentRecall] at length
  change before.environmentRecall.length + budget = horizon at beforeBudget
  change final.environmentRecall.length + 0 = horizon at afterBudget
  have equal : count = budget := by omega
  subst count
  change _ ∈ (((app.invoke players who before).bind
    (app.runRounds scheduler players budget)).map app.finished).support
  rw [PMF.support_map]
  refine ⟨final, ?_, rfl⟩
  rw [PMF.support_bind]
  refine Set.mem_iUnion₂.mpr ⟨before.respond app who response, ?_, tail⟩
  rw [ReactiveApplication.invoke, PMF.support_map]
  exact ⟨response, drawn, rfl⟩

omit [Fintype Player] in
private theorem auditable_response_tail_collection
    {horizon budget count : Nat} {scheduler : (application setup leaks).Scheduler}
    (complete : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (players : Player → (application setup leaks).Policy)
    (before final : (application setup leaks).Execution) (who : Player)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨budget, some who, before⟩))
    (finalTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨0, none, final⟩))
    (response : (application setup leaks).Action)
    (drawn : response ∈ (players who (before.recall who)
      (before.observe (application setup leaks) who)).support)
    (classified : auditableServiceResponse setup leaks who (before.recall who)
      (before.observe (application setup leaks) who) response)
    (tail : final ∈ ((application setup leaks).runRounds scheduler players count
      (before.respond (application setup leaks) who response)).support)
    (backend : EvidenceReportService (SettledEvidence setup))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ player, 0 ≤ deliveryRate player)
    (coverage : FinalForbiddenEvidenceCoverage backend observationRate deliveryRate) :
    observationRate who * deliveryRate who ≤
      TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
        (sourceServiceAudit setup leaks backend.sample) (some ⟨0, none, final⟩) who := by
  let app := application setup leaks
  obtain ⟨material, sent, classified⟩ := classified
  have responseEq : response = ⟨some material⟩ := by
    cases response with
    | mk transmission => change transmission = some material at sent; cases sent; rfl
  subst response
  rw [localServiceEnvelope_actual setup leaks trace who material] at classified
  let record : app.TrafficRecord :=
    ⟨before.application.publicView, before.network.ledger,
      ⟨(who, before.network.nextSerial who), app.packet
        (app.submit before.application who material) who (before.network.known who) material⟩⟩
  have present : record ∈ app.executionTraffic final :=
    (app.executionTraffic_runRounds scheduler players count _ final tail).subset
      ((runtime setup).signed_response_traffic leaks before who material trace)
  let first : (app.protocol (initialLaw setup) horizon scheduler).History :=
    ⟨some ⟨budget, some who, before⟩, trace⟩
  have reached := response_tail_finish players before final who trace finalTrace
    ⟨some material⟩ drawn tail
  have law := (app.run_map_state (initialLaw setup) horizon scheduler players
    (app.rank horizon first.state) first).trans
      (app.iterate_eq_finish (initialLaw setup) horizon scheduler players
        (app.rank horizon first.state) first.state (le_refl _))
  have supported := (congrArg
    (fun distribution : PMF app.ProtocolState =>
      some ⟨0, none, final⟩ ∈ distribution.support) law.symm).mp reached
  obtain ⟨last, member, lastState⟩ := PMF.support_map .. ▸ supported
  have path := (app.protocol (initialLaw setup) horizon scheduler).runRandomizedFor_reachesWithin
    ((app.information (initialLaw setup) horizon scheduler).singleMoverChooser
      (app.singleMover (initialLaw setup) horizon scheduler)
        (fun owner => app.encodePolicy (players owner))) _ first last member
  have inputs := app.stateTraffic_inputs (initialLaw setup) horizon scheduler finalTrace
  change (app.executionTraffic final).map ReactiveApplication.TrafficRecord.envelope =
    final.network.inputs at inputs
  have emitted : Emitted setup leaks final record.envelope := by
    unfold Emitted
    rw [← inputs]
    exact List.mem_map.mpr ⟨record, present, rfl⟩
  have forbidden := auditableServicePacket_forbidden_reaches setup leaks path
    ⟨budget, some who, before⟩ ⟨0, none, final⟩ rfl lastState who record.envelope rfl rfl
      classified emitted (complete ⟨0, none, final⟩ finalTrace ⟨rfl, rfl⟩)
  exact (runtime setup).settledPacket_collection leaks backend observationRate deliveryRate
    delivery_nonnegative coverage ⟨0, none, final⟩ record present forbidden

omit [Fintype Player] in
/-- The actual exit and its true original tail persist a forbidden packet or
duplicate pair. Complete play and authentic coverage give a lower bound on
the final audit's total averaged charge, without a certain sampled catch. -/
theorem bindingRepairExit_final_collection
    {horizon count : Nat} {scheduler : (application setup leaks).Scheduler}
    (complete : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (players : Player → (application setup leaks).Policy) (who : Player)
    (checkpoint : (application setup leaks).Execution × (application setup leaks).Execution ×
      BindingMemory (runtime setup) leaks)
    (exited : BindingRepairExit horizon scheduler players who checkpoint)
    (final : (application setup leaks).Execution)
    (finalTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨0, none, final⟩))
    (tail : final ∈ ((application setup leaks).runRounds scheduler players count
      checkpoint.1).support)
    (backend : EvidenceReportService (SettledEvidence setup))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ player, 0 ≤ deliveryRate player)
    (coverage : FinalForbiddenEvidenceCoverage backend observationRate deliveryRate) :
    observationRate who * deliveryRate who ≤
      TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
        (sourceServiceAudit setup leaks backend.sample) (some ⟨0, none, final⟩) who := by
  let app := application setup leaks
  have terminal := complete ⟨0, none, final⟩ finalTrace ⟨rfl, rfl⟩
  rcases exited with ⟨budget, before, response, ⟨trace⟩, drawn, same, classified⟩ |
    ⟨budget, before, command, id, packet, ⟨trace⟩, _selected, _included, found, owned,
      breach, dispatched⟩
  · rw [same] at tail
    rcases classified with auditable | recorded
    · exact auditable_response_tail_collection complete players before final who trace finalTrace
        response drawn auditable tail backend observationRate deliveryRate
        delivery_nonnegative coverage
    · obtain ⟨event, recorded, named⟩ := recorded
      obtain ⟨material, responseEq⟩ : ∃ material, response = ⟨some material⟩ := by
        cases response with
        | mk transmission =>
            cases transmission with
            | none => simp [EventGraphRuntime.submittedEvent?] at named
            | some material => exact ⟨material, rfl⟩
      subst response
      obtain ⟨first, firstPresent, secondPresent, firstOwner, different, firstNamed,
        secondNamed⟩ := recordedResponse_duplicateTraffic before who trace event recorded
          material named
      have kept := (app.executionTraffic_runRounds scheduler players count _ final tail).subset
      exact duplicateTraffic_collection ⟨0, none, final⟩ finalTrace event who first _
        (kept firstPresent) (kept secondPresent) firstOwner rfl different firstNamed secondNamed
        terminal backend observationRate deliveryRate delivery_nonnegative coverage
  · have facts := settledFacts_history (initialLaw setup) horizon scheduler trace
    have emitted := facts.carried.lookup id ⟨id, packet⟩ found
    have inputs := app.stateTraffic_inputs (initialLaw setup) horizon scheduler trace
    change (app.executionTraffic before).map ReactiveApplication.TrafficRecord.envelope =
      before.network.inputs at inputs
    change (⟨id, packet⟩ : Message Player (WitnessedPacket (graph setup))) ∈
      before.network.inputs at emitted
    rw [← inputs] at emitted
    obtain ⟨record, present, envelope⟩ := List.mem_map.mp emitted
    have kept := (app.executionTraffic_runRounds scheduler players count checkpoint.1
      final tail).subset ((app.executionTraffic_dispatch players command before
        checkpoint.1 dispatched).subset present)
    have collected := (runtime setup).signedContentBreach_collection_of_finalCoverage leaks
      backend observationRate deliveryRate delivery_nonnegative coverage ⟨0, none, final⟩
        record kept (envelope.symm ▸ breach) terminal
    simpa only [envelope, Message.sender, owned, sourceServiceAudit, application] using collected

omit [Fintype Player] in
private theorem effective_rounds_history [Finite Player]
    (menu : (application setup leaks).ResponseMenu)
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    (profile : ∀ player,
      (menu.information (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    (first : (menu.protocol (initialLaw setup) horizon scheduler).History)
    (original final : (application setup leaks).Execution)
    (current : first.state = some ⟨remaining, none, original⟩)
    (reached : final ∈ ((application setup leaks).runRounds scheduler
      (menu.decodeProfile (initialLaw setup) horizon scheduler profile) remaining
        original).support) :
    ∃ last : (menu.protocol (initialLaw setup) horizon scheduler).History,
      last.state = some ⟨0, none, final⟩ := by
  let _ := Fintype.ofFinite Player
  let app := application setup leaks
  have law := menu.run_eq_finish (initialLaw setup) horizon scheduler profile
    (app.rank horizon first.state) first (le_refl _)
  have member : some ⟨0, none, final⟩ ∈ (app.finish (initialLaw setup) horizon scheduler
      (menu.decodeProfile (initialLaw setup) horizon scheduler profile) first.state).support := by
    rw [current]
    simp only [ReactiveApplication.finish, ReactiveApplication.resume, PMF.pure_bind,
      PMF.support_map]
    exact ⟨final, reached, rfl⟩
  rw [← law, PMF.support_map] at member
  obtain ⟨last, _supported, equal⟩ := member
  exact ⟨last, equal⟩

open Classical in
/-- At an actual effective final history, an exit's real collection bound
puts the original averaged audited value below the fixed base-payoff minimum.
The audit may still sample an uncollected verdict; the bound averages it. -/
theorem bindingRepairExit_final_utility_le_lower
    (bounds : MessageBounds (graph setup))
    {horizon count : Nat} {scheduler : (application setup leaks).Scheduler}
    [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
    (complete : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (players : Player → (application setup leaks).Policy) (who : Player)
    (checkpoint : (application setup leaks).Execution × (application setup leaks).Execution ×
      BindingMemory (runtime setup) leaks)
    (exited : BindingRepairExit horizon scheduler players who checkpoint)
    (final : (application setup leaks).Execution)
    (history : ((bounds.menu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (current : history.state = some ⟨0, none, final⟩)
    (tail : final ∈ ((application setup leaks).runRounds scheduler players count
      checkpoint.1).support)
    (base : (application setup leaks).ProtocolState → Player → ℝ)
    (backend : EvidenceReportService (SettledEvidence setup))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ player, 0 ≤ deliveryRate player)
    (coverage : FinalForbiddenEvidenceCoverage backend observationRate deliveryRate)
    (positive : 0 < observationRate who * deliveryRate who) :
    let probability := fun player => observationRate player * deliveryRate player
    let deposit := asyncAuditDeposit setup leaks bounds horizon scheduler base probability
    let extremum := fun next : ((bounds.menu (runtime setup) leaks).protocol
      (initialLaw setup) horizon scheduler).History => base next.state who
    TerminalAudit.utility base ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks backend.sample) deposit (some ⟨0, none, final⟩) who ≤
        FinitePayoffBounds.lower extremum := by
  intro probability deposit extremum
  have trace := current ▸ (bounds.menu (runtime setup) leaks).toRawTrace (initialLaw setup)
    horizon scheduler history.trace
  have collected := bindingRepairExit_final_collection complete players who checkpoint exited
    final trace tail backend observationRate deliveryRate delivery_nonnegative coverage
  have nonnegative := asyncAuditDeposit_nonnegative setup leaks bounds horizon scheduler
    base probability who positive
  have upper := FinitePayoffBounds.le_upper extremum history
  change base history.state who ≤ FinitePayoffBounds.upper extremum at upper
  rw [current] at upper
  have sufficient : FinitePayoffBounds.upper extremum - probability who * deposit who =
      FinitePayoffBounds.lower extremum := by
    change FinitePayoffBounds.upper extremum - probability who *
      ((FinitePayoffBounds.upper extremum - FinitePayoffBounds.lower extremum) /
        probability who) = FinitePayoffBounds.lower extremum
    rw [mul_div_cancel₀ _ positive.ne']
    ring
  change base _ who - _ * deposit who ≤ _
  exact (sub_le_sub upper (mul_le_mul_of_nonneg_right collected nonnegative)).trans
    sufficient.le

open Classical in
/-- The actual repeated coupling's original marginal and exit/tail witnesses
bound its final non-frame fiber. Policies are the actual full effective profile;
no assessment posterior, retained-tail cleanliness or right-value bound is used. -/
private theorem bindingRepair_complement_expected_utility_le_lower
    (bounds : MessageBounds (graph setup))
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
    (complete : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (profile : ∀ player, ((bounds.menu (runtime setup) leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    (who : Player)
    (first : ((bounds.menu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (original : (application setup leaks).Execution)
    (current : first.state = some ⟨remaining, none, original⟩)
    (coupling : PMF ((application setup leaks).Execution ×
      (application setup leaks).Execution × BindingMemory (runtime setup) leaks))
    (left : coupling.map Prod.fst = (application setup leaks).runRounds scheduler
      ((bounds.menu (runtime setup) leaks).decodeProfile (initialLaw setup) horizon
        scheduler profile) remaining original)
    (related : ∀ next ∈ coupling.support,
      (next.2.2.Frame (runtime setup) leaks who next.1 next.2.1 ∧
        next.2.2.shadow.OwnBindings who) ∨
      ∃ count checkpoint,
        BindingRepairExit horizon scheduler
          ((bounds.menu (runtime setup) leaks).decodeProfile (initialLaw setup) horizon
            scheduler profile) who checkpoint ∧
        next.1 ∈ ((application setup leaks).runRounds scheduler
          ((bounds.menu (runtime setup) leaks).decodeProfile (initialLaw setup) horizon
            scheduler profile) count checkpoint.1).support)
    (base : (application setup leaks).ProtocolState → Player → ℝ)
    (backend : EvidenceReportService (SettledEvidence setup))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ player, 0 ≤ deliveryRate player)
    (coverage : FinalForbiddenEvidenceCoverage backend observationRate deliveryRate)
    (positive : 0 < observationRate who * deliveryRate who) :
    let survived := fun next : (application setup leaks).Execution ×
      (application setup leaks).Execution × BindingMemory (runtime setup) leaks => decide
        (next.2.2.Frame (runtime setup) leaks who next.1 next.2.1 ∧
          next.2.2.shadow.OwnBindings who)
    let conditional := fiberPosterior coupling survived false
    let probability := fun player => observationRate player * deliveryRate player
    let deposit := asyncAuditDeposit setup leaks bounds horizon scheduler base probability
    let extremum := fun next : ((bounds.menu (runtime setup) leaks).protocol
      (initialLaw setup) horizon scheduler).History => base next.state who
    false ∈ (coupling.map survived).support →
      expect conditional (fun next => TerminalAudit.utility base
        ((runtime setup).serviceAuditObservation leaks) (sourceServiceAudit setup leaks
          backend.sample) deposit (some ⟨0, none, next.1⟩) who) ≤
        FinitePayoffBounds.lower extremum := by
  intro survived conditional probability deposit extremum possible
  let app := application setup leaks
  let menu := bounds.menu (runtime setup) leaks
  let payoff := fun next : app.Execution × app.Execution × BindingMemory (runtime setup) leaks =>
    TerminalAudit.utility base ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks backend.sample) deposit (some ⟨0, none, next.1⟩) who
  have actual (next : app.Execution × app.Execution × BindingMemory (runtime setup) leaks)
      (member : next ∈ conditional.support) :
      ∃ last : (menu.protocol (initialLaw setup) horizon scheduler).History,
        last.state = some ⟨0, none, next.1⟩ := by
    have outer := (mem_support_fiberPosterior possible member).2
    have supported : next.1 ∈ (app.runRounds scheduler
        (menu.decodeProfile (initialLaw setup) horizon scheduler profile)
        remaining original).support := by
      rw [← left, PMF.support_map]
      exact ⟨next, outer, rfl⟩
    exact effective_rounds_history menu profile first original next.1 current supported
  have nonnegative := asyncAuditDeposit_nonnegative setup leaks bounds horizon scheduler
    base probability who positive
  change 0 ≤ deposit who at nonnegative
  have integrable : PayoffIntegrable conditional payoff := by
    apply payoffIntegrable_of_abs_le_on_support (payoffIntegrable_constant conditional
      (|FinitePayoffBounds.lower extremum| + |FinitePayoffBounds.upper extremum| + deposit who))
    intro next member
    obtain ⟨last, equal⟩ := actual next member
    have lower := FinitePayoffBounds.lower_le extremum last
    have upper := FinitePayoffBounds.le_upper extremum last
    change FinitePayoffBounds.lower extremum ≤ base last.state who at lower
    change base last.state who ≤ FinitePayoffBounds.upper extremum at upper
    rw [equal] at lower upper
    have charge := TerminalAudit.charge_mem_Icc ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks backend.sample) (some ⟨0, none, next.1⟩) who
    have chargeLower := mul_nonneg charge.1 nonnegative
    have chargeUpper : TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
        (sourceServiceAudit setup leaks backend.sample) (some ⟨0, none, next.1⟩) who *
          deposit who ≤ deposit who := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right charge.2 nonnegative
    change |base _ who - _ * deposit who| ≤
      |(|FinitePayoffBounds.lower extremum| + |FinitePayoffBounds.upper extremum| + deposit who)|
    have constantNonnegative := add_nonneg
      (add_nonneg (abs_nonneg (FinitePayoffBounds.lower extremum))
        (abs_nonneg (FinitePayoffBounds.upper extremum))) nonnegative
    rw [abs_of_nonneg constantNonnegative, abs_le]
    constructor
    · linarith [neg_abs_le (FinitePayoffBounds.lower extremum),
        abs_nonneg (FinitePayoffBounds.upper extremum)]
    · linarith [le_abs_self (FinitePayoffBounds.upper extremum),
        abs_nonneg (FinitePayoffBounds.lower extremum)]
  apply expect_le_const conditional payoff integrable
    (FinitePayoffBounds.lower extremum)
  intro next member
  have selected := (mem_support_fiberPosterior possible member).1
  have outer := (mem_support_fiberPosterior possible member).2
  rcases related next outer with good | ⟨count, checkpoint, exited, tail⟩
  · change decide _ = false at selected
    rw [decide_eq_true good] at selected
    cases selected
  · obtain ⟨last, equal⟩ := actual next member
    exact bindingRepairExit_final_utility_le_lower bounds complete _ who checkpoint exited
      next.1 last equal tail base backend observationRate deliveryRate
        delivery_nonnegative coverage positive

open Classical in
/-- A selected initial unusable response and its actual retained default
produce the same repeated evaluator coupling with an original-side financial
bound on the final non-frame fiber. The profile may be the target assessment
with any whole focal alternative. Its foreign policies and all subsequent
retained tails are left unchanged, and no right-value comparison is claimed. -/
theorem sourceServiceMissing_unusable_repeated_exit_value_bound
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    (values : bounds.CoversBindingValues)
    {horizon leftRemaining rightRemaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
    (complete : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (original repaired : (application setup leaks).Execution) (who : Player)
    (memory : BindingMemory (runtime setup) leaks)
    (frame : memory.Frame (runtime setup) leaks who original repaired)
    (onlyBindings : memory.shadow.OwnBindings who)
    (past : memory.shadow.CompletedAt original.application.config)
    (initial : ((bounds.menu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (current : initial.state = some ⟨leftRemaining, some who, original⟩)
    (rightTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨rightRemaining, some who, repaired⟩))
    (rightAtTurn : OwnSubmissionsAtTurn setup leaks repaired who)
    (rightSlots : CanonicalSlotsUsed setup leaks repaired who)
    (clear : (runtime setup).serviceRisk leaks bound who (repaired.recall who)
      (repaired.observe (application setup leaks) who) = false)
    (response : (application setup leaks).Action)
    (effective : response ∈ (bounds.menu (runtime setup) leaks).actions who
      (original.recall who) (original.observe (application setup leaks) who))
    (unusable : unusableServiceBindingResponse setup leaks who (repaired.recall who)
      (repaired.observe (application setup leaks) who) response)
    (profile : ∀ player, ((bounds.menu (runtime setup) leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    (reference : List (application setup leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall who).length)
    (base : (application setup leaks).ProtocolState → Player → ℝ)
    (backend : EvidenceReportService (SettledEvidence setup))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ player, 0 ≤ deliveryRate player)
    (coverage : FinalForbiddenEvidenceCoverage backend observationRate deliveryRate)
    (positive : 0 < observationRate who * deliveryRate who) :
    let app := application setup leaks
    let menu := bounds.menu (runtime setup) leaks
    let players := menu.decodeProfile (initialLaw setup) horizon scheduler profile
    let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
      (bounds.riskMenu (runtime setup) leaks bound) who reference (players who)
    let input := (repaired.recall who, repaired.observe app who)
    let selected := BindingMemory.retainedResponse (runtime setup) leaks
      (bounds.riskMenu (runtime setup) leaks bound) who memory input response
    let remembered : BindingMemory (runtime setup) leaks :=
      ⟨selected.2, memory.responses ++ [(memory.shadow.inputView (runtime setup) leaks
        input.2, response)]⟩
    let probability := fun player => observationRate player * deliveryRate player
    let deposit := asyncAuditDeposit setup leaks bounds horizon scheduler base probability
    let extremum := fun next : (menu.protocol (initialLaw setup) horizon scheduler).History =>
      base next.state who
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = app.runRounds scheduler players leftRemaining
        (original.respond app who response) ∧
      coupling.map Prod.snd = strategy.runJoint who players scheduler leftRemaining
        (repaired.respond app who selected.1) remembered ∧
      let survived := fun next : app.Execution × app.Execution ×
        BindingMemory (runtime setup) leaks => decide
          (next.2.2.Frame (runtime setup) leaks who next.1 next.2.1 ∧
            next.2.2.shadow.OwnBindings who)
      false ∈ (coupling.map survived).support →
        expect (fiberPosterior coupling survived false) (fun next => TerminalAudit.utility base
          ((runtime setup).serviceAuditObservation leaks) (sourceServiceAudit setup leaks
            backend.sample) deposit (some ⟨0, none, next.1⟩) who) ≤
          FinitePayoffBounds.lower extremum := by
  intro app menu players strategy input selected remembered probability deposit extremum
  have rawTrace := current ▸ menu.toRawTrace (initialLaw setup) horizon scheduler initial.trace
  have copiedPlayers : Function.update players who
      (app.decodePolicy (menu.embedPolicy (initialLaw setup) horizon scheduler who
        (profile who))) = players := by
    change Function.update players who (players who) = players
    exact Function.update_eq_self who players
  obtain ⟨coupling, first, second, related⟩ :=
    sourceServiceMissing_unusable_repeated_repair_coupling bounds bound values complete
      original repaired who memory frame onlyBindings past rawTrace rightTrace rightAtTurn
      rightSlots clear response effective unusable (profile who) players reference started
  rw [copiedPlayers] at first second related
  refine ⟨coupling, first, second, ?_⟩
  let joint : Player → Option app.Action := fun player =>
    if player = who then some response else none
  have prior : (menu.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨leftRemaining, some who, original⟩) := current ▸ initial.trace
  have afterTrace : (menu.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨leftRemaining, none, original.respond app who response⟩) := by
    refine prior.extend joint ?_ ?_
    · constructor
      · simp [ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.terminal]
      · intro player
        by_cases same : player = who
        · subst player
          simpa [joint, ReactiveApplication.ResponseMenu.protocol,
            ReactiveApplication.ResponseMenu.available, ReactiveApplication.actor] using effective
        · simp [joint, ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.actor,
            same, Ne.symm same]
    · change _ ∈ (PMF.pure _).support
      simp only [joint, ↓reduceIte, Option.getD_some, PMF.mem_support_pure_iff _ _]
      rfl
  apply bindingRepair_complement_expected_utility_le_lower bounds complete profile who
    ⟨_, afterTrace⟩ (original.respond app who response) rfl coupling first ?_
      base backend observationRate deliveryRate delivery_nonnegative coverage positive
  intro next member
  rcases related next member with good |
    ⟨_stopped, _within, checkpoint, _leftPrefix, _rightPrefix, exited, leftTail, _rightTail⟩
  · exact Or.inl ⟨good.1, good.2.1⟩
  · exact Or.inr ⟨_, checkpoint, exited, leftTail⟩

end Vegas
