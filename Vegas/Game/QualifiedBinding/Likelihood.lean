/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.QualifiedBinding.ReplayCoverage

/-! # Literal native likelihood and selected source Nature mass -/

noncomputable section

namespace Vegas.PhaseProposalQualifiedBinding

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (values : ∀ who (key : setup.ProposalRecoveryComponent who),
    PMF (setup.CommitRecoveryValueChoice who key.1))

open scoped ENNReal

attribute [local implicit_reducible] InformationModel.InformationSite

variable (implementation : ReservedConcurrentImplementation setup)

local notation "nativeApplication" => implementation.application
local notation "nativeMenu" => PhaseCount.onePacketMenu implementation.runtime
  implementation.leaks implementation.bounds
local notation "nativeInitial" => implementation.initial
local notation "nativeProtocol" => ReactiveApplication.ResponseMenu.protocol
  nativeMenu nativeInitial implementation.horizon implementation.scheduler

/-- The actual trace's behavioral atoms and its transition mass form the
literal finite-history likelihood, before any source-coordinate partition. -/
private theorem sourceReplay_native_history_factor
    (profile : ∀ owner, ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).BehavioralPolicy owner)
    {state : (nativeProtocol).State} (trace : (nativeProtocol).Trace state) :
    (((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).historyReachWeight profile ⟨state, trace⟩).toReal =
      trace.transitionMass *
        ∏ owner, ((nativeMenu).information nativeInitial implementation.horizon
          implementation.scheduler).ownPlayReachProbability (profile owner)
            (((nativeMenu).information nativeInitial implementation.horizon
              implementation.scheduler).ownPlay owner trace) := by
  let model := (nativeMenu).information nativeInitial implementation.horizon
    implementation.scheduler
  obtain ⟨records, recordsEq, _provenance, chance, _nonnegative, mass, factor⟩ :=
    model.exists_continuation_ownPlay_factor
      (Trace.start : (nativeProtocol).Trace (nativeProtocol).init) trace
        (TracePrefix.start trace)
  have chanceEq : chance = trace.transitionMass := by
    simpa only [Trace.transitionMass_start, mul_one] using mass
  have recordsActual (owner : Player) : records owner = model.ownPlay owner trace := by
    simpa only [InfoSignals.ownPlay, List.append_nil] using (recordsEq owner).symm
  have exactFactor := factor profile
  simp only [Trace.length, Nat.sub_zero, chanceEq, recordsActual] at exactFactor
  exact exactFactor

/-- One actual command disintegrates against the posterior of the original
whole tape, including at zero command atoms. -/
private theorem sourceReplay_scheduler_density
    (past : List (nativeApplication).EnvironmentEntry)
    (view : (nativeApplication).EnvironmentView) (command : (nativeApplication).Command)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength) :
    implementation.scheduler past view command *
        ((nativeApplication).schedulerMixture implementation.prior
          (ReservedEpoch.family implementation.runtime implementation.leaks
            (ReservedEpoch.packetCapacity implementation.runtime))).posterior
              (past ++ [⟨view, command⟩]) tape =
      ((nativeApplication).schedulerMixture implementation.prior
          (ReservedEpoch.family implementation.runtime implementation.leaks
            (ReservedEpoch.packetCapacity implementation.runtime))).posterior past tape *
        ReservedEpoch.family implementation.runtime implementation.leaks
          (ReservedEpoch.packetCapacity implementation.runtime) tape past view command := by
  let mixture := (nativeApplication).schedulerMixture implementation.prior
    (ReservedEpoch.family implementation.runtime implementation.leaks
      (ReservedEpoch.packetCapacity implementation.runtime))
  let joint := (mixture.posterior past).bind fun selected =>
    mixture.respond selected (past, view)
  have marginal : joint.map Prod.fst = implementation.scheduler past view := rfl
  have density := mul_fiberPosterior_map_snd_apply joint command tape
  rw [marginal] at density
  have atom : joint (command, tape) = mixture.posterior past tape *
      ReservedEpoch.family implementation.runtime implementation.leaks
        (ReservedEpoch.packetCapacity implementation.runtime) tape past view command := by
    exact bind_map_tag_apply (mixture.posterior past)
      (fun selected => ReservedEpoch.family implementation.runtime implementation.leaks
        (ReservedEpoch.packetCapacity implementation.runtime) selected past view) command tape
  change implementation.scheduler past view command *
      mixture.posterior (past ++ [⟨view, command⟩]) tape = _
  rw [ReactiveApplication.SchedulerImplementation.posterior_snoc]
  exact density.trans atom

/-- Evaluate the existing transition kernel on the actual recorded path with
the original whole tape fixed. No new trace or support totalization is used. -/
private def sourceReplayFixedTransitionMass
    (tape : ReservedEpoch.Tape Player implementation.tapeLength) :
    ∀ {state : (nativeProtocol).State}, (nativeProtocol).Trace state → ℝ
  | _, .start => 1
  | after, @Trace.extend _ _ before _ prior joint _ _ =>
      sourceReplayFixedTransitionMass tape prior *
        ((nativeApplication).transition nativeInitial implementation.horizon
          (ReservedEpoch.family implementation.runtime implementation.leaks
            (ReservedEpoch.packetCapacity implementation.runtime) tape) before joint after).toReal

private theorem sourceReplay_tape_step_density
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    {before after : (nativeProtocol).State} (prior : (nativeProtocol).Trace before)
    (joint : Player → Option (nativeApplication).Action)
    (legal : (nativeProtocol).Legal before joint)
    (moved : after ∈ ((nativeProtocol).step before ⟨joint, legal⟩).support) :
    ((nativeProtocol).step before ⟨joint, legal⟩) after *
        prefixTapeLaw setup implementation ⟨after, prior.extend joint legal moved⟩ tape =
      prefixTapeLaw setup implementation ⟨before, prior⟩ tape *
        (nativeApplication).transition nativeInitial implementation.horizon
          (ReservedEpoch.family implementation.runtime implementation.leaks
            (ReservedEpoch.packetCapacity implementation.runtime) tape) before joint after := by
  cases before with
  | none =>
    change after ∈ ((nativeInitial).map fun state =>
      some (⟨implementation.horizon, none,
        ReactiveApplication.Execution.initial nativeApplication state⟩ :
          (nativeApplication).Control)).support at moved
    obtain ⟨state, _supported, rfl⟩ := PMF.support_map .. ▸ moved
    change _ * implementation.prior tape = implementation.prior tape * _
    exact mul_comm _ _
  | some control =>
    rcases control with ⟨remaining, actor, execution⟩
    cases actor with
    | some owner =>
      change after ∈ (PMF.pure (some (⟨remaining, none,
        execution.respond nativeApplication owner ((joint owner).getD ⟨none⟩)⟩ :
          (nativeApplication).Control))).support at moved
      cases (PMF.mem_support_pure_iff ..).mp moved
      simp only [ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.transition,
        PMF.pure_apply, ↓reduceIte, prefixTapeLaw,
        ReactiveApplication.respond_environmentRecall, one_mul, mul_one]
    | none =>
      cases remaining with
      | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
      | succ remaining =>
        change after ∈ ((implementation.scheduler execution.environmentRecall
          (execution.observeEnvironment nativeApplication)).bind fun command =>
            (execution.environmentStep nativeApplication command).map fun next =>
              some (⟨remaining, command.actor? nativeApplication, next⟩ :
                (nativeApplication).Control)).support at moved
        obtain ⟨command, _chosen, supported⟩ :=
          Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
        obtain ⟨next, advanced, rfl⟩ := PMF.support_map .. ▸ supported
        change (nativeApplication).transition nativeInitial implementation.horizon
          implementation.scheduler (some ⟨remaining + 1, none, execution⟩) joint
            (some ⟨remaining, command.actor? nativeApplication, next⟩) * _ = _
        rw [(nativeApplication).transition_environment_apply nativeInitial
            implementation.horizon implementation.scheduler remaining execution next command
              advanced joint,
          (nativeApplication).transition_environment_apply nativeInitial
            implementation.horizon
              (ReservedEpoch.family implementation.runtime implementation.leaks
                (ReservedEpoch.packetCapacity implementation.runtime) tape) remaining execution
                  next command advanced joint]
        have recorded := (nativeApplication).environmentStep_environmentRecall execution next
          command advanced
        simp only [prefixTapeLaw, recorded]
        have density := sourceReplay_scheduler_density setup implementation
          execution.environmentRecall (execution.observeEnvironment nativeApplication) command tape
        let mixture := (nativeApplication).schedulerMixture implementation.prior
          (ReservedEpoch.family implementation.runtime implementation.leaks
            (ReservedEpoch.packetCapacity implementation.runtime))
        calc
          _ = (implementation.scheduler execution.environmentRecall
              (execution.observeEnvironment nativeApplication) command *
                mixture.posterior (execution.environmentRecall ++
                  [⟨execution.observeEnvironment nativeApplication, command⟩]) tape) *
                    (execution.environmentStep nativeApplication command) next := by ac_rfl
          _ = _ := by rw [density]; ac_rfl

/-- The original tape posterior telescopes along the actual trace. All
initializer and public Nature atoms stay in the fixed-tape transition product. -/
private theorem sourceReplay_transition_tape_factor
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    {state : (nativeProtocol).State} (trace : (nativeProtocol).Trace state) :
    trace.transitionMass * (prefixTapeLaw setup implementation ⟨state, trace⟩ tape).toReal =
      (implementation.prior tape).toReal *
        sourceReplayFixedTransitionMass setup implementation tape trace := by
  induction trace with
  | start =>
    change 1 * (implementation.prior tape).toReal = (implementation.prior tape).toReal * 1
    ring
  | @extend before after prior joint legal moved ih =>
    have density := congrArg ENNReal.toReal
      (sourceReplay_tape_step_density setup implementation tape prior joint legal moved)
    simp only [ENNReal.toReal_mul] at density
    rw [Trace.transitionMass_extend, sourceReplayFixedTransitionMass]
    calc
      _ = prior.transitionMass * _ := by ring
      _ = prior.transitionMass *
          ((prefixTapeLaw setup implementation ⟨before, prior⟩ tape).toReal * _) :=
            congrArg (prior.transitionMass * ·) density
      _ = _ := by rw [← mul_assoc, ih]; ring

/-- Literal native reach with its original whole tape is the fixed-tape
Nature product times every actual own-response product. -/
private theorem sourceReplay_native_tape_factor
    (profile : ∀ owner, ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).BehavioralPolicy owner)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    {state : (nativeProtocol).State} (trace : (nativeProtocol).Trace state) :
    (((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).historyReachWeight profile ⟨state, trace⟩).toReal *
          (prefixTapeLaw setup implementation ⟨state, trace⟩ tape).toReal =
      (implementation.prior tape).toReal *
        sourceReplayFixedTransitionMass setup implementation tape trace *
          ∏ owner, ((nativeMenu).information nativeInitial implementation.horizon
            implementation.scheduler).ownPlayReachProbability (profile owner)
              (((nativeMenu).information nativeInitial implementation.horizon
                implementation.scheduler).ownPlay owner trace) := by
  rw [sourceReplay_native_history_factor setup implementation profile trace]
  let own := ∏ owner, ((nativeMenu).information nativeInitial implementation.horizon
    implementation.scheduler).ownPlayReachProbability (profile owner)
      (((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).ownPlay owner trace)
  change (trace.transitionMass * own) *
    (prefixTapeLaw setup implementation ⟨state, trace⟩ tape).toReal =
      (implementation.prior tape).toReal *
        sourceReplayFixedTransitionMass setup implementation tape trace * own
  calc
    _ = (trace.transitionMass *
        (prefixTapeLaw setup implementation ⟨state, trace⟩ tape).toReal) * own := by ring
    _ = _ := by rw [sourceReplay_transition_tape_factor setup implementation tape trace]

/-- Menu restriction preserves the literal product of reference-response atoms
at every original private input on the actual native trace. -/
private theorem sourceReplay_prescribed_own_atom
    (rates : PhaseProposalRates) (owner : Player) (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control)) :
    ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).ownPlayReachProbability
      (phaseProposalReferenceStrategy setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan nativeInitial implementation.horizon
          implementation.scheduler values rates owner)
      (((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).ownPlay owner trace) =
      (((nativeApplication).privateTranscriptFrom [] (control.execution.recall owner)).map
        (fun record => phaseProposalReferencePolicy setup .concurrent implementation.runtime
          implementation.leaks implementation.bounds implementation.plan values rates owner
            record.1.1 record.1.2 record.2)).prod.toReal := by
  have own : ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).ownPlay owner trace =
      (nativeApplication).recallOwnPlay (control.execution.recall owner) := by
    change ((nativeMenu).signals nativeInitial implementation.horizon
      implementation.scheduler).ownPlay owner trace = _
    rw [← (nativeMenu).ownPlay_toRawTrace nativeInitial implementation.horizon
      implementation.scheduler owner trace, (nativeApplication).trace_ownPlay]
    rfl
  rw [own]
  exact (nativeMenu).ownPlayFrom_restrictPolicy nativeInitial implementation.horizon
    implementation.scheduler owner
      (phaseProposalReferencePolicy setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan values rates owner)
      (fun past view response supported => phaseProposalReferencePolicy_covered setup .concurrent
        implementation.runtime implementation.leaks implementation.bounds implementation.plan
          values rates owner past view response supported) [] (control.execution.recall owner)

/-- The prescribed native atom retains the whole initial law, original tape,
public Nature and each literal response probability at its actual input. -/
private theorem sourceReplay_prescribed_native_atom
    (rates : PhaseProposalRates)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control)) :
    (((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).historyReachWeight
      (phaseProposalReferenceStrategy setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan nativeInitial implementation.horizon
          implementation.scheduler values rates) ⟨some control, trace⟩).toReal *
            (prefixTapeLaw setup implementation ⟨some control, trace⟩ tape).toReal =
      (implementation.prior tape).toReal *
        sourceReplayFixedTransitionMass setup implementation tape trace *
          ∏ owner, (((nativeApplication).privateTranscriptFrom []
            (control.execution.recall owner)).map (fun record =>
              phaseProposalReferencePolicy setup .concurrent implementation.runtime
                implementation.leaks implementation.bounds implementation.plan values rates owner
                  record.1.1 record.1.2 record.2)).prod.toReal := by
  rw [sourceReplay_native_tape_factor setup implementation
    (phaseProposalReferenceStrategy setup .concurrent implementation.runtime implementation.leaks
      implementation.bounds implementation.plan nativeInitial implementation.horizon
        implementation.scheduler values rates) tape trace]
  apply congrArg (fun product => (implementation.prior tape).toReal *
    sourceReplayFixedTransitionMass setup implementation tape trace * product)
  exact Finset.prod_congr rfl fun owner _ =>
    sourceReplay_prescribed_own_atom setup values implementation rates owner control trace

/-- At an actual counted input, the physical response atom separates into
its genuine class atom and the literal alias-script atom at that same input. -/
private theorem sourceReplay_counted_response_atom
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (rates : PhaseProposalRates) (waitPositive : 0 < rates.waiting.val)
    (waitBelow : rates.waiting.val < 1) (slotPositive : 0 < rates.slots.val)
    (badPositive : 0 < rates.badPreparation.val) (badBelow : rates.badPreparation.val < 1)
    (remaining : Nat) (owner : Player) (execution : (nativeApplication).Execution)
    (trace : (nativeProtocol).Trace (some ⟨remaining, some owner, execution⟩))
    (tag : Option (Handle (serviceGraph setup .concurrent) × Raw L))
    (response : PhaseProposal.Response implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner)) :
    phaseProposalReferencePolicy setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan values rates owner (execution.recall owner)
          (execution.observe nativeApplication owner) response.val =
      phaseProposalBaseClasses setup .concurrent implementation.runtime implementation.leaks
          implementation.bounds implementation.plan values rates owner (execution.recall owner)
            (execution.observe nativeApplication owner)
              (PhaseProposal.projectResponse implementation.runtime implementation.leaks
                implementation.bounds owner (execution.recall owner)
                  (execution.observe nativeApplication owner) response) *
        sourceReplayAliases setup implementation rates.aliases owner execution tag
          (PhaseProposal.projectResponse implementation.runtime implementation.leaks
            implementation.bounds owner (execution.recall owner)
              (execution.observe nativeApplication owner) response) (tag, some response.val) := by
  classical
  unfold phaseProposalReferencePolicy
  rw [pmf_map_apply_of_injective _ Subtype.val_injective response]
  unfold phaseProposalReferenceResponses PhaseProposal.splitResponseLaw
  rw [phaseProposalReferenceClasses_eq_of_counted setup .concurrent implementation.runtime
    implementation.leaks implementation.bounds implementation.plan operational.completePending
      operational.outputValues operational.maximalPhases values fullValues rates waitPositive
        waitBelow slotPositive badPositive badBelow implementation.horizon implementation.scheduler
          remaining owner execution trace]
  rw [sourceReplayAliases_atom setup implementation rates.aliases owner execution tag _ response]
  exact bind_apply_of_unique_branch _ _ response
    (PhaseProposal.projectResponse implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner) response)
    (fun selected _ supported => (PMF.splitKernel_supported _ _ _ _ _ _ selected response
      supported).symm)

/-- A silent or noncommitment packet has no hidden preparation coordinate.
Its genuine class atom is exactly its mechanical packet atom, and its private
syntax contributes the alias atom at the actual counted input. -/
private theorem sourceReplay_noncommit_response_atom
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (rates : PhaseProposalRates) (waitPositive : 0 < rates.waiting.val)
    (waitBelow : rates.waiting.val < 1) (slotPositive : 0 < rates.slots.val)
    (badPositive : 0 < rates.badPreparation.val) (badBelow : rates.badPreparation.val < 1)
    (remaining : Nat) (owner : Player) (execution : (nativeApplication).Execution)
    (trace : (nativeProtocol).Trace (some ⟨remaining, some owner, execution⟩))
    (tag : Option (Handle (serviceGraph setup .concurrent) × Raw L))
    (response : PhaseProposal.Response implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner))
    (noncommit : ∀ material, response.val.transmission = some material →
      ∀ event handle, material.call.packet ≠ .commitment event handle) :
    phaseProposalBaseClasses setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan values rates owner (execution.recall owner)
          (execution.observe nativeApplication owner)
          (PhaseProposal.projectResponse implementation.runtime implementation.leaks
            implementation.bounds owner (execution.recall owner)
              (execution.observe nativeApplication owner) response) =
      foreignMechanicalAtom setup implementation rates execution owner response.val ∧
    phaseProposalReferencePolicy setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan values rates owner (execution.recall owner)
          (execution.observe nativeApplication owner) response.val =
      foreignMechanicalAtom setup implementation rates execution owner response.val *
        sourceReplayAliases setup implementation rates.aliases owner execution tag
          (PhaseProposal.projectResponse implementation.runtime implementation.leaks
            implementation.bounds owner (execution.recall owner)
              (execution.observe nativeApplication owner) response) (tag, some response.val) := by
  classical
  let past := execution.recall owner
  let view := execution.observe nativeApplication owner
  let packet := fun action : (nativeApplication).Action => action.transmission.map
    (fun material => (PhaseCount.localEnvelope implementation.runtime implementation.leaks
      owner past view material).payload)
  let project := PhaseProposal.projectResponse implementation.runtime implementation.leaks
    implementation.bounds owner past view
  let classes := phaseProposalBaseClasses setup .concurrent implementation.runtime
    implementation.leaks implementation.bounds implementation.plan values rates owner past view
  have preparation (action : (nativeApplication).Action)
      (same : packet action = packet response.val) :
      action.transmission.bind PhaseProposal.bindingPreparation = none := by
    cases transmitted : action.transmission with
    | none => simp only [Option.bind_none]
    | some material =>
        cases original : response.val.transmission with
        | none =>
            simp only [packet, transmitted, original, Option.map_some, Option.map_none,
              reduceCtorEq] at same
        | some fixed =>
            have calls := congrArg (fun selected => selected.map
              (fun entry : CommitAttemptPacket (serviceGraph setup .concurrent) =>
                entry.packet.call)) same
            have call : material.call.packet = fixed.call.packet := by
              simpa only [packet, transmitted, original, Option.map_some,
                PhaseCount.localEnvelope, PhaseCount.maskPacket_call, Option.some.injEq]
                using calls
            cases shape : material.call.packet with
            | commitment event handle =>
                exact False.elim (noncommit fixed original event handle (call.symm.trans shape))
            | opening event handle raw =>
                simp only [Option.bind_some, PhaseProposal.bindingPreparation, shape]
            | malformed raw =>
                simp only [Option.bind_some, PhaseProposal.bindingPreparation, shape]
  have unique (selected : PhaseProposal.ResponseClass implementation.runtime
      implementation.leaks implementation.bounds owner past view)
      (same : selected.val.2 = (project response).val.2) : selected = project response := by
    obtain ⟨other, represented⟩ := selected.property
    have packets := same
    rw [← represented] at packets
    change packet other.val = packet response.val at packets
    apply Subtype.ext
    rw [← represented]
    apply Prod.ext
    · exact (preparation other.val packets).trans
        (preparation response.val rfl).symm
    · exact packets
  have classAtom : (classes.map fun selected => selected.val.2) (project response).val.2 =
      classes (project response) := by
    rw [← pmf_bind_pure_eq_map,
      bind_apply_of_unique_branch classes (fun selected => PMF.pure selected.val.2)
        (project response).val.2 (project response)]
    · rw [PMF.pure_apply_self, mul_one]
    · intro selected _ supported
      exact unique selected ((PMF.mem_support_pure_iff ..).mp supported).symm
  have marginal : (classes.map fun selected => selected.val.2) =
      (phaseProposalBasePolicy setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan values rates owner past view).map packet := by
    dsimp only [classes]
    rw [phaseProposalBaseClasses, PMF.map_comp,
      ← phaseProposalBaseResponses_map_val setup .concurrent implementation.runtime
        implementation.leaks implementation.bounds implementation.plan values rates owner
          past view, PMF.map_comp]
    rfl
  have mechanical : foreignMechanicalAtom setup implementation rates execution owner response.val =
      classes (project response) := by
    dsimp only [foreignMechanicalAtom]
    rw [mechanicalForeignPolicy_packet_eq_base setup values implementation, ← marginal]
    change (classes.map fun selected => selected.val.2) (project response).val.2 * _ = _
    rw [classAtom]
    cases transmitted : response.val.transmission with
    | none => simp only [mul_one]
    | some material =>
        cases shape : material.call.packet with
        | commitment event handle => exact (noncommit material transmitted event handle shape).elim
        | opening event handle raw => simp only [shape, mul_one]
        | malformed raw => simp only [shape, mul_one]
  refine ⟨mechanical.symm, ?_⟩
  rw [sourceReplay_counted_response_atom setup values implementation operational fullValues rates
    waitPositive waitBelow slotPositive badPositive badBelow remaining owner execution trace tag
      response, mechanical]

/-- One actual proper foreign response charges its mapped ordinary draw once;
the preparation flag stays inside the mechanical atom and the alias stays at
the actual reconstructed input. -/
private theorem sourceReplay_proper_response_atom
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (rates : PhaseProposalRates) (waitPositive : 0 < rates.waiting.val)
    (waitBelow : rates.waiting.val < 1) (slotPositive : 0 < rates.slots.val)
    (badPositive : 0 < rates.badPreparation.val) (badBelow : rates.badPreparation.val < 1)
    (remaining : Nat) (owner : Player) (execution : (nativeApplication).Execution)
    (trace : (nativeProtocol).Trace (some ⟨remaining, some owner, execution⟩))
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (key : setup.ProposalRecoveryComponent owner)
    (query : phaseProposalQuery? setup .concurrent implementation.runtime implementation.leaks
      implementation.plan owner event (execution.recall owner)
        (execution.observe nativeApplication owner) = some key)
    (response : PhaseProposal.Response implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner))
    (material : WitnessedSubmission (serviceGraph setup .concurrent))
    (sent : response.val.transmission = some material)
    (value : L.Val payload)
    (prepared : PhaseProposal.bindingPreparation material = some (⟨payload, value⟩ : Raw L))
    (serial : Nat) (packet : material.call.packet = .commitment event (owner, .prepared serial))
    (tag : Option (Handle (serviceGraph setup .concurrent) × Raw L)) :
    phaseProposalReferencePolicy setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan values rates owner (execution.recall owner)
          (execution.observe nativeApplication owner) response.val =
      foreignMechanicalAtom setup implementation rates execution owner response.val *
        ((values owner key).map (fun choice => phaseRecoveryDomainValue setup .concurrent event
          owner payload binding choice.val.val)) value *
        sourceReplayAliases setup implementation rates.aliases owner execution tag
          (PhaseProposal.projectResponse implementation.runtime implementation.leaks
            implementation.bounds owner (execution.recall owner)
              (execution.observe nativeApplication owner) response) (tag, some response.val) := by
  unfold phaseProposalReferencePolicy
  rw [pmf_map_apply_of_injective _ Subtype.val_injective response,
    (foreign_binding_response_atom setup values implementation operational fullValues rates
      waitPositive waitBelow slotPositive badPositive badBelow remaining owner execution trace event
        payload binding request key query response material sent value prepared serial packet).2,
    sourceReplayAliases_atom setup implementation rates.aliases owner execution tag _ response]

/-- A proper counted SEND supplies its genuine typed query and its literal
draw atom at that actual input. Neither is an additional ledger premise. -/
private theorem sourceReplay_proper_callback_atom
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (rates : PhaseProposalRates) (waitPositive : 0 < rates.waiting.val)
    (waitBelow : rates.waiting.val < 1) (slotPositive : 0 < rates.slots.val)
    (badPositive : 0 < rates.badPreparation.val) (badBelow : rates.badPreparation.val < 1)
    (remaining : Nat) (owner : Player) (execution : (nativeApplication).Execution)
    (trace : (nativeProtocol).Trace (some ⟨remaining, some owner, execution⟩))
    (response : PhaseProposal.Response implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner))
    (clean : ¬ PhaseProposal.GeneratedUnusableBindingAction implementation.runtime
      implementation.leaks owner response.val)
    (material : WitnessedSubmission (serviceGraph setup .concurrent))
    (sent : response.val.transmission = some material)
    (event : (serviceGraph setup .concurrent).EventId)
    (handle : Handle (serviceGraph setup .concurrent))
    (packet : material.call.packet = .commitment event handle)
    (tag : Option (Handle (serviceGraph setup .concurrent) × Raw L)) :
    ∃ (payload : L.Ty)
      (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
      (key : setup.ProposalRecoveryComponent owner) (serial : Nat) (value : L.Val payload),
      handle = (owner, .prepared serial) ∧
      execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩ ∧
      phaseProposalQuery? setup .concurrent implementation.runtime implementation.leaks
        implementation.plan owner event (execution.recall owner)
          (execution.observe nativeApplication owner) = some key ∧
      PhaseProposal.bindingPreparation material = some (⟨payload, value⟩ : Raw L) ∧
      phaseProposalBaseClasses setup .concurrent implementation.runtime implementation.leaks
          implementation.bounds implementation.plan values rates owner (execution.recall owner)
            (execution.observe nativeApplication owner)
            (PhaseProposal.projectResponse implementation.runtime implementation.leaks
              implementation.bounds owner (execution.recall owner)
                (execution.observe nativeApplication owner) response) =
        foreignMechanicalAtom setup implementation rates execution owner response.val *
          ((values owner key).map (fun choice => phaseRecoveryDomainValue setup .concurrent event
            owner payload binding choice.val.val)) value ∧
      phaseProposalReferencePolicy setup .concurrent implementation.runtime implementation.leaks
          implementation.bounds implementation.plan values rates owner (execution.recall owner)
            (execution.observe nativeApplication owner) response.val =
        foreignMechanicalAtom setup implementation rates execution owner response.val *
          ((values owner key).map (fun choice => phaseRecoveryDomainValue setup .concurrent event
            owner payload binding choice.val.val)) value *
          sourceReplayAliases setup implementation rates.aliases owner execution tag
            (PhaseProposal.projectResponse implementation.runtime implementation.leaks
              implementation.bounds owner (execution.recall owner)
                (execution.observe nativeApplication owner) response) (tag, some response.val) := by
  classical
  have action : response.val = (⟨some material⟩ : (nativeApplication).Action) :=
    congrArg (fun selected => (⟨selected⟩ : (nativeApplication).Action)) sent
  have available : (⟨some material⟩ : (nativeApplication).Action) ∈
      PhaseCount.onePacketActions implementation.runtime implementation.leaks
        implementation.bounds owner (execution.recall owner)
          (execution.observe nativeApplication owner) := action ▸ response.property
  have initialEq : (setup.initialLaw.map encodeInputs).map
      (PhaseRuntimeState.initial implementation.plan) = nativeInitial := PMF.map_comp _ _ _
  have counted : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
        implementation.horizon implementation.scheduler).Trace
          (some ⟨remaining, some owner, execution⟩) := by
    rw [initialEq]
    exact trace
  obtain ⟨coordinate, requested⟩ := PhaseCount.onePacket_request_of_nonsilent
    implementation.runtime implementation.leaks implementation.bounds implementation.plan
      (setup.initialLaw.map encodeInputs) implementation.horizon implementation.scheduler
        remaining owner execution counted material available
  have named := PhaseCount.onePacket_event_of_request implementation.runtime implementation.leaks
    implementation.bounds implementation.plan (serviceGraph_revealRelaxedOrdered setup .concurrent)
      (setup.initialLaw.map encodeInputs) implementation.horizon implementation.scheduler
        remaining owner execution counted coordinate requested material available
  rw [packet] at named
  have eventEq : coordinate.event = event := Option.some.inj named.symm
  have request := requested
  change execution.application.SeedRequest owner ⟨coordinate.attempt, coordinate.event⟩ at request
  rw [requested.1, eventEq] at request
  have permitted : PhaseCount.permits ((nativeApplication).outputs (execution.recall owner))
      (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
        (execution.recall owner) (execution.observe nativeApplication owner) material) = true := by
    rcases ((PhaseCount.mem_onePacketActions implementation.runtime implementation.leaks
      implementation.bounds owner _ _ _).mp available).2 with impossible |
        ⟨other, same, permitted⟩
    · cases impossible
    · cases Option.some.inj same
      exact permitted
  have correct := ((PhaseCount.permits_eq_true_iff _ _).mp permitted).2.1
  have call : (PhaseCount.nativeMessage (PhaseCount.localEnvelope implementation.runtime
      implementation.leaks owner (execution.recall owner)
        (execution.observe nativeApplication owner) material)).payload.call =
      material.call.packet := PhaseCount.maskPacket_call _ _
  unfold CountCallCorrect at correct
  rw [call, packet] at correct
  obtain ⟨owned, _evidence, handleOwned, ⟨serial, slot⟩, _unused⟩ := correct
  change handle.1 = owner at handleOwned
  have handleEq : handle = (owner, .prepared serial) := Prod.ext handleOwned slot
  have owned' : bindingOwnedBy (serviceGraph setup .concurrent) owner event = true := owned
  obtain ⟨payload, binding⟩ : ∃ payload,
      (serviceGraph setup .concurrent).outputLayout event = .binding owner payload := by
    cases output : (serviceGraph setup .concurrent).outputLayout event with
    | binding actor payload =>
        have same : actor = owner := by
          simpa only [bindingOwnedBy, output, decide_eq_true_eq] using owned'
        subst actor
        exact ⟨payload, rfl⟩
    | publicData payload => simp only [bindingOwnedBy, output, Bool.false_eq_true] at owned'
    | privateInput actor payload =>
        simp only [bindingOwnedBy, output, Bool.false_eq_true] at owned'
    | publication payload => simp only [bindingOwnedBy, output, Bool.false_eq_true] at owned'
  have shape : response.val =
      (⟨some ⟨⟨.commitment event (owner, .prepared serial), material.call.opening⟩,
        material.evidence⟩⟩ : (nativeApplication).Action) := by
    rw [← handleEq, ← packet]
    exact action
  have usable : material.call.opening.bind (fun raw => raw.as? payload) ≠ none := by
    intro missing
    exact clean ⟨event, payload, serial, material.call.opening, material.evidence, binding,
      shape, missing⟩
  obtain ⟨value, decoded⟩ := Option.ne_none_iff_exists'.mp usable
  have prepared : PhaseProposal.bindingPreparation material =
      some (⟨payload, value⟩ : Raw L) := by
    simp only [PhaseProposal.bindingPreparation, packet, binding, decoded, Option.map_some]
  have rawTrace := (nativeMenu).toRawTrace nativeInitial implementation.horizon
    implementation.scheduler trace
  obtain ⟨key, query, _positive⟩ := phaseProposalDomainValues_fullSupport_of_binding setup
    .concurrent implementation.runtime implementation.leaks operational.completePending
      implementation.plan operational.maximalPhases values fullValues implementation.horizon
        implementation.scheduler rawTrace owner rfl event payload binding request
  refine ⟨payload, binding, key, serial, value, handleEq, request, query, prepared, ?_, ?_⟩
  · exact (foreign_binding_response_atom setup values implementation operational fullValues rates
      waitPositive waitBelow slotPositive badPositive badBelow remaining owner execution trace event
        payload binding request key query response material sent value prepared serial
          (packet.trans (congrArg (Payload.commitment event) handleEq))).1
  · exact sourceReplay_proper_response_atom setup values implementation operational fullValues rates
      waitPositive waitBelow slotPositive badPositive badBelow remaining owner execution trace event
        payload binding request key query response material sent value prepared serial
          (packet.trans (congrArg (Payload.commitment event) handleEq)) tag

open Classical in
/-- The proper typed draw at one literal binding callback. Silent callbacks
and nonbinding packets contribute one; the queried law uses this actual input. -/
private def sourceReplayBindingDrawAtom
    (owner : Player) (past : List (nativeApplication).PlayerEntry)
    (view : (nativeApplication).PlayerView) (action : (nativeApplication).Action) : ℝ≥0∞ :=
  match action.transmission with
  | none => 1
  | some material => match material.call.packet with
    | .commitment event _ => match PhaseProposal.bindingPreparation material with
      | none => 0
      | some ⟨payload, value⟩ =>
        if binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload
          then match phaseProposalQuery? setup .concurrent implementation.runtime
              implementation.leaks implementation.plan owner event past view with
          | none => 0
          | some key => ((values owner key).map (fun choice => phaseRecoveryDomainValue setup
              .concurrent event owner payload binding choice.val.val)) value
        else 0
    | .opening .. | .malformed .. => 1

/-- At a genuine clean callback the class contains exactly its mechanical
factor and, only for a proper SEND, its literal updated queried draw. -/
private theorem sourceReplay_clean_callback_draw_atom
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (rates : PhaseProposalRates) (waitPositive : 0 < rates.waiting.val)
    (waitBelow : rates.waiting.val < 1) (slotPositive : 0 < rates.slots.val)
    (badPositive : 0 < rates.badPreparation.val) (badBelow : rates.badPreparation.val < 1)
    (remaining : Nat) (owner : Player) (execution : (nativeApplication).Execution)
    (trace : (nativeProtocol).Trace (some ⟨remaining, some owner, execution⟩))
    (response : PhaseProposal.Response implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner))
    (clean : ¬ PhaseProposal.GeneratedUnusableBindingAction implementation.runtime
      implementation.leaks owner response.val)
    (tag : Option (Handle (serviceGraph setup .concurrent) × Raw L)) :
    let draw := sourceReplayBindingDrawAtom setup values implementation owner
      (execution.recall owner) (execution.observe nativeApplication owner) response.val
    phaseProposalBaseClasses setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan values rates owner (execution.recall owner)
          (execution.observe nativeApplication owner)
          (PhaseProposal.projectResponse implementation.runtime implementation.leaks
            implementation.bounds owner (execution.recall owner)
              (execution.observe nativeApplication owner) response) =
        foreignMechanicalAtom setup implementation rates execution owner response.val * draw ∧
      phaseProposalReferencePolicy setup .concurrent implementation.runtime implementation.leaks
          implementation.bounds implementation.plan values rates owner (execution.recall owner)
            (execution.observe nativeApplication owner) response.val =
        foreignMechanicalAtom setup implementation rates execution owner response.val * draw *
          sourceReplayAliases setup implementation rates.aliases owner execution tag
            (PhaseProposal.projectResponse implementation.runtime implementation.leaks
              implementation.bounds owner (execution.recall owner)
                (execution.observe nativeApplication owner) response) (tag, some response.val) := by
  classical
  dsimp only
  by_cases bindingPacket : ∃ (material : WitnessedSubmission (serviceGraph setup .concurrent))
      (event : (serviceGraph setup .concurrent).EventId)
      (handle : Handle (serviceGraph setup .concurrent)),
      response.val.transmission = some material ∧ material.call.packet = .commitment event handle
  · obtain ⟨material, event, handle, sent, packet⟩ := bindingPacket
    obtain ⟨payload, binding, key, serial, value, _handle, _request, queried, prepared,
      classAtom, responseAtom⟩ := sourceReplay_proper_callback_atom setup values implementation
        operational fullValues rates waitPositive waitBelow slotPositive badPositive badBelow
          remaining owner execution trace response clean material sent event handle packet tag
    have draw : sourceReplayBindingDrawAtom setup values implementation owner
        (execution.recall owner) (execution.observe nativeApplication owner) response.val =
          ((values owner key).map (fun choice => phaseRecoveryDomainValue setup .concurrent event
            owner payload binding choice.val.val)) value := by
      simp only [sourceReplayBindingDrawAtom, sent, packet, prepared, dite_eq_left binding, queried]
    rw [draw]
    exact ⟨classAtom, responseAtom⟩
  · have noncommit : ∀ material, response.val.transmission = some material →
        ∀ event handle, material.call.packet ≠ .commitment event handle := by
      intro material sent event handle called
      exact bindingPacket ⟨material, event, handle, sent, called⟩
    have draw : sourceReplayBindingDrawAtom setup values implementation owner
        (execution.recall owner) (execution.observe nativeApplication owner) response.val = 1 := by
      cases sent : response.val.transmission with
      | none => simp only [sourceReplayBindingDrawAtom, sent]
      | some material =>
          cases packet : material.call.packet with
          | commitment event handle => exact (noncommit material sent event handle packet).elim
          | opening => simp only [sourceReplayBindingDrawAtom, sent, packet]
          | malformed => simp only [sourceReplayBindingDrawAtom, sent, packet]
    rw [draw, mul_one]
    exact sourceReplay_noncommit_response_atom setup values implementation operational
      fullValues rates waitPositive waitBelow slotPositive badPositive badBelow remaining owner
        execution trace tag response noncommit

open Classical in
/-- Every recalled callback contributes its class and alias atoms at the
literal earlier input. The indexed products retain silent callbacks and all
historical preparations, including those of a subsequently excluded owner. -/
theorem sourceReplay_foreign_callback_product
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (rates : PhaseProposalRates) (waitPositive : 0 < rates.waiting.val)
    (waitBelow : rates.waiting.val < 1) (slotPositive : 0 < rates.slots.val)
    (badPositive : 0 < rates.badPreparation.val) (badBelow : rates.badPreparation.val < 1)
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control)) :
    ∃ selected : (owner : Player) →
        (index : Fin (control.execution.recall owner).length) →
        PhaseProposal.Response implementation.runtime implementation.leaks implementation.bounds
          owner ((control.execution.recall owner).take index.val)
            (control.execution.recall owner)[index.val].beforeView,
      (∀ owner index, (selected owner index).val =
        (control.execution.recall owner)[index.val].action) ∧
      (∀ (owner : Player) (first second : Fin (control.execution.recall owner).length)
        (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent))),
        (control.execution.recall owner)[first.val].emitted = some message →
        (control.execution.recall owner)[second.val].emitted = some message → first = second) ∧
      (∀ (owner : Player) (index : Fin (control.execution.recall owner).length),
        ∃ (before : (nativeApplication).Control)
          (prior : (nativeProtocol).Trace (some before)),
        TracePrefix prior trace ∧ before.actor = some owner ∧
          before.execution.recall owner = (control.execution.recall owner).take index.val ∧
          (control.execution.recall owner)[index.val].beforeView =
            before.execution.observe nativeApplication owner) ∧
      let classes := fun (owner : Player)
          (index : Fin (control.execution.recall owner).length) =>
        phaseProposalBaseClasses setup .concurrent implementation.runtime implementation.leaks
          implementation.bounds implementation.plan values rates owner
            ((control.execution.recall owner).take index.val)
            (control.execution.recall owner)[index.val].beforeView
            (PhaseProposal.projectResponse implementation.runtime implementation.leaks
              implementation.bounds owner ((control.execution.recall owner).take index.val)
                (control.execution.recall owner)[index.val].beforeView (selected owner index))
      let aliases := fun (owner : Player)
          (index : Fin (control.execution.recall owner).length) =>
        PMF.splitKernel
          (PhaseProposal.projectResponse implementation.runtime implementation.leaks
            implementation.bounds owner ((control.execution.recall owner).take index.val)
              (control.execution.recall owner)[index.val].beforeView)
          (PhaseProposal.canonicalResponse implementation.runtime implementation.leaks
            implementation.bounds owner ((control.execution.recall owner).take index.val)
              (control.execution.recall owner)[index.val].beforeView)
          (PhaseProposal.project_canonicalResponse implementation.runtime implementation.leaks
            implementation.bounds owner ((control.execution.recall owner).take index.val)
              (control.execution.recall owner)[index.val].beforeView)
          rates.aliases.val rates.aliases.property.1 rates.aliases.property.2
          (PhaseProposal.projectResponse implementation.runtime implementation.leaks
            implementation.bounds owner ((control.execution.recall owner).take index.val)
              (control.execution.recall owner)[index.val].beforeView (selected owner index))
          (selected owner index)
      (∀ owner index, phaseProposalReferencePolicy setup .concurrent implementation.runtime
          implementation.leaks implementation.bounds implementation.plan values rates owner
          ((control.execution.recall owner).take index.val)
          (control.execution.recall owner)[index.val].beforeView
          (control.execution.recall owner)[index.val].action =
        classes owner index * aliases owner index) ∧
      (∀ who : Player,
        (∏ owner ∈ Finset.univ.erase who,
          (((nativeApplication).privateTranscriptFrom [] (control.execution.recall owner)).map
            (fun record => phaseProposalReferencePolicy setup .concurrent implementation.runtime
              implementation.leaks implementation.bounds implementation.plan values rates owner
                record.1.1 record.1.2 record.2)).prod.toReal) =
        (∏ owner ∈ Finset.univ.erase who, ∏ index, (classes owner index).toReal) *
          (∏ owner ∈ Finset.univ.erase who, ∏ index, (aliases owner index).toReal)) ∧
      ∀ (who : Player) (tape : ReservedEpoch.Tape Player implementation.tapeLength),
        (((nativeMenu).information nativeInitial implementation.horizon
            implementation.scheduler).historyReachWeight
          (phaseProposalReferenceStrategy setup .concurrent implementation.runtime
            implementation.leaks implementation.bounds implementation.plan nativeInitial
              implementation.horizon implementation.scheduler values rates)
          ⟨some control, trace⟩).toReal *
            (prefixTapeLaw setup implementation ⟨some control, trace⟩ tape).toReal =
          (implementation.prior tape).toReal *
            sourceReplayFixedTransitionMass setup implementation tape trace *
            ((nativeMenu).information nativeInitial implementation.horizon
              implementation.scheduler).ownPlayReachProbability
              (phaseProposalReferenceStrategy setup .concurrent implementation.runtime
                implementation.leaks implementation.bounds implementation.plan nativeInitial
                  implementation.horizon implementation.scheduler values rates who)
              (((nativeMenu).information nativeInitial implementation.horizon
                implementation.scheduler).ownPlay who trace) *
            (∏ owner ∈ Finset.univ.erase who, ∏ index, (classes owner index).toReal) *
            (∏ owner ∈ Finset.univ.erase who, ∏ index, (aliases owner index).toReal) := by
  have factual (owner : Player) (index : Fin (control.execution.recall owner).length) :
      ∃ (before : (nativeApplication).Control)
        (prior : (nativeProtocol).Trace (some before)),
        TracePrefix prior trace ∧ before.actor = some owner ∧
          before.execution.recall owner = (control.execution.recall owner).take index.val ∧
          (control.execution.recall owner)[index.val].beforeView =
            before.execution.observe nativeApplication owner ∧
          (control.execution.recall owner)[index.val].action ∈ (nativeMenu).actions owner
            ((control.execution.recall owner).take index.val)
            (before.execution.observe nativeApplication owner) := by
    have recalled : control.execution.recall owner =
        (control.execution.recall owner).take index.val ++
          (control.execution.recall owner)[index.val] ::
            (control.execution.recall owner).drop (index.val + 1) := by
      rw [← List.drop_eq_getElem_cons index.isLt]
      exact (List.take_append_drop index.val _).symm
    exact (nativeMenu).recorded_response_at nativeInitial implementation.horizon
      implementation.scheduler control trace owner
        ((control.execution.recall owner).take index.val)
        (control.execution.recall owner)[index.val]
        ((control.execution.recall owner).drop (index.val + 1)) recalled
  have available (owner : Player) (index : Fin (control.execution.recall owner).length) :
      (control.execution.recall owner)[index.val].action ∈ (nativeMenu).actions owner
        ((control.execution.recall owner).take index.val)
        (control.execution.recall owner)[index.val].beforeView := by
    obtain ⟨before, _prior, _kept, _acting, _past, viewed, offered⟩ := factual owner index
    simpa only [viewed] using offered
  let selected := fun (owner : Player)
      (index : Fin (control.execution.recall owner).length) =>
    (⟨(control.execution.recall owner)[index.val].action, available owner index⟩ :
      PhaseProposal.Response implementation.runtime implementation.leaks implementation.bounds
        owner ((control.execution.recall owner).take index.val)
          (control.execution.recall owner)[index.val].beforeView)
  refine ⟨selected, fun _ _ => rfl, ?_, ?_, ?_⟩
  · intro owner first second message firstSent secondSent
    have order := (nativeApplication).emissionOrder_history implementation.scheduler nativeInitial
      implementation.horizon ((nativeMenu).toRawTrace nativeInitial implementation.horizon
        implementation.scheduler trace)
    have outputUnique : ((nativeApplication).outputs (control.execution.recall owner)).Nodup := by
      apply List.Nodup.of_map Message.id
      rw [order owner]
      exact List.nodup_range.map (fun _ _ equal => (Prod.mk.inj equal).2)
    change ((control.execution.recall owner).filterMap
      ReactiveApplication.PlayerEntry.emitted).Pairwise (· ≠ ·) at outputUnique
    have distinct := List.pairwise_filterMap.mp outputUnique
    apply Fin.ext
    rcases lt_trichotomy first.val second.val with earlier | equal | later
    · exact False.elim ((distinct.rel_getElem_of_lt first.isLt second.isLt earlier)
        message firstSent message secondSent rfl)
    · exact equal
    · exact False.elim ((distinct.rel_getElem_of_lt second.isLt first.isLt later)
        message secondSent message firstSent rfl)
  · intro owner index
    obtain ⟨before, prior, kept, acting, past, viewed, _offered⟩ := factual owner index
    exact ⟨before, prior, kept, acting, past, viewed⟩
  · intro classes aliases
    have atoms (owner : Player) (index : Fin (control.execution.recall owner).length) :
        phaseProposalReferencePolicy setup .concurrent implementation.runtime implementation.leaks
          implementation.bounds implementation.plan values rates owner
          ((control.execution.recall owner).take index.val)
          (control.execution.recall owner)[index.val].beforeView
          (control.execution.recall owner)[index.val].action =
            classes owner index * aliases owner index := by
      obtain ⟨⟨remaining, actor, execution⟩, prior, _kept, acting, past, viewed, offered⟩ :=
        factual owner index
      change actor = some owner at acting
      subst actor
      let response : PhaseProposal.Response implementation.runtime implementation.leaks
          implementation.bounds owner (execution.recall owner)
            (execution.observe nativeApplication owner) :=
        ⟨(control.execution.recall owner)[index.val].action, by
          change (control.execution.recall owner)[index.val].action ∈
            PhaseCount.onePacketActions implementation.runtime implementation.leaks
              implementation.bounds owner ((control.execution.recall owner).take index.val)
                (execution.observe nativeApplication owner) at offered
          rw [← past] at offered
          exact offered⟩
      have atom := sourceReplay_counted_response_atom setup values implementation operational
        fullValues rates waitPositive waitBelow slotPositive badPositive badBelow remaining owner
          execution prior none response
      rw [sourceReplayAliases_atom setup implementation rates.aliases owner execution none _
        response] at atom
      let factor (past : List (nativeApplication).PlayerEntry)
          (view : (nativeApplication).PlayerView)
          (chosen : PhaseProposal.Response implementation.runtime implementation.leaks
            implementation.bounds owner past view) : Prop :=
        phaseProposalReferencePolicy setup .concurrent implementation.runtime implementation.leaks
            implementation.bounds implementation.plan values rates owner past view chosen.val =
          phaseProposalBaseClasses setup .concurrent implementation.runtime implementation.leaks
              implementation.bounds implementation.plan values rates owner past view
              (PhaseProposal.projectResponse implementation.runtime implementation.leaks
                implementation.bounds owner past view chosen) *
            PMF.splitKernel
              (PhaseProposal.projectResponse implementation.runtime implementation.leaks
                implementation.bounds owner past view)
              (PhaseProposal.canonicalResponse implementation.runtime implementation.leaks
                implementation.bounds owner past view)
              (PhaseProposal.project_canonicalResponse implementation.runtime implementation.leaks
                implementation.bounds owner past view)
              rates.aliases.val rates.aliases.property.1 rates.aliases.property.2
              (PhaseProposal.projectResponse implementation.runtime implementation.leaks
                implementation.bounds owner past view chosen) chosen
      have transport (firstPast secondPast : List (nativeApplication).PlayerEntry)
          (firstView secondView : (nativeApplication).PlayerView)
          (samePast : firstPast = secondPast) (sameView : firstView = secondView)
          (first : PhaseProposal.Response implementation.runtime implementation.leaks
            implementation.bounds owner firstPast firstView)
          (second : PhaseProposal.Response implementation.runtime implementation.leaks
            implementation.bounds owner secondPast secondView)
          (sameAction : first.val = second.val) :
          factor firstPast firstView first → factor secondPast secondView second := by
        subst secondPast
        subst secondView
        have sameResponse : first = second := Subtype.ext sameAction
        cases sameResponse
        exact id
      exact transport _ _ _ _ past viewed.symm response (selected owner index) rfl atom
    have foreignProduct (who : Player) :
        (∏ owner ∈ Finset.univ.erase who,
          (((nativeApplication).privateTranscriptFrom [] (control.execution.recall owner)).map
            (fun record => phaseProposalReferencePolicy setup .concurrent implementation.runtime
              implementation.leaks implementation.bounds implementation.plan values rates owner
                record.1.1 record.1.2 record.2)).prod.toReal) =
          (∏ owner ∈ Finset.univ.erase who, ∏ index, (classes owner index).toReal) *
            (∏ owner ∈ Finset.univ.erase who, ∏ index, (aliases owner index).toReal) := by
      calc
        _ = ∏ owner ∈ Finset.univ.erase who,
          ∏ index : Fin (control.execution.recall owner).length,
            (phaseProposalReferencePolicy setup .concurrent implementation.runtime
              implementation.leaks implementation.bounds implementation.plan values rates owner
              ((control.execution.recall owner).take index.val)
              (control.execution.recall owner)[index.val].beforeView
              (control.execution.recall owner)[index.val].action).toReal := by
          apply Finset.prod_congr rfl
          intro owner _member
          simpa only [List.nil_append] using
            (nativeApplication).privateTranscriptFrom_product
              (phaseProposalReferencePolicy setup .concurrent implementation.runtime
                implementation.leaks implementation.bounds implementation.plan values rates owner)
              [] (control.execution.recall owner)
        _ = ∏ owner ∈ Finset.univ.erase who,
          ∏ index : Fin (control.execution.recall owner).length,
            (classes owner index * aliases owner index).toReal := by
          apply Finset.prod_congr rfl
          intro owner _member
          apply Finset.prod_congr rfl
          intro index _present
          exact congrArg ENNReal.toReal (atoms owner index)
        _ = _ := by simp only [ENNReal.toReal_mul, Finset.prod_mul_distrib]
    refine ⟨atoms, foreignProduct, ?_⟩
    intro who tape
    let responseProduct := fun owner =>
      (((nativeApplication).privateTranscriptFrom [] (control.execution.recall owner)).map
        (fun record => phaseProposalReferencePolicy setup .concurrent implementation.runtime
          implementation.leaks implementation.bounds implementation.plan values rates owner
            record.1.1 record.1.2 record.2)).prod.toReal
    have splitProduct : (∏ owner, responseProduct owner) =
        responseProduct who * ∏ owner ∈ Finset.univ.erase who, responseProduct owner :=
      (Finset.mul_prod_erase Finset.univ responseProduct (Finset.mem_univ who)).symm
    have focal := sourceReplay_prescribed_own_atom setup values implementation rates who
      control trace
    change _ = responseProduct who at focal
    rw [sourceReplay_prescribed_native_atom setup values implementation rates tape control trace]
    change (implementation.prior tape).toReal *
        sourceReplayFixedTransitionMass setup implementation tape trace *
          (∏ owner, responseProduct owner) = _
    rw [splitProduct, ← focal]
    rw [show (∏ owner ∈ Finset.univ.erase who, responseProduct owner) =
        (∏ owner ∈ Finset.univ.erase who, ∏ index, (classes owner index).toReal) *
          (∏ owner ∈ Finset.univ.erase who, ∏ index, (aliases owner index).toReal) from
      foreignProduct who]
    ring

omit [Fintype Player] in
/-- At a decoded binding query, the ordinary enriched source atom is exactly
the queried domain law's typed-value atom. The original domain law is retained;
neither a uniform payload law nor a representative source query is substituted. -/
theorem sourceReplay_source_value_atom
    {Field : Type} {layout : Field → EventField Player L}
    (refs : ContextRefs layout setup.context)
    (outputs : ∀ event, FieldRef layout (outputLayout setup.program event))
    (who : Player) (information : setup.proposalRecoveryModel.InfoState who)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding who payload)
    (store : Store layout) (past : List (OwnAction Player L))
    (view : ProtocolView who setup.program)
    (decoded : decodeEventView? setup.program refs outputs who event store past = some view)
    (typed : ((setup.proposalRecoveryQuery who information).1).1.1.1 =
      some (ProtocolView.virtualBindings who (setup.context.map Prod.fst).toFinset
        setup.program view))
    (active : setup.commitRecoveryActive who
      ((setup.proposalRecoveryQuery who information).1).1.1)
    (selected : setup.CommitRecoveryValueChoice who
      (setup.proposalRecoveryQuery who information).1) :
    ((sourceUnflaggedStrategy setup values who information).map Subtype.val)
        (selected.val.val.map ProposalRecoveryMove.ordinary) =
      ((values who (setup.proposalRecoveryQuery who information)).map (fun choice =>
        phaseRecoveryDomainValue setup .concurrent event who payload binding choice.val.val))
          (phaseRecoveryDomainValue setup .concurrent event who payload binding
            selected.val.val) := by
  let key := setup.proposalRecoveryQuery who information
  let raw := fun choice : setup.CommitRecoveryValueChoice who key.1 =>
    choice.val.val.map ProposalRecoveryMove.ordinary
  have rawInjective : Function.Injective raw := by
    intro first second equal
    apply Subtype.ext
    apply Subtype.ext
    have semantic := congrArg (Option.map (fun move : ProposalRecoveryMove Player L =>
      move.semantic)) equal
    simpa only [raw, Option.map_map, Function.comp_def, ProposalRecoveryMove.ordinary,
      Option.map_id'] using semantic
  have rawLaw : (sourceUnflaggedStrategy setup values who information).map Subtype.val =
      (values who key).map raw := by
    unfold sourceUnflaggedStrategy
    rw [setup.proposalRecovery_ordinary_choice_law, PMF.map_comp]
    apply congrArg (fun transform => (values who key).map transform)
    funext choice
    change choice.val.val.map (fun move => ProposalRecoveryMove.label move false) =
      choice.val.val.map ProposalRecoveryMove.ordinary
    simp only [ProposalRecoveryMove.label_false]
  rw [rawLaw]
  change ((values who key).map raw) (raw selected) = _
  rw [pmf_map_apply_of_injective _ rawInjective selected,
    pmf_map_apply_of_injective _
      (phaseRecoveryDomainValue_injective setup .concurrent refs outputs who event payload
        binding store past view decoded key.1 typed active) selected]

/-- The literal initializer and public Nature probability at an actual row.
Scheduler and behavioral response probabilities are excluded. -/
private def sourceReplayNatureStepAtom
    (before after : (nativeProtocol).State) : ℝ≥0∞ :=
  match before with
  | none => (nativeApplication).transition nativeInitial implementation.horizon
      implementation.scheduler none (fun _ => none) after
  | some control => match control.actor with
    | some _ => 1
    | none => if control.remaining = 0 then 1 else
        match after with
        | none => 0
        | some next => match next.execution.environmentRecall.getLast? with
          | none => 0
          | some entry => (control.execution.environmentStep nativeApplication entry.command)
              next.execution

/-- The physical foreign-packet factors in the original chronological trace. -/
private def sourceReplayPacketStepAtom (rates : PhaseProposalRates) (who : Player)
    (before : (nativeProtocol).State) (joint : Player → Option (nativeApplication).Action) :
    ℝ≥0∞ :=
  match before with
  | none => 1
  | some control => match control.actor with
    | none => 1
    | some owner => if owner = who then 1 else
        match joint owner with
        | none => 0
        | some response => foreignMechanicalAtom setup implementation rates control.execution
            owner response

private theorem sourceReplay_mechanical_step_factor
    (rates : PhaseProposalRates) (who : Player)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    {before after : (nativeProtocol).State} (joint : Player → Option (nativeApplication).Action)
    (legal : (nativeProtocol).Legal before joint)
    (moved : after ∈ ((nativeProtocol).step before ⟨joint, legal⟩).support) :
    (nativeApplication).transition nativeInitial implementation.horizon
        (ReservedEpoch.family implementation.runtime implementation.leaks
          (ReservedEpoch.packetCapacity implementation.runtime) tape) before joint after *
      sourceReplayPacketStepAtom setup implementation rates who before joint =
    sourceReplayNatureStepAtom setup implementation before after *
      mechanicalStepAtom setup implementation rates who tape before after joint := by
  cases before with
  | none =>
    simp only [sourceReplayPacketStepAtom, sourceReplayNatureStepAtom, mechanicalStepAtom,
      ReactiveApplication.transition, mul_one]
  | some control =>
    rcases control with ⟨remaining, actor, execution⟩
    cases actor with
    | some owner =>
      change after ∈ (PMF.pure (some (⟨remaining, none,
        execution.respond nativeApplication owner ((joint owner).getD ⟨none⟩)⟩ :
          (nativeApplication).Control))).support at moved
      cases (PMF.mem_support_pure_iff ..).mp moved
      simp only [ReactiveApplication.transition, PMF.pure_apply_self,
        sourceReplayPacketStepAtom, sourceReplayNatureStepAtom, mechanicalStepAtom, one_mul]
      cases joint owner <;> rfl
    | none =>
      cases remaining with
      | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
      | succ remaining =>
        change after ∈ ((implementation.scheduler execution.environmentRecall
          (execution.observeEnvironment nativeApplication)).bind fun command =>
            (execution.environmentStep nativeApplication command).map fun next =>
              some (⟨remaining, command.actor? nativeApplication, next⟩ :
                (nativeApplication).Control)).support at moved
        obtain ⟨command, _selected, supported⟩ :=
          Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
        obtain ⟨next, advanced, rfl⟩ := PMF.support_map .. ▸ supported
        have recorded := (nativeApplication).environmentStep_environmentRecall execution next
          command advanced
        have last : next.environmentRecall.getLast? =
            some ⟨execution.observeEnvironment nativeApplication, command⟩ := by
          rw [recorded, List.getLast?_concat]
        change (nativeApplication).transition nativeInitial implementation.horizon
          (ReservedEpoch.family implementation.runtime implementation.leaks
            (ReservedEpoch.packetCapacity implementation.runtime) tape)
              (some ⟨remaining + 1, none, execution⟩) joint
                (some ⟨remaining, command.actor? nativeApplication, next⟩) * _ = _
        rw [(nativeApplication).transition_environment_apply nativeInitial implementation.horizon
          (ReservedEpoch.family implementation.runtime implementation.leaks
            (ReservedEpoch.packetCapacity implementation.runtime) tape) remaining execution next
              command advanced joint]
        simp only [sourceReplayPacketStepAtom, sourceReplayNatureStepAtom, mechanicalStepAtom,
          Nat.succ_ne_zero, ↓reduceIte, last, mul_one]
        exact mul_comm _ _

/-- Every counted physical packet has positive mechanical weight at the
actual initialized input. Properness contributes its literal positive flag. -/
private theorem sourceReplay_foreign_packet_positive
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (rates : PhaseProposalRates) (waitPositive : 0 < rates.waiting.val)
    (waitBelow : rates.waiting.val < 1) (slotPositive : 0 < rates.slots.val)
    (badPositive : 0 < rates.badPreparation.val) (badBelow : rates.badPreparation.val < 1)
    (remaining : Nat) (owner : Player) (execution : (nativeApplication).Execution)
    (trace : (nativeProtocol).Trace (some ⟨remaining, some owner, execution⟩))
    (response : (nativeApplication).Action)
    (available : response ∈ PhaseCount.onePacketActions implementation.runtime
      implementation.leaks implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner)) :
    0 < (foreignMechanicalAtom setup implementation rates execution owner response).toReal := by
  have packet := mechanicalForeignPolicy_packet_supported setup values implementation operational
    fullValues rates waitPositive waitBelow slotPositive badPositive badBelow remaining owner
      execution trace response available
  have flag : 0 < ENNReal.ofReal (1 - rates.badPreparation.val) :=
    ENNReal.ofReal_pos.mpr (sub_pos.mpr badBelow)
  apply ENNReal.toReal_pos
  · dsimp only [foreignMechanicalAtom]
    apply mul_ne_zero packet
    cases transmitted : response.transmission with
    | none => exact one_ne_zero
    | some material =>
        cases shape : material.call.packet with
        | commitment event handle => simpa only [shape] using flag.ne'
        | opening event handle raw => simpa only [shape] using (one_ne_zero : (1 : ℝ≥0∞) ≠ 0)
        | malformed raw => simpa only [shape] using (one_ne_zero : (1 : ℝ≥0∞) ≠ 0)
  · dsimp only [foreignMechanicalAtom]
    refine ENNReal.mul_ne_top (PMF.apply_ne_top _ _) ?_
    cases transmitted : response.transmission with
    | none => exact ENNReal.one_ne_top
    | some material =>
        cases shape : material.call.packet with
        | commitment event handle =>
            simpa only [shape] using (ENNReal.ofReal_ne_top :
              ENNReal.ofReal (1 - rates.badPreparation.val) ≠ ∞)
        | opening event handle raw => simpa only [shape] using ENNReal.one_ne_top
        | malformed raw => simpa only [shape] using ENNReal.one_ne_top

def sourceReplayNatureMass :
    ∀ {state : (nativeProtocol).State}, (nativeProtocol).Trace state → ℝ
  | _, .start => 1
  | after, @Trace.extend _ _ before _ prior _ _ _ =>
      sourceReplayNatureMass prior *
        (sourceReplayNatureStepAtom setup implementation before after).toReal

omit [Fintype Player] in
/-- Proposal labels retain the literal Nature atom of every semantic row. -/
private theorem sourceReplay_lift_mass
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    (setup.proposalRecoveryLiftTrace labels trace).transitionMass = trace.transitionMass := by
  induction trace with
  | start => rfl
  | @extend before after prior joint legal moved ih =>
      simp only [Setup.proposalRecoveryLiftTrace, Trace.transitionMass_extend, ih]
      exact congrArg (fun kernel : PMF setup.commitRecoveryProtocol.State =>
        prior.transitionMass * (kernel after).toReal)
          (setup.proposalRecoveryLiftJoint_step labels ⟨before, joint, legal, after, moved⟩)

omit [Fintype Player] in
/-- The saved source initializer charges the original correlated draw once. -/
private theorem sourceReplay_initial_source_mass
    (theta : State L setup.context) (drawn : theta ∈ setup.initialLaw.support) :
    (RecoverySourceCheckpoint.initialized setup .concurrent implementation.plan theta
      drawn).trace.transitionMass = (setup.initialLaw theta).toReal := by
  have raw := congrArg (fun history : setup.commitRecoveryProtocol.History =>
    history.trace.transitionMass)
      (initialized_checkpoint_history setup .concurrent implementation.plan theta drawn)
  rw [raw]
  change 1 * ((setup.initialLaw.map fun input =>
    some (CommitRecoveryState.atPoint
      (ProtocolState.entry setup.program (setup.initialConfig input)) ∅ 0))
        (some (CommitRecoveryState.atPoint
          (ProtocolState.entry setup.program (setup.initialConfig theta)) ∅ 0))).toReal = _
  have injective : Function.Injective fun input : State L setup.context =>
      some (CommitRecoveryState.atPoint
        (ProtocolState.entry setup.program (setup.initialConfig input)) ∅ 0) := by
    intro first second same
    have points := congrArg CommitRecoveryState.point (Option.some.inj same)
    exact congrArg Config.state (ProtocolState.entry_injective setup.program points)
  rw [one_mul, pmf_map_apply_of_injective _ injective]

omit [Fintype Player] in
/-- A genuine source sample retains its original draw atom in the actual
syntactic suffix, with arbitrary inherited exclusions. -/
private theorem sourceReplay_source_sample_atom
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (name : VarId) (payload : L.Ty) (fresh : name ∉ Γ.map Prod.fst)
    (law : L.DistExpr (SourcePublicCtx L Γ) payload)
    (next : SourceProgram Player L ((name, .publicData payload) :: Γ) O)
    (lift : ProtocolState (.sample name fresh law next) → ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program (.sample name fresh law next) lift)
    (source : Config Player L Γ) (excluded : Finset Player) (generation : Nat)
    (joint : Player → Option (CommitRecoveryMove Player L)) (value : L.Val payload) :
    (CommitRecoveryState.atPoint
      (lift (ProtocolState.entry (.sample name fresh law next) source)) excluded generation).step
        joint (CommitRecoveryState.atPoint
          (lift (.inr (ProtocolState.entry next (sampleSuccessor name source value))))
          excluded generation) = L.evalDist law (sourcePublicEnv source.state) value := by
  let state := CommitRecoveryState.atPoint
    (lift (ProtocolState.entry (.sample name fresh law next) source)) excluded generation
  have notCommit : ProtocolState.atCommit setup.program state.point = false := by
    simp only [state, CommitRecoveryState.atPoint, origin.atCommit_lift,
      ProtocolState.entry, ProtocolState.atCommit, Sum.elim_inl]
  change state.step joint _ = _
  rw [state.step_noncommit_law (CommitRecoveryState.atPoint_blockFrontier _ _ _)
    notCommit joint]
  change ((ProtocolState.recoveryStep setup.program
    (lift (ProtocolState.entry (.sample name fresh law next) source)) excluded joint).map _) _ = _
  rw [origin.recoveryStep_lift]
  simp only [ProtocolState.recoveryStep, ProtocolState.entry, Sum.elim_inl,
    PMF.map_comp, Function.comp_def]
  apply pmf_map_apply_of_injective
  intro first second same
  have points := congrArg CommitRecoveryState.point same
  have suffix := sourceReplaySuffixInjective setup origin points
  have configs := ProtocolState.entry_injective next (Sum.inr.inj suffix)
  exact congrArg (fun config => config.state.get .here) configs

/-- The native initializer retains every encoded input of the joint draw. -/
private theorem sourceReplay_initial_native_atom
    (theta : State L setup.context) :
    (nativeApplication).transition nativeInitial implementation.horizon
        implementation.scheduler none (fun _ => none)
          (some ⟨implementation.horizon, none,
            ReactiveApplication.Execution.initial nativeApplication
              (PhaseRuntimeState.initial implementation.plan (encodeInputs theta))⟩) =
      setup.initialLaw theta := by
  change ((setup.initialLaw.map fun input =>
    PhaseRuntimeState.initial implementation.plan (encodeInputs input)).map fun state =>
      some (⟨implementation.horizon, none,
        ReactiveApplication.Execution.initial nativeApplication state⟩ :
          (nativeApplication).Control)) _ = _
  rw [PMF.map_comp]
  apply pmf_map_apply_of_injective
  intro first second same
  have physical := congrArg (fun control : (nativeApplication).Control =>
    control.execution.application.current.native.config.inputs) (Option.some.inj same)
  simp only [phaseInitial_eq_raw] at physical
  change encodeInputs first = encodeInputs second at physical
  funext name kind source
  have firstRead := encodeInputs_get first source
  have secondRead := encodeInputs_get second source
  rw [physical, secondRead] at firstRead
  cases kind <;> exact firstRead.symm

omit [Fintype Player] in
/-- A physical sample atom is its original public draw, through all automatic
normalization and with arbitrary inherited exclusions. -/
private theorem sourceReplay_sample_atom
    (physical : (nativeApplication).Execution)
    (event : (serviceGraph setup .concurrent).EventId)
    (ready : physical.application.current.native.config.cut.Ready event)
    (payload : L.Ty) (law : PublicDist (graphLayout setup.program) payload)
    (output : (serviceGraph setup .concurrent).outputLayout event = .publicData payload)
    (code : cast (congrArg (EventCode (graphLayout setup.program)) output)
      ((serviceGraph setup .concurrent).nodes event) = .sample payload law)
    (allowed : physical.application.commandAllowed (.executeSample event) = true)
    (draw : PMF (L.Val payload))
    (evaluates : law.eval? physical.application.current.native.config.store = some draw)
    (value : L.Val payload) :
    physical.environmentStep nativeApplication (.application (.executeSample event))
      (PhaseRuntimeState.normalizeExecution implementation.runtime implementation.leaks
        (PhaseBindingRepair.rawSample implementation.runtime implementation.leaks physical
          event payload output ready value)) = draw value := by
  let next (raw : L.Val payload) :=
    PhaseRuntimeState.normalizeExecution implementation.runtime implementation.leaks
      (PhaseBindingRepair.rawSample implementation.runtime implementation.leaks physical
        event payload output ready raw)
  have stored (raw : L.Val payload) :
      (next raw).application.current.native.config.outputs event =
        some (cast (congrArg EventField.Value output.symm) raw) := by
    exact PhaseRuntimeState.normalize_sample_output physical.application event ready payload
      output allowed (cast (congrArg EventField.Value output.symm) raw)
  have injective : Function.Injective next := by
    intro first second same
    have read := congrArg (fun execution : (nativeApplication).Execution =>
      execution.application.current.native.config.outputs event) same
    rw [stored first, stored second] at read
    exact (cast_inj _).mp (Option.some.inj read)
  have kernel := PhaseBindingRepair.sample_environment_law implementation.runtime
    implementation.leaks physical event ready payload law output code
      (nodeView_eq_sample output code) allowed draw evaluates
  rw [kernel]
  exact pmf_map_apply_of_injective draw injective value

/-- The first actual selected checkpoint and native initializer have identical
whole-draw mass, including hidden input correlations. -/
private theorem sourceReplay_initial_nature_mass
    (operational : implementation.Operational)
    (control : (nativeApplication).Control)
    (joint : Player → Option (nativeApplication).Action)
    (legal : (nativeProtocol).Legal none joint)
    (moved : some control ∈ ((nativeProtocol).step none ⟨joint, legal⟩).support) :
    sourceReplayNatureMass setup implementation (.extend .start joint legal moved) =
      (canonicalSource setup implementation operational
        ⟨some control, .extend .start joint legal moved⟩).trace.transitionMass := by
  let trace : (nativeProtocol).Trace (some control) := .extend .start joint legal moved
  have selected := (checkpointSelectionStep setup implementation operational
    (.start : (nativeProtocol).Trace none) joint legal moved PUnit.unit).property
  obtain ⟨theta, drawn, physical, history⟩ := selected
  have selectedHistory :
      (⟨_, (checkpointSelection setup implementation operational trace).val.checkpoint.trace⟩ :
        setup.commitRecoveryProtocol.History) =
      ⟨_, (RecoverySourceCheckpoint.initialized setup .concurrent implementation.plan
        theta drawn).trace⟩ := history
  have mass := congrArg (fun history : setup.commitRecoveryProtocol.History =>
    history.trace.transitionMass) selectedHistory
  change 1 * (sourceReplayNatureStepAtom setup implementation none (some control)).toReal = _
  rw [one_mul]
  change _ = (setup.proposalRecoveryLiftTrace _
    (checkpointSelection setup implementation operational
      trace).val.checkpoint.trace).transitionMass
  rw [sourceReplay_lift_mass, mass,
    sourceReplay_initial_source_mass setup implementation theta drawn]
  have reached : some control ∈ ((nativeProtocol).step none ⟨joint, legal⟩).support := moved
  change some control ∈ ((nativeInitial).map fun native =>
    some (⟨implementation.horizon, none,
      ReactiveApplication.Execution.initial nativeApplication native⟩ :
        (nativeApplication).Control)).support at reached
  obtain ⟨native, _nativeSupport, sameControl⟩ := PMF.support_map .. ▸ reached
  have controlEq : control = ⟨implementation.horizon, none,
      ReactiveApplication.Execution.initial nativeApplication native⟩ :=
    Option.some.inj sameControl.symm
  have nativeEq : native =
      PhaseRuntimeState.initial implementation.plan (encodeInputs theta) := by
    simpa only [controlEq, ReactiveApplication.Execution.initial] using physical
  subst native
  rw [controlEq]
  exact congrArg ENNReal.toReal (sourceReplay_initial_native_atom setup implementation theta)


omit [Fintype Player] in
private theorem sourceReplay_close_within_saved
    (current : CommitRecoveryState setup.program)
    (within : ProtocolState.remaining setup.program current.point ≤
      ProtocolState.remaining setup.program current.saved) :
    ProtocolState.remaining setup.program current.close.point ≤
      ProtocolState.remaining setup.program current.close.saved := by
  unfold CommitRecoveryState.close
  split
  · split
    · split <;> exact le_rfl
    · exact le_rfl
  · split
    · exact within
    · exact le_rfl

omit [Fintype Player] in
private theorem sourceReplay_trace_within_saved
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    state.elim True (fun current =>
      ProtocolState.remaining setup.program current.point ≤
        ProtocolState.remaining setup.program current.saved) := by
  induction trace with
  | start => trivial
  | @extend before after prior joint legal moved ih =>
      cases before with
      | none =>
          obtain ⟨inputs, supported, rfl⟩ := (PMF.mem_support_map_iff ..).mp moved
          exact le_rfl
      | some current =>
          obtain ⟨next, supported, rfl⟩ := (PMF.mem_support_map_iff ..).mp moved
          obtain ⟨raw, rawSupported, rfl⟩ := current.step_raw_result joint next supported
          have consumed := ProtocolState.recoveryStep_remaining setup.program current.point
            current.excluded joint raw.1 legal.1 rawSupported
          apply sourceReplay_close_within_saved
          change ProtocolState.remaining setup.program raw.1.1 ≤
            ProtocolState.remaining setup.program current.saved
          change ProtocolState.remaining setup.program current.point ≤
            ProtocolState.remaining setup.program current.saved at ih
          omega

omit [Fintype Player] in
private theorem sourceReplay_saved_remaining_step
    {before after : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace before)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal before joint)
    (moved : after ∈ (setup.commitRecoveryProtocol.step before ⟨joint, legal⟩).support) :
    after.elim (instructionCount setup.program)
        (fun current => ProtocolState.remaining setup.program current.saved) ≤
      before.elim (instructionCount setup.program)
        (fun current => ProtocolState.remaining setup.program current.saved) := by
  cases before with
  | none =>
      obtain ⟨inputs, supported, rfl⟩ := (PMF.mem_support_map_iff ..).mp moved
      simp only [Option.elim_some, Option.elim_none, CommitRecoveryState.atPoint,
        ProtocolState.remaining_entry, le_refl]
  | some current =>
      obtain ⟨next, supported, rfl⟩ := (PMF.mem_support_map_iff ..).mp moved
      obtain ⟨raw, rawSupported, rfl⟩ := current.step_raw_result joint next supported
      have within := sourceReplay_trace_within_saved setup trace
      have consumed := ProtocolState.recoveryStep_remaining setup.program current.point
        current.excluded joint raw.1 legal.1 rawSupported
      exact close_saved_remaining_le (current.install raw.1 raw.2) (by
        change ProtocolState.remaining setup.program raw.1.1 ≤
          ProtocolState.remaining setup.program current.saved
        change ProtocolState.remaining setup.program current.point ≤
          ProtocolState.remaining setup.program current.saved at within
        omega)

omit [Fintype Player] in
private theorem sourceReplay_saved_remaining_le_of_prefix
    {first last : setup.commitRecoveryProtocol.State}
    (prior : setup.commitRecoveryProtocol.Trace first)
    (trace : setup.commitRecoveryProtocol.Trace last) (retained : TracePrefix prior trace) :
    last.elim (instructionCount setup.program)
        (fun current => ProtocolState.remaining setup.program current.saved) ≤
      first.elim (instructionCount setup.program)
        (fun current => ProtocolState.remaining setup.program current.saved) := by
  induction retained with
  | refl => exact le_rfl
  | @extend before after middle earlier joint legal moved ih =>
      exact (sourceReplay_saved_remaining_step setup middle joint legal moved).trans ih

omit [Fintype Player] in
private theorem sourceReplay_actor_at_rank :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : ProtocolState program)
      (event : Fin (eventCount program)),
      event.val = instructionCount program - ProtocolState.remaining program point →
        ProtocolState.actor program point = eventOwner? program event := by
  intro Γ O program
  induction program with
  | ret payoffs => intro point event; exact Fin.elim0 event
  | sample name fresh law suffix ih =>
      intro point event rank
      cases point with
      | inl source =>
          have same : event = ⟨0, by simp only [eventCount]; omega⟩ := by
            apply Fin.ext
            simpa only [instructionCount, ProtocolState.remaining, Sum.elim_inl,
              Nat.sub_self] using rank
          rw [same]
          rfl
      | inr point =>
          have bound := ProtocolState.remaining_le_instructionCount suffix point
          have width := event.isLt
          have counts := eventCount_eq_instructionCount suffix
          simp only [instructionCount, ProtocolState.remaining, Sum.elim_inr] at rank
          simp only [eventCount] at width
          let tail : Fin (eventCount suffix) := ⟨event.val - 1, by omega⟩
          have same : event = tail.succ := Fin.ext (by
            change event.val = event.val - 1 + 1
            omega)
          have tailRank : tail.val = instructionCount suffix -
              ProtocolState.remaining suffix point := by
            dsimp only [tail]
            omega
          rw [same]
          exact ih point tail tailRank
  | commit name owner fresh guard suffix ih =>
      intro point event rank
      cases point with
      | inl source =>
          have same : event = ⟨0, by simp only [eventCount]; omega⟩ := by
            apply Fin.ext
            simpa only [instructionCount, ProtocolState.remaining, Sum.elim_inl,
              Nat.sub_self] using rank
          rw [same]
          rfl
      | inr point =>
          have bound := ProtocolState.remaining_le_instructionCount suffix point
          have width := event.isLt
          have counts := eventCount_eq_instructionCount suffix
          simp only [instructionCount, ProtocolState.remaining, Sum.elim_inr] at rank
          simp only [eventCount] at width
          let tail : Fin (eventCount suffix) := ⟨event.val - 1, by omega⟩
          have same : event = tail.succ := Fin.ext (by
            change event.val = event.val - 1 + 1
            omega)
          have tailRank : tail.val = instructionCount suffix -
              ProtocolState.remaining suffix point := by
            dsimp only [tail]
            omega
          rw [same]
          exact ih point tail tailRank
  | reveal published owner name fresh selected unresolved suffix ih =>
      intro point event rank
      cases point with
      | inl source =>
          have same : event = ⟨0, by simp only [eventCount]; omega⟩ := by
            apply Fin.ext
            simpa only [instructionCount, ProtocolState.remaining, Sum.elim_inl,
              Nat.sub_self] using rank
          rw [same]
          rfl
      | inr point =>
          have bound := ProtocolState.remaining_le_instructionCount suffix point
          have width := event.isLt
          have counts := eventCount_eq_instructionCount suffix
          simp only [instructionCount, ProtocolState.remaining, Sum.elim_inr] at rank
          simp only [eventCount] at width
          let tail : Fin (eventCount suffix) := ⟨event.val - 1, by omega⟩
          have same : event = tail.succ := Fin.ext (by
            change event.val = event.val - 1 + 1
            omega)
          have tailRank : tail.val = instructionCount suffix -
              ProtocolState.remaining suffix point := by
            dsimp only [tail]
            omega
          rw [same]
          exact ih point tail tailRank

omit [Fintype Player] in
private theorem sourceReplay_owned_step_atom
    (current : CommitRecoveryState setup.program) (owner : Player)
    (acting : ProtocolState.actor setup.program current.point = some owner)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal (some current) joint)
    (next : CommitRecoveryState setup.program)
    (moved : some next ∈
      (setup.commitRecoveryProtocol.step (some current) ⟨joint, legal⟩).support) :
    (setup.commitRecoveryProtocol.step (some current) ⟨joint, legal⟩) (some next) = 1 := by
  have supported : next ∈ (current.step joint).support := by
    change some next ∈ ((current.step joint).map some).support at moved
    obtain ⟨other, supported, same⟩ := (PMF.mem_support_map_iff ..).mp moved
    cases Option.some.inj same
    exact supported
  change ((current.step joint).map some) (some next) = 1
  rw [pmf_map_apply_of_injective _ (Option.some_injective _)]
  apply (PMF.apply_eq_one_iff _ _).mpr
  ext result
  constructor
  · intro member
    exact Set.mem_singleton_iff.mpr
      (setup.commitRecovery_step_unique_of_actor current owner acting joint
        result next member supported)
  · intro same
    cases Set.mem_singleton_iff.mp same
    exact supported

omit [Fintype Player] in
private theorem sourceReplay_owned_interval_mass
    {first last : setup.commitRecoveryProtocol.State}
    (prior : setup.commitRecoveryProtocol.Trace first)
    (trace : setup.commitRecoveryProtocol.Trace last)
    (retained : TracePrefix prior trace)
    (owned : ∀ {before after : setup.commitRecoveryProtocol.State}
      (middle : setup.commitRecoveryProtocol.Trace before)
      (joint : Player → Option (CommitRecoveryMove Player L))
      (legal : setup.commitRecoveryProtocol.Legal before joint)
      (moved : after ∈ (setup.commitRecoveryProtocol.step before ⟨joint, legal⟩).support),
      TracePrefix prior middle → TracePrefix (middle.extend joint legal moved) trace →
        ∃ (current : CommitRecoveryState setup.program) (owner : Player),
          before = some current ∧
          ProtocolState.actor setup.program current.point = some owner) :
    trace.transitionMass = prior.transitionMass := by
  induction retained with
  | refl => rfl
  | @extend before after middle earlier joint legal moved ih =>
      have lastKept : TracePrefix middle (middle.extend joint legal moved) :=
        .extend .refl joint legal moved
      have mass : middle.transitionMass = prior.transitionMass := by
        apply ih
        intro source target initialTrace row rowLegal rowMoved left right
        exact owned initialTrace row rowLegal rowMoved left (right.trans lastKept)
      obtain ⟨current, owner, source, acting⟩ :=
        owned middle joint legal moved earlier .refl
      cases source
      obtain ⟨next, supported, same⟩ := (PMF.mem_support_map_iff ..).mp moved
      cases same
      have atom := sourceReplay_owned_step_atom setup current owner acting
        joint legal next moved
      rw [Trace.transitionMass_extend, atom, ENNReal.toReal_one, mul_one, mass]

omit [Fintype Player] in
private theorem sourceReplay_prefix_some
    (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) (retained : TracePrefix prior trace) :
    ∃ current, state = some current := by
  cases retained with
  | refl => exact ⟨first, rfl⟩
  | @extend source target middle earlier joint legal moved =>
      cases source with
      | none =>
          obtain ⟨inputs, supported, same⟩ := (PMF.mem_support_map_iff ..).mp moved
          exact ⟨_, same.symm⟩
      | some current =>
          obtain ⟨next, supported, same⟩ := (PMF.mem_support_map_iff ..).mp moved
          exact ⟨next, same.symm⟩

omit [Fintype Player] in
private theorem sourceReplay_actor_none_not_commit :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : ProtocolState program),
      ProtocolState.actor program point = none →
        ProtocolState.atCommit program point = false := by
  intro Γ O program
  induction program with
  | ret payoffs => intro point; exact fun _ => rfl
  | sample name fresh law suffix ih =>
      intro point
      cases point with
      | inl source => exact fun _ => rfl
      | inr point => exact ih point
  | commit name owner fresh guard suffix ih =>
      intro point
      cases point with
      | inl source => intro impossible; cases impossible
      | inr point => exact ih point
  | reveal published owner name fresh selected unresolved suffix ih =>
      intro point
      cases point with
      | inl source => exact fun _ => rfl
      | inr point => exact ih point

omit [Fintype Player] in
private theorem sourceReplay_sample_free_interval_mass
    (first last : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    (trace : setup.commitRecoveryProtocol.Trace (some last))
    (retained : TracePrefix prior trace)
    (nonchance : ∀ event : Fin (eventCount setup.program),
      instructionCount setup.program - ProtocolState.remaining setup.program first.saved ≤
        event.val →
      event.val < instructionCount setup.program -
        ProtocolState.remaining setup.program last.saved →
      ∃ owner, eventOwner? setup.program event = some owner) :
    trace.transitionMass = prior.transitionMass := by
  apply sourceReplay_owned_interval_mass setup prior trace retained
  intro before after middle joint legal moved left right
  obtain ⟨current, rfl⟩ := sourceReplay_prefix_some setup first prior middle left
  cases acting : ProtocolState.actor setup.program current.point with
  | some owner => exact ⟨current, owner, rfl, acting⟩
  | none =>
      have notCommit := sourceReplay_actor_none_not_commit setup.program current.point acting
      have saved := (setup.commitRecovery_blockFrontier middle).saved_eq_point_of_not_atCommit
        notCommit
      obtain ⟨next, supported, rfl⟩ := (PMF.mem_support_map_iff ..).mp moved
      obtain ⟨raw, rawSupported, nextEq⟩ := current.step_noncommit_atPoint
        (setup.commitRecovery_blockFrontier middle) notCommit joint next supported
      have consumed := ProtocolState.recoveryStep_remaining setup.program current.point
        current.excluded joint raw legal.1 rawSupported
      have lower := sourceReplay_saved_remaining_le_of_prefix setup prior middle left
      have upper := sourceReplay_saved_remaining_le_of_prefix setup
        (middle.extend joint legal moved) trace right
      change ProtocolState.remaining setup.program current.saved ≤
        ProtocolState.remaining setup.program first.saved at lower
      change ProtocolState.remaining setup.program last.saved ≤
        ProtocolState.remaining setup.program next.saved at upper
      rw [saved] at lower
      rw [nextEq] at upper
      change ProtocolState.remaining setup.program last.saved ≤
        ProtocolState.remaining setup.program raw.1 at upper
      have bound := ProtocolState.remaining_le_instructionCount setup.program current.point
      have positive : 0 < ProtocolState.remaining setup.program current.point := by omega
      let event : Fin (eventCount setup.program) :=
        ⟨instructionCount setup.program - ProtocolState.remaining setup.program current.point,
          by rw [eventCount_eq_instructionCount]; omega⟩
      obtain ⟨owner, owned⟩ := nonchance event (by dsimp only [event]; omega)
        (by dsimp only [event]; omega)
      have sourceActor := sourceReplay_actor_at_rank setup.program current.point event rfl
      rw [acting, owned] at sourceActor
      cases sourceActor

omit [Fintype Player] in
private theorem sourceReplay_drain_ownerless_output
    (phase : RuntimePhase (serviceGraph setup .concurrent)) (fuel : Nat)
    (current : RecoveryState (serviceGraph setup .concurrent))
    (event : (serviceGraph setup .concurrent).EventId)
    (ownerless : (serviceGraph setup .concurrent).actor? event = none) :
    (phase.drainFuel fuel current).native.config.outputs event =
      current.native.config.outputs event := by
  induction fuel generalizing current with
  | zero => rfl
  | succ fuel ih =>
      unfold RuntimePhase.drainFuel
      split
      · rename_i pending
        rw [ih]
        obtain ⟨owner, acting, _excluded⟩ := (Classical.choose_spec pending).2.owned
        have different : event ≠ Classical.choose pending := by
          intro same
          rw [← same, ownerless] at acting
          cases acting
        obtain ⟨action, supported⟩ := current.completeAutomatic_step
          (Classical.choose pending) (Classical.choose_spec pending).2
        rw [Config.step, PMF.support_map] at supported
        obtain ⟨value, _supported, completed⟩ := supported
        rw [← completed]
        exact Config.complete_output_of_ne _ _ _ _ _ _ different
      · rfl

omit [Fintype Player] in
private theorem sourceReplay_settle_ownerless_output
    (phases : List (RuntimePhase (serviceGraph setup .concurrent)))
    (generation : Nat) (entry current : RecoveryState (serviceGraph setup .concurrent))
    (retired : List (RetiredCommitAttempt (serviceGraph setup .concurrent)))
    (event : (serviceGraph setup .concurrent).EventId)
    (ownerless : (serviceGraph setup .concurrent).actor? event = none)
    (same : entry.native.config.outputs event = current.native.config.outputs event) :
    (PhaseRuntimeState.settle phases generation entry current retired).current.native.config.outputs
      event = current.native.config.outputs event := by
  induction phases generalizing generation entry current retired with
  | nil => rfl
  | cons phase remaining ih =>
      have drain (state : RecoveryState (serviceGraph setup .concurrent)) :
          (phase.drain state).native.config.outputs event = state.native.config.outputs event :=
        sourceReplay_drain_ownerless_output setup phase _ state event ownerless
      have rebuilt :
          (phase.drain (PhaseRuntimeState.restore entry
            (phase.drain current))).native.config.outputs event =
              current.native.config.outputs event :=
        (drain _).trans same
      unfold PhaseRuntimeState.settle
      dsimp only
      split
      · split
        · split
          · exact rebuilt
          · exact (ih generation _ _ _ rfl).trans rebuilt
        · exact (ih generation _ _ _ rfl).trans (drain current)
      · exact drain current

omit [Fintype Player] in
private theorem sourceReplay_frontier_completed_before
    (state : PhaseRuntimeState (serviceGraph setup .concurrent)) (frontier : state.Frontier)
    (event : (serviceGraph setup .concurrent).EventId)
    (below : event.val < state.attempt.phase) :
    event ∈ state.current.native.config.cut.completed := by
  have positioned := frontier.positioned
  cases phases : state.phases with
  | nil =>
      rw [phases] at positioned
      have positioned : state.current.native.config.cut.IsPrefix _ := positioned
      exact (positioned.2 event).mpr event.isLt
  | cons phase remaining =>
      rw [phases] at positioned
      apply positioned.2.1 event
      simpa only [PhaseRuntimeState.attempt, phases, List.head?_cons,
        Option.map_some, Option.getD_some] using below

omit [Fintype Player] in
private theorem sourceReplay_live_ownerless_missing
    (state : PhaseRuntimeState (serviceGraph setup .concurrent))
    (frontier : state.Frontier) (live : state.Live)
    (event : (serviceGraph setup .concurrent).EventId)
    (ownerless : (serviceGraph setup .concurrent).actor? event = none)
    (lower : state.attempt.phase ≤ event.val) :
    event ∉ state.current.native.config.cut.completed := by
  intro completed
  have positioned := frontier.positioned
  cases installed : state.phases with
  | nil =>
      have bound := event.isLt
      simp only [PhaseRuntimeState.attempt, installed, List.head?_nil, Option.map_none,
        Option.getD_none] at lower
      omega
  | cons phase remaining =>
      rw [installed] at positioned
      have above : phase.low ≤ event.val := by
        simpa only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
          Option.getD_some] using lower
      have below := positioned.2.2 event completed
      have publicOutput := EventCode.output_public_of_actor_none
        ((serviceGraph setup .concurrent).nodes event) ownerless
      have notPublication := EventCode.not_publication_of_actor_none
        ((serviceGraph setup .concurrent).nodes event) ownerless
      have typed := phase.fields event above below
      have kind : phase.kind = .sample := by
        cases kind : phase.kind with
        | sample => rfl
        | commitment =>
            rw [kind] at typed
            obtain ⟨owner, payload, shape⟩ := typed
            rw [shape] at publicOutput
            exact publicOutput.elim
        | reveal =>
            rw [kind] at typed
            obtain ⟨payload, shape⟩ := typed
            exact (notPublication (by rw [shape]; trivial)).elim
      have singleton := phase.sample_singleton kind
      apply live phase (by rw [installed]; exact Option.mem_some_iff.mpr rfl)
      intro query inside
      have bounds := (phase.mem_events query).mp inside
      have same : query = event := Fin.ext (by omega)
      exact same ▸ completed

omit [Fintype Player] in
private theorem sourceReplay_live_ownerless_saved_output
    (state : PhaseRuntimeState (serviceGraph setup .concurrent))
    (frontier : state.Frontier) (live : state.Live) (stored : state.StoredCheckpoint)
    (nonempty : state.phases ≠ [])
    (event : (serviceGraph setup .concurrent).EventId)
    (ownerless : (serviceGraph setup .concurrent).actor? event = none) :
    state.entry.native.config.outputs event = state.current.native.config.outputs event := by
  have entryPrefix : state.entry.native.config.cut.IsPrefix state.attempt.phase := by
    have positioned := frontier.positioned
    cases installed : state.phases with
    | nil => exact (nonempty installed).elim
    | cons phase remaining =>
        rw [installed] at positioned
        simpa only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
          Option.getD_some] using positioned.1
  by_cases below : event.val < state.attempt.phase
  · have completed := (entryPrefix.2 event).mpr below
    have present := (state.entry.native.config.output_available event).mpr completed
    obtain ⟨value, entryRead⟩ := Option.isSome_iff_exists.mp present
    have currentRead := stored (.inr event) value entryRead
    exact entryRead.trans currentRead.symm
  · have entryMissing : state.entry.native.config.outputs event = none := by
      cases reading : state.entry.native.config.outputs event with
      | none => rfl
      | some value =>
          have completed := (state.entry.native.config.output_available event).mp (by
            rw [reading]; rfl)
          exact (below ((entryPrefix.2 event).mp completed)).elim
    have currentMissing : state.current.native.config.outputs event = none := by
      cases reading : state.current.native.config.outputs event with
      | none => rfl
      | some value =>
          have completed := (state.current.native.config.output_available event).mp (by
            rw [reading]; rfl)
          exact (sourceReplay_live_ownerless_missing setup state frontier live event ownerless
            (by omega) completed).elim
    exact entryMissing.trans currentMissing.symm

omit [Fintype Player] in
private theorem sourceReplay_expire_ownerless
    (current : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (event : (serviceGraph setup .concurrent).EventId)
    (ownerless : (serviceGraph setup .concurrent).actor? event = none) :
    environmentStep implementation.runtime current (.expire event) = PMF.pure current := by
  by_cases ready : current.config.cut.Ready event
  · cases activated : current.activatedAt event with
    | none =>
        exact environmentStep_expire_of_not_activated implementation.runtime current event
          ready activated
    | some entered =>
        by_cases due : implementation.runtime.deadline event ≤ current.clock - entered
        · cases view : nodeView (serviceGraph setup .concurrent) event with
          | bind owner payload output code =>
              have acting := (EventCode.actor_cast output
                ((serviceGraph setup .concurrent).nodes event)).symm.trans
                  (congrArg EventCode.actor code)
              change (serviceGraph setup .concurrent).actor? event = some owner at acting
              rw [ownerless] at acting
              cases acting
          | resolve owner payload binding checks output code =>
              have acting := (EventCode.actor_cast output
                ((serviceGraph setup .concurrent).nodes event)).symm.trans
                  (congrArg EventCode.actor code)
              change (serviceGraph setup .concurrent).actor? event = some owner at acting
              rw [ownerless] at acting
              cases acting
          | sample payload law output code =>
              exact environmentStep_expire_sample_eq implementation.runtime current event ready
                entered activated due payload law output code view
        · exact environmentStep_expire_of_not_due implementation.runtime current event ready
            entered activated due
  · exact environmentStep_expire_of_not_ready implementation.runtime current event ready

omit [Fintype Player] in
private theorem sourceReplay_environment_ownerless_output
    (current next : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (command : EnvironmentCommand (serviceGraph setup .concurrent))
    (event : (serviceGraph setup .concurrent).EventId)
    (ownerless : (serviceGraph setup .concurrent).actor? event = none)
    (other : command ≠ .executeSample event)
    (moved : next ∈ (environmentStep implementation.runtime current command).support) :
    next.config.outputs event = current.config.outputs event := by
  have stepOther (address : (serviceGraph setup .concurrent).EventId)
      (different : event ≠ address) (ready : current.config.cut.Ready address)
      (action : (serviceGraph setup .concurrent).Action address)
      (supported : next.config ∈ (current.config.step address ready action).support) :
      next.config.outputs event = current.config.outputs event := by
    rw [Config.step, PMF.support_map] at supported
    obtain ⟨value, _supported, same⟩ := supported
    rw [← same]
    exact Config.complete_output_of_ne _ _ _ _ _ _ different
  cases command with
  | advanceClock =>
      rw [environmentStep, PMF.mem_support_pure_iff] at moved
      cases moved
      rfl
  | expire address =>
      by_cases same : event = address
      · subst address
        rw [sourceReplay_expire_ownerless setup implementation current event ownerless,
          PMF.mem_support_pure_iff] at moved
        cases moved
        rfl
      · rcases environmentStep_expire_config_eq_or_mem_step implementation.runtime current next
          address moved with unchanged | ⟨ready, action, supported⟩
        · rw [unchanged]
        · exact stepOther address same ready action supported
  | executeSample address =>
      have different : event ≠ address := fun same => other (by cases same; rfl)
      rcases (environmentStep_executeSample_config_activated implementation.runtime current next
        address moved).2 with ⟨unchanged, _activated⟩ | ⟨ready, action, supported, _activated⟩
      · rw [unchanged]
      · exact stepOther address different ready action supported

omit [Fintype Player] in
private theorem sourceReplay_handle_ownerless_output
    (current next : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (message : Message Player (Payload (serviceGraph setup .concurrent)))
    (event : (serviceGraph setup .concurrent).EventId)
    (ownerless : (serviceGraph setup .concurrent).actor? event = none)
    (accepted : EventGraphRuntime.handle implementation.runtime current message = some next) :
    next.config.outputs event = current.config.outputs event := by
  obtain ⟨address, named, acting⟩ := handle_event_actor implementation.runtime current next
    message accepted
  obtain ⟨actual, actualNamed, ready, action, supported⟩ :=
    handle_config_mem_step implementation.runtime current next message accepted
  have same : actual = address := Option.some.inj (actualNamed.symm.trans named)
  subst actual
  have different : event ≠ address := by
    intro same
    rw [← same, ownerless] at acting
    cases acting
  rw [Config.step, PMF.support_map] at supported
  obtain ⟨value, _supported, same⟩ := supported
  rw [← same]
  exact Config.complete_output_of_ne _ _ _ _ _ _ different

omit [Fintype Player] in
private theorem sourceReplay_phase_handle_ownerless_output
    (current next : PhaseRuntimeState (serviceGraph setup .concurrent))
    (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)))
    (event : (serviceGraph setup .concurrent).EventId)
    (ownerless : (serviceGraph setup .concurrent).actor? event = none)
    (same : current.entry.native.config.outputs event = current.current.native.config.outputs event)
    (accepted : current.handle implementation.runtime message = some next) :
    next.current.native.config.outputs event = current.current.native.config.outputs event := by
  unfold PhaseRuntimeState.handle at accepted
  split at accepted
  · obtain ⟨native, rawAccepted, rfl⟩ := Option.map_eq_some_iff.mp accepted
    have raw := sourceReplay_handle_ownerless_output setup implementation current.current.native
      native ⟨message.id, message.payload.packet.call⟩ event ownerless rawAccepted
    have normalized := sourceReplay_settle_ownerless_output setup current.phases
      current.generation current.entry
      (current.current.inclusionResult message.payload.packet.call native) current.retired event
      ownerless (same.trans raw.symm)
    exact normalized.trans raw
  · cases accepted

omit [Fintype Player] in
private theorem sourceReplay_phase_environment_ownerless_output
    (current next : PhaseRuntimeState (serviceGraph setup .concurrent))
    (command : EnvironmentCommand (serviceGraph setup .concurrent))
    (event : (serviceGraph setup .concurrent).EventId)
    (ownerless : (serviceGraph setup .concurrent).actor? event = none)
    (same : current.entry.native.config.outputs event = current.current.native.config.outputs event)
    (other : command ≠ .executeSample event)
    (moved : next ∈ (current.environment implementation.runtime command).support) :
    next.current.native.config.outputs event = current.current.native.config.outputs event := by
  unfold PhaseRuntimeState.environment at moved
  split at moved
  · obtain ⟨native, rawMoved, rfl⟩ := (PMF.mem_support_map_iff ..).mp moved
    have raw := sourceReplay_environment_ownerless_output setup implementation
      current.current.native native command event ownerless other rawMoved
    have normalized := sourceReplay_settle_ownerless_output setup current.phases
      current.generation current.entry (current.current.environmentResult command native)
      current.retired event ownerless (same.trans raw.symm)
    exact normalized.trans raw
  · cases (PMF.mem_support_pure_iff _ _).mp moved
    rfl

omit [Fintype Player] in
private theorem sourceReplay_reactive_environment_ownerless_output
    (current next : (nativeApplication).Execution) (command : (nativeApplication).Command)
    (event : (serviceGraph setup .concurrent).EventId)
    (ownerless : (serviceGraph setup .concurrent).actor? event = none)
    (same : current.application.entry.native.config.outputs event =
      current.application.current.native.config.outputs event)
    (other : command ≠ .application (.executeSample event))
    (moved : next ∈ (current.environmentStep nativeApplication command).support) :
    next.application.current.native.config.outputs event =
      current.application.current.native.config.outputs event := by
  unfold ReactiveApplication.Execution.environmentStep at moved
  rw [PMF.support_map] at moved
  obtain ⟨updated, supported, rfl⟩ := moved
  cases command with
  | wait =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      rfl
  | activate owner =>
      obtain ⟨network, _supported, rfl⟩ := (PMF.mem_support_map_iff ..).mp supported
      rfl
  | «include» id =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      change (current.includePending nativeApplication id).application.current.native.config.outputs
        event = current.application.current.native.config.outputs event
      unfold ReactiveApplication.Execution.includePending
      cases included : current.network.includePending id with
      | mk envelope network =>
          cases envelope with
          | none => rfl
          | some message =>
              dsimp only
              change ((current.application.handle implementation.runtime message).getD
                current.application).current.native.config.outputs event = _
              cases accepted : current.application.handle implementation.runtime message with
              | none => rfl
              | some application =>
                  exact sourceReplay_phase_handle_ownerless_output setup implementation
                    current.application application message event ownerless same accepted
  | application operation =>
      obtain ⟨application, applicationMoved, rfl⟩ := (PMF.mem_support_map_iff ..).mp supported
      exact sourceReplay_phase_environment_ownerless_output setup implementation
        current.application application operation event ownerless same
          (fun equal => other (by cases equal; rfl))
            applicationMoved

private theorem sourceReplay_environment_crossed_rank_owned
    (current next : (nativeApplication).Execution)
    (first : RecoverySourceWitness setup .concurrent implementation.plan current.application)
    (last : RecoverySourceWitness setup .concurrent implementation.plan next.application)
    (live : current.application.Live) (nonempty : current.application.phases ≠ [])
    (command : (nativeApplication).Command)
    (event : (serviceGraph setup .concurrent).EventId)
    (other : command ≠ .application (.executeSample event))
    (moved : next ∈ (current.environmentStep nativeApplication command).support)
    (lower : current.application.attempt.phase ≤ event.val)
    (upper : event.val < next.application.attempt.phase) :
    ∃ owner, eventOwner? setup.program event = some owner := by
  cases acting : (serviceGraph setup .concurrent).actor? event with
  | some owner =>
      refine ⟨owner, ?_⟩
      rw [eventOwner?_eq_actor]
      exact acting
  | none =>
      have missing := sourceReplay_live_ownerless_missing setup current.application
        first.order.frontier live event acting lower
      have same := sourceReplay_live_ownerless_saved_output setup current.application
        first.order.frontier live first.stored nonempty event acting
      have output := sourceReplay_reactive_environment_ownerless_output setup implementation
        current next command event acting same other moved
      have completed := sourceReplay_frontier_completed_before setup next.application
        last.order.frontier event upper
      have present := (next.application.current.native.config.output_available event).mpr completed
      rw [output] at present
      exact False.elim (missing
        ((current.application.current.native.config.output_available event).mp present))

private theorem sourceReplay_nonsample_interval_mass
    (current next : (nativeApplication).Execution)
    (first : RecoverySourceWitness setup .concurrent implementation.plan current.application)
    (last : RecoverySourceWitness setup .concurrent implementation.plan next.application)
    (live : current.application.Live) (nonempty : current.application.phases ≠ [])
    (command : (nativeApplication).Command)
    (nonsample : ∀ event : (serviceGraph setup .concurrent).EventId,
      command ≠ .application (.executeSample event))
    (moved : next ∈ (current.environmentStep nativeApplication command).support)
    (retained : TracePrefix first.checkpoint.trace last.checkpoint.trace) :
    last.checkpoint.trace.transitionMass = first.checkpoint.trace.transitionMass := by
  apply sourceReplay_sample_free_interval_mass setup _ _ first.checkpoint.trace
    last.checkpoint.trace retained
  intro event lower upper
  change instructionCount setup.program - ProtocolState.remaining setup.program
    (first.checkpoint.residual.lift
      (ProtocolState.entry first.checkpoint.residual.tail first.checkpoint.source)) ≤ event.val
    at lower
  change event.val < instructionCount setup.program - ProtocolState.remaining setup.program
    (last.checkpoint.residual.lift
      (ProtocolState.entry last.checkpoint.residual.tail last.checkpoint.source)) at upper
  rw [first.checkpoint.saved_position] at lower
  rw [last.checkpoint.saved_position] at upper
  exact sourceReplay_environment_crossed_rank_owned setup implementation current next first last
    live nonempty command event (nonsample event) moved lower upper

omit [Fintype Player] in
private theorem sourceReplay_sample_interval_mass
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (name : VarId) (payload : L.Ty) (fresh : name ∉ Γ.map Prod.fst)
    (law : L.DistExpr (SourcePublicCtx L Γ) payload)
    (suffix : SourceProgram Player L ((name, .publicData payload) :: Γ) O)
    (lift : ProtocolState (.sample name fresh law suffix) → ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program (.sample name fresh law suffix) lift)
    (source : Config Player L Γ) (unique : (Γ.map Prod.fst).Nodup)
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.sample name fresh law suffix))
    (aligned : CompiledReadoutSuffix setup.program (.sample name fresh law suffix) refs embedding)
    (excluded : Finset Player) (generation : Nat)
    (prior : setup.commitRecoveryProtocol.Trace (some (CommitRecoveryState.atPoint
      (lift (ProtocolState.entry (.sample name fresh law suffix) source)) excluded generation)))
    {state : PhaseRuntimeState (serviceGraph setup .concurrent)}
    (last : RecoverySourceCheckpoint setup .concurrent state) (stored : state.StoredCheckpoint)
    (retained : TracePrefix prior last.trace) (longer : prior.length < last.trace.length)
    (value : L.Val payload)
    (observed :
      let head : Fin (eventCount (.sample name fresh law suffix)) := ⟨0, by simp [eventCount]⟩
      let field : FieldRef (graphLayout setup.program) (.publicData payload) := by
        simpa only [head, outputLayout, Fin.mk_zero, Fin.cases_zero] using embedding.ref head
      field.get? state.current.native.config.store = some value)
    (nonchance : ∀ event : Fin (eventCount setup.program),
      instructionCount setup.program - instructionCount suffix ≤ event.val →
      event.val < instructionCount setup.program - ProtocolState.remaining setup.program
        (last.residual.lift (ProtocolState.entry last.residual.tail last.source)) →
      ∃ owner, eventOwner? setup.program event = some owner) :
    last.trace.transitionMass =
      prior.transitionMass * (L.evalDist law (sourcePublicEnv source.state) value).toReal := by
  let sourceStart := CommitRecoveryState.atPoint
    (lift (ProtocolState.entry (.sample name fresh law suffix) source)) excluded generation
  rcases retained.reachesWithin.eq_or_step with sameHistory | firstStep
  · have lengths := congrArg (fun history : setup.commitRecoveryProtocol.History =>
      history.trace.length) sameHistory
    change prior.length = last.trace.length at lengths
    omega
  · obtain ⟨joint, legal, reached, moved, fuel, onward⟩ := firstStep
    obtain ⟨next, supported, rfl⟩ := (PMF.mem_support_map_iff ..).mp moved
    have notCommit : ProtocolState.atCommit setup.program sourceStart.point = false := by
      simp only [sourceStart, CommitRecoveryState.atPoint, origin.atCommit_lift,
        ProtocolState.entry, ProtocolState.atCommit, Sum.elim_inl]
    have kernel : sourceStart.step joint =
        (L.evalDist law (sourcePublicEnv source.state)).map (fun sampled =>
          CommitRecoveryState.atPoint
            (lift (.inr (ProtocolState.entry suffix (sampleSuccessor name source sampled))))
            excluded generation) := by
      rw [sourceStart.step_noncommit_law (CommitRecoveryState.atPoint_blockFrontier _ _ _)
        notCommit joint]
      change (ProtocolState.recoveryStep setup.program
        (lift (ProtocolState.entry (.sample name fresh law suffix) source)) excluded joint).map _ =
          _
      rw [origin.recoveryStep_lift]
      simp only [ProtocolState.recoveryStep, ProtocolState.entry, Sum.elim_inl, PMF.map_comp,
        Function.comp_def]
      rfl
    change next ∈ (sourceStart.step joint).support at supported
    rw [kernel] at supported
    obtain ⟨sampled, _sampledSupport, rfl⟩ := (PMF.mem_support_map_iff ..).mp supported
    let head : Fin (eventCount (.sample name fresh law suffix)) := ⟨0, by simp [eventCount]⟩
    let field : FieldRef (graphLayout setup.program) (.publicData payload) := by
      simpa only [head, outputLayout, Fin.mk_zero, Fin.cases_zero] using embedding.ref head
    let nextRefs := ContextRefs.cons (name := name) (cell := .publicData payload) field refs
    let nextEmbedding := embedding.tail suffix (by simp only [eventCount]) (fun _ => rfl)
    have nextAligned : CompiledReadoutSuffix setup.program suffix nextRefs nextEmbedding :=
      aligned.sampleTail setup.program fresh law suffix refs embedding
    have nextUnique : (((name, .publicData payload) :: Γ).map Prod.fst).Nodup := by
      simpa only [List.map_cons] using List.nodup_cons.mpr ⟨fresh, unique⟩
    have agreement : nextRefs.Agrees (sampleSuccessor name source sampled).state
        state.entry.native.config.store :=
      sourceReplaySuffixSavedAgreement setup suffix
        (fun point => lift (.inr point)) (origin.sampleTail fresh law suffix)
        (sampleSuccessor name source sampled) nextUnique nextRefs nextEmbedding nextAligned _
        (prior.extend joint legal moved) rfl rfl last onward.tracePrefix
    have savedRead : field.get? state.entry.native.config.store = some sampled :=
      agreement .here
    have currentRead : field.get? state.current.native.config.store = some sampled :=
      field.get?_preserved _ _ (fun query result present => stored query result present)
        sampled savedRead
    change field.get? state.current.native.config.store = some value at observed
    have sameValue : sampled = value := Option.some.inj (currentRead.symm.trans observed)
    subst sampled
    have tailMass : last.trace.transitionMass =
        (prior.extend joint legal moved).transitionMass := by
      apply sourceReplay_sample_free_interval_mass setup _ _
        (prior.extend joint legal moved) last.trace onward.tracePrefix
      intro event lower upper
      apply nonchance event
      · simpa only [CommitRecoveryState.atPoint, origin.remaining_lift,
          ProtocolState.remaining, Sum.elim_inr, ProtocolState.remaining_entry] using lower
      · exact upper
    have atom : (setup.commitRecoveryProtocol.step (some sourceStart) ⟨joint, legal⟩)
        (some (CommitRecoveryState.atPoint
          (lift (.inr (ProtocolState.entry suffix (sampleSuccessor name source value))))
          excluded generation)) = L.evalDist law (sourcePublicEnv source.state) value := by
      change ((sourceStart.step joint).map some) _ = _
      rw [pmf_map_apply_of_injective _ (Option.some_injective _)]
      exact sourceReplay_source_sample_atom setup name payload fresh law suffix lift origin
        source excluded generation joint value
    rw [tailMass, Trace.transitionMass_extend, atom]

private theorem sourceReplay_nonsample_environment_atom
    (operational : implementation.Operational)
    (current next : (nativeApplication).Execution) (command : (nativeApplication).Command)
    (nonsample : ∀ event : (serviceGraph setup .concurrent).EventId,
      command ≠ .application (.executeSample event))
    (moved : next ∈ (current.environmentStep nativeApplication command).support) :
    current.environmentStep nativeApplication command next = 1 := by
  have deterministic : ∃ ending,
      current.environmentStep nativeApplication command = PMF.pure ending := by
    cases command with
    | activate owner =>
        have complete : (nativeApplication).observePending =
            MessageNetwork.completePendingObservation := operational.completePending
        rw [ReactiveApplication.Execution.activation_samples, complete]
        simp only [MessageNetwork.completePendingObservation, PMF.pure_map]
        exact ⟨_, rfl⟩
    | wait =>
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
        exact ⟨_, rfl⟩
    | «include» id =>
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
        exact ⟨_, rfl⟩
    | application operation =>
        cases operation with
        | executeSample event => exact (nonsample event rfl).elim
        | advanceClock =>
            change ∃ ending, (PMF.map _ (PMF.map _
              (PhaseRuntimeState.environment implementation.runtime current.application
                .advanceClock))) =
                PMF.pure ending
            simp only [PhaseRuntimeState.environment, environmentStep]
            split <;> simp only [PMF.pure_map] <;> exact ⟨_, rfl⟩
        | expire event =>
            change ∃ ending, (PMF.map _ (PMF.map _
              (PhaseRuntimeState.environment implementation.runtime current.application
                (.expire event)))) =
                PMF.pure ending
            simp only [PhaseRuntimeState.environment, environmentStep]
            split <;> simp only [PMF.pure_map] <;> exact ⟨_, rfl⟩
  obtain ⟨ending, kernel⟩ := deterministic
  rw [kernel, PMF.mem_support_pure_iff] at moved
  cases moved
  rw [kernel, PMF.pure_apply_self]

private theorem sourceReplay_sample_command_interval_mass
    (current next : (nativeApplication).Execution)
    (first : RecoverySourceWitness setup .concurrent implementation.plan current.application)
    (last : RecoverySourceWitness setup .concurrent implementation.plan next.application)
    (live : current.application.Live)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (remaining : List (RuntimePhase (serviceGraph setup .concurrent)))
    (installed : current.application.phases = phase :: remaining) (kind : phase.kind = .sample)
    (event : (serviceGraph setup .concurrent).EventId)
    (ready : current.application.current.native.config.cut.Ready event)
    (allowed : current.application.commandAllowed (.executeSample event) = true)
    (moved : next ∈
      (current.environmentStep nativeApplication (.application (.executeSample event))).support)
    (retained : TracePrefix first.checkpoint.trace last.checkpoint.trace) :
    last.checkpoint.trace.transitionMass = first.checkpoint.trace.transitionMass *
      (current.environmentStep nativeApplication
        (.application (.executeSample event)) next).toReal := by
  have nonempty : current.application.phases ≠ [] := by
    rw [installed]
    exact List.cons_ne_nil _ _
  have low : phase.low = current.application.attempt.phase := by
    simp only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
      Option.getD_some]
  have inside : event ∈ phase.events := by
    simpa only [PhaseRuntimeState.commandAllowed, installed, List.head?_cons, Option.any_some,
      decide_eq_true_eq] using allowed
  have bounds := (phase.mem_events event).mp inside
  have singleton := phase.sample_singleton kind
  have eventRank : event.val = current.application.attempt.phase := by omega
  have applicationMoved : next.application ∈
      (current.application.environment implementation.runtime (.executeSample event)).support := by
    have supported := moved
    unfold ReactiveApplication.Execution.environmentStep at supported
    obtain ⟨updated, supported, endingEq⟩ := (PMF.mem_support_map_iff ..).mp supported
    have applicationEq := congrArg (fun execution : (nativeApplication).Execution =>
      execution.application) endingEq
    change updated.application = next.application at applicationEq
    obtain ⟨application, supported, updatedEq⟩ := (PMF.mem_support_map_iff ..).mp supported
    have updatedApplication := congrArg (fun execution : (nativeApplication).Execution =>
      execution.application) updatedEq
    change application = updated.application at updatedApplication
    rw [← applicationEq, ← updatedApplication]
    exact supported
  have ownerless : (serviceGraph setup .concurrent).actor? event = none := by
    have output := phase.fields event bounds.1 bounds.2
    rw [kind] at output
    obtain ⟨payload, output⟩ := output
    cases viewed : nodeView (serviceGraph setup .concurrent) event with
    | bind owner ty shape code => cases shape.symm.trans output
    | resolve owner ty binding checks shape code => cases shape.symm.trans output
    | sample ty law shape code =>
        exact (EventCode.actor_cast shape _).symm.trans (congrArg EventCode.actor code)
  have advanced := PhaseRuntimeState.sample_advances_phase implementation.runtime
    current.application next.application first.order.frontier phase
      (by rw [installed]; rfl) kind event (by omega) ready ownerless applicationMoved
  have longer : first.checkpoint.trace.length < last.checkpoint.trace.length := by
    have bounded := retained.length_le
    by_contra notLonger
    have same := retained.eq_of_length (by omega)
    have ranks := congrArg (fun history : setup.commitRecoveryProtocol.History =>
      history.state.map (fun state => instructionCount setup.program -
        ProtocolState.remaining setup.program state.saved)) same
    have sameRank : current.application.attempt.phase = next.application.attempt.phase := by
      simpa only [Option.map_some, CommitRecoveryState.atPoint,
        first.checkpoint.saved_position, last.checkpoint.saved_position] using Option.some.inj ranks
    omega
  generalize checkpointEq : first.checkpoint = checkpoint at retained longer ⊢
  rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, source, refs, registry, embedding, before,
    compiled, terminalAligned, agrees, guards, failures, unique, ranks, actors, commits,
    owners, endpoints, automatic, histories, memories, steps, menus, readouts, prior,
    views, historyAlignment, origin⟩
  have total := compiled.countEq
  have positive : 0 < eventCount program := by
    have bounded := event.isLt
    change event.val < eventCount setup.program at bounded
    change current.application.attempt.phase + eventCount program = eventCount setup.program
      at total
    omega
  let zero : Fin (eventCount program) := ⟨0, positive⟩
  have ranked : (embedding.event zero).val = current.application.attempt.phase := by
    have ranked := compiled.rankEq zero
    dsimp only [zero] at ranked
    omega
  have sameEvent : event = embedding.event zero := Fin.ext (eventRank.trans ranked.symm)
  have headSample : RuntimePhaseKind.sample.Matches (outputLayout program zero) := by
    have typed := phase.fields (embedding.event zero) (by omega) (by omega)
    rw [kind] at typed
    change RuntimePhaseKind.sample.Matches (outputLayout setup.program (embedding.event zero))
      at typed
    rw [embedding.layout_eq] at typed
    exact typed
  cases program with
  | ret payoffs => simp only [eventCount] at positive; omega
  | commit name owner fresh guard suffix =>
      obtain ⟨payload, impossible⟩ := headSample
      cases impossible
  | reveal published owner name fresh selected unresolved suffix =>
      obtain ⟨payload, impossible⟩ := headSample
      cases impossible
  | @sample _ _ name payload fresh law suffix =>
      subst event
      have output : (serviceGraph setup .concurrent).outputLayout (embedding.event zero) =
          .publicData payload := by
        change outputLayout setup.program (embedding.event zero) = .publicData payload
        simpa only [zero, outputLayout, Fin.mk_zero, Fin.cases_zero] using embedding.layout_eq zero
      have code : cast (congrArg (EventCode (graphLayout setup.program)) output)
          ((serviceGraph setup .concurrent).nodes (embedding.event zero)) =
            .sample payload (compilePublicDist refs law) := by
        change cast (congrArg (EventCode (graphLayout setup.program)) output)
          ((toEventGraph setup.program).nodes (embedding.event zero)) =
            .sample payload (compilePublicDist refs law)
        simpa only [zero, compileRankedNodes, outputLayout, Fin.mk_zero, Fin.cases_zero]
          using compiled.nodeEq zero
      have currentAgrees :
          refs.Agrees source.state current.application.current.native.config.store := by
        intro readName cell selected
        exact (refs.get selected).get?_preserved _ _
          (fun field value present => first.stored field value present) _ (agrees selected)
      let draw := L.evalDist law (sourcePublicEnv source.state)
      have evaluates : (compilePublicDist refs law).eval?
          current.application.current.native.config.store = some draw := by
        rw [PublicDist.eval?, compilePublicDist_evalLaw? refs source.state _ currentAgrees law]
        rfl
      have kernel := PhaseBindingRepair.sample_environment_law implementation.runtime
        implementation.leaks current (embedding.event zero) ready payload
          (compilePublicDist refs law) output code (nodeView_eq_sample output code) allowed
            draw evaluates
      have supported := moved
      rw [kernel] at supported
      obtain ⟨value, _sampled, nextEq⟩ := (PMF.mem_support_map_iff ..).mp supported
      cases nextEq
      let raw := PhaseBindingRepair.rawSample implementation.runtime implementation.leaks current
        (embedding.event zero) payload output ready value
      have kept := PhaseRuntimeState.normalize_keepsStore_of_noncommitment raw.application phase
        remaining installed (by rw [kind]; decide)
      have nativeRead :
          let head : Fin (eventCount (.sample name fresh law suffix)) :=
            ⟨0, by simp only [eventCount]; omega⟩
          let field : FieldRef (graphLayout setup.program) (.publicData payload) := by
            simpa only [head, outputLayout, Fin.mk_zero, Fin.cases_zero] using embedding.ref head
          field.get? (PhaseRuntimeState.normalizeExecution implementation.runtime
            implementation.leaks raw).application.current.native.config.store = some value := by
        dsimp only
        apply FieldRef.get?_preserved _ _ _
          (fun field result present => kept field result present)
        change cast (congrArg (fun kind => Option kind.Value) output)
          ((current.application.current.native.complete (embedding.event zero) ready
            (cast (congrArg EventField.Action output.symm) PUnit.unit)
            (cast (congrArg EventField.Value output.symm) value)).config.outputs
              (embedding.event zero)) = some value
        change cast (congrArg (fun kind => Option kind.Value) output)
          ((current.application.current.native.config.complete (embedding.event zero) ready
            (cast (congrArg EventField.Action output.symm) PUnit.unit)
            (cast (congrArg EventField.Value output.symm) value)).outputs
              (embedding.event zero)) = some value
        rw [Config.complete_output_same]
        have castSome {A B : Type} (same : A = B) (item : A) :
            cast (congrArg Option same) (some item) = some (cast same item) := by
          cases same
          rfl
        rw [castSome (congrArg EventField.Value output), cast_cast]
        simp only [cast_eq]
      have sourceMass := sourceReplay_sample_interval_mass setup name payload fresh law suffix
        lift origin source unique refs embedding terminalAligned current.application.entry.excluded
          current.application.generation prior last.checkpoint last.stored retained longer value
            nativeRead (by
              intro query lower upper
              have afterSample : current.application.attempt.phase + 1 =
                  instructionCount setup.program - instructionCount suffix := by
                simp only [eventCount, eventCount_eq_instructionCount] at total
                omega
              have queryLower : current.application.attempt.phase ≤ query.val := by omega
              have queryUpper : query.val <
                  (PhaseRuntimeState.normalizeExecution implementation.runtime
                    implementation.leaks raw).application.attempt.phase := by
                change query.val < instructionCount setup.program -
                  ProtocolState.remaining setup.program
                    (last.checkpoint.residual.lift (ProtocolState.entry
                      last.checkpoint.residual.tail last.checkpoint.source)) at upper
                rwa [last.checkpoint.saved_position] at upper
              exact sourceReplay_environment_crossed_rank_owned setup implementation current _
                first last live nonempty (.application (.executeSample (embedding.event zero)))
                  query (by intro equal; cases equal; omega) moved queryLower queryUpper)
      have atom := sourceReplay_sample_atom setup implementation current (embedding.event zero)
        ready payload (compilePublicDist refs law) output code allowed draw evaluates value
      rw [sourceMass, atom]

omit [Fintype Player] in
private theorem sourceReplay_same_attempt_interval_mass
    {before after : PhaseRuntimeState (serviceGraph setup .concurrent)}
    (first : RecoverySourceCheckpoint setup .concurrent before)
    (last : RecoverySourceCheckpoint setup .concurrent after)
    (same : before.attempt = after.attempt) (retained : TracePrefix first.trace last.trace) :
    last.trace.transitionMass = first.trace.transitionMass := by
  have generation := congrArg CommitAttemptId.generation same
  have phases := congrArg CommitAttemptId.phase same
  have counts := setup.commitRecovery_same_generation_length retained.reachesWithin _ _ rfl rfl
    generation
  have firstPosition := first.saved_position
  have lastPosition := last.saved_position
  have firstBound := ProtocolState.remaining_le_instructionCount setup.program
    (first.residual.lift (ProtocolState.entry first.residual.tail first.source))
  have lastBound := ProtocolState.remaining_le_instructionCount setup.program
    (last.residual.lift (ProtocolState.entry last.residual.tail last.source))
  have lengths : first.trace.length = last.trace.length := by
    change ProtocolState.remaining setup.program
        (last.residual.lift (ProtocolState.entry last.residual.tail last.source)) +
          last.trace.length =
      ProtocolState.remaining setup.program
        (first.residual.lift (ProtocolState.entry first.residual.tail first.source)) +
          first.trace.length at counts
    omega
  have histories := retained.eq_of_length lengths
  exact (congrArg (fun history : setup.commitRecoveryProtocol.History =>
    history.trace.transitionMass) histories).symm

private theorem sourceReplay_stuttering_sample_interval_mass
    (current next : (nativeApplication).Execution)
    (first : RecoverySourceWitness setup .concurrent implementation.plan current.application)
    (last : RecoverySourceWitness setup .concurrent implementation.plan next.application)
    (live : current.application.Live) (nonempty : current.application.phases ≠ [])
    (event : (serviceGraph setup .concurrent).EventId)
    (allowed : current.application.commandAllowed (.executeSample event) = true)
    (rawKernel : environmentStep implementation.runtime current.application.current.native
      (.executeSample event) = PMF.pure current.application.current.native)
    (moved : next ∈
      (current.environmentStep nativeApplication (.application (.executeSample event))).support)
    (retained : TracePrefix first.checkpoint.trace last.checkpoint.trace) :
    last.checkpoint.trace.transitionMass = first.checkpoint.trace.transitionMass *
      (current.environmentStep nativeApplication
        (.application (.executeSample event)) next).toReal := by
  have rawState : current.application.current.environmentResult (.executeSample event)
      current.application.current.native = current.application.current := by
    cases current.application.current
    rfl
  have kernel : current.environmentStep nativeApplication (.application (.executeSample event)) =
      PMF.pure { current with
        application := current.application.normalize
        environmentRecall := current.environmentRecall ++
          [⟨current.observeEnvironment nativeApplication,
            .application (.executeSample event)⟩] } := by
    change PMF.map _ (PMF.map _
      (PhaseRuntimeState.environment implementation.runtime current.application
        (.executeSample event))) = _
    simp only [PhaseRuntimeState.environment,
      allowed, ↓reduceIte, rawKernel, PMF.pure_map]
    rw [rawState]
    rfl
  have supported := moved
  rw [kernel, PMF.mem_support_pure_iff] at supported
  cases supported
  have sourceMass : last.checkpoint.trace.transitionMass =
      first.checkpoint.trace.transitionMass := by
    apply sourceReplay_sample_free_interval_mass setup _ _ first.checkpoint.trace
      last.checkpoint.trace retained
    intro query lower upper
    change instructionCount setup.program - ProtocolState.remaining setup.program
      (first.checkpoint.residual.lift
        (ProtocolState.entry first.checkpoint.residual.tail first.checkpoint.source)) ≤ query.val
      at lower
    change query.val < instructionCount setup.program - ProtocolState.remaining setup.program
      (last.checkpoint.residual.lift
        (ProtocolState.entry last.checkpoint.residual.tail last.checkpoint.source)) at upper
    rw [first.checkpoint.saved_position] at lower
    rw [last.checkpoint.saved_position] at upper
    cases acting : (serviceGraph setup .concurrent).actor? query with
    | some owner =>
        refine ⟨owner, ?_⟩
        rw [eventOwner?_eq_actor]
        exact acting
    | none =>
        have same := sourceReplay_live_ownerless_saved_output setup current.application
          first.order.frontier live first.stored nonempty query acting
        have output := sourceReplay_settle_ownerless_output setup current.application.phases
          current.application.generation current.application.entry current.application.current
          current.application.retired query acting same
        have completed := sourceReplay_frontier_completed_before setup _ last.order.frontier query
          upper
        have available := current.application.normalize.current.native.config.output_available query
        have present := available.mpr completed
        unfold PhaseRuntimeState.normalize at present
        rw [output] at present
        have oldCompleted := (current.application.current.native.config.output_available query).mp
          present
        exact (sourceReplay_live_ownerless_missing setup current.application first.order.frontier
          live query acting lower oldCompleted).elim
  rw [sourceMass, kernel, PMF.pure_apply_self, ENNReal.toReal_one, mul_one]

private theorem sourceReplay_disallowed_sample_interval_mass
    (current next : (nativeApplication).Execution)
    (first : RecoverySourceWitness setup .concurrent implementation.plan current.application)
    (last : RecoverySourceWitness setup .concurrent implementation.plan next.application)
    (event : (serviceGraph setup .concurrent).EventId)
    (disallowed : current.application.commandAllowed (.executeSample event) = false)
    (moved : next ∈
      (current.environmentStep nativeApplication (.application (.executeSample event))).support)
    (retained : TracePrefix first.checkpoint.trace last.checkpoint.trace) :
    last.checkpoint.trace.transitionMass = first.checkpoint.trace.transitionMass *
      (current.environmentStep nativeApplication
        (.application (.executeSample event)) next).toReal := by
  have kernel : current.environmentStep nativeApplication (.application (.executeSample event)) =
      PMF.pure { current with environmentRecall := current.environmentRecall ++
        [⟨current.observeEnvironment nativeApplication,
          .application (.executeSample event)⟩] } := by
    change PMF.map _ (PMF.map _
      (PhaseRuntimeState.environment implementation.runtime current.application
        (.executeSample event))) = _
    simp only [PhaseRuntimeState.environment,
      disallowed, Bool.false_eq_true, ↓reduceIte, PMF.pure_map]
  have supported := moved
  rw [kernel, PMF.mem_support_pure_iff] at supported
  cases supported
  have sourceMass := sourceReplay_same_attempt_interval_mass setup first.checkpoint
    last.checkpoint rfl retained
  rw [sourceMass, kernel, PMF.pure_apply_self, ENNReal.toReal_one, mul_one]

private theorem sourceReplay_environment_interval_mass
    (operational : implementation.Operational)
    (current next : (nativeApplication).Execution)
    (first : RecoverySourceWitness setup .concurrent implementation.plan current.application)
    (last : RecoverySourceWitness setup .concurrent implementation.plan next.application)
    (live : current.application.Live) (command : (nativeApplication).Command)
    (moved : next ∈ (current.environmentStep nativeApplication command).support)
    (retained : TracePrefix first.checkpoint.trace last.checkpoint.trace) :
    last.checkpoint.trace.transitionMass = first.checkpoint.trace.transitionMass *
      ((current.environmentStep nativeApplication command) next).toReal := by
  have nonsampleCase (nonsample : ∀ event : (serviceGraph setup .concurrent).EventId,
      command ≠ .application (.executeSample event)) :
      last.checkpoint.trace.transitionMass = first.checkpoint.trace.transitionMass *
        ((current.environmentStep nativeApplication command) next).toReal := by
    have atom := sourceReplay_nonsample_environment_atom setup implementation operational current
      next command nonsample moved
    have sourceMass : last.checkpoint.trace.transitionMass =
        first.checkpoint.trace.transitionMass := by
      by_cases empty : current.application.phases = []
      · apply sourceReplay_sample_free_interval_mass setup _ _ first.checkpoint.trace
          last.checkpoint.trace retained
        intro event lower _upper
        change instructionCount setup.program - ProtocolState.remaining setup.program
          (first.checkpoint.residual.lift
            (ProtocolState.entry first.checkpoint.residual.tail first.checkpoint.source)) ≤
              event.val
          at lower
        rw [first.checkpoint.saved_position] at lower
        simp only [PhaseRuntimeState.attempt, empty, List.head?_nil, Option.map_none,
          Option.getD_none] at lower
        have bounded := event.isLt
        change event.val < eventCount setup.program at bounded
        have counts := eventCount_eq_instructionCount setup.program
        change eventCount setup.program ≤ event.val at lower
        exact (by omega : False).elim
      · exact sourceReplay_nonsample_interval_mass setup implementation current next first last live
          empty command nonsample moved retained
    rw [sourceMass, atom, ENNReal.toReal_one, mul_one]
  cases command with
  | activate owner => exact nonsampleCase (by intro event impossible; cases impossible)
  | wait => exact nonsampleCase (by intro event impossible; cases impossible)
  | «include» id => exact nonsampleCase (by intro event impossible; cases impossible)
  | application operation =>
      cases operation with
      | advanceClock => exact nonsampleCase (by intro event impossible; cases impossible)
      | expire address => exact nonsampleCase (by intro event impossible; cases impossible)
      | executeSample event =>
          by_cases allowed : current.application.commandAllowed (.executeSample event) = true
          · have nonempty : current.application.phases ≠ [] := by
              intro empty
              simp only [PhaseRuntimeState.commandAllowed, empty, List.head?_nil, Option.any_none,
                Bool.false_eq_true] at allowed
            by_cases ready : current.application.current.native.config.cut.Ready event
            · cases viewed : nodeView (serviceGraph setup .concurrent) event with
              | bind owner payload output code =>
                  have kernel := environmentStep_executeSample_of_nonsample implementation.runtime
                    current.application.current.native event ready (by
                      intro ty law shape code impossible
                      rw [viewed] at impossible
                      cases impossible)
                  exact sourceReplay_stuttering_sample_interval_mass setup implementation current
                    next first last live nonempty event allowed kernel moved retained
              | resolve owner payload binding checks output code =>
                  have kernel := environmentStep_executeSample_of_nonsample implementation.runtime
                    current.application.current.native event ready (by
                      intro ty law shape code impossible
                      rw [viewed] at impossible
                      cases impossible)
                  exact sourceReplay_stuttering_sample_interval_mass setup implementation current
                    next first last live nonempty event allowed kernel moved retained
              | sample payload law output code =>
                  obtain ⟨phase, remaining, installed⟩ : ∃ phase remaining,
                      current.application.phases = phase :: remaining := by
                    cases installed : current.application.phases with
                    | nil => exact (nonempty installed).elim
                    | cons phase remaining => exact ⟨phase, remaining, rfl⟩
                  have inside : event ∈ phase.events := by
                    simpa only [PhaseRuntimeState.commandAllowed, installed, List.head?_cons,
                      Option.any_some, decide_eq_true_eq] using allowed
                  have bounds := (phase.mem_events event).mp inside
                  have typed := phase.fields event bounds.1 bounds.2
                  have kind : phase.kind = .sample := by
                    cases kind : phase.kind with
                    | sample => rfl
                    | commitment =>
                        rw [kind] at typed
                        obtain ⟨owner, ty, impossible⟩ := typed
                        cases impossible.symm.trans output
                    | reveal =>
                        rw [kind] at typed
                        obtain ⟨ty, impossible⟩ := typed
                        cases impossible.symm.trans output
                  exact sourceReplay_sample_command_interval_mass setup implementation current next
                    first last live phase remaining installed kind event ready allowed moved
                      retained
            · have kernel := environmentStep_executeSample_of_not_ready implementation.runtime
                current.application.current.native event ready
              exact sourceReplay_stuttering_sample_interval_mass setup implementation current next
                first last live nonempty event allowed kernel moved retained
          · exact sourceReplay_disallowed_sample_interval_mass setup implementation current next
              first last event (Bool.eq_false_iff.mpr allowed) moved retained

private theorem sourceReplay_native_step_some
    {before after : (nativeProtocol).State}
    (joint : Player → Option (nativeApplication).Action)
    (legal : (nativeProtocol).Legal before joint)
    (moved : after ∈ ((nativeProtocol).step before ⟨joint, legal⟩).support) :
    ∃ current, after = some current := by
  cases before with
  | none =>
      obtain ⟨physical, _supported, same⟩ := (PMF.mem_support_map_iff ..).mp moved
      exact ⟨_, same.symm⟩
  | some current =>
      rcases current with ⟨remaining, actor, execution⟩
      cases actor with
      | some owner =>
          change after ∈ (PMF.pure (some
            { remaining := remaining, actor := none,
              execution := execution.respond nativeApplication owner ((joint owner).getD ⟨none⟩) })
              : PMF (nativeProtocol).State).support at moved
          cases (PMF.mem_support_pure_iff _ _).mp moved
          exact ⟨_, rfl⟩
      | none =>
          cases remaining with
          | zero =>
              change after ∈ (PMF.pure (some ⟨0, none, execution⟩) :
                PMF (nativeProtocol).State).support at moved
              cases (PMF.mem_support_pure_iff _ _).mp moved
              exact ⟨_, rfl⟩
          | succ remaining =>
              change after ∈ ((implementation.scheduler execution.environmentRecall
                (execution.observeEnvironment nativeApplication)).bind fun command =>
                  (execution.environmentStep nativeApplication command).map fun next =>
                    some (⟨remaining, command.actor? nativeApplication, next⟩ :
                      (nativeApplication).Control)).support at moved
              obtain ⟨command, _chosen, supported⟩ :=
                Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
              obtain ⟨next, _advanced, same⟩ := (PMF.mem_support_map_iff ..).mp supported
              exact ⟨_, same.symm⟩

private theorem sourceReplay_native_none_trace
    (trace : (nativeProtocol).Trace none) : trace = .start := by
  have unique : ∀ {state : (nativeProtocol).State} (history : (nativeProtocol).Trace state),
      state = none → HEq history (Trace.start : (nativeProtocol).Trace (nativeProtocol).init) := by
    intro state history stateEq
    cases history with
    | start => rfl
    | extend prior joint legal moved =>
        obtain ⟨current, present⟩ := sourceReplay_native_step_some setup implementation
          joint legal moved
        rw [stateEq] at present
        cases present
  exact eq_of_heq (unique trace rfl)

private theorem sourceReplay_native_live
    (current : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some current)) : current.execution.application.Live := by
  have raw := (nativeMenu).toRawTrace nativeInitial implementation.horizon
    implementation.scheduler trace
  have living := (phaseApplication_live implementation.runtime implementation.leaks).history
    nativeInitial implementation.horizon implementation.scheduler
      (fun (state : PhaseRuntimeState (serviceGraph setup .concurrent)) supported => by
      change state ∈ (setup.initialLaw.map fun draw =>
        PhaseRuntimeState.initial implementation.plan (encodeInputs draw)).support at supported
      obtain ⟨inputs, _supported, rfl⟩ := (PMF.mem_support_map_iff ..).mp supported
      exact ⟨PhaseRuntimeState.initial_frontier implementation.plan _,
        PhaseRuntimeState.initial_live implementation.plan _⟩) raw
  exact living.2

/-- The actual selected source chronology retains the whole correlated
initializer and every original public Nature atom. -/
theorem sourceReplay_nature_mass_eq_canonical
    (operational : implementation.Operational)
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control)) :
    sourceReplayNatureMass setup implementation trace =
      (canonicalSource setup implementation operational ⟨_, trace⟩).trace.transitionMass := by
  have semantic : ∀ {state : (nativeProtocol).State} (trace : (nativeProtocol).Trace state),
      match state, checkpointSelection setup implementation operational trace with
      | none, _ => sourceReplayNatureMass setup implementation trace = 1
      | some _, selected => sourceReplayNatureMass setup implementation trace =
          selected.val.checkpoint.trace.transitionMass := by
    intro state trace
    induction trace with
    | start => rfl
    | @extend before after prior joint legal moved ih =>
        obtain ⟨ending, rfl⟩ := sourceReplay_native_step_some setup implementation joint legal moved
        cases before with
        | none =>
            cases sourceReplay_native_none_trace setup implementation prior
            have sourceStart := sourceReplay_initial_nature_mass setup implementation operational
              ending joint legal moved
            simpa only [canonicalSource, sourceReplay_lift_mass] using sourceStart
        | some current =>
            let first := (checkpointSelection setup implementation operational prior).val
            let last := (checkpointSelection setup implementation operational
              (prior.extend joint legal moved)).val
            have retained := checkpointSelection_prefix setup implementation operational current
              ending prior (prior.extend joint legal moved) (.extend .refl joint legal moved)
            change sourceReplayNatureMass setup implementation prior =
              first.checkpoint.trace.transitionMass at ih
            change sourceReplayNatureMass setup implementation prior *
              (sourceReplayNatureStepAtom setup implementation (some current)
                (some ending)).toReal =
                last.checkpoint.trace.transitionMass
            rw [ih]
            rcases current with ⟨remaining, actor, execution⟩
            cases actor with
            | some owner =>
                change some ending ∈ (PMF.pure (some
                  { remaining := remaining, actor := none,
                    execution := execution.respond nativeApplication owner
                      ((joint owner).getD ⟨none⟩) }) : PMF (nativeProtocol).State).support at moved
                cases (PMF.mem_support_pure_iff _ _).mp moved
                have same : execution.application.attempt =
                    (execution.respond nativeApplication owner
                      ((joint owner).getD ⟨none⟩)).application.attempt := by
                  cases (joint owner).getD ⟨none⟩ with
                  | mk transmission => cases transmission <;> rfl
                have mass := sourceReplay_same_attempt_interval_mass setup first.checkpoint
                  last.checkpoint same retained
                simpa only [sourceReplayNatureStepAtom, ENNReal.toReal_one, mul_one] using mass.symm
            | none =>
                cases remaining with
                | zero =>
                    change some ending ∈ (PMF.pure (some ⟨0, none, execution⟩) :
                      PMF (nativeProtocol).State).support at moved
                    cases (PMF.mem_support_pure_iff _ _).mp moved
                    have mass := sourceReplay_same_attempt_interval_mass setup first.checkpoint
                      last.checkpoint rfl retained
                    simpa only [sourceReplayNatureStepAtom, ↓reduceIte, ENNReal.toReal_one,
                      mul_one] using mass.symm
                | succ remaining =>
                    change some ending ∈ ((implementation.scheduler execution.environmentRecall
                      (execution.observeEnvironment nativeApplication)).bind fun command =>
                        (execution.environmentStep nativeApplication command).map fun next =>
                          some (⟨remaining, command.actor? nativeApplication, next⟩ :
                            (nativeApplication).Control)).support at moved
                    obtain ⟨command, _chosen, supported⟩ :=
                      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
                    obtain ⟨next, advanced, same⟩ := (PMF.mem_support_map_iff ..).mp supported
                    cases Option.some.inj same
                    have living := sourceReplay_native_live setup implementation _ prior
                    have mass := sourceReplay_environment_interval_mass setup implementation
                      operational execution next first last living command advanced retained
                    have recorded := (nativeApplication).environmentStep_environmentRecall
                      execution next command advanced
                    have latest : next.environmentRecall.getLast? =
                        some ⟨execution.observeEnvironment nativeApplication, command⟩ := by
                      rw [recorded, List.getLast?_concat]
                    simpa only [sourceReplayNatureStepAtom, Nat.succ_ne_zero, ↓reduceIte, latest]
                      using mass.symm
  change sourceReplayNatureMass setup implementation trace =
    (setup.proposalRecoveryLiftTrace _
      (checkpointSelection setup implementation operational trace).val.checkpoint.trace
      ).transitionMass
  rw [sourceReplay_lift_mass]
  exact semantic trace

def sourceReplayResponseProducts (rates : PhaseProposalRates) (who : Player) :
    ∀ {state : (nativeProtocol).State}, (nativeProtocol).Trace state → ℝ × ℝ × ℝ
  | _, .start => (1, 1, 1)
  | _, @Trace.extend _ _ before _ prior joint _ _ =>
      let previous := sourceReplayResponseProducts rates who prior
      let extra : ℝ × ℝ := match before with
        | none => (1, 1)
        | some control => match control.actor with
          | none => (1, 1)
          | some owner => if owner = who then (1, 1) else match joint owner with
            | none => (0, 0)
            | some action =>
              ((sourceReplayBindingDrawAtom setup values implementation owner
                (control.execution.recall owner)
                (control.execution.observe nativeApplication owner) action).toReal,
                (sourceReplayAliasAtom setup implementation rates.aliases owner
                  control.execution (none, some action)).toReal)
      (previous.1 * (sourceReplayPacketStepAtom setup implementation rates who before joint).toReal,
        previous.2.1 * extra.1, previous.2.2 * extra.2)

private theorem sourceReplayResponseProducts_mechanical_extend
    (rates : PhaseProposalRates) (who : Player)
    {before after : (nativeProtocol).State} (prior : (nativeProtocol).Trace before)
    (joint : Player → Option (nativeApplication).Action)
    (legal : (nativeProtocol).Legal before joint)
    (moved : after ∈ ((nativeProtocol).step before ⟨joint, legal⟩).support) :
    (sourceReplayResponseProducts setup values implementation rates who
      (prior.extend joint legal moved)).1 =
        (sourceReplayResponseProducts setup values implementation rates who prior).1 *
          (sourceReplayPacketStepAtom setup implementation rates who before joint).toReal := rfl

/-- The literal finite packet product is strictly positive on every actual
counted trace. Subsequent atom cancellation therefore uses no zero convention. -/
private theorem sourceReplay_mechanical_product_positive
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (rates : PhaseProposalRates) (waitPositive : 0 < rates.waiting.val)
    (waitBelow : rates.waiting.val < 1) (slotPositive : 0 < rates.slots.val)
    (badPositive : 0 < rates.badPreparation.val) (badBelow : rates.badPreparation.val < 1)
    (who : Player) {state : (nativeProtocol).State}
    (trace : (nativeProtocol).Trace state) :
    0 < (sourceReplayResponseProducts setup values implementation rates who trace).1 := by
  induction trace with
  | start => exact zero_lt_one
  | @extend before after prior joint legal moved ih =>
      rw [sourceReplayResponseProducts_mechanical_extend]
      apply mul_pos ih
      cases before with
      | none => exact zero_lt_one
      | some control =>
          rcases control with ⟨remaining, actor, execution⟩
          cases actor with
          | none => exact zero_lt_one
          | some owner =>
              by_cases same : owner = who
              · simp only [sourceReplayPacketStepAtom, same, ↓reduceIte, ENNReal.toReal_one,
                  zero_lt_one]
              · obtain ⟨response, selected, available⟩ :
                    ∃ response : (nativeApplication).Action, joint owner = some response ∧
                      response ∈ PhaseCount.onePacketActions implementation.runtime
                        implementation.leaks implementation.bounds owner (execution.recall owner)
                          (execution.observe nativeApplication owner) := by
                  have offered := legal.2 owner
                  cases chosen : joint owner with
                  | none => rw [chosen] at offered; exact (offered rfl).elim
                  | some response => exact ⟨response, rfl, (chosen ▸ offered).2⟩
                simpa only [sourceReplayPacketStepAtom, same, ↓reduceIte, selected] using
                  sourceReplay_foreign_packet_positive setup values implementation operational
                    fullValues rates waitPositive waitBelow slotPositive badPositive badBelow
                      remaining owner execution prior response available

/-- The actual foreign response product separates every proper queried draw
and every raw alias from the physical packet product. Historical focal BAD
remains in the focal policy and imposes no extra goodness condition. -/
private theorem sourceReplay_foreign_response_products
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (rates : PhaseProposalRates) (waitPositive : 0 < rates.waiting.val)
    (waitBelow : rates.waiting.val < 1) (slotPositive : 0 < rates.slots.val)
    (badPositive : 0 < rates.badPreparation.val) (badBelow : rates.badPreparation.val < 1)
    (who : Player) {state : (nativeProtocol).State}
    (trace : (nativeProtocol).Trace state)
    (foreign : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler owner
          ⟨state, trace⟩) :
    (∏ owner ∈ Finset.univ.erase who,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).ownPlayReachProbability
          (phaseProposalReferenceStrategy setup .concurrent implementation.runtime
            implementation.leaks implementation.bounds implementation.plan nativeInitial
              implementation.horizon implementation.scheduler values rates owner)
          (((nativeMenu).information nativeInitial implementation.horizon
            implementation.scheduler).ownPlay owner trace)) =
      (sourceReplayResponseProducts setup values implementation rates who trace).1 *
        (sourceReplayResponseProducts setup values implementation rates who trace).2.1 *
        (sourceReplayResponseProducts setup values implementation rates who trace).2.2 := by
  classical
  let model := (nativeMenu).information nativeInitial implementation.horizon
    implementation.scheduler
  let profile := phaseProposalReferenceStrategy setup .concurrent implementation.runtime
    implementation.leaks implementation.bounds implementation.plan nativeInitial
      implementation.horizon implementation.scheduler values rates
  let own := fun {state} (history : (nativeProtocol).Trace state) owner =>
    model.ownPlayReachProbability (profile owner) (model.ownPlay owner history)
  change (∏ owner ∈ Finset.univ.erase who, own trace owner) = _
  revert foreign
  induction trace with
  | start =>
      intro _foreign
      change (∏ _owner ∈ Finset.univ.erase who, (1 : ℝ)) = 1 * 1 * 1
      simp only [Finset.prod_const_one, mul_one]
  | @extend before after prior joint legal moved ih =>
      intro foreign
      have earlierGood : ∀ owner, owner ≠ who →
          ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
            implementation.leaks implementation.bounds nativeInitial implementation.horizon
              implementation.scheduler owner ⟨before, prior⟩ := by
        intro owner different unusable
        obtain ⟨record, member, bad⟩ := unusable
        have retained : TracePrefix prior (prior.extend joint legal moved) :=
          .extend .refl joint legal moved
        exact foreign owner different ⟨record,
          (model.ownPlay_isSuffix_of_reachesWithin owner retained.reachesWithin).subset member,
          bad⟩
      have previous := ih earlierGood
      let weight := fun owner => match joint owner with
        | none => (1 : ℝ)
        | some action => (((profile owner (model.infoOf owner prior)).map Subtype.val)
            (some action)).toReal
      have update (owner : Player) : own (prior.extend joint legal moved) owner =
          own prior owner * weight owner := by
        dsimp only [own]
        rw [InfoSignals.ownPlay_extend]
        cases selected : joint owner with
        | none => simp only [selected, weight, mul_one]
        | some action =>
            simp only [selected, weight, InformationModel.ownPlayReachProbability]
            ring
      have product : (∏ owner ∈ Finset.univ.erase who,
          own (prior.extend joint legal moved) owner) =
            (∏ owner ∈ Finset.univ.erase who, own prior owner) *
              ∏ owner ∈ Finset.univ.erase who, weight owner := by
        calc
          _ = ∏ owner ∈ Finset.univ.erase who, own prior owner * weight owner :=
            Finset.prod_congr rfl fun owner _member => update owner
          _ = _ := Finset.prod_mul_distrib
      rw [product, previous]
      cases before with
      | none =>
          have silent (owner : Player) : joint owner = none := by
            cases selected : joint owner with
            | none => rfl
            | some action =>
                have active := (selected ▸ legal.2 owner).1
                change none = some owner at active
                cases active
          simp only [weight, silent, Finset.prod_const_one, sourceReplayResponseProducts,
            sourceReplayPacketStepAtom, ENNReal.toReal_one, mul_one]
      | some control =>
          rcases control with ⟨remaining, actor, execution⟩
          cases actor with
          | none =>
              have silent (owner : Player) : joint owner = none := by
                cases selected : joint owner with
                | none => rfl
                | some action =>
                    have active := (selected ▸ legal.2 owner).1
                    change none = some owner at active
                    cases active
              simp only [weight, silent, Finset.prod_const_one, sourceReplayResponseProducts,
                sourceReplayPacketStepAtom, ENNReal.toReal_one, mul_one]
          | some owner =>
              have silent (other : Player) (different : other ≠ owner) : joint other = none := by
                cases selected : joint other with
                | none => rfl
                | some action =>
                    have active := (selected ▸ legal.2 other).1
                    change some owner = some other at active
                    exact (different (Option.some.inj active).symm).elim
              by_cases focal : owner = who
              · subst owner
                have weights : (∏ owner ∈ Finset.univ.erase who, weight owner) = 1 := by
                  apply Finset.prod_eq_one
                  intro owner member
                  simp only [weight, silent owner (Finset.mem_erase.mp member).1]
                rw [weights]
                simp only [sourceReplayResponseProducts, sourceReplayPacketStepAtom,
                  ↓reduceIte, ENNReal.toReal_one, mul_one]
              · obtain ⟨action, selected, offered⟩ :
                    ∃ action : (nativeApplication).Action, joint owner = some action ∧
                      action ∈ PhaseCount.onePacketActions implementation.runtime
                        implementation.leaks implementation.bounds owner (execution.recall owner)
                          (execution.observe nativeApplication owner) := by
                  cases selected : joint owner with
                  | none =>
                      have inactive := selected ▸ legal.2 owner
                      exact (inactive rfl).elim
                  | some action => exact ⟨action, rfl, (selected ▸ legal.2 owner).2⟩
                let response : PhaseProposal.Response implementation.runtime implementation.leaks
                    implementation.bounds owner (execution.recall owner)
                      (execution.observe nativeApplication owner) := ⟨action, offered⟩
                have clean : ¬ PhaseProposal.GeneratedUnusableBindingAction
                    implementation.runtime implementation.leaks owner action := by
                  intro unusable
                  apply foreign owner focal
                  refine ⟨(model.infoOf owner prior, action), ?_, unusable⟩
                  rw [InfoSignals.ownPlay_extend, selected]
                  exact List.mem_cons_self
                have atom := sourceReplay_clean_callback_draw_atom setup values implementation
                  operational fullValues rates waitPositive waitBelow slotPositive badPositive
                    badBelow remaining owner execution prior response clean none
                have aliasAtom : sourceReplayAliasAtom setup implementation rates.aliases owner
                    execution (none, some action) =
                    sourceReplayAliases setup implementation rates.aliases owner execution none
                      (PhaseProposal.projectResponse implementation.runtime implementation.leaks
                        implementation.bounds owner (execution.recall owner)
                          (execution.observe nativeApplication owner) response)
                        (none, some action) := by
                  simp only [sourceReplayAliasAtom, dite_eq_left offered]
                  rfl
                have row : phaseProposalReferencePolicy setup .concurrent implementation.runtime
                    implementation.leaks implementation.bounds implementation.plan values rates
                      owner (execution.recall owner) (execution.observe nativeApplication owner)
                        action =
                    foreignMechanicalAtom setup implementation rates execution owner action *
                      sourceReplayBindingDrawAtom setup values implementation owner
                        (execution.recall owner)
                        (execution.observe nativeApplication owner) action *
                      sourceReplayAliasAtom setup implementation rates.aliases owner execution
                        (none, some action) := by
                  rw [aliasAtom]
                  exact atom.2
                have rowReal := congrArg ENNReal.toReal row
                simp only [ENNReal.toReal_mul] at rowReal
                have information : model.infoOf owner prior =
                    some (execution.recall owner, execution.observe nativeApplication owner) := by
                  change ((nativeMenu).signals nativeInitial implementation.horizon
                    implementation.scheduler).infoOf owner prior = _
                  rw [(nativeMenu).info nativeInitial implementation.horizon
                    implementation.scheduler owner prior]
                  simp only [ReactiveApplication.observe, ↓reduceIte]
                have weightEq : weight owner =
                    (phaseProposalReferencePolicy setup .concurrent implementation.runtime
                      implementation.leaks implementation.bounds implementation.plan values rates
                        owner (execution.recall owner)
                          (execution.observe nativeApplication owner) action).toReal := by
                  dsimp only [weight]
                  simp only [selected]
                  rw [information, phaseProposalReferenceStrategy_map_val]
                  exact congrArg ENNReal.toReal
                    (pmf_map_apply_of_injective _ (Option.some_injective _) action)
                have weights : (∏ other ∈ Finset.univ.erase who, weight other) = weight owner := by
                  apply Finset.prod_eq_single owner
                  · intro other _member different
                    simp only [weight, silent other different]
                  · intro absent
                    exact (absent (Finset.mem_erase.mpr ⟨focal, Finset.mem_univ owner⟩)).elim
                rw [weights, weightEq, rowReal]
                simp only [sourceReplayResponseProducts, sourceReplayPacketStepAtom,
                  focal, ↓reduceIte, selected]
                ring

/-- On the actual trace, the fixed-tape transition factors and the foreign
packet factors are exactly public Nature times the existing mechanical path.
The whole initializer is retained once, before the first source row. -/
private theorem sourceReplay_mechanical_path_factor
    (rates : PhaseProposalRates) (who : Player)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    {state : (nativeProtocol).State} (trace : (nativeProtocol).Trace state) :
    sourceReplayFixedTransitionMass setup implementation tape trace *
        (sourceReplayResponseProducts setup values implementation rates who trace).1 =
      sourceReplayNatureMass setup implementation trace *
        (mechanicalPathAtom setup implementation rates who tape trace).toReal := by
  induction trace with
  | start =>
    simp only [sourceReplayFixedTransitionMass, sourceReplayResponseProducts,
      sourceReplayNatureMass, mechanicalPathAtom, ENNReal.toReal_one, mul_one]
  | @extend before after prior joint legal moved ih =>
    have row := congrArg ENNReal.toReal
      (sourceReplay_mechanical_step_factor setup implementation rates who tape joint legal moved)
    simp only [ENNReal.toReal_mul] at row
    rw [sourceReplayFixedTransitionMass, sourceReplayResponseProducts_mechanical_extend,
      sourceReplayNatureMass,
      mechanicalPathAtom, ENNReal.toReal_mul]
    calc
      _ = (sourceReplayFixedTransitionMass setup implementation tape prior *
          (sourceReplayResponseProducts setup values implementation rates who prior).1) *
            (((nativeApplication).transition nativeInitial implementation.horizon
              (ReservedEpoch.family implementation.runtime implementation.leaks
                (ReservedEpoch.packetCapacity implementation.runtime) tape) before joint after
                  ).toReal *
              (sourceReplayPacketStepAtom setup implementation rates who before joint).toReal) :=
                by ring
      _ = _ := by rw [ih, row]; ring

/-- The actual native atom separates scheduler/packet mechanics from public
Nature. The packet product is retained literally for the subsequent proper-draw
and alias partition; no division or zero-case convention is introduced. -/
private theorem sourceReplay_prescribed_mechanical_atom
    (operational : implementation.Operational)
    (rates : PhaseProposalRates) (who : Player)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control)) :
    (((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).historyReachWeight
      (phaseProposalReferenceStrategy setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan nativeInitial implementation.horizon
          implementation.scheduler values rates) ⟨some control, trace⟩).toReal *
        (prefixTapeLaw setup implementation ⟨some control, trace⟩ tape).toReal *
          (sourceReplayResponseProducts setup values implementation rates who trace).1 =
      (implementation.prior tape).toReal *
        (canonicalSource setup implementation operational
          ⟨some control, trace⟩).trace.transitionMass *
          (mechanicalPathAtom setup implementation rates who tape trace).toReal *
            ∏ owner, (((nativeApplication).privateTranscriptFrom []
              (control.execution.recall owner)).map (fun record =>
                phaseProposalReferencePolicy setup .concurrent implementation.runtime
                  implementation.leaks implementation.bounds implementation.plan values rates owner
                    record.1.1 record.1.2 record.2)).prod.toReal := by
  have native := sourceReplay_prescribed_native_atom setup values implementation rates tape
    control trace
  rw [native]
  calc
    _ = (implementation.prior tape).toReal *
        (sourceReplayFixedTransitionMass setup implementation tape trace *
          (sourceReplayResponseProducts setup values implementation rates who trace).1) *
            ∏ owner, (((nativeApplication).privateTranscriptFrom []
              (control.execution.recall owner)).map (fun record =>
                phaseProposalReferencePolicy setup .concurrent implementation.runtime
                  implementation.leaks implementation.bounds implementation.plan values rates owner
                    record.1.1 record.1.2 record.2)).prod.toReal := by ring
    _ = _ := by
      rw [sourceReplay_mechanical_path_factor setup values implementation rates who tape trace]
      rw [sourceReplay_nature_mass_eq_canonical setup implementation operational control trace]
      ring

/-- The original native and tape atom retains the whole initializer once,
the selected source Nature mass, and every actual queried draw and alias.
Only the original focal owner's raw policy remains unsplit. -/
theorem sourceReplay_prescribed_response_atom
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (rates : PhaseProposalRates) (waitPositive : 0 < rates.waiting.val)
    (waitBelow : rates.waiting.val < 1) (slotPositive : 0 < rates.slots.val)
    (badPositive : 0 < rates.badPreparation.val) (badBelow : rates.badPreparation.val < 1)
    (who : Player) (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (foreign : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler owner
          ⟨some control, trace⟩) :
    (((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).historyReachWeight
      (phaseProposalReferenceStrategy setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan nativeInitial implementation.horizon
          implementation.scheduler values rates) ⟨some control, trace⟩).toReal *
        (prefixTapeLaw setup implementation ⟨some control, trace⟩ tape).toReal =
      (implementation.prior tape).toReal *
        (canonicalSource setup implementation operational
          ⟨some control, trace⟩).trace.transitionMass *
          (mechanicalPathAtom setup implementation rates who tape trace).toReal *
            ((nativeMenu).information nativeInitial implementation.horizon
              implementation.scheduler).ownPlayReachProbability
                (phaseProposalReferenceStrategy setup .concurrent implementation.runtime
                  implementation.leaks implementation.bounds implementation.plan nativeInitial
                    implementation.horizon implementation.scheduler values rates who)
                (((nativeMenu).information nativeInitial implementation.horizon
                  implementation.scheduler).ownPlay who trace) *
            (sourceReplayResponseProducts setup values implementation rates who trace).2.1 *
            (sourceReplayResponseProducts setup values implementation rates who trace).2.2 := by
  classical
  let responseProduct := fun owner =>
    (((nativeApplication).privateTranscriptFrom [] (control.execution.recall owner)).map
      (fun record => phaseProposalReferencePolicy setup .concurrent implementation.runtime
        implementation.leaks implementation.bounds implementation.plan values rates owner
          record.1.1 record.1.2 record.2)).prod.toReal
  have splitProduct : (∏ owner, responseProduct owner) =
      responseProduct who * ∏ owner ∈ Finset.univ.erase who, responseProduct owner :=
    (Finset.mul_prod_erase Finset.univ responseProduct (Finset.mem_univ who)).symm
  have foreignProduct : (∏ owner ∈ Finset.univ.erase who, responseProduct owner) =
      (sourceReplayResponseProducts setup values implementation rates who trace).1 *
        (sourceReplayResponseProducts setup values implementation rates who trace).2.1 *
        (sourceReplayResponseProducts setup values implementation rates who trace).2.2 := by
    simpa only [sourceReplay_prescribed_own_atom setup values implementation rates] using
      sourceReplay_foreign_response_products setup values implementation operational fullValues
        rates waitPositive waitBelow slotPositive badPositive badBelow who trace foreign
  have focal := sourceReplay_prescribed_own_atom setup values implementation rates who control trace
  change _ = responseProduct who at focal
  rw [sourceReplay_prescribed_native_atom setup values implementation rates tape control trace]
  change (implementation.prior tape).toReal *
    sourceReplayFixedTransitionMass setup implementation tape trace *
      (∏ owner, responseProduct owner) = _
  rw [splitProduct, foreignProduct, ← focal]
  calc
    _ = (implementation.prior tape).toReal *
        (sourceReplayFixedTransitionMass setup implementation tape trace *
          (sourceReplayResponseProducts setup values implementation rates who trace).1) *
        ((nativeMenu).information nativeInitial implementation.horizon
          implementation.scheduler).ownPlayReachProbability
            (phaseProposalReferenceStrategy setup .concurrent implementation.runtime
              implementation.leaks implementation.bounds implementation.plan nativeInitial
                implementation.horizon implementation.scheduler values rates who)
            (((nativeMenu).information nativeInitial implementation.horizon
              implementation.scheduler).ownPlay who trace) *
        (sourceReplayResponseProducts setup values implementation rates who trace).2.1 *
        (sourceReplayResponseProducts setup values implementation rates who trace).2.2 := by ring
    _ = _ := by
      rw [sourceReplay_mechanical_path_factor setup values implementation rates who tape trace,
        sourceReplay_nature_mass_eq_canonical setup implementation operational control trace]
      ring

local notation "nativeModel" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu implementation.runtime implementation.leaks implementation.bounds)
  implementation.initial implementation.horizon implementation.scheduler

open Classical in
/-- A positive qualified native anchor has a nonzero literal mechanical
coefficient. Both the original tape atom and every mechanical path factor
are recovered from the actual native atom, without a quotient. -/
private theorem sourceReplay_mechanicalCoefficient_ne_zero
    (operational : implementation.Operational)
    (scale nativeBad : Set.Icc (0 : ℝ) 1)
    (scalePositive : 0 < scale.val) (scaleBelow : scale.val < 1)
    (nativeBadPositive : 0 < nativeBad.val) (nativeBadBelow : nativeBad.val < 1)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (nativeProfile : ∀ owner, (nativeModel).BehavioralPolicy owner)
    (nativePrescribed : nativeProfile = phaseProposalReferenceStrategy setup .concurrent
      implementation.runtime implementation.leaks implementation.bounds implementation.plan
      nativeInitial implementation.horizon implementation.scheduler values
      ⟨nativeBad, scale, scale, scale⟩)
    (who : Player) (site : (nativeModel).InformationSite who)
    (event : (serviceGraph setup .concurrent).EventId)
    (index : MechanicalIndex setup implementation who)
    (history : (nativeModel).InformationHistory who site.1)
    (sameWord : mechanicalWord setup implementation who history.val.trace = index.1.val)
    (reached : (nativeModel).historyReachWeight nativeProfile history.val ≠ 0)
    (tapeSupported : prefixTapeLaw setup implementation history.val index.2 ≠ 0)
    (foreign : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler owner
          history.val)
    (alive : history.val.state.elim True (fun control =>
      who ∉ control.execution.application.current.excluded))
    (admitted : bindingAdmissionBit setup implementation who event history.val index.2 = true) :
    mechanicalCoefficient setup implementation ⟨nativeBad, scale, scale, scale⟩ nativeProfile
      who site event index ≠ 0 := by
  have anchor := mechanicalCoefficient_eq_of_anchor setup values implementation operational
    scale nativeBad scalePositive scaleBelow nativeBadPositive nativeBadBelow fullValues
      nativeProfile nativePrescribed who site event index history sameWord reached tapeSupported
        foreign alive admitted
  rw [anchor]
  have reachedReal := ENNReal.toReal_pos reached
    ((nativeModel).historyReachWeight_ne_top nativeProfile history.val)
  have ownPositive : 0 < (nativeModel).ownPlayReachProbability (nativeProfile who)
      ((nativeModel).ownPlay who history.val.trace) := by
    rw [(nativeModel).historyReachProbability_eq_player_mul_counterfactual nativeProfile who
      history.val.trace, (nativeModel).playerReachProbability_eq_ownPlayReachProbability]
      at reachedReal
    exact pos_of_mul_pos_left reachedReal
      ((nativeModel).counterfactualReachProbability_nonneg nativeProfile who history.val.trace)
  have ownNonzero := (ENNReal.ofReal_pos.mpr ownPositive).ne'
  rcases history with ⟨⟨state, trace⟩, _information⟩
  cases state with
  | none => simp only [bindingAdmissionBit, Bool.false_eq_true] at admitted
  | some control =>
      have tapeReal := ENNReal.toReal_pos tapeSupported (PMF.apply_ne_top _ _)
      have packet := sourceReplay_mechanical_product_positive setup values implementation
        operational fullValues ⟨nativeBad, scale, scale, scale⟩ scalePositive scaleBelow
          scalePositive nativeBadPositive nativeBadBelow who trace
      have atom := sourceReplay_prescribed_mechanical_atom setup values implementation
        operational ⟨nativeBad, scale, scale, scale⟩ who index.2 control trace
      rw [← nativePrescribed] at atom
      have nonzero : (implementation.prior index.2).toReal *
          (canonicalSource setup implementation operational
            ⟨some control, trace⟩).trace.transitionMass *
          (mechanicalPathAtom setup implementation ⟨nativeBad, scale, scale, scale⟩ who
            index.2 trace).toReal *
          ∏ owner, (((nativeApplication).privateTranscriptFrom []
            (control.execution.recall owner)).map (fun record =>
              phaseProposalReferencePolicy setup .concurrent implementation.runtime
                implementation.leaks implementation.bounds implementation.plan values
                ⟨nativeBad, scale, scale, scale⟩ owner record.1.1 record.1.2 record.2)).prod.toReal
            ≠ 0 := by
        rw [← atom]
        exact (mul_pos (mul_pos reachedReal tapeReal) packet).ne'
      have first := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp nonzero).1)
      have priorReal := (mul_ne_zero_iff.mp first.1).1
      have pathReal := first.2
      have priorNonzero : implementation.prior index.2 ≠ 0 := by
        intro zero
        exact priorReal (by rw [zero, ENNReal.toReal_zero])
      have pathNonzero : mechanicalPathAtom setup implementation
          ⟨nativeBad, scale, scale, scale⟩ who index.2 trace ≠ 0 := by
        intro zero
        exact pathReal (by rw [zero, ENNReal.toReal_zero])
      exact mul_ne_zero (mul_ne_zero priorNonzero ownNonzero) pathNonzero

open Classical in
/-- A zero mechanical coefficient has no positive original annotated atom.
This includes every posterior entry and complete issued word, before any
source or mechanical factor is canceled. -/
theorem annotated_forced_block_zero_of_coefficient_zero
    (operational : implementation.Operational)
    (scale nativeBad : Set.Icc (0 : ℝ) 1)
    (scalePositive : 0 < scale.val) (scaleBelow : scale.val < 1)
    (nativeBadPositive : 0 < nativeBad.val) (nativeBadBelow : nativeBad.val < 1)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner, (nativeModel).BehavioralPolicy owner)
    (nativePrescribed : nativeProfile = phaseProposalReferenceStrategy setup .concurrent
      implementation.runtime implementation.leaks implementation.bounds implementation.plan
      nativeInitial implementation.horizon implementation.scheduler values
      ⟨nativeBad, scale, scale, scale⟩)
    (who : Player) (site : (nativeModel).InformationSite who)
    (index : MechanicalIndex setup implementation who)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (value : L.Val payload) (cut completed : setup.proposalRecoveryProtocol.History)
    (zero : mechanicalCoefficient setup implementation ⟨nativeBad, scale, scale, scale⟩
      nativeProfile who site event index = 0) :
    annotatedForcedBlockWeight setup values implementation operational sourceProfile nativeProfile
      who site index event payload value cut completed = 0 := by
  unfold annotatedForcedBlockWeight
  apply ENNReal.tsum_eq_zero.mpr
  intro history
  by_cases mechanical : mechanicalWord setup implementation who history.val.trace = index.1.val
  · rw [ite_eq_left mechanical]
    apply ENNReal.tsum_eq_zero.mpr
    intro entry
    apply ENNReal.tsum_eq_zero.mpr
    intro word
    by_contra positive
    have prefixWeight := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp positive).1).1
    have admission := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp positive).1).2
    have admitted : bindingAdmissionBit setup implementation who event history.val index.2 =
        true := by
      cases chosen : bindingAdmissionBit setup implementation who event history.val index.2
      · simp only [chosen, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false] at admission
      · rfl
    unfold annotatedPrefixWeight at prefixWeight
    dsimp only at prefixWeight
    obtain ⟨weights, qualified⟩ := mul_ne_zero_iff.mp prefixWeight
    obtain ⟨reached, tapeSupported⟩ := mul_ne_zero_iff.mp weights
    have good : (∀ owner, owner ≠ who →
        ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
          implementation.leaks implementation.bounds nativeInitial implementation.horizon
            implementation.scheduler owner history.val) ∧
        history.val.state.elim True (fun control =>
          who ∉ control.execution.application.current.excluded) := by
      by_contra bad
      rw [ite_eq_right bad] at qualified
      exact qualified rfl
    exact sourceReplay_mechanicalCoefficient_ne_zero setup values implementation operational
      scale nativeBad scalePositive scaleBelow nativeBadPositive nativeBadBelow fullValues
        nativeProfile nativePrescribed who site event index history mechanical reached tapeSupported
          good.1 good.2 admitted zero
  · exact ite_eq_right mechanical

end Vegas.PhaseProposalQualifiedBinding
