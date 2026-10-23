/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseProposalGenuineReference

/-! # The actual unusable-preparation mass at a genuine binding

Semantic guard rejection is not part of this event. The event is a nonsilent
binding response whose private preparation has no value of the declared type.
All its actual raw aliases are summed before the bound is taken.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks

open Classical in
private def unusableClass
    {owner : Player} {past : List (app).PlayerEntry} {view : (app).PlayerView}
    (chosen : PhaseProposal.ResponseClass runtime leaks bounds owner past view) : Bool :=
  decide (chosen.val.1 = none ∧ chosen.val.2 ≠ none)

open Classical in
private def unusableResponse (response : (app).Action) : Bool :=
  decide (response.transmission.bind PhaseProposal.bindingPreparation = none ∧
    response.transmission ≠ none)

private theorem unusableResponse_class (owner : Player) (past : List (app).PlayerEntry)
    (view : (app).PlayerView)
    (response : PhaseProposal.Response runtime leaks bounds owner past view) :
    unusableClass setup mode runtime leaks bounds
        (PhaseProposal.projectResponse runtime leaks bounds owner past view response) =
      unusableResponse setup mode runtime leaks response.val := by
  classical
  cases transmitted : response.val.transmission <;>
    simp only [unusableClass, unusableResponse, PhaseProposal.projectResponse,
      PhaseProposal.responseClass, transmitted, Option.bind_none, Option.map_none,
      Option.bind_some, Option.map_some, ne_eq, reduceCtorEq, not_false_eq_true]

omit [Fintype Player] in
private theorem unusableResponse_binding (owner : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (serial : Nat) (result : PublicationResult (L.Val payload)) :
    unusableResponse setup mode runtime leaks
        (phaseBindingResponse runtime leaks owner event payload result serial) =
      decide (result = .failure) := by
  classical
  change setup.eventGraph.outputLayout event = .binding owner payload at binding
  cases result <;>
    simp [unusableResponse, phaseBindingResponse, PhaseProposal.bindingPreparation, binding,
      Raw.as?_mk]

omit [Fintype Player] in
private theorem encoded_unusable (owner : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (results : PMF (PublicationResult (L.Val payload))) (serial : Nat) :
    ((results.map (phaseBindingResponse runtime leaks owner event payload · serial)).map
        (unusableResponse setup mode runtime leaks)) =
      results.map (fun result => decide (result = .failure)) := by
  classical
  rw [PMF.map_comp]
  apply congrArg (fun encode => results.map encode)
  funext result
  exact unusableResponse_binding setup mode runtime leaks owner event payload binding serial result

private theorem slot_unusable_le (owner : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (results : List (app).PlayerEntry → (app).PlayerView →
      PMF (PublicationResult (L.Val payload)))
    (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    (((PhaseCount.phaseBindingSlotPolicy runtime leaks bounds owner event payload results past
      view).map (unusableResponse setup mode runtime leaks)) true).toReal ≤
      (((results past view).map (fun result => decide (result = .failure))) true).toReal := by
  classical
  unfold PhaseCount.phaseBindingSlotPolicy
  split
  · rw [PMF.map_bind]
    have branches : ∀ serial ∈ (PMF.uniformOfFinset _ ‹_›).support,
        (((results past view).map
          (phaseBindingResponse runtime leaks owner event payload · serial)).map
            (unusableResponse setup mode runtime leaks)) =
          (results past view).map (fun result => decide (result = .failure)) := by
      intro serial _
      exact encoded_unusable setup mode runtime leaks owner event payload binding _ serial
    rw [bind_congr_on_support _ branches, PMF.bind_const]
  · simp only [PMF.pure_map, unusableResponse, Option.bind_none, ne_eq, not_true_eq_false,
      and_false, decide_false, PMF.pure_apply, Bool.true_eq_false, ↓reduceIte,
      ENNReal.toReal_zero]
    exact ENNReal.toReal_nonneg

private theorem allocator_unusable_le (owner : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (results : List (app).PlayerEntry → (app).PlayerView →
      PMF (PublicationResult (L.Val payload)))
    (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    (((PhaseCount.phaseBindingPolicy runtime leaks bounds owner event payload results past
      view).map (unusableResponse setup mode runtime leaks)) true).toReal ≤
      (((results past view).map (fun result => decide (result = .failure))) true).toReal := by
  classical
  unfold PhaseCount.phaseBindingPolicy
  split
  · simp only [PMF.pure_map, unusableResponse, Option.bind_none, ne_eq, not_true_eq_false,
      and_false, decide_false, PMF.pure_apply, Bool.true_eq_false, ↓reduceIte,
      ENNReal.toReal_zero]
    exact ENNReal.toReal_nonneg
  · split
    · rw [encoded_unusable setup mode runtime leaks owner event payload binding]
    · simp only [PMF.pure_map, unusableResponse, Option.bind_none, ne_eq, not_true_eq_false,
        and_false, decide_false, PMF.pure_apply, Bool.true_eq_false, ↓reduceIte,
        ENNReal.toReal_zero]
      exact ENNReal.toReal_nonneg

private theorem encoder_unusable_le (owner : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (results : List (app).PlayerEntry → (app).PlayerView →
      PMF (PublicationResult (L.Val payload)))
    (rates : PhaseProposalRates) (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    (((PhaseCount.bindingResultEncoder runtime leaks bounds owner event payload results
      rates.slots.val rates.slots.property.1 rates.slots.property.2 past view).map
        (unusableResponse setup mode runtime leaks)) true).toReal ≤
      (((results past view).map (fun result => decide (result = .failure))) true).toReal := by
  classical
  unfold PhaseCount.bindingResultEncoder
  rw [mix_map, mix_apply_toReal]
  have first := mul_le_mul_of_nonneg_left
    (slot_unusable_le setup mode runtime leaks bounds owner event payload binding results past
      view)
    rates.slots.property.1
  have second := mul_le_mul_of_nonneg_left
    (allocator_unusable_le setup mode runtime leaks bounds owner event payload binding results
      past view) (sub_nonneg.mpr rates.slots.property.2)
  nlinarith

/-- After summing actual aliases, an unusable nonsilent preparation has total
mass at most the independent private bad atom. General typed source values,
including those that later fail guards, contribute no mass to this event. -/
theorem phaseProposalReferenceResponses_badPreparation_mass_le
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    (rates : PhaseProposalRates) (waitPositive : 0 < rates.waiting.val)
    (waitBelow : rates.waiting.val < 1) (slotPositive : 0 < rates.slots.val)
    (badPositive : 0 < rates.badPreparation.val) (badBelow : rates.badPreparation.val < 1)
    (horizon : Nat) (scheduler : (app).Scheduler) (remaining : Nat) (owner : Player)
    (execution : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some ⟨remaining, some owner, execution⟩))
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩) :
    (((phaseProposalReferenceResponses setup mode runtime leaks bounds plan values rates owner
      (execution.recall owner) (execution.observe app owner)).map
        (fun response => unusableResponse setup mode runtime leaks response.val)) true).toReal ≤
      rates.badPreparation.val := by
  classical
  let past := execution.recall owner
  let view := execution.observe app owner
  have projected := congrArg (fun law => law.map (unusableClass setup mode runtime leaks bounds))
    (phaseProposalReferenceResponses_project_of_counted setup mode runtime leaks bounds plan
      complete covered maximal values fullValues rates waitPositive waitBelow slotPositive
      badPositive badBelow horizon scheduler remaining owner execution trace)
  have factored : (fun response : PhaseProposal.Response runtime leaks bounds owner past view =>
      unusableClass setup mode runtime leaks bounds
        (PhaseProposal.projectResponse runtime leaks bounds owner past view response)) =
      fun response => unusableResponse setup mode runtime leaks response.val := by
    funext response
    exact unusableResponse_class setup mode runtime leaks bounds owner past view response
  simp only [PMF.map_comp, Function.comp_def] at projected
  rw [factored] at projected
  rw [projected]
  have baseProjected : (phaseProposalBaseClasses setup mode runtime leaks bounds plan values rates
      owner past view).map (unusableClass setup mode runtime leaks bounds) =
      (phaseProposalBasePolicy setup mode runtime leaks bounds plan values rates owner past
        view).map
        (unusableResponse setup mode runtime leaks) := by
    unfold phaseProposalBaseClasses
    simp only [PMF.map_comp, Function.comp_def]
    rw [factored]
    change ((phaseProposalBaseResponses setup mode runtime leaks bounds plan values rates owner
      past view).map (unusableResponse setup mode runtime leaks ∘ Subtype.val)) = _
    rw [← PMF.map_comp, phaseProposalBaseResponses_map_val setup mode runtime leaks bounds plan
      values rates owner past view]
  rw [baseProjected]
  let inputs := setup.initialLaw.map encodeInputs
  have counted : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, execution⟩) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact trace
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace
  obtain ⟨draw, native⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler counted)
  obtain ⟨key, queried, _ordinary⟩ := phaseProposalDomainValues_fullSupport_of_binding setup mode
    runtime leaks complete plan maximal values fullValues horizon scheduler raw owner rfl event
      payload binding request
  have resultMass : (((phaseProposalBindingResults setup mode runtime leaks plan values rates
      owner event payload binding past view).map (fun result => decide (result = .failure)))
        true).toReal = rates.badPreparation.val := by
    unfold phaseProposalBindingResults
    rw [queried, mix_map, PMF.map_comp]
    have ordinary : (fun value : setup.CommitRecoveryValueChoice owner key.1 =>
        decide (PublicationResult.success
          (phaseRecoveryDomainValue setup mode event owner payload binding value.val.val) =
            PublicationResult.failure)) = fun _ => false := by
      funext value
      simp
    simp only [Function.comp_def] at ordinary ⊢
    rw [ordinary, pmf_map_fun_const, PMF.pure_map, mix_apply_toReal]
    simp
  unfold phaseProposalBasePolicy
  rw [phasePolicyDispatch_binding setup mode runtime leaks _ _ execution native owner event payload
    binding request, mix_map, mix_apply_toReal]
  have encoder := encoder_unusable_le setup mode runtime leaks bounds owner event payload binding
    (phaseProposalBindingResults setup mode runtime leaks plan values rates owner event payload
      binding) rates past view
  rw [resultMass] at encoder
  have weighted := mul_le_mul_of_nonneg_left encoder (sub_nonneg.mpr rates.waiting.property.2)
  have rest : (1 - rates.waiting.val) * rates.badPreparation.val ≤ rates.badPreparation.val :=
    mul_le_of_le_one_left rates.badPreparation.property.1
      (by linarith [rates.waiting.property.1])
  simp only [PMF.pure_map, unusableResponse, Option.bind_none, ne_eq, not_true_eq_false,
    and_false, decide_false, PMF.pure_apply, Bool.true_eq_false, ↓reduceIte,
    ENNReal.toReal_zero, mul_zero, zero_add]
  exact weighted.trans rest

/-- Each literal missing/mistyped binding alias has mass at most the actual
bad-preparation rate. The bound includes rare private evidence aliases. -/
theorem phaseProposalReferenceResponses_badPreparation_atom_le
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    (rates : PhaseProposalRates) (waitPositive : 0 < rates.waiting.val)
    (waitBelow : rates.waiting.val < 1) (slotPositive : 0 < rates.slots.val)
    (badPositive : 0 < rates.badPreparation.val) (badBelow : rates.badPreparation.val < 1)
    (horizon : Nat) (scheduler : (app).Scheduler) (remaining : Nat) (owner : Player)
    (execution : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some ⟨remaining, some owner, execution⟩))
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (serial : Nat) (opening : Option (Raw L)) (evidence : EvidenceRequest (serviceGraph setup mode))
    (member : (⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩ :
      (app).Action) ∈ PhaseCount.onePacketActions runtime leaks bounds owner
        (execution.recall owner) (execution.observe app owner))
    (unusable : opening.bind (fun raw => raw.as? payload) = none) :
    (phaseProposalReferenceResponses setup mode runtime leaks bounds plan values rates owner
      (execution.recall owner) (execution.observe app owner)
      ⟨⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩, member⟩).toReal ≤
        rates.badPreparation.val := by
  classical
  let response : PhaseProposal.Response runtime leaks bounds owner (execution.recall owner)
      (execution.observe app owner) :=
    ⟨⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩, member⟩
  let law := phaseProposalReferenceResponses setup mode runtime leaks bounds plan values rates
    owner (execution.recall owner) (execution.observe app owner)
  let signal := fun chosen : PhaseProposal.Response runtime leaks bounds owner
      (execution.recall owner) (execution.observe app owner) =>
    unusableResponse setup mode runtime leaks chosen.val
  have signaled : signal response = true := by
    simp only [signal, response, unusableResponse, PhaseProposal.bindingPreparation,
      Option.bind_some, binding, unusable, Option.map_none, ne_eq, reduceCtorEq,
      not_false_eq_true, and_self, decide_true]
  have atom : law response ≤ (law.map signal) true := by
    rw [← pmf_bind_pure_eq_map, PMF.bind_apply]
    have selected := ENNReal.le_tsum
      (f := fun chosen => law chosen * PMF.pure (signal chosen) true) response
    simpa only [signaled, PMF.pure_apply_self, mul_one] using selected
  exact (ENNReal.toReal_mono (PMF.apply_ne_top _ _) atom).trans
    (phaseProposalReferenceResponses_badPreparation_mass_le setup mode runtime leaks bounds plan
      complete covered maximal values fullValues rates waitPositive waitBelow slotPositive
        badPositive badBelow horizon scheduler remaining owner execution trace event payload
          (by exact binding) request)

end Vegas
