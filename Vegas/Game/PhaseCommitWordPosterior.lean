/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCommitWordPolicy
import Vegas.Pending.PhaseNativeInvariant

/-! # Complete-word conditioning at actual binding responses

The posterior belongs to the concrete whole-block member policy. Callback
guards and the physical slot channel follow from the initialized trace.
Only source/canonical and slot channels are included; raw noise is separate.
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
  {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
  (wellFormed : setup.WellFormed)
  (assessment : setup.commitRecoveryModel.BehavioralAssessment)
  (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
  (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
  (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
  (menu : (phaseApplication runtime leaks).ResponseMenu)
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  (capacity : horizon ≤ bounds.candidateCount)
  (control : (phaseApplication runtime leaks).Control)
  (trace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
    horizon scheduler).Trace (some control)) (active : control.actor = some who)
  (request : control.execution.application.SeedRequest who
    ⟨control.execution.application.attempt, event⟩)
  (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs (control.execution.recall who),
    PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
  (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
  (inside : low ≤ event.val ∧ event.val < low + block.length)
  (address : control.execution.application.attempt = ⟨low, generation⟩)

local notation "app" => phaseApplication runtime leaks
local notation "past" => control.execution.recall who
local notation "view" => control.execution.observe (app) who
local notation "family" => phaseCommitWordPolicy setup mode runtime leaks bounds wellFormed
  assessment block low generation slotWeight slotNonnegative slotBounded who
local notation "missing" => PMF.map (fun choice => CommitRecoveryMove.missed (Subtype.val choice))
  (assessment.strategy who (setup.commitRecoveryClearInformation wellFormed who
    (phaseSourceView? setup mode runtime leaks who event view)))
local notation "readWord" => fun word : DecisionView who Δ =>
  Prod.fst (phaseRecoveryBindingData setup mode event who payload binding
    (CommitRecoveryMove.lift (block.wordAction who (event.val - low) word)))

include binding capacity trace active request unsent values inside address in
private theorem member_response_of_history :
    ∃ serial, (PhaseCount.phaseBindingSlots runtime leaks bounds who event payload past
      view).Nonempty ∧ ∀ word, family word past view =
        PhaseCount.phaseBindingWordResponse runtime leaks bounds who event payload missing serial
          slotWeight slotNonnegative slotBounded (readWord word) past view := by
  have raw := menu.toRawTrace (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler trace
  obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    raw
  obtain ⟨serial, _bounded, serialEq, nonempty, _covered, current⟩ :=
    PhaseCount.phaseBindingWordPolicy_of_history runtime leaks bounds who event payload binding
      (fun _ observedView => (assessment.strategy who
        (setup.commitRecoveryClearInformation wellFormed who
          (phaseSourceView? setup mode runtime leaks who event observedView))).map
            (fun choice => CommitRecoveryMove.missed choice.1))
      slotWeight slotNonnegative slotBounded readWord menu plan inputs horizon scheduler capacity
        control trace active request unsent values
  refine ⟨serial, nonempty, ?_⟩
  intro word
  rw [phaseCommitWordPolicy_binding setup mode runtime leaks bounds wellFormed assessment block
    low generation slotWeight slotNonnegative slotBounded who word control.execution valid event
      payload binding request inside address]
  exact current word

include binding capacity trace active request unsent values inside address in
/-- A supported silence at a genuine unsent callback leaves the posterior of
the whole-block member implementation unchanged. Original omission mass is
derived positive from that actual response, rather than assumed. -/
theorem phaseCommitWordPolicy_posterior_wait_of_history
    (prior : PMF (DecisionView who Δ))
    (supported : (⟨none⟩ : (app).Action) ∈
      (((app).policyMixture prior family).policy past view).support) :
    ((app).policyMixture prior family).posterior
        ((control.execution.respond (app) who ⟨none⟩).recall who) =
      ((app).policyMixture prior family).posterior past := by
  obtain ⟨serial, nonempty, current⟩ := member_response_of_history setup mode runtime leaks bounds
    wellFormed assessment block low generation slotWeight slotNonnegative slotBounded who event
      payload binding menu plan inputs horizon scheduler capacity control trace active request
        unsent values inside address
  have common (word : DecisionView who Δ) : family word past view ⟨none⟩ = missing true := by
    rw [current word]
    exact PhaseCount.phaseBindingWordResponse_silence runtime leaks bounds who event payload _
      serial slotWeight slotNonnegative slotBounded (readWord word) past view nonempty
  have mass : ((app).policyMixture prior family).policy past view ⟨none⟩ = missing true := by
    rw [(app).policyMixture_policy, PMF.bind_apply]
    simp_rw [common]
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have positive : missing true ≠ 0 := by
    rw [← mass]
    exact (PMF.mem_support_iff ..).mp supported
  have unchanged := (app).policyMixture_posterior_snoc_of_likelihood prior family past
    (⟨view, ⟨none⟩, none⟩ : (app).PlayerEntry) (missing true) (fun word _ => common word) positive
  simpa only [ReactiveApplication.Execution.respond, ite_true] using unchanged

include binding capacity trace active request unsent values inside address in
/-- A supported encoded send at the actual callback conditions precisely the
previous owned-word posterior on the encoded typed result. Accepted failure
is included. The source raw-mixture branch is not identified with this law. -/
theorem phaseCommitWordPolicy_posterior_send_of_history
    (prior : PMF (DecisionView who Δ)) (result : PublicationResult (L.Val payload)) (slot : Nat)
    (supported : phaseBindingResponse runtime leaks who event payload result slot ∈
      (((app).policyMixture prior family).policy past view).support) :
    ((app).policyMixture prior family).posterior
        ((control.execution.respond (app) who
          (phaseBindingResponse runtime leaks who event payload result slot)).recall who) =
      fiberPosterior (((app).policyMixture prior family).posterior past) readWord result := by
  obtain ⟨serial, _nonempty, current⟩ := member_response_of_history setup mode runtime leaks bounds
    wellFormed assessment block low generation slotWeight slotNonnegative slotBounded who event
      payload binding menu plan inputs horizon scheduler capacity control trace active request
        unsent values inside address
  let before := ((app).policyMixture prior family).posterior past
  let response := phaseBindingResponse runtime leaks who event payload result slot
  let kernel := fun value => PhaseCount.phaseBindingWordResponse runtime leaks bounds who event
    payload missing serial slotWeight slotNonnegative slotBounded value past view
  have produced : ∃ word ∈ before.support, readWord word = result ∧
      response ∈ (kernel result).support := by
    rw [(app).policyMixture_policy] at supported
    obtain ⟨word, member, emitted⟩ := (PMF.mem_support_bind_iff ..).mp supported
    rw [current word] at emitted
    have sending : response ≠ (⟨none⟩ : (app).Action) := by
      intro equal
      have sent := congrArg (fun action : (app).Action => action.transmission.isNone) equal
      cases sent
    obtain ⟨other, encoded⟩ := PhaseCount.phaseBindingWordResponse_nonsilent runtime leaks bounds
      who event payload missing serial slotWeight slotNonnegative slotBounded (readWord word)
        past view response emitted sending
    have equal : readWord word = result :=
      ((phaseBindingResponse_eq_iff runtime leaks who event payload result (readWord word)
        slot other).mp encoded).2.symm
    exact ⟨word, member, equal, equal ▸ emitted⟩
  have decoded := PhaseCount.phaseBindingWordResponse_posterior_send runtime leaks bounds payload
    before readWord who event missing serial slotWeight slotNonnegative slotBounded past view
      result slot produced
  let joint := before.bind fun word => (kernel (readWord word)).map fun action => (word, action)
  have signal : response ∈ (joint.map Prod.snd).support := by
    obtain ⟨word, member, equal, emitted⟩ := produced
    apply (PMF.mem_support_map_iff ..).mpr
    refine ⟨(word, response), (PMF.mem_support_bind_iff ..).mpr ?_, rfl⟩
    exact ⟨word, member, (PMF.mem_support_map_iff ..).mpr
      ⟨response, equal.symm ▸ emitted, rfl⟩⟩
  have moved := map_fiberPosterior_readout joint Prod.swap Prod.fst response signal
  have projected := congrArg (fun law => law.map Prod.snd) moved
  have swap : joint.map Prod.swap = before.bind fun word =>
      (family word past view).map fun action => (action, word) := by
    simp only [joint, PMF.map_bind, PMF.map_comp]
    apply congrArg (PMF.bind before)
    funext word
    rw [current word]
    rfl
  rw [swap] at projected
  rw [ReactiveApplication.Implementation.posterior_respond]
  change (fiberPosterior (before.bind fun word =>
    (family word past view).map fun action => (action, word)) Prod.fst response).map Prod.snd = _
  rw [← projected, PMF.map_comp]
  change (fiberPosterior joint Prod.snd response).map Prod.fst = _
  exact decoded

end Vegas
