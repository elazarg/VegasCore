/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedPolicyProgress
import Vegas.Compile.SealedResolutionClosure
import Interaction.MessageApplicationCheckpoints
import Interaction.SealedResolutionCompletion

/-! # Protocol-phase charges in actual compiled execution traces

A charge refers to adjacent snapshots of the shared native runner. It records
the compiled command and the supported native step, not just a command that
could occur at some unrelated snapshot. A source slot receives at most one
registration charge, even when arbitrary native traffic and timeouts intervene.
Repeated submission charges are bounded by service checkpoints on the same
trace. Queue drainage and whole-application completion are operational premises;
acceptance of an honest payload is derived from the executed compiled phase.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- An actual adjacent native step performs a registration allowed by the
compiled source policy. The trace itself is supplied by the shared runner. -/
def RegistrationAt (supported : SealedFragment G ty) (nullValue : L.Val ty) (window : Nat)
    (trace : (supported.resolvingRuntime nullValue window).messageApplication.PolicyTrace)
    (who : Player) (policy : CommitPolicy G who) (slot index : Nat) : Prop :=
  ∃ value : L.Val ty,
    .privateCommand ⟨(slot, value)⟩ ∈
        (supported.resolvingPolicy nullValue window who policy
          ((trace.drop index).first.principalHistory who)
          (State.observe _ (trace.drop index).first.native who)).support ∧
      (trace.drop (index + 1)).first ∈
        ((supported.resolvingRuntime nullValue window).messageApplication.playerStep who
          (trace.drop index).first (.privateCommand ⟨(slot, value)⟩)).support

/-- A ready target at an actual compiled-player invocation supplies the exact
selected site and the executed protocol phase. All snapshot invariants come
from the canonical initial execution and its supported native prefix. -/
theorem trace_ready_progress (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat)
    (players : Player →
      (supported.resolvingRuntime nullValue window).messageApplication.PlayerPolicy)
    (environment :
      (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Player))
    (trace : (supported.resolvingRuntime nullValue window).messageApplication.PolicyTrace)
    (htrace : trace ∈
      ((supported.resolvingRuntime nullValue window).messageApplication.tracePolicies
        players environment schedule (PolicyExecution.initial _
          (State.initial _ (supported.resolvingRuntime nullValue window).initial))).support)
    (who : Player) (policy : CommitPolicy G who)
    (hpolicy : players who = supported.resolvingPolicy nullValue window who policy)
    (index : Nat) (hcall : schedule[index]? = some (.player who))
    (target : Fin G.nodeCount)
    (hnotDone : (trace.drop index).first.native.application.visible.completed target.val = false)
    (hrequires : (G.messagePrerequisites target).all
      (trace.drop index).first.native.application.visible.completed = true)
    (howned :
      (∃ guard, (G.nodeRow target).sem = .commit who guard) ∨
      ∃ (producer : Fin G.nodeCount) (guard : EventGuard L),
        (G.nodeRow target).sem = .reveal (G.nodeTarget producer) ∧
        (G.nodeRow producer).sem = .commit who guard) :
    ∃ (selected : Fin G.nodeCount)
        (command : (supported.resolvingRuntime nullValue window).messageApplication.PlayerCommand),
      selected.val ≤ target.val ∧
      (trace.drop index).first.native.application.visible.completed selected.val = false ∧
      (G.messagePrerequisites selected).all
        (trace.drop index).first.native.application.visible.completed = true ∧
      supported.ProgressCommand who
        ((supported.resolvingRuntime nullValue window).eventHistory
          ((trace.drop index).first.principalHistory who)) selected command ∧
      command ∈ (supported.resolvingPolicy nullValue window who policy
        ((trace.drop index).first.principalHistory who)
        (State.observe _ (trace.drop index).first.native who)).support ∧
      (trace.drop (index + 1)).first ∈
        ((supported.resolvingRuntime nullValue window).messageApplication.playerStep who
          (trace.drop index).first command).support := by
  let runtime := supported.resolvingRuntime nullValue window
  let initial := PolicyExecution.initial runtime.messageApplication
    (State.initial runtime.messageApplication runtime.initial)
  let before := (trace.drop index).first
  have hprefix := (runtime.messageApplication.tracePolicies_drop_support players environment
    schedule initial trace htrace index).1
  have hinvariant := runtime.runPolicies_eventInvariant players environment (schedule.take index)
    initial before SealedResolution.EventInvariant.initial hprefix
  have hmemory := SealedResolution.RegistrationMemory.runPolicies players environment
    (schedule.take index) initial before SealedResolution.RegistrationMemory.initial hprefix
  have hclosed := supported.resolvingRuntime_runPolicies_resolutionClosed nullValue window
    players environment (schedule.take index) before hprefix
  have hinvoke := runtime.messageApplication.tracePolicies_drop_invoke players environment
    schedule initial trace htrace index (.player who) hcall
  simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hinvoke
  obtain ⟨command, hcommand, hstep⟩ := hinvoke
  rw [hpolicy] at hcommand
  obtain ⟨selected, hbound, hselected, hready, hphase⟩ :=
    supported.resolvingPolicy_progress_of_ready nullValue window who policy before
      hinvariant hmemory hclosed target hnotDone hrequires howned command hcommand
  exact ⟨selected, command, hbound, hselected, hready, hphase, hcommand, hstep⟩

/-- A submitted compiled protocol phase completes its selected source site
once subsequent native service drains the queue. All intervening policies are
arbitrary; readiness and binding are derived from the executed compiled phase. -/
theorem ProgressCommand.submission_completed_of_drained (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat) (who : Player)
    (execution submitted next :
      (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (hinvariant : SealedResolution.EventInvariant (supported.resolvingRuntime nullValue window)
      execution.native.application)
    (hmemory : SealedResolution.RegistrationMemory (supported.resolvingRuntime nullValue window)
      execution)
    (hclosed : execution.native.application.visible.ResolutionClosed
      (supported.resolvingRuntime nullValue window))
    (node : Fin G.nodeCount) (payload : SealedProgram.Payload Player (L.Val ty))
    (hphase : supported.ProgressCommand who
      ((supported.resolvingRuntime nullValue window).eventHistory
        (execution.principalHistory who)) node (.submit payload))
    (hnotDone : execution.native.application.visible.completed node.val = false)
    (hrequires : (G.messagePrerequisites node).all
      execution.native.application.visible.completed = true)
    (hstep : submitted ∈
      ((supported.resolvingRuntime nullValue window).messageApplication.playerStep
        who execution (.submit payload)).support)
    (players : Player →
      (supported.resolvingRuntime nullValue window).messageApplication.PlayerPolicy)
    (environment :
      (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Player))
    (hnext : next ∈ ((supported.resolvingRuntime nullValue window).messageApplication.runPolicies
      players environment schedule submitted).support)
    (hempty : next.native.pool.pending = []) :
    next.native.application.visible.completed node.val = true := by
  let runtime := supported.resolvingRuntime nullValue window
  have hnative : submitted.native =
      { execution.native with pool := (execution.native.pool.submit who payload).2 } := by
    simp only [playerStep, advance, PlayerCommand.toAction, MessageApplication.step,
      FinDist.pure_bind, FinDist.mem_support_pure] at hstep
    subst submitted
    rfl
  have happlication : submitted.native.application = execution.native.application := by
    rw [hnative]
  have hpending : (⟨(who, execution.native.pool.nextSerial who), payload⟩ :
      Message Player (SealedProgram.Payload Player (L.Val ty))) ∈
        submitted.native.pool.pending := by
    rw [hnative]
    exact List.mem_append_right _ List.mem_cons_self
  cases hphase with
  | commitment guard hsem value hcache =>
      have hrule : runtime.program.rules[node.val]? =
          some ⟨.commit who, G.messagePrerequisites node⟩ := by
        change supported.compile.rules[node.val]? = _
        rw [supported.compile_rule, G.sealedRule_commit_eq node who guard hsem]
      have hlookup : execution.native.application.service.lookup (who, node.val) =
          some value := (hmemory who node.val).trans
        ((runtime.eventHistory_cache (runtime.program.registrationEncoding node.val)
          (execution.principalHistory who)).symm.trans hcache)
      have hresult := runtime.runPolicies_commitment_pendingOrCompleted players environment
        schedule submitted next who (execution.native.pool.nextSerial who) node.val
        (G.messagePrerequisites node) value hrule hpending
        (by rw [happlication]; exact hlookup) (by rw [happlication]; exact hrequires) hnext
      rcases hresult with hdone | hpending
      · exact hdone
      · simp only [hempty, List.not_mem_nil, false_and] at hpending
  | opening producer guard hreveal hproducer value hcache =>
      have hrule : runtime.program.rules[node.val]? =
          some ⟨.reveal who producer.val, G.messagePrerequisites node⟩ := by
        change supported.compile.rules[node.val]? = _
        rw [supported.compile_rule,
          G.sealedRule_reveal_eq node producer who guard hreveal hproducer]
      have hsourceRule : runtime.program.rules[producer.val]? =
          some ⟨.commit who, G.messagePrerequisites producer⟩ := by
        change supported.compile.rules[producer.val]? = _
        rw [supported.compile_rule, G.sealedRule_commit_eq producer who guard hproducer]
      have haccepted := supported.ready_reveal_source_accepted nullValue window execution
        hinvariant hclosed node producer who guard hreveal hproducer hnotDone hrequires
      have hlookup : execution.native.application.service.lookup (who, producer.val) =
          some value := (hmemory who producer.val).trans
        ((runtime.eventHistory_cache (runtime.program.registrationEncoding producer.val)
          (execution.principalHistory who)).symm.trans hcache)
      have hresult := runtime.runPolicies_opening_pendingOrCompleted players environment
        schedule submitted next who (execution.native.pool.nextSerial who) node.val producer.val
        (G.messagePrerequisites node) (G.messagePrerequisites producer) value hrule hsourceRule
        (by rw [happlication]; exact hinvariant) hpending
        (by rw [happlication]; exact haccepted) (by rw [happlication]; exact hlookup)
        (by rw [happlication]; exact hrequires) hnext
      rcases hresult with hdone | hpending
      · exact hdone
      · simp only [hempty, List.not_mem_nil, false_and] at hpending

private theorem registrationAt_not_later (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat)
    (players : Player →
      (supported.resolvingRuntime nullValue window).messageApplication.PlayerPolicy)
    (environment :
      (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Player))
    (execution : (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (trace : (supported.resolvingRuntime nullValue window).messageApplication.PolicyTrace)
    (hmemory : SealedResolution.RegistrationMemory (supported.resolvingRuntime nullValue window)
      execution)
    (htrace : trace ∈
      ((supported.resolvingRuntime nullValue window).messageApplication.tracePolicies
        players environment schedule execution).support)
    (who : Player) (policy : CommitPolicy G who) (slot earlier later : Nat)
    (hlt : earlier < later)
    (hearlier : supported.RegistrationAt nullValue window trace who policy slot earlier)
    (hlater : supported.RegistrationAt nullValue window trace who policy slot later) : False := by
  let runtime := supported.resolvingRuntime nullValue window
  let before := (trace.drop earlier).first
  let after := (trace.drop (earlier + 1)).first
  obtain ⟨value, hcommand, hstep⟩ := hearlier
  have hprefix := (runtime.messageApplication.tracePolicies_drop_support players environment
    schedule execution trace htrace earlier).1
  have hbeforeMemory : runtime.RegistrationMemory before :=
    SealedResolution.RegistrationMemory.runPolicies players environment (schedule.take earlier)
      execution before hmemory hprefix
  have hfresh := supported.resolvingPolicy_registration_fresh nullValue window who policy
    before hbeforeMemory slot value hcommand
  have hstored : after.native.application.service.lookup (who, slot) = some value := by
    simp only [playerStep, advance, PlayerCommand.toAction, MessageApplication.step,
      FinDist.pure_bind, FinDist.mem_support_pure] at hstep
    change after = _ at hstep
    rw [hstep]
    exact (before.native.application.service.seal_first who slot value hfresh).2
  have hafterMemory : runtime.RegistrationMemory after :=
    SealedResolution.RegistrationMemory.playerStep before after who _ hbeforeMemory hstep
  have hbetween := runtime.messageApplication.tracePolicies_between players environment
    schedule execution trace htrace (earlier + 1) (later - (earlier + 1))
  rw [Nat.add_sub_of_le (by omega : earlier + 1 ≤ later)] at hbetween
  obtain ⟨otherValue, hotherCommand, _⟩ := hlater
  exact supported.runPolicies_no_reregistration nullValue window players environment
    ((schedule.drop (earlier + 1)).take (later - (earlier + 1))) after
    (trace.drop later).first hafterMemory who slot value hstored hbetween policy otherValue
    hotherCommand

/-- Two registration charges for one source slot in the same supported native
trace refer to the same invocation position. No service premise is needed. -/
theorem registrationAt_unique (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat)
    (players : Player →
      (supported.resolvingRuntime nullValue window).messageApplication.PlayerPolicy)
    (environment :
      (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Player))
    (execution : (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (trace : (supported.resolvingRuntime nullValue window).messageApplication.PolicyTrace)
    (hmemory : SealedResolution.RegistrationMemory (supported.resolvingRuntime nullValue window)
      execution)
    (htrace : trace ∈
      ((supported.resolvingRuntime nullValue window).messageApplication.tracePolicies
        players environment schedule execution).support)
    (who : Player) (policy : CommitPolicy G who) (slot left right : Nat)
    (hleft : supported.RegistrationAt nullValue window trace who policy slot left)
    (hright : supported.RegistrationAt nullValue window trace who policy slot right) :
    left = right := by
  rcases lt_trichotomy left right with hlt | heq | hgt
  · exact (supported.registrationAt_not_later nullValue window players environment schedule
      execution trace hmemory htrace who policy slot left right hlt hleft hright).elim
  · exact heq
  · exact (supported.registrationAt_not_later nullValue window players environment schedule
      execution trace hmemory htrace who policy slot right left hgt hright hleft).elim

/-- Any selected finite set of actual invocation positions contains at most
one fresh registration of a given source slot. -/
theorem registration_count_le_one (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat)
    (players : Player →
      (supported.resolvingRuntime nullValue window).messageApplication.PlayerPolicy)
    (environment :
      (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Player))
    (execution : (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (trace : (supported.resolvingRuntime nullValue window).messageApplication.PolicyTrace)
    (hmemory : SealedResolution.RegistrationMemory (supported.resolvingRuntime nullValue window)
      execution)
    (htrace : trace ∈
      ((supported.resolvingRuntime nullValue window).messageApplication.tracePolicies
        players environment schedule execution).support)
    (who : Player) (policy : CommitPolicy G who) (slot : Nat) (indices : Finset Nat)
    (hindices : ∀ index ∈ indices,
      supported.RegistrationAt nullValue window trace who policy slot index) :
    indices.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro left hleft right hright
  exact supported.registrationAt_unique nullValue window players environment schedule
    execution trace hmemory htrace who policy slot left right
    (hindices left hleft) (hindices right hright)

/-- A canonical submission actually executed at a ready, unfinished source
site. The before/after snapshots belong to the shared native trace. -/
def SubmissionAt (supported : SealedFragment G ty) (nullValue : L.Val ty) (window : Nat)
    (trace : (supported.resolvingRuntime nullValue window).messageApplication.PolicyTrace)
    (who : Player) (node : Fin G.nodeCount) (index : Nat) : Prop :=
  (trace.drop index).first.native.application.visible.completed node.val = false ∧
    (G.messagePrerequisites node).all
      (trace.drop index).first.native.application.visible.completed = true ∧
    ∃ payload,
      supported.ProgressCommand who
        ((supported.resolvingRuntime nullValue window).eventHistory
          ((trace.drop index).first.principalHistory who)) node (.submit payload) ∧
      (trace.drop (index + 1)).first ∈
        ((supported.resolvingRuntime nullValue window).messageApplication.playerStep who
          (trace.drop index).first (.submit payload)).support

section SubmissionCounting

variable (supported : SealedFragment G ty) (nullValue : L.Val ty) (window : Nat)
    (players : Player →
      (supported.resolvingRuntime nullValue window).messageApplication.PlayerPolicy)
    (environment :
      (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Player))
    (trace : (supported.resolvingRuntime nullValue window).messageApplication.PolicyTrace)
    (htrace : trace ∈
      ((supported.resolvingRuntime nullValue window).messageApplication.tracePolicies
        players environment schedule (PolicyExecution.initial _
          (State.initial _ (supported.resolvingRuntime nullValue window).initial))).support)

include htrace

/-- A source site submitted before a service checkpoint cannot still be
selected as unfinished after that checkpoint. Traffic between these positions
is arbitrary, including defaults and retransmissions. -/
theorem submissionAt_not_after_service (who : Player) (node : Fin G.nodeCount)
    (earlier checkpoint later : Nat)
    (hafter : earlier + 1 ≤ checkpoint) (hbefore : checkpoint ≤ later)
    (hearlier : supported.SubmissionAt nullValue window trace who node earlier)
    (hlater : supported.SubmissionAt nullValue window trace who node later)
    (hservice : (supported.resolvingRuntime nullValue window).complete
        (trace.drop checkpoint).first.native.application.visible = true ∨
      (trace.drop checkpoint).first.native.pool.pending = []) : False := by
  let runtime := supported.resolvingRuntime nullValue window
  let initial := PolicyExecution.initial runtime.messageApplication
    (State.initial runtime.messageApplication runtime.initial)
  let before := (trace.drop earlier).first
  let submitted := (trace.drop (earlier + 1)).first
  let serviced := (trace.drop checkpoint).first
  have hdone : serviced.native.application.visible.completed node.val = true := by
    rcases hservice with hcomplete | hempty
    · exact runtime.complete_node _ node.val hcomplete (by
        change node.val < supported.compile.rules.length
        simpa only [supported.compile_rules, List.length_map, Graph.nodeOrder, List.length_finRange]
          using node.isLt)
    · obtain ⟨hnotDone, hrequires, payload, hphase, hstep⟩ := hearlier
      have hprefix := (runtime.messageApplication.tracePolicies_drop_support players environment
        schedule initial trace htrace earlier).1
      have hinvariant := runtime.runPolicies_eventInvariant players environment
        (schedule.take earlier) initial before SealedResolution.EventInvariant.initial hprefix
      have hmemory := SealedResolution.RegistrationMemory.runPolicies players environment
        (schedule.take earlier) initial before SealedResolution.RegistrationMemory.initial hprefix
      have hclosed := supported.resolvingRuntime_runPolicies_resolutionClosed nullValue window
        players environment (schedule.take earlier) before hprefix
      have hbetween := runtime.messageApplication.tracePolicies_between players environment
        schedule initial trace htrace (earlier + 1) (checkpoint - (earlier + 1))
      rw [Nat.add_sub_of_le hafter] at hbetween
      exact ProgressCommand.submission_completed_of_drained supported nullValue window who
        before submitted serviced hinvariant hmemory hclosed node payload hphase hnotDone
        hrequires hstep players environment
        ((schedule.drop (earlier + 1)).take (checkpoint - (earlier + 1))) hbetween hempty
  have hbetween := runtime.messageApplication.tracePolicies_between players environment
    schedule initial trace htrace checkpoint (later - checkpoint)
  rw [Nat.add_sub_of_le hbefore] at hbetween
  have hretained := runtime.runPolicies_completed players environment
    ((schedule.drop checkpoint).take (later - checkpoint)) serviced (trace.drop later).first
    node.val hdone hbetween
  rw [hlater.1] at hretained
  contradiction

/-- With service no later than the next poll after `delay` further rounds,
a source site receives at most `delay + 1` designated submission polls.
Positions may skip extra player calls; no constant-selector premise is used. -/
theorem submission_count_le (who : Player) (node : Fin G.nodeCount)
    (position : Nat → Nat) (hposition : StrictMono position) (delay : Nat)
    (rounds : Finset Nat)
    (hsubmissions : ∀ round ∈ rounds,
      supported.SubmissionAt nullValue window trace who node (position round))
    (hservice : ∀ round ∈ rounds, ∃ checkpoint,
      position round + 1 ≤ checkpoint ∧ checkpoint ≤ position (round + delay + 1) ∧
      ((supported.resolvingRuntime nullValue window).complete
          (trace.drop checkpoint).first.native.application.visible = true ∨
        (trace.drop checkpoint).first.native.pool.pending = [])) :
    rounds.card ≤ delay + 1 := by
  classical
  by_cases hnonempty : rounds.Nonempty
  · let first := rounds.min' hnonempty
    have hfirst : first ∈ rounds := Finset.min'_mem rounds hnonempty
    obtain ⟨checkpoint, hafter, hbefore, hserviced⟩ := hservice first hfirst
    have hsubset : rounds ⊆ Finset.Icc first (first + delay) := by
      intro round hround
      refine Finset.mem_Icc.mpr ⟨Finset.min'_le rounds round hround, ?_⟩
      by_contra hlate
      have hlater : checkpoint ≤ position round :=
        hbefore.trans (hposition.monotone (by omega))
      exact supported.submissionAt_not_after_service nullValue window players environment
        schedule trace htrace who node (position first) checkpoint (position round)
        hafter hlater (hsubmissions first hfirst) (hsubmissions round hround) hserviced
    have hcard := Finset.card_le_card hsubset
    rw [Nat.card_Icc] at hcard
    omega
  · simpa only [Finset.not_nonempty_iff_eq_empty.mp hnonempty, Finset.card_empty] using
      (Nat.zero_le (delay + 1))

/-- Summing actual registration and submission charges over a finite source
prefix bounds all designated polls. Sites may become ready out of order. -/
theorem phase_count_le (who : Player) (policy : CommitPolicy G who)
    (target : Fin G.nodeCount) (position : Nat → Nat) (hposition : StrictMono position)
    (delay : Nat) (rounds : Finset Nat) (selected : Nat → Fin G.nodeCount)
    (hbound : ∀ round ∈ rounds, (selected round).val ≤ target.val)
    (hphases : ∀ round ∈ rounds,
      supported.RegistrationAt nullValue window trace who policy
          (selected round).val (position round) ∨
        supported.SubmissionAt nullValue window trace who (selected round) (position round))
    (hservice : ∀ round ∈ rounds, ∃ checkpoint,
      position round + 1 ≤ checkpoint ∧ checkpoint ≤ position (round + delay + 1) ∧
      ((supported.resolvingRuntime nullValue window).complete
          (trace.drop checkpoint).first.native.application.visible = true ∨
        (trace.drop checkpoint).first.native.pool.pending = [])) :
    rounds.card ≤ (target.val + 1) * (delay + 2) := by
  classical
  let runtime := supported.resolvingRuntime nullValue window
  let initial := PolicyExecution.initial runtime.messageApplication
    (State.initial runtime.messageApplication runtime.initial)
  have hfiber : ∀ slot ∈ Finset.range (target.val + 1),
      (rounds.filter (fun round => (selected round).val = slot)).card ≤ delay + 2 := by
    intro slot hslot
    let node : Fin G.nodeCount := ⟨slot, by have := Finset.mem_range.mp hslot; omega⟩
    let fiber := rounds.filter (fun round => (selected round).val = slot)
    let registered := fiber.filter (fun round =>
      supported.RegistrationAt nullValue window trace who policy slot (position round))
    let submitted := fiber.filter (fun round =>
      ¬ supported.RegistrationAt nullValue window trace who policy slot (position round))
    have hregistered : registered.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro left hleft right hright
      apply hposition.injective
      exact supported.registrationAt_unique nullValue window players environment schedule
        initial trace SealedResolution.RegistrationMemory.initial htrace who policy slot
        (position left) (position right) (Finset.mem_filter.mp hleft).2
        (Finset.mem_filter.mp hright).2
    have hsubmitted : submitted.card ≤ delay + 1 := by
      apply supported.submission_count_le nullValue window players environment schedule trace
        htrace who node position hposition delay submitted
      · intro round hround
        obtain ⟨hfiber, hnotRegistration⟩ := Finset.mem_filter.mp hround
        obtain ⟨hround, hselected⟩ := Finset.mem_filter.mp hfiber
        have heq : selected round = node := Fin.ext hselected
        rcases hphases round hround with hregistration | hsubmission
        · exact (hnotRegistration (hselected ▸ hregistration)).elim
        · exact heq ▸ hsubmission
      · intro round hround
        exact hservice round (Finset.mem_filter.mp (Finset.mem_filter.mp hround).1).1
    have hsplit : registered.card + submitted.card = fiber.card :=
      fiber.card_filter_add_card_filter_not _
    change fiber.card ≤ delay + 2
    omega
  have htotal := Finset.card_le_mul_card_image_of_maps_to
    (f := fun round => (selected round).val) (s := rounds)
    (t := Finset.range (target.val + 1))
    (fun round hround => Finset.mem_range.mpr (by have := hbound round hround; omega))
    (delay + 2) hfiber
  simpa only [Finset.card_range, Nat.mul_comm] using htotal

/-- A ready unfinished owned target cannot persist across more than the
source-prefix phase budget of actual compiled-player polls. All phase,
registration, and acceptance facts are derived from the native execution;
only the operational service checkpoints are supplied by the environment. -/
theorem ready_poll_count_le (who : Player) (policy : CommitPolicy G who)
    (hpolicy : players who = supported.resolvingPolicy nullValue window who policy)
    (target : Fin G.nodeCount)
    (howned :
      (∃ guard, (G.nodeRow target).sem = .commit who guard) ∨
      ∃ (producer : Fin G.nodeCount) (guard : EventGuard L),
        (G.nodeRow target).sem = .reveal (G.nodeTarget producer) ∧
        (G.nodeRow producer).sem = .commit who guard)
    (position : Nat → Nat) (hposition : StrictMono position)
    (delay : Nat) (rounds : Finset Nat)
    (hcall : ∀ round ∈ rounds, schedule[position round]? = some (.player who))
    (hnotDone : ∀ round ∈ rounds,
      (trace.drop (position round)).first.native.application.visible.completed target.val = false)
    (hrequires : ∀ round ∈ rounds, (G.messagePrerequisites target).all
      (trace.drop (position round)).first.native.application.visible.completed = true)
    (hservice : ∀ round ∈ rounds, ∃ checkpoint,
      position round + 1 ≤ checkpoint ∧ checkpoint ≤ position (round + delay + 1) ∧
      ((supported.resolvingRuntime nullValue window).complete
          (trace.drop checkpoint).first.native.application.visible = true ∨
        (trace.drop checkpoint).first.native.pool.pending = [])) :
    rounds.card ≤ (target.val + 1) * (delay + 2) := by
  classical
  have hchoices : ∀ round, ∃ selected : Fin G.nodeCount,
      selected.val ≤ target.val ∧ (round ∈ rounds →
        supported.RegistrationAt nullValue window trace who policy selected.val (position round) ∨
          supported.SubmissionAt nullValue window trace who selected (position round)) := by
    intro round
    by_cases hround : round ∈ rounds
    · obtain ⟨selected, command, hbound, hselected, hready, hphase, hcommand, hstep⟩ :=
        supported.trace_ready_progress nullValue window players environment schedule trace
          htrace who policy hpolicy (position round) (hcall round hround) target
          (hnotDone round hround) (hrequires round hround) howned
      refine ⟨selected, hbound, fun _ => ?_⟩
      cases hphase with
      | registration guard hsem value hcache => exact Or.inl ⟨value, hcommand, hstep⟩
      | commitment guard hsem value hcache =>
          exact Or.inr ⟨hselected, hready, _,
            .commitment selected guard hsem value hcache, hstep⟩
      | opening producer guard hreveal hproducer value hcache =>
          exact Or.inr ⟨hselected, hready, _,
            .opening selected producer guard hreveal hproducer value hcache, hstep⟩
    · exact ⟨target, le_rfl, fun h => (hround h).elim⟩
  choose selected hbound hphases using hchoices
  exact supported.phase_count_le nullValue window players environment schedule trace htrace
    who policy target position hposition delay rounds selected (fun round _ => hbound round)
    hphases hservice

/-- A target ready at the first designated poll has completed before the last
poll of any longer-than-budget polling interval. An unfinished last pre-state
would make every poll, including that last invocation, chargeable. This theorem
does not yet distinguish service completion from timeout completion. -/
theorem completed_by_poll (who : Player) (policy : CommitPolicy G who)
    (hpolicy : players who = supported.resolvingPolicy nullValue window who policy)
    (target : Fin G.nodeCount)
    (howned :
      (∃ guard, (G.nodeRow target).sem = .commit who guard) ∨
      ∃ (producer : Fin G.nodeCount) (guard : EventGuard L),
        (G.nodeRow target).sem = .reveal (G.nodeTarget producer) ∧
        (G.nodeRow producer).sem = .commit who guard)
    (position : Nat → Nat) (hposition : StrictMono position)
    (delay count : Nat) (hcount : (target.val + 1) * (delay + 2) < count)
    (hcall : ∀ round < count, schedule[position round]? = some (.player who))
    (hready : (G.messagePrerequisites target).all
      (trace.drop (position 0)).first.native.application.visible.completed = true)
    (hservice : ∀ round < count, ∃ checkpoint,
      position round + 1 ≤ checkpoint ∧ checkpoint ≤ position (round + delay + 1) ∧
      ((supported.resolvingRuntime nullValue window).complete
          (trace.drop checkpoint).first.native.application.visible = true ∨
        (trace.drop checkpoint).first.native.pool.pending = [])) :
    (trace.drop (position (count - 1))).first.native.application.visible.completed
      target.val = true := by
  let runtime := supported.resolvingRuntime nullValue window
  let initial := PolicyExecution.initial runtime.messageApplication
    (State.initial runtime.messageApplication runtime.initial)
  have hmono : ∀ left right, left ≤ right → ∀ node,
      (trace.drop (position left)).first.native.application.visible.completed node = true →
      (trace.drop (position right)).first.native.application.visible.completed node = true := by
    intro left right hle node hcompleted
    have hpositions := hposition.monotone hle
    have hbetween := runtime.messageApplication.tracePolicies_between players environment
      schedule initial trace htrace (position left) (position right - position left)
    rw [Nat.add_sub_of_le hpositions] at hbetween
    exact runtime.runPolicies_completed players environment
      ((schedule.drop (position left)).take (position right - position left))
      (trace.drop (position left)).first (trace.drop (position right)).first node
      hcompleted hbetween
  cases hcompleted :
      (trace.drop (position (count - 1))).first.native.application.visible.completed target.val with
  | true => rfl
  | false =>
      have hbound := supported.ready_poll_count_le nullValue window players environment schedule
        trace htrace who policy hpolicy target howned position hposition delay (Finset.range count)
        (fun round hround => hcall round (Finset.mem_range.mp hround))
        (fun round hround => by
          cases h : (trace.drop (position round)).first.native.application.visible.completed
              target.val with
          | false => rfl
          | true =>
              have hfinal := hmono round (count - 1) (by
                have := Finset.mem_range.mp hround
                omega)
                target.val h
              rw [hcompleted] at hfinal
              contradiction)
        (fun round _ => List.all_eq_true.mpr (fun node hnode =>
          hmono 0 round (Nat.zero_le round) node (List.all_eq_true.mp hready node hnode)))
        (fun round hround => hservice round (Finset.mem_range.mp hround))
      rw [Finset.card_range] at hbound
      omega

end SubmissionCounting

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.registration_count_le_one' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.registration_count_le_one

/-- info: 'Vegas.EventGraph.SealedFragment.submission_count_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.submission_count_le

/-- info: 'Vegas.EventGraph.SealedFragment.ready_poll_count_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.ready_poll_count_le

/-- info: 'Vegas.EventGraph.SealedFragment.completed_by_poll' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.completed_by_poll
