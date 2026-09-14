/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Finset
import Vegas.Compile.SealedCandidateReady
import Vegas.Compile.SealedCandidateProgress
import Interaction.SealedResolutionCompletion

/-! # Bounded honest polling in the candidate host

Every designated poll is charged to its actual selected graph site. Private
preparation can be charged only once; a submitted site completes at the next
service checkpoint. The finite charge bound is shared with the registered host.
All opponent policies and all traffic between the checkpoints are unrestricted.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
variable (supported : SealedFragment G ty) (nullValue : L.Val ty) (window : Nat)
    (players : Player →
      (supported.resolvingRuntime nullValue window).candidateApplication.PlayerPolicy)
    (environment : (supported.resolvingRuntime nullValue
      window).candidateApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Player))
    (trace : (supported.resolvingRuntime nullValue window).candidateApplication.PolicyTrace)
    (htrace : trace ∈
      ((supported.resolvingRuntime nullValue window).candidateApplication.tracePolicies players
        environment schedule (PolicyExecution.initial _ (State.initial _
          (supported.resolvingRuntime nullValue window).candidateInitial))).support)
    (who : Player) (policy : CommitPolicy G who)
    (hpolicy : players who = (supported.resolvingRuntime nullValue window).candidatePlayerPolicy
      (supported.resolvingPolicy nullValue window who policy))

include htrace hpolicy

private theorem candidate_preparation_not_later (earlier later slot : Nat)
    (hlt : earlier < later) (firstValue laterValue : L.Val ty)
    (hstep : (trace.drop (earlier + 1)).first ∈
      ((supported.resolvingRuntime nullValue window).candidateApplication.playerStep who
        (trace.drop earlier).first (.privateCommand ⟨(slot, firstValue)⟩)).support)
    (hlater : .privateCommand ⟨(slot, laterValue)⟩ ∈
      (players who ((trace.drop later).first.principalHistory who)
        (State.observe _ (trace.drop later).first.native who)).support) : False := by
  let runtime := supported.resolvingRuntime nullValue window
  let initial := PolicyExecution.initial runtime.candidateApplication
    (State.initial _ runtime.candidateInitial)
  let after := (trace.drop (earlier + 1)).first
  have hfixed : after.native.application.service.lookup (who, slot) ≠ .fresh := by
    simp only [playerStep, advance, PlayerCommand.toAction, MessageApplication.step,
      FinDist.pure_bind, FinDist.mem_support_pure] at hstep
    change after = _ at hstep
    rw [hstep]
    change (((trace.drop earlier).first.native.application.service).prepare
      who slot firstValue).lookup (who, slot) ≠ .fresh
    rw [CommitmentCandidates.lookup_prepare_self]
    split <;> simp
  have hprefix := (runtime.candidateApplication.tracePolicies_drop_support players environment
    schedule initial trace htrace (earlier + 1)).1
  have hbetween := runtime.candidateApplication.tracePolicies_between players environment
    schedule initial trace htrace (earlier + 1) (later - (earlier + 1))
  rw [Nat.add_sub_of_le (by omega : earlier + 1 ≤ later)] at hbetween
  exact supported.candidatePolicy_no_reregistration nullValue window who policy players environment
    hpolicy (schedule.take (earlier + 1))
    ((schedule.drop (earlier + 1)).take (later - (earlier + 1))) after
    (trace.drop later).first hprefix hbetween slot hfixed laterValue hlater

private theorem candidate_submission_completed_at_checkpoint
    (earlier checkpoint : Nat) (hafter : earlier + 1 ≤ checkpoint)
    (node : Fin G.nodeCount) (payload : SealedProgram.Payload Player (L.Val ty))
    (hnode : payload.node? = some node.val)
    (hcommand : .submit payload ∈
      (players who ((trace.drop earlier).first.principalHistory who)
        (State.observe _ (trace.drop earlier).first.native who)).support)
    (hstep : (trace.drop (earlier + 1)).first ∈
      ((supported.resolvingRuntime nullValue window).candidateApplication.playerStep who
        (trace.drop earlier).first (.submit payload)).support)
    (hservice : (supported.resolvingRuntime nullValue window).complete
        (trace.drop checkpoint).first.native.application.visible = true ∨
      (trace.drop checkpoint).first.native.pool.pending = []) :
    (trace.drop checkpoint).first.native.application.visible.completed node.val = true := by
  let runtime := supported.resolvingRuntime nullValue window
  let initial := PolicyExecution.initial runtime.candidateApplication
    (State.initial _ runtime.candidateInitial)
  rcases hservice with hcomplete | hempty
  · exact runtime.complete_node _ node.val hcomplete (by
      change node.val < supported.compile.rules.length
      simpa only [supported.compile_rules, List.length_map, Graph.nodeOrder,
        List.length_finRange] using node.isLt)
  · have hprefix := (runtime.candidateApplication.tracePolicies_drop_support players environment
      schedule initial trace htrace earlier).1
    have hbetween := runtime.candidateApplication.tracePolicies_between players environment
      schedule initial trace htrace (earlier + 1) (checkpoint - (earlier + 1))
    rw [Nat.add_sub_of_le hafter] at hbetween
    obtain ⟨found, hfound, hcompleted⟩ :=
      supported.candidatePolicy_submission_completed_of_drained nullValue window who policy
        players environment hpolicy (schedule.take earlier)
        ((schedule.drop (earlier + 1)).take (checkpoint - (earlier + 1)))
        (trace.drop earlier).first (trace.drop (earlier + 1)).first
        (trace.drop checkpoint).first hprefix payload hcommand hstep hbetween hempty
    have heq : found = node := Fin.ext (Option.some.inj (hfound.symm.trans hnode))
    exact heq ▸ hcompleted

/-- Every finite set of ready, unfinished honest polls obeys the graph-prefix
phase budget. A service checkpoint drains the actual queue or has completed
the whole application; successful validation is derived from the native policy. -/
theorem candidate_ready_poll_count_le (target : Fin G.nodeCount)
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
  let runtime := supported.resolvingRuntime nullValue window
  let initial := PolicyExecution.initial runtime.candidateApplication
    (State.initial _ runtime.candidateInitial)
  have hchoices : ∀ round, ∃ (selected : Fin G.nodeCount)
      (command : runtime.candidateApplication.PlayerCommand),
      round ∈ rounds → selected.val ≤ target.val ∧
        (trace.drop (position round)).first.native.application.visible.completed selected.val =
          false ∧
        supported.ProgressCommand who
          (runtime.eventHistory (runtime.registeredPlayerHistory
            ((trace.drop (position round)).first.principalHistory who))) selected command ∧
        command ∈ (players who ((trace.drop (position round)).first.principalHistory who)
          (State.observe _ (trace.drop (position round)).first.native who)).support ∧
        (trace.drop (position round + 1)).first ∈
          (runtime.candidateApplication.playerStep who (trace.drop (position round)).first
            command).support := by
    intro round
    by_cases hround : round ∈ rounds
    · have hprefix := (runtime.candidateApplication.tracePolicies_drop_support players environment
        schedule initial trace htrace (position round)).1
      have hinvoke := runtime.candidateApplication.tracePolicies_drop_invoke players environment
        schedule initial trace htrace (position round) (.player who) (hcall round hround)
      simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hinvoke
      obtain ⟨command, hcommand, hstep⟩ := hinvoke
      obtain ⟨selected, hbound, hselected, _, hphase⟩ :=
        supported.candidatePolicy_progress_of_ready nullValue window who policy players environment
          hpolicy (schedule.take (position round)) (trace.drop (position round)).first hprefix
          target
          (hnotDone round hround) (hrequires round hround) howned command hcommand
      exact ⟨selected, command, fun _ => ⟨hbound, hselected, hphase, hcommand, hstep⟩⟩
    · exact ⟨target, .wait, fun h => (hround h).elim⟩
  choose selected command hchosen using hchoices
  let preparation := fun site round => ∃ value : L.Val ty,
    command round = .privateCommand ⟨(site, value)⟩
  let submission := fun site round => ∃ payload : SealedProgram.Payload Player (L.Val ty),
    command round = .submit payload ∧ payload.node? = some site
  apply Finset.card_le_of_bounded_charges rounds (fun round => (selected round).val)
    (target.val + 1) delay preparation submission
  · intro round hround
    have := (hchosen round hround).1
    omega
  · intro round hround
    have hphase := (hchosen round hround).2.2.1
    change (∃ value : L.Val ty,
      command round = .privateCommand ⟨((selected round).val, value)⟩) ∨
        ∃ payload, command round = .submit payload ∧ payload.node? = some (selected round).val
    generalize command round = actual at hphase ⊢
    cases hphase with
    | registration => exact Or.inl ⟨_, rfl⟩
    | commitment => exact Or.inr ⟨_, rfl, rfl⟩
    | opening => exact Or.inr ⟨_, rfl, rfl⟩
  · intro site _ left hleft right hright hprepareLeft hprepareRight
    obtain ⟨leftValue, hleftValue⟩ := hprepareLeft
    obtain ⟨rightValue, hrightValue⟩ := hprepareRight
    have hleftStep := (hchosen left hleft).2.2.2.2
    have hrightStep := (hchosen right hright).2.2.2.2
    have hleftCommand := (hchosen left hleft).2.2.2.1
    have hrightCommand := (hchosen right hright).2.2.2.1
    rw [hleftValue] at hleftStep hleftCommand
    rw [hrightValue] at hrightStep hrightCommand
    rcases lt_trichotomy left right with hlt | heq | hgt
    · exact (supported.candidate_preparation_not_later nullValue window players environment
        schedule trace htrace who policy hpolicy (position left) (position right) site
        (hposition hlt) leftValue rightValue hleftStep hrightCommand).elim
    · exact heq
    · exact (supported.candidate_preparation_not_later nullValue window players environment
        schedule trace htrace who policy hpolicy (position right) (position left) site
        (hposition hgt) rightValue leftValue hrightStep hleftCommand).elim
  · intro site _ left hleft right hright hsubmitLeft hsubmitRight _hle
    obtain ⟨payload, hleftPayload, hnode⟩ := hsubmitLeft
    obtain ⟨rightPayload, hrightPayload, hrightNode⟩ := hsubmitRight
    have hphase := (hchosen left hleft).2.2.1
    rw [hleftPayload] at hphase
    have hselected : payload.node? = some (selected left).val := by cases hphase <;> rfl
    have hrightPhase := (hchosen right hright).2.2.1
    rw [hrightPayload] at hrightPhase
    have hrightSelected : rightPayload.node? = some (selected right).val := by
      cases hrightPhase <;> rfl
    have heq : selected left = selected right := Fin.ext
      (Option.some.inj (hselected.symm.trans hnode) |>.trans
        (Option.some.inj (hrightSelected.symm.trans hrightNode)).symm)
    by_contra hlate
    obtain ⟨checkpoint, hafter, hbefore, hserviced⟩ := hservice left hleft
    have hcommand := (hchosen left hleft).2.2.2.1
    have hstep := (hchosen left hleft).2.2.2.2
    rw [hleftPayload] at hcommand hstep
    have hcompleted := supported.candidate_submission_completed_at_checkpoint nullValue window
      players environment schedule trace htrace who policy hpolicy (position left) checkpoint
      hafter (selected left) payload hselected hcommand hstep hserviced
    have hretained := runtime.tracePolicies_completed
      (fun (service : CommitmentCandidates Player Nat (L.Val ty)) owner slot value =>
        service.prepare owner slot value)
      runtime.candidateHandle runtime.candidateHandle_records players environment schedule initial
      trace htrace checkpoint (position right)
      (hbefore.trans (hposition.monotone (by omega))) (selected left).val hcompleted
    rw [heq, (hchosen right hright).2.1] at hretained
    contradiction

/-- A target ready at the first designated poll has completed before the last
poll of any longer-than-budget polling interval. An unfinished last pre-state
would make every poll, including that last invocation, chargeable. This theorem
does not yet distinguish service completion from timeout completion. -/
theorem candidate_completed_by_poll (target : Fin G.nodeCount)
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
  let initial := PolicyExecution.initial runtime.candidateApplication
    (State.initial runtime.candidateApplication runtime.candidateInitial)
  have hmono : ∀ left right, left ≤ right → ∀ node,
      (trace.drop (position left)).first.native.application.visible.completed node = true →
      (trace.drop (position right)).first.native.application.visible.completed node = true := by
    intro left right hle node hcompleted
    exact runtime.tracePolicies_completed
      (fun (service : CommitmentCandidates Player Nat (L.Val ty)) owner slot value =>
        service.prepare owner slot value)
      runtime.candidateHandle runtime.candidateHandle_records players environment schedule
      initial trace htrace (position left) (position right) (hposition.monotone hle)
      node hcompleted
  cases hcompleted :
      (trace.drop (position (count - 1))).first.native.application.visible.completed target.val with
  | true => rfl
  | false =>
      have hbound := supported.candidate_ready_poll_count_le nullValue window players environment
        schedule trace htrace who policy hpolicy target howned position hposition delay
        (Finset.range count)
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

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.candidate_ready_poll_count_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.candidate_ready_poll_count_le


/-- info: 'Vegas.EventGraph.SealedFragment.candidate_completed_by_poll'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.candidate_completed_by_poll
