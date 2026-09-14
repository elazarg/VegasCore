/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedCandidateOpening
import Interaction.SealedCandidateEvents
import Interaction.MessageApplicationMessageInvariant

/-! # Unique authenticated candidate acceptance

The public log selects one handle per source site, independently of its
openability. Acceptance authenticates the rule owner, and later traffic and
deadline resolution preserve the selected handle. These are properties of
arbitrary policy runs, not obligations imposed on a deviator.
-/

noncomputable section

namespace Interaction.SealedProgram

universe uPrincipal uValue
variable {Principal : Type uPrincipal} {Value : Type uValue}

variable [DecidableEq Principal] [DecidableEq Value]

theorem candidateMessage?_accepted_owner (program : SealedProgram Principal)
    (candidates next : CommitmentCandidates Principal Nat Value)
    (events : List (Event Principal Value))
    (message : Message Principal (Payload Principal Value)) (node : Nat)
    (handle : CommitmentHandle Principal Nat)
    (hvalid : program.candidateMessage? candidates events message =
      some (next, .accepted node handle)) :
    (∃ requires, program.rules[node]? = some ⟨.commit handle.1, requires⟩) ∧
      done events node = false ∧ message.sender = handle.1 := by
  rcases program.candidateMessage?_effect candidates events message _ hvalid with
    ⟨index, selected, hpayload, heq⟩ | ⟨index, selected, value, _hpayload, heq⟩
  · cases heq
    simp only [candidateMessage?, hpayload] at hvalid
    cases hrule : program.rules[node]? with
    | none => simp [hrule] at hvalid
    | some rule =>
        simp only [hrule] at hvalid
        cases hkind : rule.kind with
        | disabled | reveal => simp only [hkind] at hvalid; contradiction
        | commit owner =>
            simp only [hkind] at hvalid
            split at hvalid
            next hchecks =>
              refine ⟨⟨rule.requires, ?_⟩, hchecks.2.2.1, hchecks.1.trans hchecks.2.1.symm⟩
              have hshape : rule = ⟨.commit handle.1, rule.requires⟩ := by
                cases rule
                simp_all
              exact congrArg some hshape
            next => contradiction
  · cases heq

end Interaction.SealedProgram

namespace Interaction.SealedResolution

open MessageApplication GameTheory.Math.Probability

universe uPrincipal uValue
variable {Principal : Type uPrincipal} {Value : Type uValue}
variable (runtime : SealedResolution Principal Value)

private theorem accepted?_stamp (state : PublicState Principal Value) (visited node : Nat) :
    SealedProgram.accepted? (state.stamp visited).events node =
      SealedProgram.accepted? state.events node := by
  unfold PublicState.stamp
  split <;> rfl

private theorem accepted?_append_opened (events : List (SealedProgram.Event Principal Value))
    (visited node : Nat) (value : Value) :
    SealedProgram.accepted? (events ++ [.opened visited value]) node =
      SealedProgram.accepted? events node := by
  simp [SealedProgram.accepted?, List.findSome?_append]

private theorem expire_accepted? (state : PublicState Principal Value) (visited node : Nat)
    (kind : SealedRuleKind Principal) :
    SealedProgram.accepted? (runtime.expire state visited kind).events node =
      SealedProgram.accepted? state.events node := by
  cases kind <;> simp only [expire, accepted?_append_opened]

private theorem visit_accepted? (resolveExpired : Bool) (state : PublicState Principal Value)
    (visited node : Nat) :
    SealedProgram.accepted? (runtime.visit resolveExpired state visited).events node =
      SealedProgram.accepted? state.events node := by
  unfold visit
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · dsimp only
        split
        · exact (accepted?_append_opened _ _ _ _).trans (accepted?_stamp _ _ _)
        · split
          · exact (runtime.expire_accepted? _ _ _ _).trans (accepted?_stamp _ _ _)
          · exact accepted?_stamp _ _ _
      · dsimp only
        split
        · exact (runtime.expire_accepted? _ _ _ _).trans (accepted?_stamp _ _ _)
        · exact accepted?_stamp _ _ _

/-- Clock scans and propagated defaults do not change the first accepted handle. -/
theorem refresh_accepted? (resolveExpired : Bool) (state : PublicState Principal Value)
    (node : Nat) :
    SealedProgram.accepted? (runtime.refresh resolveExpired state).events node =
      SealedProgram.accepted? state.events node := by
  unfold refresh
  generalize List.range runtime.program.rules.length = nodes
  induction nodes generalizing state with
  | nil => rfl
  | cons visited rest ih =>
      exact (ih (runtime.visit resolveExpired state visited)).trans
        (runtime.visit_accepted? resolveExpired state visited node)

/-- Every accepted event names the site's unique selection and its rule owner. -/
def CandidateAcceptanceInvariant (state : PublicState Principal Value) : Prop :=
  ∀ node handle, SealedProgram.Event.accepted node handle ∈ state.events →
    SealedProgram.accepted? state.events node = some handle ∧
      ∃ requires, runtime.program.rules[node]? = some ⟨.commit handle.1, requires⟩

namespace CandidateAcceptanceInvariant

variable {runtime} {state : PublicState Principal Value}

theorem refresh (invariant : CandidateAcceptanceInvariant runtime state) (resolveExpired : Bool) :
    CandidateAcceptanceInvariant runtime (runtime.refresh resolveExpired state) := by
  intro node handle hmem
  rw [runtime.refresh_accepted?]
  exact invariant node handle
    ((runtime.refresh_accepted_iff resolveExpired state node handle).mp hmem)

theorem initial : CandidateAcceptanceInvariant runtime runtime.candidateInitial.visible := by
  exact (show CandidateAcceptanceInvariant runtime {} from by
    simp [CandidateAcceptanceInvariant]).refresh false

variable [DecidableEq Principal] [DecidableEq Value]

theorem handle {application next : ApplicationState Principal Value
      (CommitmentCandidates Principal Nat Value)}
    (invariant : CandidateAcceptanceInvariant runtime application.visible)
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (hnext : runtime.candidateHandle application message = some next) :
    CandidateAcceptanceInvariant runtime next.visible := by
  unfold candidateHandle at hnext
  split at hnext
  · contradiction
  · cases hmessage : (runtime.program.discharge application.visible.timeouts).candidateMessage?
        application.service application.visible.events message with
    | none => simp [hmessage] at hnext
    | some result =>
        simp only [hmessage, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hnext
        subst next
        apply CandidateAcceptanceInvariant.refresh (resolveExpired := false)
        intro node handle hmem
        simp only [List.mem_append, List.mem_singleton] at hmem
        rcases hmem with hprior | hnew
        · obtain ⟨hread, hrule⟩ := invariant node handle hprior
          exact ⟨SealedProgram.accepted?_append_of_some _ _ node handle hread, hrule⟩
        · obtain ⟨⟨requires, hrule⟩, hnot, _hsender⟩ :=
            SealedProgram.candidateMessage?_accepted_owner
              (runtime.program.discharge application.visible.timeouts)
              application.service result.1 application.visible.events message node handle
              (by simpa only [hnew] using hmessage)
          refine ⟨?_, ?_⟩
          · have hnone := SealedProgram.accepted?_none_of_not_done _ node hnot
            rw [← hnew]
            simp only [SealedProgram.accepted?, List.findSome?_append] at hnone ⊢
            simp [hnone]
          · simp only [SealedProgram.discharge, List.getElem?_map] at hrule
            cases horiginal : runtime.program.rules[node]? with
            | none => simp [horiginal] at hrule
            | some rule =>
                simp only [horiginal, Option.map_some, Option.some.injEq] at hrule
                refine ⟨rule.requires, ?_⟩
                have hshape : rule = ⟨.commit handle.1, rule.requires⟩ := by
                  cases rule
                  simp_all [SealedRule.discharge]
                exact congrArg some hshape

end CandidateAcceptanceInvariant

variable [DecidableEq Principal] [DecidableEq Value]

theorem runPolicies_candidate_acceptance
    (players : Principal → runtime.candidateApplication.PlayerPolicy)
    (environment : runtime.candidateApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Principal))
    (execution next : runtime.candidateApplication.PolicyExecution)
    (hinitial : CandidateAcceptanceInvariant runtime execution.native.application.visible)
    (hnext : next ∈ (runtime.candidateApplication.runPolicies
      players environment schedule execution).support) :
    CandidateAcceptanceInvariant runtime next.native.application.visible := by
  apply runtime.candidateApplication.runPolicies_application_invariant
    (fun state => CandidateAcceptanceInvariant runtime state.visible) ?_ ?_ ?_
    players environment schedule execution next hinitial hnext
  · intro state owner command hstate
    exact hstate
  · intro state message result hstate hresult
    exact hstate.handle message hresult
  · intro state command result hstate hresult
    simp only [candidateApplication, host, FinDist.mem_support_pure] at hresult
    subst result
    have hclock : CandidateAcceptanceInvariant runtime
        { state.visible with clock := state.visible.clock + 1 } := hstate
    exact hclock.refresh true

/-- The selected pointer persists under arbitrary suffix policies, even after timeout. -/
theorem runPolicies_candidate_accepted?
    (players : Principal → runtime.candidateApplication.PlayerPolicy)
    (environment : runtime.candidateApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Principal))
    (execution next : runtime.candidateApplication.PolicyExecution)
    (node : Nat) (handle : CommitmentHandle Principal Nat)
    (hread : SealedProgram.accepted? execution.native.application.visible.events node = some handle)
    (hnext : next ∈ (runtime.candidateApplication.runPolicies
      players environment schedule execution).support) :
    SealedProgram.accepted? next.native.application.visible.events node = some handle := by
  apply runtime.candidateApplication.runPolicies_application_invariant
    (fun state => SealedProgram.accepted? state.visible.events node = some handle) ?_ ?_ ?_
    players environment schedule execution next hread hnext
  · intro state owner command hstate
    exact hstate
  · intro state message result hstate hresult
    change runtime.candidateHandle state message = some result at hresult
    unfold candidateHandle at hresult
    split at hresult
    · contradiction
    · cases hmessage : (runtime.program.discharge state.visible.timeouts).candidateMessage?
          state.service state.visible.events message with
      | none => simp [hmessage] at hresult
      | some admitted =>
          simp only [hmessage, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hresult
          subst result
          rw [runtime.refresh_accepted?]
          exact SealedProgram.accepted?_append_of_some _ _ node handle hstate
  · intro state command result hstate hresult
    simp only [candidateApplication, host, FinDist.mem_support_pure] at hresult
    subst result
    exact (runtime.refresh_accepted? true _ node).trans hstate

/-- Every accepted commitment inherits any property of supported authenticated
submissions. Retained packets preserve the property through delivery and replay;
unrelated submissions and private candidate preparation remain unrestricted. -/
theorem runPolicies_candidate_accepted_property
    (property : Nat → CommitmentHandle Principal Nat → Prop)
    (players : Principal → runtime.candidateApplication.PlayerPolicy)
    (environment : runtime.candidateApplication.EnvironmentPolicy)
    (hsubmit : ∀ (execution : runtime.candidateApplication.PolicyExecution) sender payload,
      .submit payload ∈ (players sender (execution.principalHistory sender)
        (State.observe _ execution.native sender)).support →
      ∀ node handle, payload = .commitment node handle → sender = handle.1 → property node handle)
    (schedule : List (@Invocation Principal)) (next : runtime.candidateApplication.PolicyExecution)
    (hnext : next ∈ (runtime.candidateApplication.runPolicies players environment schedule
      (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial))).support) :
    ∀ node handle, SealedProgram.Event.accepted node handle ∈
      next.native.application.visible.events → property node handle := by
  let safe := fun message : Message Principal (SealedProgram.Payload Principal Value) =>
    ∀ node handle, message.payload = .commitment node handle →
      message.sender = handle.1 → property node handle
  let invariant := fun state : runtime.candidateApplication.Application =>
    ∀ node handle, SealedProgram.Event.accepted node handle ∈ state.visible.events →
      property node handle
  have hresult := runtime.candidateApplication.runPolicies_message_application_invariant
    safe invariant (fun _ _ _ hstate => hstate) (by
      intro state message result hstate hsafe hresult
      change runtime.candidateHandle state message = some result at hresult
      unfold candidateHandle at hresult
      split at hresult
      · contradiction
      · cases hmessage : (runtime.program.discharge state.visible.timeouts).candidateMessage?
            state.service state.visible.events message with
        | none => simp [hmessage] at hresult
        | some admitted =>
            simp only [hmessage, Option.bind_eq_bind, Option.bind_some,
              Option.some.injEq] at hresult
            subst result
            intro node handle hmem
            have hbefore := (runtime.refresh_accepted_iff false
              { state.visible with events := state.visible.events ++ [admitted.2] }
              node handle).mp hmem
            simp only [List.mem_append, List.mem_singleton] at hbefore
            rcases hbefore with hprior | hnew
            · exact hstate node handle hprior
            · have hvalid : (runtime.program.discharge state.visible.timeouts).candidateMessage?
                  state.service state.visible.events message =
                    some (admitted.1, .accepted node handle) := by
                simpa only [hnew] using hmessage
              have hsender := ((runtime.program.discharge state.visible.timeouts
                ).candidateMessage?_accepted_owner state.service admitted.1 state.visible.events
                  message node handle hvalid).2.2
              rcases (runtime.program.discharge state.visible.timeouts).candidateMessage?_effect
                  state.service state.visible.events message _ hvalid with
                ⟨index, selected, hpayload, heq⟩ | ⟨index, selected, value, _hp, heq⟩
              · have hevent := congrArg Prod.snd heq
                cases hevent
                exact hsafe node handle hpayload hsender
              · have hevent := congrArg Prod.snd heq
                cases hevent) (by
      intro state command result hstate hresult
      simp only [candidateApplication, host, FinDist.mem_support_pure] at hresult
      subst result
      intro node handle hmem
      exact hstate node handle ((runtime.refresh_accepted_iff true
        { state.visible with clock := state.visible.clock + 1 } node handle).mp hmem))
    players environment (fun execution sender payload hchosen _serial =>
      hsubmit execution sender payload hchosen) schedule _ next MessagePool.Satisfies.empty
    (by
      intro node handle hmem
      have hnone := (runtime.refresh_accepted_iff false {} node handle).mp hmem
      exact False.elim (List.not_mem_nil hnone)) hnext
  exact hresult.2

/-- Reading at a site's first acceptance or at the common first-timeout
checkpoint gives the same selected handle and meaning. The whole trace may
continue after timeout. Candidate preparation and player policies are arbitrary. -/
theorem tracePolicies_candidate_acceptance_checkpoint
    (players : Principal → runtime.candidateApplication.PlayerPolicy)
    (environment : runtime.candidateApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Principal))
    (trace : runtime.candidateApplication.PolicyTrace)
    (htrace : trace ∈ (runtime.candidateApplication.tracePolicies players environment schedule
      (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial))).support)
    (node : Nat) (owner : Principal) (requires : List Nat)
    (hrule : runtime.program.rules[node]? = some ⟨.commit owner, requires⟩) :
    let selected := trace.firstRelease (fun execution :
        runtime.candidateApplication.PolicyExecution =>
      SealedProgram.done execution.native.application.visible.events node ||
        !execution.native.application.visible.timeouts.isEmpty)
    let stopped := trace.firstRelease (fun execution :
        runtime.candidateApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty)
    SealedProgram.accepted? selected.native.application.visible.events node =
        SealedProgram.accepted? stopped.native.application.visible.events node ∧
      ∀ handle, SealedProgram.accepted? selected.native.application.visible.events node =
        some handle → selected.native.application.service.lookup handle =
          stopped.native.application.service.lookup handle := by
  intro selected stopped
  let read := fun execution : runtime.candidateApplication.PolicyExecution =>
    SealedProgram.accepted? execution.native.application.visible.events node
  let cutoff := fun execution : runtime.candidateApplication.PolicyExecution =>
    !execution.native.application.visible.timeouts.isEmpty
  have hcut := runtime.candidateApplication.tracePolicies_firstRelease_congr players environment
    (fun execution => SealedProgram.done execution.native.application.visible.events node ||
      cutoff execution) (fun execution => (read execution).isSome || cutoff execution)
    schedule _ trace htrace (by
      intro front execution hexecution
      have hpublic := runtime.runPolicies_candidate_publicEvents players environment front
        _ execution (PublicEventInvariant.initial runtime) hexecution
      rw [hpublic.done_eq_accepted_isSome runtime node owner requires hrule])
  have hread : read selected = read stopped := by
    change read (trace.firstRelease _) = read (trace.firstRelease cutoff)
    rw [hcut]
    exact runtime.candidateApplication.tracePolicies_firstRelease_option players environment
      read cutoff (fun front before after hafter handle hhandle =>
        runtime.runPolicies_candidate_accepted? players environment front before after node
          handle hhandle hafter) schedule _ trace htrace
  refine ⟨hread, ?_⟩
  intro handle hhandle
  have hstopped : read stopped = some handle := hread.symm.trans hhandle
  have hselected := (runtime.tracePolicies_candidate_accepted_frozen players environment
    schedule trace htrace _ node handle hhandle).2
  have hstop := (runtime.tracePolicies_candidate_accepted_frozen players environment
    schedule trace htrace cutoff node handle hstopped).2
  exact hselected.symm.trans hstop

end Interaction.SealedResolution

/-- info: 'Interaction.SealedResolution.runPolicies_candidate_acceptance' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.runPolicies_candidate_acceptance

/-- info: 'Interaction.SealedResolution.tracePolicies_candidate_acceptance_checkpoint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.tracePolicies_candidate_acceptance_checkpoint
