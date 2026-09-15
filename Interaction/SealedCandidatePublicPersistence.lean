/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedCandidateEvents

/-! # Persistence of completed candidate public events

Once a node has an included public event, later candidate traffic and deadline
resolution cannot add another event at that node.  This is a local event-log
fact and requires no policy, service, or global event-uniqueness assumption.
-/

noncomputable section

namespace Interaction.SealedProgram

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]

/-- Candidate admission certifies that the emitted event's node was not
already done in the validator's input event log. -/
theorem candidateMessage?_event_not_done
    (program : SealedProgram Principal)
    (candidates : CommitmentCandidates Principal Nat Value)
    (events : List (Event Principal Value))
    (message : Message Principal (Payload Principal Value))
    (result : CommitmentCandidates Principal Nat Value × Event Principal Value)
    (hresult : program.candidateMessage? candidates events message = some result) :
    done events result.2.node = false := by
  unfold candidateMessage? at hresult
  cases hpayload : message.payload with
  | malformed | cleartext => simp only [hpayload] at hresult; contradiction
  | commitment node handle =>
      simp only [hpayload] at hresult
      cases hrule : program.rules[node]? with
      | none => simp only [hrule] at hresult; contradiction
      | some rule =>
          simp only [hrule] at hresult
          cases hkind : rule.kind with
          | disabled | reveal => simp only [hkind] at hresult; contradiction
          | commit owner =>
              simp only [hkind] at hresult
              split at hresult
              · rename_i hchecks
                cases hresult
                exact hchecks.2.2.1
              · contradiction
  | opening node handle claimed =>
      simp only [hpayload] at hresult
      cases hrule : program.rules[node]? with
      | none => simp only [hrule] at hresult; contradiction
      | some rule =>
          simp only [hrule] at hresult
          cases hkind : rule.kind with
          | disabled | commit => simp only [hkind] at hresult; contradiction
          | reveal owner source =>
              simp only [hkind] at hresult
              split at hresult
              · rename_i hchecks
                cases hresult
                exact hchecks.2.2.1
              · contradiction

end Interaction.SealedProgram

namespace Interaction.SealedResolution

open MessageApplication GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]

private def eventsAt (events : List (SealedProgram.Event Principal Value))
    (node : Nat) : List (SealedProgram.Event Principal Value) :=
  events.filter fun event => event.node == node

omit [DecidableEq Principal] [DecidableEq Value] in
private theorem done_append_of_done
    (events suffix : List (SealedProgram.Event Principal Value)) (node : Nat)
    (hdone : SealedProgram.done events node = true) :
    SealedProgram.done (events ++ suffix) node = true := by
  simp only [SealedProgram.done, List.any_append, Bool.or_eq_true]
  exact Or.inl hdone

omit [DecidableEq Principal] [DecidableEq Value] in
private theorem eventsAt_append_other
    (events : List (SealedProgram.Event Principal Value))
    (event : SealedProgram.Event Principal Value) (node : Nat)
    (hother : event.node ≠ node) :
    eventsAt (events ++ [event]) node = eventsAt events node := by
  simp [eventsAt, hother]

omit [DecidableEq Principal] [DecidableEq Value] in
private theorem visit_eventsAt_of_done
    (runtime : SealedResolution Principal Value) (resolveExpired : Bool)
    (state : PublicState Principal Value) (visited node : Nat)
    (hdone : SealedProgram.done state.events node = true) :
    SealedProgram.done (runtime.visit resolveExpired state visited).events node = true ∧
      eventsAt (runtime.visit resolveExpired state visited).events node =
        eventsAt state.events node := by
  have hstate : SealedProgram.done state.events node = true ∧
      eventsAt state.events node = eventsAt state.events node := ⟨hdone, rfl⟩
  by_cases hsame : visited = node
  · subst visited
    cases hrule : runtime.program.rules[node]? with
    | none => simpa [SealedResolution.visit, hrule] using hstate
    | some rule =>
        simp only [SealedResolution.visit, hrule]
        have hcompleted : state.completed node = true := by
          simp [PublicState.completed, hdone]
        rw [hcompleted]
        exact ⟨hdone, rfl⟩
  · cases hrule : runtime.program.rules[visited]? with
    | none => simpa [SealedResolution.visit, hrule] using hstate
    | some rule =>
        have hstampDone :
            SealedProgram.done (state.stamp visited).events node = true := by
          simpa using hdone
        have hstampEvents : eventsAt (state.stamp visited).events node =
            eventsAt state.events node := by
          simp
        have happended :
            SealedProgram.done
                ((state.stamp visited).events ++
                  [.opened visited runtime.nullValue]) node = true ∧
              eventsAt
                  ((state.stamp visited).events ++
                    [.opened visited runtime.nullValue]) node =
                eventsAt state.events node := by
          refine ⟨done_append_of_done _ _ node hstampDone, ?_⟩
          exact (eventsAt_append_other _ _ node (by
            change visited ≠ node
            exact hsame)).trans hstampEvents
        cases hkind : rule.kind with
        | disabled =>
            simpa [SealedResolution.visit, hrule, hkind] using hstate
        | commit owner =>
            simp only [SealedResolution.visit, hrule]
            split
            · exact ⟨hdone, rfl⟩
            · simp only [hkind]
              split
              · simpa [SealedResolution.expire, hkind] using
                  And.intro hstampDone hstampEvents
              · exact ⟨hstampDone, hstampEvents⟩
        | reveal owner source =>
            simp only [SealedResolution.visit, hrule]
            split
            · exact ⟨hdone, rfl⟩
            · simp only [hkind]
              split
              · exact happended
              · split
                · simpa [SealedResolution.expire, hkind] using happended
                · exact ⟨hstampDone, hstampEvents⟩

omit [DecidableEq Principal] [DecidableEq Value] in
private theorem refresh_eventsAt_of_done
    (runtime : SealedResolution Principal Value) (resolveExpired : Bool)
    (state : PublicState Principal Value) (node : Nat)
    (hdone : SealedProgram.done state.events node = true) :
    SealedProgram.done (runtime.refresh resolveExpired state).events node = true ∧
      eventsAt (runtime.refresh resolveExpired state).events node =
        eventsAt state.events node := by
  unfold SealedResolution.refresh
  generalize List.range runtime.program.rules.length = nodes
  induction nodes generalizing state with
  | nil => exact ⟨hdone, rfl⟩
  | cons visited rest ih =>
      have hvisit := runtime.visit_eventsAt_of_done resolveExpired state visited node hdone
      exact ⟨(ih (runtime.visit resolveExpired state visited) hvisit.1).1,
        (ih (runtime.visit resolveExpired state visited) hvisit.1).2.trans hvisit.2⟩

private theorem candidateHandle_eventsAt_of_done
    (runtime : SealedResolution Principal Value)
    (state next : ApplicationState Principal Value
      (CommitmentCandidates Principal Nat Value))
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (node : Nat) (hdone : SealedProgram.done state.visible.events node = true)
    (hnext : runtime.candidateHandle state message = some next) :
    SealedProgram.done next.visible.events node = true ∧
      eventsAt next.visible.events node = eventsAt state.visible.events node := by
  unfold SealedResolution.candidateHandle at hnext
  split at hnext
  · contradiction
  · cases hmessage : (runtime.program.discharge state.visible.timeouts).candidateMessage?
        state.service state.visible.events message with
    | none => simp [hmessage] at hnext
    | some result =>
        simp only [hmessage, Option.bind_eq_bind, Option.bind_some,
          Option.some.injEq] at hnext
        subst next
        have hother : result.2.node ≠ node := by
          intro heq
          have hnotDone :=
            (runtime.program.discharge state.visible.timeouts).candidateMessage?_event_not_done
              state.service state.visible.events message result hmessage
          rw [heq, hdone] at hnotDone
          contradiction
        let recorded : PublicState Principal Value :=
          { state.visible with events := state.visible.events ++ [result.2] }
        have hrecordedDone : SealedProgram.done recorded.events node = true := by
          exact done_append_of_done _ _ node hdone
        have hrecordedEvents : eventsAt recorded.events node =
            eventsAt state.visible.events node := by
          simp [recorded, eventsAt, hother]
        have hrefresh := runtime.refresh_eventsAt_of_done false recorded node hrecordedDone
        exact ⟨hrefresh.1, hrefresh.2.trans hrecordedEvents⟩

/-- Once a node is done in the included candidate event log, arbitrary later
candidate traffic and timeout continuation preserve exactly the prior event
occurrences at that node, including their order and multiplicity. -/
theorem runPolicies_candidate_events_at_done
    (runtime : SealedResolution Principal Value)
    (players : Principal → runtime.candidateApplication.PlayerPolicy)
    (environment : runtime.candidateApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Principal))
    (initial next : runtime.candidateApplication.PolicyExecution)
    (node : Nat)
    (hdone : SealedProgram.done initial.native.application.visible.events node = true)
    (hnext : next ∈ (runtime.candidateApplication.runPolicies
      players environment schedule initial).support) :
    next.native.application.visible.events.filter (fun event => event.node == node) =
      initial.native.application.visible.events.filter (fun event => event.node == node) := by
  have hinvariant := runtime.candidateApplication.runPolicies_application_invariant
    (fun state => SealedProgram.done state.visible.events node = true ∧
      eventsAt state.visible.events node = eventsAt initial.native.application.visible.events node)
    (by intro state owner command hstate; exact hstate)
    (by
      intro state message after hstate hafter
      exact runtime.candidateHandle_eventsAt_of_done state after message node hstate.1 hafter |>
        fun preserved => ⟨preserved.1, preserved.2.trans hstate.2⟩)
    (by
      intro state command after hstate hafter
      simp only [candidateApplication, host, FinDist.mem_support_pure] at hafter
      subst after
      have hrefresh := runtime.refresh_eventsAt_of_done true
        { state.visible with clock := state.visible.clock + 1 } node hstate.1
      exact ⟨hrefresh.1, hrefresh.2.trans hstate.2⟩)
    players environment schedule initial next ⟨hdone, rfl⟩ hnext
  exact hinvariant.2

end Interaction.SealedResolution

/-- info: 'Interaction.SealedResolution.runPolicies_candidate_events_at_done'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.runPolicies_candidate_events_at_done
