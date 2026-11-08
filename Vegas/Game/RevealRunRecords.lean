/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealRunPath

/-! # The records a round adds

A round completes at most one event by a decision: the event of the packet it
includes, or the event it expires, which was ready when the round began. Every
other record the round adds is an automatic completion without a decision. So
in a round of a run, while the deviator's earliest pending reveal is `target`,
the deviator records no decision except at `target`.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {mode : EventGraph.ExecutionMode} {duration : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- **A round's new records.** Every record a round adds, from an execution
whose ready events are reveals, records no decision, or completes an event that
was ready when the round began. -/
theorem round_new_record_ready
    {scheduler : (serviceApplication setup mode duration leaks).Scheduler}
    {players : Player → (serviceApplication setup mode duration leaks).Policy}
    (current next : (serviceApplication setup mode duration leaks).Execution)
    (publications : ∀ event, current.application.config.cut.Ready event →
      ((serviceGraph setup mode).outputLayout event).IsPublication)
    (reached : next ∈ ((serviceApplication setup mode duration leaks).round scheduler players
      current).support)
    (event : (serviceGraph setup mode).EventId)
    (fresh : event ∉ current.application.config.cut.completed)
    (done : event ∈ next.application.config.cut.completed) :
    (∀ record, completionOf next.application.config event = some record →
      record.decision = none) ∨ current.application.config.cut.Ready event := by
  classical
  let app := serviceApplication setup mode duration leaks
  let timeouts := serviceTimeouts setup mode duration
  obtain ⟨command, selected, middle, moved, cases⟩ := round_cases setup leaks reached
  have nextConfig : next.application.config = middle.application.config := by
    rcases cases with ⟨_, rfl⟩ | ⟨actor, _, response, _, rfl⟩
    · rfl
    · exact (reactive_respond_application timeouts leaks middle actor response).1
  rw [nextConfig] at done ⊢
  obtain ⟨record, recorded⟩ := Option.isSome_iff_exists.mp
    ((completionOf_isSome_iff middle.application.config event).mpr done)
  obtain ⟨present, recordEvent⟩ :=
    (completionOf_eq_some_iff middle.application.config event record).mp recorded
  have newRecord : record ∉ current.application.config.history := fun inside =>
    fresh ((current.application.config.history_exact event).mp
      (List.mem_map.mpr ⟨record, inside, recordEvent⟩))
  have silentOf (silent : record.decision = none) :
      ∀ other, completionOf middle.application.config event = some other →
        other.decision = none := by
    intro other found
    rw [recorded] at found
    cases found
    exact silent
  cases command with
  | activate actor =>
      have same := activation_application setup leaks current middle actor moved
      rw [same] at done
      exact (fresh done).elim
  | wait =>
      obtain ⟨updated, supported', rfl⟩ := PMF.support_map .. ▸ moved
      cases (PMF.mem_support_pure_iff _ _).mp supported'
      exact (fresh done).elim
  | «include» id =>
      obtain ⟨updated, supported', rfl⟩ := PMF.support_map .. ▸ moved
      cases (PMF.mem_support_pure_iff _ _).mp supported'
      cases found : current.network.lookup id with
      | none =>
          exact (fresh (by simpa only [ReactiveApplication.Execution.includePending,
            MessageNetwork.includePending, found] using done)).elim
      | some message =>
          cases accepted : app.handle current.application message with
          | none =>
              have unchanged : (current.includePending app id).application =
                  current.application := by
                simp only [ReactiveApplication.Execution.includePending,
                  MessageNetwork.includePending, found, accepted, Option.getD_none]
              exfalso
              apply fresh
              change event ∈ (current.includePending app id).application.config.cut.completed
                at done
              rw [unchanged] at done
              exact done
          | some after =>
              have applicationEq : (current.includePending app id).application = after := by
                simp only [ReactiveApplication.Execution.includePending,
                  MessageNetwork.includePending, found, accepted, Option.getD_some]
              obtain ⟨native, handled, drained⟩ := reactiveHandle_call accepted
              have middleDrain : native.drain.config =
                  ({ current.includePending app id with environmentRecall :=
                    current.environmentRecall ++ [⟨current.observeEnvironment app,
                      .include id⟩] } : app.Execution).application.config := by
                change native.drain.config = (current.includePending app id).application.config
                rw [applicationEq, drained]
              rw [← middleDrain] at present
              cases call : message.payload.call with
              | malformed raw =>
                  rw [call] at handled
                  simp [handle] at handled
              | commitment named candidate =>
                  rw [call] at handled
                  obtain ⟨_, readyNamed, _, owner, payload, outputEq, codeEq, _⟩ :=
                    (handle_commitment_iff timeouts current.application native message.id named
                      candidate).mp handled
                  have publication := publications named readyNamed
                  rw [outputEq] at publication
                  exact publication.elim
              | opening named candidate raw =>
                  rw [call] at handled
                  obtain ⟨readyNamed, action, member, -⟩ := handle_opening_config_step timeouts
                    current.application native message.id named candidate raw handled
                  rcases newRecord_step_drain current.application.config native named readyNamed
                      action member record newRecord present with
                    ⟨_, value, recordEq⟩ | ⟨silent, -⟩
                  · have eventEq : event = named := by rw [← recordEvent, recordEq]; rfl
                    subst eventEq
                    exact Or.inr readyNamed
                  · exact Or.inl (silentOf silent)
  | application operation =>
      obtain ⟨updated, supported', rfl⟩ := PMF.support_map .. ▸ moved
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported'
      change state ∈ ((EventGraphRuntime.environmentStep timeouts current.application
        operation).map EventGraphRuntime.State.drain).support at changed
      obtain ⟨native, nativeMoved, rfl⟩ := PMF.support_map .. ▸ changed
      rcases completionStep_environmentStep timeouts current.application native operation
          nativeMoved with ⟨same, _, _⟩ | ⟨stepped, readyStepped, action, member, _, _⟩
      · have fresh' : record ∉ native.config.history := by rw [same]; exact newRecord
        obtain ⟨silent, -⟩ := drainRecord_of_not_mem native record fresh' present
        exact Or.inl (silentOf silent)
      rcases newRecord_step_drain current.application.config native stepped readyStepped action
          member record newRecord present with
        ⟨_, value, recordEq⟩ | ⟨silent, -⟩
      · have eventEq : event = stepped := by rw [← recordEvent, recordEq]; rfl
        subst eventEq
        exact Or.inr readyStepped
      · exact Or.inl (silentOf silent)

end Vegas
