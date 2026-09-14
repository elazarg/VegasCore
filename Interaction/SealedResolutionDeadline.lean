/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedResolutionProgress
import Interaction.SealedResolutionEvents

/-! # Readiness and timeout provenance

Readiness timestamps are created only by a scan of an actual ready rule, at
the scan's current clock.  A timeout therefore carries both a genuine retained
timestamp and a deadline that has elapsed on the public clock.
-/

noncomputable section

namespace Interaction.SealedResolution

open GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}

def PublicState.ReadySound (runtime : SealedResolution Principal Value)
    (state : PublicState Principal Value) : Prop :=
  ∀ node timestamp, state.firstReady? node = some timestamp →
    ∃ rule, runtime.program.rules[node]? = some rule ∧
      rule.requires.all state.completed = true

def PublicState.DeadlineSound (runtime : SealedResolution Principal Value)
    (state : PublicState Principal Value) : Prop :=
  ∀ node, node ∈ state.timeouts →
    ∃ rule timestamp,
      runtime.program.rules[node]? = some rule ∧
      state.firstReady? node = some timestamp ∧
      timestamp + runtime.window ≤ state.clock ∧
      rule.requires.all state.completed = true

private theorem findSome?_append_of_none {α β : Type*} (f : α → Option β)
    (left right : List α) (h : left.findSome? f = none) :
    (left ++ right).findSome? f = right.findSome? f := by
  induction left with
  | nil => rfl
  | cons head tail ih =>
      cases hhead : f head with
      | none => simpa [hhead] using ih (by simpa [hhead] using h)
      | some found => simp [hhead] at h

private theorem PublicState.firstReady?_stamp_origin
    (state : PublicState Principal Value) (stamped target timestamp : Nat)
    (hready : (state.stamp stamped).firstReady? target = some timestamp) :
    state.firstReady? target = some timestamp ∨
      target = stamped ∧ timestamp = state.clock := by
  cases hstamped : state.firstReady? stamped with
  | some prior =>
      left
      simpa [PublicState.stamp, hstamped] using hready
  | none =>
      rw [show state.stamp stamped =
          { state with readyAt := state.readyAt ++ [(stamped, state.clock)] } by
        simp [PublicState.stamp, hstamped]] at hready
      cases htarget : state.firstReady? target with
      | some prior =>
          left
          have hpersist := state.firstReady?_stamp_of_some stamped target prior htarget
          rw [show state.stamp stamped =
              { state with readyAt := state.readyAt ++ [(stamped, state.clock)] } by
            simp [PublicState.stamp, hstamped]] at hpersist
          have heq : prior = timestamp := Option.some.inj (hpersist.symm.trans hready)
          subst timestamp
          rfl
      | none =>
          right
          unfold PublicState.firstReady? at hready htarget
          rw [findSome?_append_of_none _ _ _ htarget] at hready
          simp only [List.findSome?_singleton] at hready
          split at hready
          · rename_i heq
            exact ⟨heq.symm, Option.some.inj hready |>.symm⟩
          · contradiction

private theorem all_completed_visit
    (runtime : SealedResolution Principal Value) (resolveExpired : Bool)
    (state : PublicState Principal Value) (visited : Nat) (nodes : List Nat)
    (hall : nodes.all state.completed = true) :
    nodes.all (runtime.visit resolveExpired state visited).completed = true := by
  apply List.all_eq_true.mpr
  intro node hnode
  exact runtime.visit_completed resolveExpired state visited node
    (List.all_eq_true.mp hall node hnode)

private theorem fold_firstReady?_of_some
    (runtime : SealedResolution Principal Value) (resolveExpired : Bool)
    (nodes : List Nat) (state : PublicState Principal Value) (target timestamp : Nat)
    (hready : state.firstReady? target = some timestamp) :
    (nodes.foldl (runtime.visit resolveExpired) state).firstReady? target = some timestamp := by
  induction nodes generalizing state with
  | nil => exact hready
  | cons node rest ih =>
      exact ih (runtime.visit resolveExpired state node)
        (runtime.visit_firstReady?_of_some resolveExpired state node target timestamp hready)

private theorem fold_clock
    (runtime : SealedResolution Principal Value) (resolveExpired : Bool)
    (nodes : List Nat) (state : PublicState Principal Value) :
    (nodes.foldl (runtime.visit resolveExpired) state).clock = state.clock := by
  induction nodes generalizing state with
  | nil => rfl
  | cons node rest ih =>
      exact (ih (runtime.visit resolveExpired state node)).trans
        (runtime.visit_clock resolveExpired state node)

private theorem fold_all_completed
    (runtime : SealedResolution Principal Value) (resolveExpired : Bool)
    (nodes targets : List Nat) (state : PublicState Principal Value)
    (hall : targets.all state.completed = true) :
    targets.all (nodes.foldl (runtime.visit resolveExpired) state).completed = true := by
  induction nodes generalizing state with
  | nil => exact hall
  | cons node rest ih =>
      exact ih (runtime.visit resolveExpired state node)
        (all_completed_visit runtime resolveExpired state node targets hall)

private theorem visit_firstReady?_eq_stamp
    (runtime : SealedResolution Principal Value) (resolveExpired : Bool)
    (state : PublicState Principal Value) (visited target : Nat)
    (rule : SealedRule Principal) (hrule : runtime.program.rules[visited]? = some rule)
    (hcompleted : state.completed visited = false)
    (hrequires : rule.requires.all state.completed = true)
    (hkind : rule.kind ≠ .disabled) :
    (runtime.visit resolveExpired state visited).firstReady? target =
      (state.stamp visited).firstReady? target := by
  cases rule with
  | mk kind requires =>
      cases kind with
      | disabled => exact False.elim (hkind rfl)
      | commit owner =>
          simp only [SealedResolution.visit, hrule, hcompleted, Bool.false_or,
            hrequires, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          split <;> simp [SealedResolution.expire, PublicState.firstReady?]
      | reveal owner source =>
          simp only [SealedResolution.visit, hrule, hcompleted, Bool.false_or,
            hrequires, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          split
          · simp [PublicState.firstReady?]
          · split <;> simp [SealedResolution.expire, PublicState.firstReady?]

private theorem visit_firstReady?_origin
    (runtime : SealedResolution Principal Value) (resolveExpired : Bool)
    (state : PublicState Principal Value) (visited target timestamp : Nat)
    (hready : (runtime.visit resolveExpired state visited).firstReady? target =
      some timestamp) :
    state.firstReady? target = some timestamp ∨
      target = visited ∧ timestamp = state.clock ∧
        ∃ rule, runtime.program.rules[visited]? = some rule ∧
          rule.requires.all (runtime.visit resolveExpired state visited).completed = true := by
  cases hrule : runtime.program.rules[visited]? with
  | none => exact Or.inl (by simpa [SealedResolution.visit, hrule] using hready)
  | some rule =>
      by_cases hcompleted : state.completed visited = true
      · exact Or.inl (by simpa [SealedResolution.visit, hrule, hcompleted] using hready)
      · have hcompletedFalse := Bool.eq_false_of_not_eq_true hcompleted
        cases hrequires : rule.requires.all state.completed with
        | false =>
            exact Or.inl (by simpa [SealedResolution.visit, hrule, hcompletedFalse,
              hrequires] using hready)
        | true =>
            have hafterRequires :=
              all_completed_visit runtime resolveExpired state visited rule.requires hrequires
            cases hkind : rule.kind with
            | disabled =>
                exact Or.inl (by
                  simpa [SealedResolution.visit, hrule, hcompletedFalse, hrequires, hkind]
                    using hready)
            | commit owner =>
                have hstamp : (state.stamp visited).firstReady? target = some timestamp := by
                  rw [← runtime.visit_firstReady?_eq_stamp resolveExpired state visited target
                    rule hrule hcompletedFalse hrequires (by simp [hkind])]
                  exact hready
                rcases state.firstReady?_stamp_origin visited target timestamp hstamp with
                  hprior | ⟨rfl, htime⟩
                · exact Or.inl hprior
                · exact Or.inr ⟨rfl, htime, rule, by simp, hafterRequires⟩
            | reveal owner source =>
                have hstamp : (state.stamp visited).firstReady? target = some timestamp := by
                  rw [← runtime.visit_firstReady?_eq_stamp resolveExpired state visited target
                    rule hrule hcompletedFalse hrequires (by simp [hkind])]
                  exact hready
                rcases state.firstReady?_stamp_origin visited target timestamp hstamp with
                  hprior | ⟨rfl, htime⟩
                · exact Or.inl hprior
                · exact Or.inr ⟨rfl, htime, rule, by simp, hafterRequires⟩

/-- A timestamp newly created by one full refresh equals the refreshed public
clock and belongs to a real rule whose prerequisites are then complete. -/
theorem refresh_firstReady?_of_none
    (runtime : SealedResolution Principal Value) (resolveExpired : Bool)
    (state : PublicState Principal Value) (node timestamp : Nat)
    (hnone : state.firstReady? node = none)
    (hready : (runtime.refresh resolveExpired state).firstReady? node = some timestamp) :
    timestamp = (runtime.refresh resolveExpired state).clock ∧
      ∃ rule, runtime.program.rules[node]? = some rule ∧
        rule.requires.all (runtime.refresh resolveExpired state).completed = true := by
  unfold SealedResolution.refresh at hready ⊢
  generalize List.range runtime.program.rules.length = nodes at hready ⊢
  induction nodes generalizing state with
  | nil => simp [hnone] at hready
  | cons visited rest ih =>
      simp only [List.foldl_cons] at hready ⊢
      let middle := runtime.visit resolveExpired state visited
      cases hmiddle : middle.firstReady? node with
      | none => exact ih middle hmiddle hready
      | some recorded =>
          have horigin := runtime.visit_firstReady?_origin resolveExpired state visited node
            recorded hmiddle
          rcases horigin with hprior | ⟨hnode, htime, rule, hrule, hrequires⟩
          · rw [hnone] at hprior
            contradiction
          · have hfinalReady := runtime.fold_firstReady?_of_some resolveExpired rest middle
              node recorded hmiddle
            have htimestamp : timestamp = recorded :=
              Option.some.inj (hready.symm.trans hfinalReady)
            subst timestamp
            refine ⟨?_, rule, ?_, runtime.fold_all_completed resolveExpired rest
              rule.requires middle hrequires⟩
            · calc
                recorded = state.clock := htime
                _ = middle.clock := (runtime.visit_clock resolveExpired state visited).symm
                _ = (rest.foldl (runtime.visit resolveExpired) middle).clock :=
                  (runtime.fold_clock resolveExpired rest middle).symm
            · simpa [hnode] using hrule

namespace PublicState.ReadySound

variable {runtime : SealedResolution Principal Value} {state : PublicState Principal Value}

theorem refresh (sound : state.ReadySound runtime) (resolveExpired : Bool) :
    (runtime.refresh resolveExpired state).ReadySound runtime := by
  intro node timestamp hready
  cases hprior : state.firstReady? node with
  | none => exact (runtime.refresh_firstReady?_of_none resolveExpired state node timestamp
      hprior hready).2
  | some recorded =>
      obtain ⟨rule, hrule, hrequires⟩ := sound node recorded hprior
      have hpersist := runtime.refresh_firstReady?_of_some resolveExpired state node recorded hprior
      have htime : timestamp = recorded := Option.some.inj (hready.symm.trans hpersist)
      subst timestamp
      refine ⟨rule, hrule, ?_⟩
      apply List.all_eq_true.mpr
      intro prerequisite hprerequisite
      exact runtime.refresh_completed resolveExpired state prerequisite
        (List.all_eq_true.mp hrequires prerequisite hprerequisite)

theorem initial (runtime : SealedResolution Principal Value) :
    runtime.initial.visible.ReadySound runtime := by
  apply (show ({} : PublicState Principal Value).ReadySound runtime by
    intro node timestamp hready
    simp [PublicState.firstReady?] at hready).refresh false

end PublicState.ReadySound

private theorem visit_new_timeout
    (runtime : SealedResolution Principal Value) (resolveExpired : Bool)
    (state : PublicState Principal Value) (visited target : Nat)
    (hprior : target ∉ state.timeouts)
    (htimeout : target ∈ (runtime.visit resolveExpired state visited).timeouts) :
    target = visited ∧
      ∃ rule timestamp,
        runtime.program.rules[visited]? = some rule ∧
        (runtime.visit resolveExpired state visited).firstReady? visited = some timestamp ∧
        timestamp + runtime.window ≤
          (runtime.visit resolveExpired state visited).clock ∧
        rule.requires.all
          (runtime.visit resolveExpired state visited).completed = true := by
  cases hrule : runtime.program.rules[visited]? with
  | none => simp [SealedResolution.visit, hrule, hprior] at htimeout
  | some rule =>
      by_cases hcompleted : state.completed visited = true
      · simp [SealedResolution.visit, hrule, hcompleted, hprior] at htimeout
      · have hcompletedFalse := Bool.eq_false_of_not_eq_true hcompleted
        have hrequires : rule.requires.all state.completed = true := by
          cases hrequires : rule.requires.all state.completed with
          | false =>
              simp [SealedResolution.visit, hrule, hcompletedFalse, hrequires,
                hprior] at htimeout
          | true => rfl
        have hafterRequires :=
          all_completed_visit runtime resolveExpired state visited rule.requires hrequires
        obtain ⟨timestamp, hstamp⟩ := state.firstReady?_stamp_self visited
        cases hkind : rule.kind with
        | disabled =>
            simp [SealedResolution.visit, hrule, hcompletedFalse, hrequires, hkind,
              hprior] at htimeout
        | commit owner =>
            cases resolveExpired with
            | false =>
                simp [SealedResolution.visit, hrule, hcompletedFalse, hrequires, hkind,
                  hprior] at htimeout
            | true =>
                by_cases hdeadline :
                    ((state.stamp visited).firstReady? visited).getD
                      state.clock + runtime.window ≤ state.clock
                · have hvisit : runtime.visit true state visited =
                      runtime.expire (state.stamp visited) visited rule.kind := by
                    simp [SealedResolution.visit, hrule, hcompletedFalse, hrequires,
                      hkind, hdeadline]
                  have heq : target = visited := by
                    rw [hvisit] at htimeout
                    simpa [SealedResolution.expire, hkind, hprior] using htimeout
                  refine ⟨heq, rule, timestamp, by simp, ?_, ?_, hafterRequires⟩
                  · rw [hvisit]
                    simpa [SealedResolution.expire, hkind, PublicState.firstReady?]
                      using hstamp
                  · rw [runtime.visit_clock]
                    simpa [hstamp] using hdeadline
                · simp [SealedResolution.visit, hrule, hcompletedFalse, hrequires, hkind,
                    hdeadline, hprior] at htimeout
        | reveal owner source =>
            by_cases hsource : source ∈ state.timeouts
            · simp [SealedResolution.visit, hrule, hcompletedFalse, hrequires, hkind, hsource,
                hprior] at htimeout
            · cases resolveExpired with
              | false =>
                  simp [SealedResolution.visit, hrule, hcompletedFalse, hrequires, hkind, hsource,
                    hprior] at htimeout
              | true =>
                  by_cases hdeadline :
                      ((state.stamp visited).firstReady? visited).getD
                        state.clock + runtime.window ≤ state.clock
                  · have hvisit : runtime.visit true state visited =
                        runtime.expire (state.stamp visited) visited rule.kind := by
                      simp [SealedResolution.visit, hrule, hcompletedFalse, hrequires,
                        hkind, hsource, hdeadline]
                    have heq : target = visited := by
                      rw [hvisit] at htimeout
                      simpa [SealedResolution.expire, hkind, hprior] using htimeout
                    refine ⟨heq, rule, timestamp, by simp, ?_, ?_,
                      hafterRequires⟩
                    · rw [hvisit]
                      simpa [SealedResolution.expire, hkind, PublicState.firstReady?]
                        using hstamp
                    · rw [runtime.visit_clock]
                      simpa [hstamp] using hdeadline
                  · simp [SealedResolution.visit, hrule, hcompletedFalse, hrequires, hkind, hsource,
                      hdeadline, hprior] at htimeout

namespace PublicState.DeadlineSound

variable {runtime : SealedResolution Principal Value} {state : PublicState Principal Value}

private theorem visit (sound : state.DeadlineSound runtime)
    (resolveExpired : Bool) (visited : Nat) :
    (runtime.visit resolveExpired state visited).DeadlineSound runtime := by
  intro node htimeout
  by_cases hprior : node ∈ state.timeouts
  · obtain ⟨rule, timestamp, hrule, hready, hdeadline, hrequires⟩ := sound node hprior
    refine ⟨rule, timestamp, hrule,
      runtime.visit_firstReady?_of_some resolveExpired state visited node timestamp hready,
      ?_, ?_⟩
    · rwa [runtime.visit_clock]
    · exact all_completed_visit runtime resolveExpired state visited rule.requires hrequires
  · obtain ⟨rfl, rule, timestamp, hrule, hready, hdeadline, hrequires⟩ :=
      runtime.visit_new_timeout resolveExpired state visited node hprior htimeout
    exact ⟨rule, timestamp, hrule, hready, hdeadline, hrequires⟩

theorem refresh (sound : state.DeadlineSound runtime) (resolveExpired : Bool) :
    (runtime.refresh resolveExpired state).DeadlineSound runtime := by
  unfold SealedResolution.refresh
  generalize List.range runtime.program.rules.length = nodes
  induction nodes generalizing state with
  | nil => exact sound
  | cons node rest ih => exact ih (sound.visit resolveExpired node)

theorem initial (runtime : SealedResolution Principal Value) :
    runtime.initial.visible.DeadlineSound runtime := by
  apply (show ({} : PublicState Principal Value).DeadlineSound runtime by
    intro node htimeout
    simp at htimeout).refresh false

end PublicState.DeadlineSound

private theorem completed_record
    (state : PublicState Principal Value) (event : SealedProgram.Event Principal Value)
    (node : Nat) (hcompleted : state.completed node = true) :
    ({ state with events := state.events ++ [event] }).completed node = true := by
  unfold PublicState.completed SealedProgram.done at hcompleted ⊢
  simp only [List.any_append, Bool.or_eq_true] at hcompleted ⊢
  rcases hcompleted with hevents | htimeout
  · exact Or.inl (Or.inl hevents)
  · exact Or.inr htimeout

private theorem expire_timeout_mem
    (runtime : SealedResolution Principal Value)
    (state : PublicState Principal Value) (visited node : Nat)
    (kind : SealedRuleKind Principal)
    (htimeout : node ∈ (runtime.expire state visited kind).timeouts) :
    node ∈ state.timeouts ∨ node = visited := by
  cases kind with
  | disabled => exact Or.inl htimeout
  | commit owner => simpa [SealedResolution.expire] using htimeout
  | reveal owner source => simpa [SealedResolution.expire] using htimeout

private theorem visit_timeout_mem
    (runtime : SealedResolution Principal Value) (resolveExpired : Bool)
    (state : PublicState Principal Value) (visited node : Nat)
    (htimeout : node ∈ (runtime.visit resolveExpired state visited).timeouts) :
    node ∈ state.timeouts ∨ node = visited := by
  have hexpired (kind : SealedRuleKind Principal)
      (hmember : node ∈
        (runtime.expire (state.stamp visited) visited kind).timeouts) :
      node ∈ state.timeouts ∨ node = visited := by
    rcases expire_timeout_mem runtime (state.stamp visited) visited node kind hmember with
      hprior | hnew
    · exact Or.inl (by simpa using hprior)
    · exact Or.inr hnew
  unfold SealedResolution.visit at htimeout
  split at htimeout
  · exact Or.inl htimeout
  · split at htimeout
    · exact Or.inl htimeout
    · dsimp only at htimeout
      split at htimeout
      · exact Or.inl htimeout
      · split at htimeout
        · rw [PublicState.stamp_timeouts] at htimeout
          exact Or.inl htimeout
        · split at htimeout
          · exact hexpired _ htimeout
          · rw [PublicState.stamp_timeouts] at htimeout
            exact Or.inl htimeout
      · split at htimeout
        · exact hexpired _ htimeout
        · rw [PublicState.stamp_timeouts] at htimeout
          exact Or.inl htimeout

private theorem visit_no_timeout_of_completed
    (runtime : SealedResolution Principal Value) (resolveExpired : Bool)
    (state : PublicState Principal Value) (visited node : Nat)
    (hcompleted : state.completed node = true) (habsent : node ∉ state.timeouts) :
    node ∉ (runtime.visit resolveExpired state visited).timeouts := by
  intro htimeout
  by_cases heq : visited = node
  · subst visited
    cases hrule : runtime.program.rules[node]? with
    | none => exact habsent (by simpa [SealedResolution.visit, hrule] using htimeout)
    | some rule =>
        exact habsent (by simpa [SealedResolution.visit, hrule, hcompleted] using htimeout)
  · rcases visit_timeout_mem runtime resolveExpired state visited node htimeout with
      hprior | hnew
    · exact habsent hprior
    · exact heq hnew.symm

private theorem refresh_no_timeout_of_completed
    (runtime : SealedResolution Principal Value) (resolveExpired : Bool)
    (state : PublicState Principal Value) (node : Nat)
    (hcompleted : state.completed node = true) (habsent : node ∉ state.timeouts) :
    node ∉ (runtime.refresh resolveExpired state).timeouts := by
  unfold SealedResolution.refresh
  generalize List.range runtime.program.rules.length = nodes
  induction nodes generalizing state with
  | nil => exact habsent
  | cons visited rest ih =>
      exact ih (runtime.visit resolveExpired state visited)
        (runtime.visit_completed resolveExpired state visited node hcompleted)
        (visit_no_timeout_of_completed runtime resolveExpired state visited node
          hcompleted habsent)

private theorem PublicState.ReadySound.record
    {runtime : SealedResolution Principal Value} {state : PublicState Principal Value}
    (sound : state.ReadySound runtime) (event : SealedProgram.Event Principal Value) :
    ({ state with events := state.events ++ [event] }).ReadySound runtime := by
  intro node timestamp hready
  obtain ⟨rule, hrule, hrequires⟩ := sound node timestamp (by
    simpa [PublicState.firstReady?] using hready)
  refine ⟨rule, hrule, ?_⟩
  apply List.all_eq_true.mpr
  intro prerequisite hprerequisite
  exact completed_record state event prerequisite
    (List.all_eq_true.mp hrequires prerequisite hprerequisite)

private theorem PublicState.DeadlineSound.record
    {runtime : SealedResolution Principal Value} {state : PublicState Principal Value}
    (sound : state.DeadlineSound runtime) (event : SealedProgram.Event Principal Value) :
    ({ state with events := state.events ++ [event] }).DeadlineSound runtime := by
  intro node htimeout
  obtain ⟨rule, timestamp, hrule, hready, hdeadline, hrequires⟩ :=
    sound node (by simpa using htimeout)
  refine ⟨rule, timestamp, hrule, by simpa [PublicState.firstReady?] using hready,
    hdeadline, ?_⟩
  apply List.all_eq_true.mpr
  intro prerequisite hprerequisite
  exact completed_record state event prerequisite
    (List.all_eq_true.mp hrequires prerequisite hprerequisite)

variable [DecidableEq Principal] [DecidableEq Value]

namespace PublicState.ReadySound

variable {runtime : SealedResolution Principal Value}
variable {state next : ApplicationState Principal Value}

omit [DecidableEq Value] in
theorem register (sound : state.visible.ReadySound runtime)
    (owner : Principal) (slot : Nat) (value : Value) :
    ({ state with service := (state.service.sealValue owner slot value).state } :
      ApplicationState Principal Value).visible.ReadySound runtime := sound

theorem handle (sound : state.visible.ReadySound runtime)
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (hnext : runtime.handle state message = some next) :
    next.visible.ReadySound runtime := by
  unfold SealedResolution.handle at hnext
  cases hvalid : runtime.validateMessage? state message with
  | none => simp [hvalid] at hnext
  | some event =>
      simp only [hvalid, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hnext
      subst next
      exact (sound.record event).refresh false

omit [DecidableEq Principal] [DecidableEq Value] in
theorem tick (sound : state.visible.ReadySound runtime) :
    (runtime.tick state).visible.ReadySound runtime := by
  unfold SealedResolution.tick
  exact (show ({ state.visible with clock := state.visible.clock + 1 } :
    PublicState Principal Value).ReadySound runtime from sound).refresh true

end PublicState.ReadySound

namespace PublicState.DeadlineSound

variable {runtime : SealedResolution Principal Value}
variable {state next : ApplicationState Principal Value}

omit [DecidableEq Value] in
theorem register (sound : state.visible.DeadlineSound runtime)
    (owner : Principal) (slot : Nat) (value : Value) :
    ({ state with service := (state.service.sealValue owner slot value).state } :
      ApplicationState Principal Value).visible.DeadlineSound runtime := sound

theorem handle (sound : state.visible.DeadlineSound runtime)
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (hnext : runtime.handle state message = some next) :
    next.visible.DeadlineSound runtime := by
  unfold SealedResolution.handle at hnext
  cases hvalid : runtime.validateMessage? state message with
  | none => simp [hvalid] at hnext
  | some event =>
      simp only [hvalid, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hnext
      subst next
      exact (sound.record event).refresh false

omit [DecidableEq Principal] [DecidableEq Value] in
theorem clock (sound : state.visible.DeadlineSound runtime) :
    ({ state.visible with clock := state.visible.clock + 1 } :
      PublicState Principal Value).DeadlineSound runtime := by
  intro node htimeout
  obtain ⟨rule, timestamp, hrule, hready, hdeadline, hrequires⟩ :=
    sound node (by simpa using htimeout)
  exact ⟨rule, timestamp, hrule, by simpa [PublicState.firstReady?] using hready,
    Nat.le_trans hdeadline (Nat.le_succ _), hrequires⟩

omit [DecidableEq Principal] [DecidableEq Value] in
theorem tick (sound : state.visible.DeadlineSound runtime) :
    (runtime.tick state).visible.DeadlineSound runtime := by
  unfold SealedResolution.tick
  exact sound.clock.refresh true

end PublicState.DeadlineSound

theorem runPolicies_readySound
    (runtime : SealedResolution Principal Value)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Principal))
    (execution next : runtime.messageApplication.PolicyExecution)
    (hinitial : execution.native.application.visible.ReadySound runtime)
    (hnext : next ∈ (runtime.messageApplication.runPolicies players environment
      schedule execution).support) :
    next.native.application.visible.ReadySound runtime := by
  apply runtime.messageApplication.runPolicies_application_invariant
    (fun state => state.visible.ReadySound runtime) ?_ ?_ ?_
      players environment schedule execution next hinitial hnext
  · intro state owner command sound
    exact sound.register owner command.down.1 command.down.2
  · intro state message after sound hafter
    exact sound.handle message hafter
  · intro state command after sound hafter
    simp only [messageApplication, FinDist.mem_support_pure] at hafter
    subst after
    exact sound.tick

theorem runPolicies_deadlineSound
    (runtime : SealedResolution Principal Value)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Principal))
    (execution next : runtime.messageApplication.PolicyExecution)
    (hinitial : execution.native.application.visible.DeadlineSound runtime)
    (hnext : next ∈ (runtime.messageApplication.runPolicies players environment
      schedule execution).support) :
    next.native.application.visible.DeadlineSound runtime := by
  apply runtime.messageApplication.runPolicies_application_invariant
    (fun state => state.visible.DeadlineSound runtime) ?_ ?_ ?_
      players environment schedule execution next hinitial hnext
  · intro state owner command sound
    exact sound.register owner command.down.1 command.down.2
  · intro state message after sound hafter
    exact sound.handle message hafter
  · intro state command after sound hafter
    simp only [messageApplication, FinDist.mem_support_pure] at hafter
    subst after
    exact sound.tick

/-- An existing readiness timestamp survives every supported finite policy
run, including arbitrary native message traffic and clock invocations. -/
theorem runPolicies_firstReady?_of_some
    (runtime : SealedResolution Principal Value)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Principal))
    (execution next : runtime.messageApplication.PolicyExecution)
    (node timestamp : Nat)
    (hready : execution.native.application.visible.firstReady? node = some timestamp)
    (hnext : next ∈ (runtime.messageApplication.runPolicies players environment
      schedule execution).support) :
    next.native.application.visible.firstReady? node = some timestamp := by
  apply runtime.messageApplication.runPolicies_application_invariant
    (fun state => state.visible.firstReady? node = some timestamp) ?_ ?_ ?_
      players environment schedule execution next hready hnext
  · intro state owner command hbefore
    simpa [messageApplication] using hbefore
  · intro state message after hbefore hafter
    change runtime.handle state message = some after at hafter
    unfold SealedResolution.handle at hafter
    cases hvalid : runtime.validateMessage? state message with
    | none => simp [hvalid] at hafter
    | some event =>
        simp only [hvalid, Option.bind_eq_bind, Option.bind_some,
          Option.some.injEq] at hafter
        subst after
        apply runtime.refresh_firstReady?_of_some false _ node timestamp
        simpa [PublicState.firstReady?] using hbefore
  · intro state command after hbefore hafter
    simp only [messageApplication, FinDist.mem_support_pure] at hafter
    subst after
    unfold SealedResolution.tick
    apply runtime.refresh_firstReady?_of_some true _ node timestamp
    simpa [PublicState.firstReady?] using hbefore

/-- Once a node has completed without timing out, arbitrary later policies
cannot retroactively add that node to the timeout record. -/
theorem runPolicies_no_timeout_of_completed
    (runtime : SealedResolution Principal Value)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Principal))
    (execution next : runtime.messageApplication.PolicyExecution)
    (node : Nat)
    (hcompleted : execution.native.application.visible.completed node = true)
    (habsent : node ∉ execution.native.application.visible.timeouts)
    (hnext : next ∈ (runtime.messageApplication.runPolicies players environment
      schedule execution).support) :
    node ∉ next.native.application.visible.timeouts := by
  have hinvariant :
      next.native.application.visible.completed node = true ∧
        node ∉ next.native.application.visible.timeouts := by
    apply runtime.messageApplication.runPolicies_application_invariant
      (fun state => state.visible.completed node = true ∧
        node ∉ state.visible.timeouts) ?_ ?_ ?_
        players environment schedule execution next ⟨hcompleted, habsent⟩ hnext
    · intro state owner command hbefore
      simpa [messageApplication] using hbefore
    · intro state message after hbefore hafter
      change runtime.handle state message = some after at hafter
      unfold SealedResolution.handle at hafter
      cases hvalid : runtime.validateMessage? state message with
      | none => simp [hvalid] at hafter
      | some event =>
          simp only [hvalid, Option.bind_eq_bind, Option.bind_some,
            Option.some.injEq] at hafter
          subst after
          have hrecorded :
              ({ state.visible with events := state.visible.events ++ [event] } :
                PublicState Principal Value).completed node = true :=
            completed_record state.visible event node hbefore.1
          exact ⟨runtime.refresh_completed false _ node hrecorded,
            refresh_no_timeout_of_completed runtime false _ node hrecorded
              (by simpa using hbefore.2)⟩
    · intro state command after hbefore hafter
      simp only [messageApplication, FinDist.mem_support_pure] at hafter
      subst after
      unfold SealedResolution.tick
      have hclocked :
          ({ state.visible with clock := state.visible.clock + 1 } :
            PublicState Principal Value).completed node = true := by
        change state.visible.completed node = true
        exact hbefore.1
      exact ⟨runtime.refresh_completed true _ node hclocked,
        refresh_no_timeout_of_completed runtime true _ node hclocked
          (by
            change node ∉ state.visible.timeouts
            exact hbefore.2)⟩
  exact hinvariant.2

private theorem handle_firstReady?_of_none
    (runtime : SealedResolution Principal Value)
    (state next : ApplicationState Principal Value)
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (node timestamp : Nat) (hnext : runtime.handle state message = some next)
    (hnone : state.visible.firstReady? node = none)
    (hready : next.visible.firstReady? node = some timestamp) :
    timestamp = next.visible.clock ∧
      ∃ rule, runtime.program.rules[node]? = some rule ∧
        rule.requires.all next.visible.completed = true := by
  unfold SealedResolution.handle at hnext
  cases hvalid : runtime.validateMessage? state message with
  | none => simp [hvalid] at hnext
  | some event =>
      simp only [hvalid, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hnext
      subst next
      exact runtime.refresh_firstReady?_of_none false _ node timestamp
        (by simpa [PublicState.firstReady?] using hnone) hready

omit [DecidableEq Principal] [DecidableEq Value] in
private theorem tick_firstReady?_of_none
    (runtime : SealedResolution Principal Value) (state : ApplicationState Principal Value)
    (node timestamp : Nat) (hnone : state.visible.firstReady? node = none)
    (hready : (runtime.tick state).visible.firstReady? node = some timestamp) :
    timestamp = (runtime.tick state).visible.clock ∧
      ∃ rule, runtime.program.rules[node]? = some rule ∧
        rule.requires.all (runtime.tick state).visible.completed = true := by
  unfold SealedResolution.tick at hready ⊢
  exact runtime.refresh_firstReady?_of_none true _ node timestamp
    (by simpa [PublicState.firstReady?] using hnone) hready

private theorem step_firstReady?_clock_of_none
    (runtime : SealedResolution Principal Value)
    (state next : runtime.messageApplication.State)
    (action : runtime.messageApplication.Action) (node timestamp : Nat)
    (hnext : next ∈ (runtime.messageApplication.step state action).support)
    (hnone : state.application.visible.firstReady? node = none)
    (hready : next.application.visible.firstReady? node = some timestamp) :
    timestamp = next.application.visible.clock := by
  cases action with
  | privateCommand owner command =>
      simp only [MessageApplication.step, messageApplication,
        FinDist.mem_support_pure] at hnext
      subst next
      rw [hnone] at hready
      contradiction
  | submit owner payload | replay owner id | deliver owner id =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at hnext
      subst next
      rw [hnone] at hready
      contradiction
  | «include» id =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at hnext
      subst next
      cases hlookup : state.pool.lookup id with
      | none =>
          rw [runtime.messageApplication.includePending_missing state id hlookup] at hready
          rw [hnone] at hready
          contradiction
      | some message =>
          cases hhandle : runtime.handle state.application message with
          | none =>
              rw [runtime.messageApplication.includePending_reject state id message hlookup
                hhandle] at hready
              rw [hnone] at hready
              contradiction
          | some application =>
              rw [runtime.messageApplication.includePending_accept state id message application
                hlookup hhandle] at hready ⊢
              exact (runtime.handle_firstReady?_of_none state.application application message
                node timestamp hhandle hnone hready).1
  | environment command =>
      simp only [MessageApplication.step, messageApplication, FinDist.map_pure,
        FinDist.mem_support_pure] at hnext
      subst next
      exact (runtime.tick_firstReady?_of_none state.application node timestamp hnone hready).1

/-- At a supported single policy invocation, a newly observed timestamp equals
that invocation's resulting clock and certifies actual rule readiness. -/
theorem invoke_firstReady?_of_none
    (runtime : SealedResolution Principal Value)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.EnvironmentPolicy)
    (before after : runtime.messageApplication.PolicyExecution)
    (invocation : @MessageApplication.Invocation Principal) (node timestamp : Nat)
    (hsound : before.native.application.visible.ReadySound runtime)
    (hnext : after ∈ (runtime.messageApplication.invoke players environment before
      invocation).support)
    (hnone : before.native.application.visible.firstReady? node = none)
    (hready : after.native.application.visible.firstReady? node = some timestamp) :
    timestamp = after.native.application.visible.clock ∧
      ∃ rule, runtime.program.rules[node]? = some rule ∧
        rule.requires.all after.native.application.visible.completed = true := by
  have hafterSound : after.native.application.visible.ReadySound runtime := by
    apply runtime.runPolicies_readySound players environment [invocation] before after hsound
    simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using hnext
  refine ⟨?_, hafterSound node timestamp hready⟩
  cases invocation with
  | player who =>
      simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨command, hcommand, hstep⟩ := hnext
      have hnative : after.native ∈
          ((runtime.messageApplication.playerStep who before command).map
            MessageInterface.PolicyExecution.native).support := by
        rw [FinDist.support_map]
        exact ⟨after, hstep, rfl⟩
      rw [runtime.messageApplication.playerStep_native] at hnative
      cases haction : MessageApplication.PlayerCommand.toAction
          runtime.messageApplication who command with
      | none =>
          simp only [haction, FinDist.mem_support_pure] at hnative
          rw [hnative] at hready
          rw [hnone] at hready
          contradiction
      | some action =>
          exact runtime.step_firstReady?_clock_of_none before.native after.native action
            node timestamp (by simpa [haction] using hnative) hnone hready
  | environment =>
      simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨command, hcommand, hstep⟩ := hnext
      have hnative : after.native ∈
          ((runtime.messageApplication.environmentPolicyStep before command).map
            MessageInterface.PolicyExecution.native).support := by
        rw [FinDist.support_map]
        exact ⟨after, hstep, rfl⟩
      rw [runtime.messageApplication.environmentStep_native] at hnative
      cases haction : MessageApplication.EnvironmentPolicyCommand.toAction
          runtime.messageApplication command with
      | none =>
          simp only [haction, FinDist.mem_support_pure] at hnative
          rw [hnative] at hready
          rw [hnone] at hready
          contradiction
      | some action =>
          exact runtime.step_firstReady?_clock_of_none before.native after.native action
            node timestamp (by simpa [haction] using hnative) hnone hready

end Interaction.SealedResolution

/-- info: 'Interaction.SealedResolution.invoke_firstReady?_of_none' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.invoke_firstReady?_of_none
