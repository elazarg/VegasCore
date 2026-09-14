/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedResolutionLaws

/-! # Finite progress facts for sealed resolution

Readiness timestamps and completion records are persistent under resolution
scans.  In particular, a ready non-disabled node is either completed by a
resolving scan or retains an unexpired timestamp at the unchanged public clock.
These are finite operational facts and require no scheduling or fairness
assumption.
-/

namespace Interaction.SealedResolution

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}

private theorem findSome?_append_of_some {α β : Type*} (f : α → Option β)
    (left right : List α) (value : β) (h : left.findSome? f = some value) :
    (left ++ right).findSome? f = some value := by
  induction left with
  | nil => simp at h
  | cons head tail ih =>
      cases hhead : f head with
      | none =>
          simpa [hhead] using ih (by simpa [hhead] using h)
      | some found => simpa [List.findSome?_cons, hhead] using h

private theorem findSome?_append_of_none {α β : Type*} (f : α → Option β)
    (left right : List α) (h : left.findSome? f = none) :
    (left ++ right).findSome? f = right.findSome? f := by
  induction left with
  | nil => rfl
  | cons head tail ih =>
      cases hhead : f head with
      | none =>
          simpa [hhead] using ih (by simpa [hhead] using h)
      | some found => simp [hhead] at h

/-- Every recorded first-readiness timestamp is no later than the public clock. -/
def PublicState.ClockBounded (state : PublicState Principal Value) : Prop :=
  ∀ node timestamp, state.firstReady? node = some timestamp → timestamp ≤ state.clock

theorem PublicState.firstReady?_stamp_of_some
    (state : PublicState Principal Value) (node target timestamp : Nat)
    (hready : state.firstReady? target = some timestamp) :
    (state.stamp node).firstReady? target = some timestamp := by
  unfold PublicState.stamp
  split
  · exact hready
  · unfold PublicState.firstReady? at hready ⊢
    exact findSome?_append_of_some _ _ _ timestamp hready

theorem PublicState.firstReady?_stamp_self
    (state : PublicState Principal Value) (node : Nat) :
    ∃ timestamp, (state.stamp node).firstReady? node = some timestamp := by
  cases hready : state.firstReady? node with
  | some timestamp =>
      exact ⟨timestamp, state.firstReady?_stamp_of_some node node timestamp hready⟩
  | none =>
      refine ⟨state.clock, ?_⟩
      rw [show state.stamp node =
          { state with readyAt := state.readyAt ++ [(node, state.clock)] } by
        simp [PublicState.stamp, hready]]
      unfold PublicState.firstReady?
      unfold PublicState.firstReady? at hready
      rw [findSome?_append_of_none _ _ _ hready]
      simp

theorem PublicState.ClockBounded.stamp
    {state : PublicState Principal Value} (hbounded : state.ClockBounded) (node : Nat) :
    (state.stamp node).ClockBounded := by
  cases hnode : state.firstReady? node with
  | some recorded =>
      simpa [PublicState.stamp, hnode] using hbounded
  | none =>
    rw [show state.stamp node =
        { state with readyAt := state.readyAt ++ [(node, state.clock)] } by
      simp [PublicState.stamp, hnode]]
    intro target timestamp hready
    unfold PublicState.firstReady? at hready
    cases htarget : state.firstReady? target with
    | some existing =>
        unfold PublicState.firstReady? at htarget
        rw [findSome?_append_of_some _ _ _ existing htarget] at hready
        cases hready
        exact hbounded target _ (by simpa [PublicState.firstReady?] using htarget)
    | none =>
        unfold PublicState.firstReady? at htarget
        rw [findSome?_append_of_none _ _ _ htarget] at hready
        simp only [List.findSome?_singleton] at hready
        split at hready
        · exact Nat.le_of_eq (Option.some.inj hready).symm
        · contradiction

private theorem PublicState.completed_append
    (state : PublicState Principal Value)
    (moreEvents : List (SealedProgram.Event Principal Value)) (moreTimeouts : List Nat)
    (node : Nat) (hcompleted : state.completed node = true) :
    ({ state with events := state.events ++ moreEvents
                  timeouts := state.timeouts ++ moreTimeouts }).completed node = true := by
  unfold PublicState.completed SealedProgram.done at hcompleted ⊢
  rw [List.any_append, List.contains_append]
  cases hevents : state.events.any (fun event => event.node == node) <;>
    cases htimeouts : state.timeouts.contains node <;> simp_all

@[simp] theorem PublicState.completed_stamp
    (state : PublicState Principal Value) (stamped target : Nat) :
    (state.stamp stamped).completed target = state.completed target := by
  unfold PublicState.stamp
  split <;> rfl

theorem visit_completed (runtime : SealedResolution Principal Value) (resolveExpired : Bool)
    (state : PublicState Principal Value) (visited target : Nat)
    (hcompleted : state.completed target = true) :
    (runtime.visit resolveExpired state visited).completed target = true := by
  unfold SealedResolution.visit
  split
  · exact hcompleted
  · split
    · exact hcompleted
    · split
      · exact hcompleted
      · dsimp only
        split
        · simpa using (state.stamp visited).completed_append
            [.opened visited runtime.nullValue] [] target (by simpa using hcompleted)
        · split
          · unfold expire
            split
            · simpa using (state.stamp visited).completed_append [] [visited] target
                (by simpa using hcompleted)
            · exact (state.stamp visited).completed_append
                [.opened visited runtime.nullValue] [visited] target (by simpa using hcompleted)
            · simpa using hcompleted
          · simpa using hcompleted
      · dsimp only
        split
        · unfold expire
          split
          · simpa using (state.stamp visited).completed_append [] [visited] target
              (by simpa using hcompleted)
          · exact (state.stamp visited).completed_append
              [.opened visited runtime.nullValue] [visited] target (by simpa using hcompleted)
          · simpa using hcompleted
        · simpa using hcompleted

theorem refresh_completed (runtime : SealedResolution Principal Value) (resolveExpired : Bool)
    (state : PublicState Principal Value) (node : Nat)
    (hcompleted : state.completed node = true) :
    (runtime.refresh resolveExpired state).completed node = true := by
  unfold refresh
  generalize List.range runtime.program.rules.length = nodes
  induction nodes generalizing state with
  | nil => exact hcompleted
  | cons visited rest ih =>
      exact ih (runtime.visit resolveExpired state visited)
        (runtime.visit_completed resolveExpired state visited node hcompleted)

theorem visit_firstReady?_of_some
    (runtime : SealedResolution Principal Value) (resolveExpired : Bool)
    (state : PublicState Principal Value) (visited target timestamp : Nat)
    (hready : state.firstReady? target = some timestamp) :
    (runtime.visit resolveExpired state visited).firstReady? target = some timestamp := by
  have hstamp := state.firstReady?_stamp_of_some visited target timestamp hready
  unfold SealedResolution.visit
  split
  · exact hready
  · split
    · exact hready
    · split
      · exact hready
      · dsimp only
        split
        · simpa [PublicState.firstReady?] using hstamp
        · split
          · unfold expire
            split <;> simpa [PublicState.firstReady?] using hstamp
          · exact hstamp
      · dsimp only
        split
        · unfold expire
          split <;> simpa [PublicState.firstReady?] using hstamp
        · exact hstamp

theorem refresh_firstReady?_of_some
    (runtime : SealedResolution Principal Value) (resolveExpired : Bool)
    (state : PublicState Principal Value) (node timestamp : Nat)
    (hready : state.firstReady? node = some timestamp) :
    (runtime.refresh resolveExpired state).firstReady? node = some timestamp := by
  unfold refresh
  generalize List.range runtime.program.rules.length = nodes
  induction nodes generalizing state with
  | nil => exact hready
  | cons visited rest ih =>
      exact ih (runtime.visit resolveExpired state visited)
        (runtime.visit_firstReady?_of_some resolveExpired state visited node timestamp hready)

theorem PublicState.ClockBounded.visit
    {runtime : SealedResolution Principal Value} {state : PublicState Principal Value}
    (hbounded : state.ClockBounded) (resolveExpired : Bool) (node : Nat) :
    (runtime.visit resolveExpired state node).ClockBounded := by
  have hstamp := hbounded.stamp node
  unfold SealedResolution.visit
  split
  · exact hbounded
  · split
    · exact hbounded
    · split
      · exact hbounded
      · dsimp only
        split
        · simpa [PublicState.ClockBounded, PublicState.firstReady?] using hstamp
        · split
          · unfold expire
            split <;>
              simpa [PublicState.ClockBounded, PublicState.firstReady?] using hstamp
          · exact hstamp
      · dsimp only
        split
        · unfold expire
          split <;>
            simpa [PublicState.ClockBounded, PublicState.firstReady?] using hstamp
        · exact hstamp

theorem PublicState.ClockBounded.refresh
    {runtime : SealedResolution Principal Value} {state : PublicState Principal Value}
    (hbounded : state.ClockBounded) (resolveExpired : Bool) :
    (runtime.refresh resolveExpired state).ClockBounded := by
  unfold SealedResolution.refresh
  generalize List.range runtime.program.rules.length = nodes
  induction nodes generalizing state with
  | nil => exact hbounded
  | cons node rest ih => exact ih (hbounded.visit resolveExpired node)

theorem PublicState.ClockBounded.initial (runtime : SealedResolution Principal Value) :
    runtime.initial.visible.ClockBounded := by
  apply PublicState.ClockBounded.refresh (resolveExpired := false)
  intro node timestamp hready
  simp [PublicState.firstReady?] at hready

private def ProgressAt (runtime : SealedResolution Principal Value)
    (state : PublicState Principal Value) (node : Nat) : Prop :=
  state.completed node = true ∨
    ∃ timestamp, state.firstReady? node = some timestamp ∧
      timestamp ≤ state.clock ∧ state.clock < timestamp + runtime.window

private theorem visit_progress
    (runtime : SealedResolution Principal Value) (state : PublicState Principal Value)
    (node : Nat) (rule : SealedRule Principal)
    (hrule : runtime.program.rules[node]? = some rule)
    (hkind : rule.kind ≠ .disabled)
    (hrequires : rule.requires.all state.completed = true)
    (hbounded : state.ClockBounded) :
    ProgressAt runtime (runtime.visit true state node) node := by
  unfold ProgressAt SealedResolution.visit
  rw [hrule]
  by_cases hcompleted : state.completed node = true
  · simp [hcompleted]
  · have hcompletedFalse : state.completed node = false := Bool.eq_false_of_not_eq_true hcompleted
    simp only [hcompletedFalse, Bool.false_or, hrequires, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte]
    obtain ⟨timestamp, htimestamp⟩ := state.firstReady?_stamp_self node
    have htimestampBounded : timestamp ≤ (state.stamp node).clock :=
      hbounded.stamp node node timestamp htimestamp
    cases hkindValue : rule.kind with
    | disabled => exact False.elim (hkind hkindValue)
    | commit owner =>
        by_cases hexpired : timestamp + runtime.window ≤ (state.stamp node).clock
        · left
          have hexpiredState : timestamp + runtime.window ≤ state.clock := by
            simpa using hexpired
          simp [htimestamp, hexpiredState, expire, PublicState.completed]
        · right
          simp only [htimestamp, Option.getD_some, decide_eq_false hexpired,
            Bool.true_and]
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact ⟨timestamp, htimestamp, htimestampBounded, Nat.lt_of_not_ge hexpired⟩
    | reveal owner source =>
        by_cases hsource : source ∈ state.timeouts
        · left
          simp [hsource, PublicState.completed, SealedProgram.done,
            SealedProgram.Event.node]
        · by_cases hexpired : timestamp + runtime.window ≤ (state.stamp node).clock
          · left
            have hexpiredState : timestamp + runtime.window ≤ state.clock := by
              simpa using hexpired
            simp [htimestamp, hsource, hexpiredState, expire, PublicState.completed,
              SealedProgram.done, SealedProgram.Event.node]
          · right
            simp only [List.contains_eq_mem, hsource, decide_false, Bool.false_eq_true,
              ↓reduceIte]
            simp only [htimestamp, Option.getD_some, decide_eq_false hexpired,
              Bool.true_and]
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact ⟨timestamp, htimestamp, htimestampBounded,
              Nat.lt_of_not_ge hexpired⟩

private theorem ProgressAt.visit
    {runtime : SealedResolution Principal Value} {state : PublicState Principal Value}
    {target : Nat} (progress : ProgressAt runtime state target)
    (resolveExpired : Bool) (visited : Nat) :
    ProgressAt runtime (runtime.visit resolveExpired state visited) target := by
  rcases progress with hcompleted | ⟨timestamp, hready, hbounded, hunexpired⟩
  · exact Or.inl (runtime.visit_completed resolveExpired state visited target hcompleted)
  · by_cases hcompleted : (runtime.visit resolveExpired state visited).completed target = true
    · exact Or.inl hcompleted
    · right
      refine ⟨timestamp,
        runtime.visit_firstReady?_of_some resolveExpired state visited target timestamp hready,
        ?_, ?_⟩
      · rwa [runtime.visit_clock]
      · rwa [runtime.visit_clock]

private theorem all_completed_visit
    (runtime : SealedResolution Principal Value) (resolveExpired : Bool)
    (state : PublicState Principal Value) (visited : Nat) (nodes : List Nat)
    (hall : nodes.all state.completed = true) :
    nodes.all (runtime.visit resolveExpired state visited).completed = true := by
  apply List.all_eq_true.mpr
  intro node hnode
  exact runtime.visit_completed resolveExpired state visited node
    (List.all_eq_true.mp hall node hnode)

private theorem ProgressAt.refresh_tail
    {runtime : SealedResolution Principal Value} {state : PublicState Principal Value}
    {target : Nat} (progress : ProgressAt runtime state target) (nodes : List Nat) :
    ProgressAt runtime (nodes.foldl (runtime.visit true) state) target := by
  induction nodes generalizing state with
  | nil => exact progress
  | cons node rest ih =>
      exact ih (progress.visit true node)

/-- A non-disabled node whose prerequisites are already complete either resolves
during a resolving refresh or remains ready with a bounded, unexpired deadline.
The index hypothesis merely says that the refresh scan visits the node. -/
theorem refresh_progress
    (runtime : SealedResolution Principal Value) (state : PublicState Principal Value)
    (node : Nat) (rule : SealedRule Principal)
    (hrule : runtime.program.rules[node]? = some rule)
    (hkind : rule.kind ≠ .disabled)
    (hrequires : rule.requires.all state.completed = true)
    (hbounded : state.ClockBounded)
    (hnode : node < runtime.program.rules.length) :
    (runtime.refresh true state).completed node = true ∨
      ∃ timestamp, (runtime.refresh true state).firstReady? node = some timestamp ∧
        timestamp ≤ (runtime.refresh true state).clock ∧
        (runtime.refresh true state).clock < timestamp + runtime.window := by
  unfold SealedResolution.refresh
  have hmem : node ∈ List.range runtime.program.rules.length := List.mem_range.mpr hnode
  generalize List.range runtime.program.rules.length = nodes at hmem ⊢
  induction nodes generalizing state with
  | nil => simp at hmem
  | cons visited rest ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hmem with hvisited | hrest
      · subst visited
        exact (runtime.visit_progress state node rule hrule hkind hrequires hbounded).refresh_tail
          rest
      · exact ih (runtime.visit true state visited)
          (all_completed_visit runtime true state visited rule.requires hrequires)
          (hbounded.visit true visited) hrest

end Interaction.SealedResolution
