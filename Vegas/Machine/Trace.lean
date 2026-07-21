import Vegas.Machine.Basic

/-!
# Machine event-batch trace semantics

Fixed primitive-event execution, semantic availability along those executions,
and bounded traces produced by history-dependent event-batch laws. Event batches
are the scheduling boundary used by checkpoint presentations and runtime
refinement.
-/

namespace Vegas

namespace Machine

variable {Player : Type}

/-- Execute a fixed primitive event list from a given state, returning only the
final state. This is the state marginal of a scheduled finite trace with the
schedule stored outside the machine. -/
noncomputable def runEventsFrom
    (M : Machine Player) (events : List M.Event) (state : M.State) :
    PMF M.State :=
  events.foldl
    (fun acc event => acc.bind fun current => M.step event current)
    (PMF.pure state)

@[simp] theorem runEventsFrom_nil
    (M : Machine Player) (state : M.State) :
    M.runEventsFrom [] state = PMF.pure state := rfl

theorem runEventsFrom_cons
    (M : Machine Player) (event : M.Event)
    (events : List M.Event) (state : M.State) :
    M.runEventsFrom (event :: events) state =
      events.foldl
        (fun acc nextEvent => acc.bind fun current =>
          M.step nextEvent current)
        (M.step event state) := by
  simp [runEventsFrom]

/-- Folding a primitive event list over an arbitrary input distribution is the
same as binding that distribution into `runEventsFrom`. -/
private theorem runEventsFrom_foldl_eq_bind
    (M : Machine Player) (events : List M.Event) (acc : PMF M.State) :
    events.foldl
        (fun acc event => acc.bind fun current => M.step event current)
        acc =
      acc.bind fun current => M.runEventsFrom events current := by
  induction events generalizing acc with
  | nil =>
      change acc = acc.bind PMF.pure
      exact (PMF.bind_pure acc).symm
  | cons event events ih =>
      change
        events.foldl
            (fun acc event => acc.bind fun current => M.step event current)
            (acc.bind fun current => M.step event current) =
          acc.bind fun current => M.runEventsFrom (event :: events) current
      rw [ih, PMF.bind_bind]
      congr
      funext current
      rw [runEventsFrom_cons]
      exact (ih (M.step event current)).symm

/-- Executing a nonempty event list is the first primitive step followed by the
remaining fixed event list. -/
theorem runEventsFrom_cons_bind
    (M : Machine Player) (event : M.Event)
    (events : List M.Event) (state : M.State) :
    M.runEventsFrom (event :: events) state =
      (M.step event state).bind fun current =>
        M.runEventsFrom events current := by
  rw [runEventsFrom_cons]
  rw [runEventsFrom_foldl_eq_bind]

/-- Executing appended event lists is Kleisli composition of the two runs. -/
theorem runEventsFrom_append
    (M : Machine Player) (events₁ events₂ : List M.Event)
    (state : M.State) :
    M.runEventsFrom (events₁ ++ events₂) state =
      (M.runEventsFrom events₁ state).bind fun current =>
        M.runEventsFrom events₂ current := by
  rw [runEventsFrom]
  rw [List.foldl_append]
  rw [runEventsFrom_foldl_eq_bind]
  rfl

/-- A fixed primitive event list is semantically available along one supported
machine execution from a source state to a destination state. -/
inductive AvailableRunFrom (M : Machine Player) :
    M.State → List M.Event → M.State → Prop where
  | nil (state : M.State) :
      AvailableRunFrom M state [] state
  | cons {source mid dst : M.State} {event : M.Event}
      {events : List M.Event} :
      M.EventAvailable source event →
      mid ∈ (M.step event source).support →
      AvailableRunFrom M mid events dst →
      AvailableRunFrom M source (event :: events) dst

namespace AvailableRunFrom

theorem append
    {M : Machine Player} {source mid dst : M.State}
    {events₁ events₂ : List M.Event}
    (left : M.AvailableRunFrom source events₁ mid)
    (right : M.AvailableRunFrom mid events₂ dst) :
    M.AvailableRunFrom source (events₁ ++ events₂) dst := by
  induction left with
  | nil state =>
      simpa using right
  | cons havailable hstep _ ih =>
      exact .cons havailable hstep (ih right)

theorem cons_inv
    {M : Machine Player} {source dst : M.State}
    {event : M.Event} {events : List M.Event}
    (hrun : M.AvailableRunFrom source (event :: events) dst) :
    ∃ mid, M.EventAvailable source event ∧
      mid ∈ (M.step event source).support ∧
      M.AvailableRunFrom mid events dst := by
  cases hrun with
  | cons havailable hstep htail =>
      exact ⟨_, havailable, hstep, htail⟩

theorem mem_runEventsFrom_support
    {M : Machine Player} {source dst : M.State}
    {events : List M.Event}
    (hrun : M.AvailableRunFrom source events dst) :
    dst ∈ (M.runEventsFrom events source).support := by
  induction hrun with
  | nil state =>
      simp
  | cons havailable hstep _ ih =>
      rw [Machine.runEventsFrom_cons_bind]
      rw [PMF.mem_support_bind_iff]
      exact ⟨_, hstep, ih⟩

end AvailableRunFrom

/-- A fixed primitive event list is semantically available from a source state
along every supported intermediate execution path. This is the support-wide
batch legality predicate needed by probabilistic runtimes: a legal batch may not
hide unavailable intermediate branches that later converge to an otherwise
available final state. -/
def AvailableBatchFrom (M : Machine Player) :
    M.State → List M.Event → Prop
  | _, [] => True
  | source, event :: events =>
      M.EventAvailable source event ∧
        ∀ mid, mid ∈ (M.step event source).support →
          M.AvailableBatchFrom mid events

namespace AvailableBatchFrom

theorem nil {M : Machine Player} (source : M.State) :
    M.AvailableBatchFrom source [] := by
  trivial

theorem cons {M : Machine Player} {source : M.State}
    {event : M.Event} {events : List M.Event}
    (havailable : M.EventAvailable source event)
    (htail :
      ∀ mid, mid ∈ (M.step event source).support →
        M.AvailableBatchFrom mid events) :
    M.AvailableBatchFrom source (event :: events) := by
  exact ⟨havailable, htail⟩

theorem singleton {M : Machine Player} {source : M.State}
    {event : M.Event}
    (havailable : M.EventAvailable source event) :
    M.AvailableBatchFrom source [event] := by
  refine cons havailable ?_
  intro mid hmid
  exact nil mid

theorem append {M : Machine Player} {source : M.State}
    {events₁ events₂ : List M.Event}
    (hleft : M.AvailableBatchFrom source events₁)
    (hright :
      ∀ mid, mid ∈ (M.runEventsFrom events₁ source).support →
        M.AvailableBatchFrom mid events₂) :
    M.AvailableBatchFrom source (events₁ ++ events₂) := by
  induction events₁ generalizing source with
  | nil =>
      exact hright source (by simp)
  | cons event events ih =>
      exact cons hleft.1 (by
        intro mid hmid
        exact ih (hleft.2 mid hmid) (by
          intro dst hdst
          exact hright dst (by
            rw [Machine.runEventsFrom_cons_bind, PMF.mem_support_bind_iff]
            exact ⟨mid, hmid, hdst⟩)))

theorem availableRunFrom_of_mem_support
    {M : Machine Player} {source dst : M.State} {events : List M.Event}
    (hbatch : M.AvailableBatchFrom source events)
    (hdst : dst ∈ (M.runEventsFrom events source).support) :
    M.AvailableRunFrom source events dst := by
  induction events generalizing source with
  | nil =>
      change dst ∈ (PMF.pure source).support at hdst
      rw [PMF.support_pure] at hdst
      subst dst
      exact Machine.AvailableRunFrom.nil source
  | cons event events ih =>
      rw [Machine.runEventsFrom_cons_bind] at hdst
      rw [PMF.mem_support_bind_iff] at hdst
      rcases hdst with ⟨mid, hmid, hdst⟩
      exact Machine.AvailableRunFrom.cons hbatch.1 hmid
        (ih (hbatch.2 mid hmid) hdst)

end AvailableBatchFrom

/-- One semantically available primitive machine step with positive support.

This is the labeled-transition-system view of `Machine`: total unavailable
steps may exist at the raw transition surface, but refinement and trace
theorems should use this relation. -/
def AvailableStep (M : Machine Player)
    (source : M.State) (event : M.Event) (target : M.State) : Prop :=
  M.EventAvailable source event ∧
    target ∈ (M.step event source).support

namespace AvailableStep

theorem available {M : Machine Player} {source target : M.State}
    {event : M.Event}
    (hstep : M.AvailableStep source event target) :
    M.EventAvailable source event :=
  hstep.1

theorem support {M : Machine Player} {source target : M.State}
    {event : M.Event}
    (hstep : M.AvailableStep source event target) :
    target ∈ (M.step event source).support :=
  hstep.2

theorem availableRunFrom_singleton
    {M : Machine Player} {source target : M.State} {event : M.Event}
    (hstep : M.AvailableStep source event target) :
    M.AvailableRunFrom source [event] target :=
  .cons hstep.available hstep.support (.nil target)

end AvailableStep

/-- Execute a sequence of macro steps, where each macro step is represented by
a list of primitive machine events.  This is the trace shape induced by a
checkpoint or frontier-round presentation. -/
noncomputable def runEventBatchesFrom
    (M : Machine Player) (batches : List (List M.Event)) (state : M.State) :
    PMF M.State :=
  batches.foldl
    (fun acc events => acc.bind fun current => M.runEventsFrom events current)
    (PMF.pure state)

@[simp] theorem runEventBatchesFrom_nil
    (M : Machine Player) (state : M.State) :
    M.runEventBatchesFrom [] state = PMF.pure state := rfl

@[simp] theorem runEventBatchesFrom_singleton
    (M : Machine Player) (events : List M.Event) (state : M.State) :
    M.runEventBatchesFrom [events] state = M.runEventsFrom events state := by
  simp [runEventBatchesFrom]

/-- Folding event batches over an arbitrary input distribution is the same as
binding that distribution into `runEventBatchesFrom`. -/
private theorem runEventBatchesFrom_foldl_eq_bind
    (M : Machine Player) (batches : List (List M.Event))
    (acc : PMF M.State) :
    batches.foldl
        (fun acc events => acc.bind fun current => M.runEventsFrom events current)
        acc =
      acc.bind fun current => M.runEventBatchesFrom batches current := by
  induction batches generalizing acc with
  | nil =>
      change acc = acc.bind PMF.pure
      exact (PMF.bind_pure acc).symm
  | cons events batches ih =>
      change
        batches.foldl
            (fun acc events => acc.bind fun current =>
              M.runEventsFrom events current)
            (acc.bind fun current => M.runEventsFrom events current) =
          acc.bind fun current =>
            M.runEventBatchesFrom (events :: batches) current
      rw [ih, PMF.bind_bind]
      congr
      funext current
      rw [runEventBatchesFrom]
      simp only [List.foldl_cons, PMF.pure_bind]
      exact (ih (M.runEventsFrom events current)).symm

/-- Running event batches is the same as running their flattened primitive event
list. -/
theorem runEventBatchesFrom_eq_runEventsFrom_flatten
    (M : Machine Player) (batches : List (List M.Event)) (state : M.State) :
    M.runEventBatchesFrom batches state =
      M.runEventsFrom batches.flatten state := by
  induction batches generalizing state with
  | nil =>
      rfl
  | cons events batches ih =>
      rw [runEventBatchesFrom]
      simp only [List.foldl_cons]
      rw [runEventBatchesFrom_foldl_eq_bind]
      simp only [PMF.pure_bind]
      simp_rw [ih]
      rw [← runEventsFrom_append]
      rfl

/-- Executing appended event-batch lists is Kleisli composition of the two
event-batch runs. -/
theorem runEventBatchesFrom_append
    (M : Machine Player) (batches₁ batches₂ : List (List M.Event))
    (state : M.State) :
    M.runEventBatchesFrom (batches₁ ++ batches₂) state =
      (M.runEventBatchesFrom batches₁ state).bind fun current =>
        M.runEventBatchesFrom batches₂ current := by
  rw [runEventBatchesFrom]
  rw [List.foldl_append]
  rw [runEventBatchesFrom_foldl_eq_bind]
  rfl

/-- A list of primitive event batches is semantically available along one
supported checkpoint execution from a source state to a destination state. -/
inductive AvailableRunBatchesFrom (M : Machine Player) :
    M.State → List (List M.Event) → M.State → Prop where
  | nil (state : M.State) :
      AvailableRunBatchesFrom M state [] state
  | cons {source mid dst : M.State} {batch : List M.Event}
      {batches : List (List M.Event)} :
      AvailableRunFrom M source batch mid →
      AvailableRunBatchesFrom M mid batches dst →
      AvailableRunBatchesFrom M source (batch :: batches) dst

namespace AvailableRunBatchesFrom

theorem mem_runEventBatchesFrom_support
    {M : Machine Player} {source dst : M.State}
    {batches : List (List M.Event)}
    (hrun : M.AvailableRunBatchesFrom source batches dst) :
    dst ∈ (M.runEventBatchesFrom batches source).support := by
  induction hrun with
  | nil state =>
      simp
  | cons hbatch _ ih =>
      rw [Machine.runEventBatchesFrom]
      simp only [List.foldl_cons, PMF.pure_bind]
      rw [runEventBatchesFrom_foldl_eq_bind]
      rw [PMF.mem_support_bind_iff]
      exact ⟨_, hbatch.mem_runEventsFrom_support, ih⟩

end AvailableRunBatchesFrom

/-- An event-batch machine trace records the event batches executed so far and the
current checkpoint state. -/
abbrev EventBatchTrace (M : Machine Player) : Type :=
  List (List M.Event) × M.State

/-- A history-dependent law for selecting the next event batch of primitive events.

The law sees the event-batch trace prefix, not only the current state. This matches
strategic schedulers whose choices can depend on public/history information
while still running through the machine's primitive transition semantics. -/
abbrev EventBatchLaw (M : Machine Player) : Type :=
  M.EventBatchTrace → PMF (List M.Event)

/-- A history-dependent event-batch law is legal when every supported batch from
a nonterminal checkpoint is semantically available for every state in the
batch execution support. -/
def IsLegalEventBatchLaw (M : Machine Player) (law : M.EventBatchLaw) : Prop :=
  ∀ trace, ¬ M.terminal trace.2 → ∀ {batch},
    batch ∈ (law trace).support →
      M.AvailableBatchFrom trace.2 batch

/-- Event-batch laws bundled with their primitive availability proof. -/
abbrev LegalEventBatchLaw (M : Machine Player) : Type :=
  { law : M.EventBatchLaw // M.IsLegalEventBatchLaw law }

/-- Bounded event-batch trace distribution from an arbitrary event-batch trace prefix.
Execution stops once the current state is terminal; otherwise one event batch is
sampled, run through the primitive machine semantics, and appended to the
prefix. -/
noncomputable def eventBatchTraceDistFrom
    (M : Machine Player) (law : M.EventBatchLaw) :
    Nat → M.EventBatchTrace → PMF M.EventBatchTrace
  | 0, trace => PMF.pure trace
  | horizon + 1, trace => by
      classical
      exact
        if M.terminal trace.2 then
          PMF.pure trace
        else
          (law trace).bind fun batch =>
            (M.runEventBatchesFrom [batch] trace.2).bind fun next =>
              M.eventBatchTraceDistFrom law horizon
                (trace.1 ++ [batch], next)

@[simp] theorem eventBatchTraceDistFrom_zero
    (M : Machine Player) (law : M.EventBatchLaw) (trace : M.EventBatchTrace) :
    M.eventBatchTraceDistFrom law 0 trace = PMF.pure trace := rfl

theorem eventBatchTraceDistFrom_succ_terminal
    (M : Machine Player) (law : M.EventBatchLaw)
    (horizon : Nat) (trace : M.EventBatchTrace)
    (hterminal : M.terminal trace.2) :
    M.eventBatchTraceDistFrom law (horizon + 1) trace = PMF.pure trace := by
  simp [eventBatchTraceDistFrom, hterminal]

theorem eventBatchTraceDistFrom_succ_nonterminal
    (M : Machine Player) (law : M.EventBatchLaw)
    (horizon : Nat) (trace : M.EventBatchTrace)
    (hterminal : ¬ M.terminal trace.2) :
    M.eventBatchTraceDistFrom law (horizon + 1) trace =
      (law trace).bind fun batch =>
        (M.runEventBatchesFrom [batch] trace.2).bind fun next =>
          M.eventBatchTraceDistFrom law horizon
            (trace.1 ++ [batch], next) := by
  simp [eventBatchTraceDistFrom, hterminal]

/-- Bounded event-batch trace distribution from the machine initial state. -/
noncomputable def eventBatchTraceDist
    (M : Machine Player) (law : M.EventBatchLaw) (horizon : Nat) :
    PMF M.EventBatchTrace :=
  M.eventBatchTraceDistFrom law horizon ([], M.init)

@[simp] theorem eventBatchTraceDist_zero
    (M : Machine Player) (law : M.EventBatchLaw) :
    M.eventBatchTraceDist law 0 = PMF.pure ([], M.init) := rfl

end Machine

end Vegas
