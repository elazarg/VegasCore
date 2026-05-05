import Vegas.Protocol.ActionGraph
import Vegas.Protocol.FOSG
import Vegas.FOSG.Observation

/-!
# Checked Vegas programs as graph machines

This module is the concrete bridge from checked Vegas syntax to the canonical
`Protocol.Machine` carrier.

Checked syntax first elaborates to `syntaxActionGraph`; `graphMachine` then
executes that graph as the canonical probabilistic machine.
The implementation still reuses the existing cursor-keyed execution functions
(`CursorCheckedWorld`, `ProgramAction`, and `cursorProgramTransition`) as the
value-level evaluator for graph steps, but the executable carrier exposed by
this module is the graph machine itself.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Program cursors have classical decidable equality. The cursor type is a
finite syntax-position carrier; using classical equality here keeps the graph
elaboration independent of proof-term shape. -/
@[reducible] noncomputable instance instDecidableEqProgramCursor
    {Γ : VCtx P L} (root : VegasCore P L Γ) :
    DecidableEq (ProgramCursor root) :=
  Classical.decEq _

/-- Action set of the checked syntax graph: every nonterminal program cursor.
The terminal `ret` cursor is the state reached after all graph actions are
complete, so it is not itself an action. -/
noncomputable def syntaxGraphActions
    (g : WFProgram P L) : Finset (ProgramCursor g.prog) := by
  classical
  letI : Fintype (ProgramCursor g.prog) :=
    ProgramCursor.instFintype g.prog
  exact Finset.univ.filter (fun cursor => 0 < syntaxSteps cursor.prog)

/-- Linear rank of a syntax cursor: how many operational nodes have already
been consumed on the path from the root to this cursor. -/
def syntaxGraphRank
    (g : WFProgram P L) (cursor : ProgramCursor g.prog) : Nat :=
  syntaxSteps g.prog - syntaxSteps cursor.prog

namespace ProgramCursor

/-- A cursor path consumes exactly the syntax nodes before the cursor target. -/
theorem path_length_add_syntaxSteps_prog
    {Γ : VCtx P L} {root : VegasCore P L Γ}
    (cursor : ProgramCursor root) :
    cursor.path.length + syntaxSteps cursor.prog = syntaxSteps root := by
  induction cursor with
  | @here Γ p =>
      change ([] : List Nat).length + syntaxSteps p = syntaxSteps p
      simp
  | @letExpr Γ x b e k cursor ih =>
      change (0 :: cursor.path).length + syntaxSteps cursor.prog =
        syntaxSteps k + 1
      simp only [List.length_cons]
      omega
  | @sample Γ x b D k cursor ih =>
      change (1 :: cursor.path).length + syntaxSteps cursor.prog =
        syntaxSteps k + 1
      simp only [List.length_cons]
      omega
  | @commit Γ x who b R k cursor ih =>
      change (2 :: cursor.path).length + syntaxSteps cursor.prog =
        syntaxSteps k + 1
      simp only [List.length_cons]
      omega
  | @reveal Γ y who x b hx k cursor ih =>
      change (3 :: cursor.path).length + syntaxSteps cursor.prog =
        syntaxSteps k + 1
      simp only [List.length_cons]
      omega

/-- Vegas syntax is linear: within one root program, cursor depth determines
the cursor. -/
theorem eq_of_path_length_eq
    {Γ : VCtx P L} {root : VegasCore P L Γ}
    (left right : ProgramCursor root)
    (h : left.path.length = right.path.length) :
    left = right := by
  induction root with
  | ret payoffs =>
      cases left
      cases right
      rfl
  | letExpr x e k ih =>
      cases left with
      | here =>
          cases right with
          | here => rfl
          | letExpr right =>
              simp [ProgramCursor.path] at h
      | letExpr left =>
          cases right with
          | here =>
              simp [ProgramCursor.path] at h
          | letExpr right =>
              simp only [ProgramCursor.path, List.length_cons,
                Nat.succ.injEq] at h
              exact congrArg ProgramCursor.letExpr (ih left right h)
  | sample x D k ih =>
      cases left with
      | here =>
          cases right with
          | here => rfl
          | sample right =>
              simp [ProgramCursor.path] at h
      | sample left =>
          cases right with
          | here =>
              simp [ProgramCursor.path] at h
          | sample right =>
              simp only [ProgramCursor.path, List.length_cons,
                Nat.succ.injEq] at h
              exact congrArg ProgramCursor.sample (ih left right h)
  | commit x who R k ih =>
      cases left with
      | here =>
          cases right with
          | here => rfl
          | commit right =>
              simp [ProgramCursor.path] at h
      | commit left =>
          cases right with
          | here =>
              simp [ProgramCursor.path] at h
          | commit right =>
              simp only [ProgramCursor.path, List.length_cons,
                Nat.succ.injEq] at h
              exact congrArg ProgramCursor.commit (ih left right h)
  | reveal y who x hx k ih =>
      cases left with
      | here =>
          cases right with
          | here => rfl
          | reveal right =>
              simp [ProgramCursor.path] at h
      | reveal left =>
          cases right with
          | here =>
              simp [ProgramCursor.path] at h
          | reveal right =>
              simp only [ProgramCursor.path, List.length_cons,
                Nat.succ.injEq] at h
              exact congrArg ProgramCursor.reveal (ih left right h)

end ProgramCursor

theorem syntaxGraphRank_eq_path_length
    (g : WFProgram P L) (cursor : ProgramCursor g.prog) :
    syntaxGraphRank g cursor = cursor.path.length := by
  unfold syntaxGraphRank
  have h := ProgramCursor.path_length_add_syntaxSteps_prog
    (P := P) (L := L) cursor
  omega

theorem syntaxGraphRank_injective
    (g : WFProgram P L) :
    Function.Injective (syntaxGraphRank g) := by
  intro left right h
  apply ProgramCursor.eq_of_path_length_eq
  rw [← syntaxGraphRank_eq_path_length g left,
    ← syntaxGraphRank_eq_path_length g right]
  exact h

/-- Actor metadata at a syntax cursor. Only `commit` nodes are strategic
player actions; administrative, sample, reveal, and ret cursors are internal. -/
def syntaxGraphActor
    {g : WFProgram P L} (cursor : ProgramCursor g.prog) : Option P :=
  match cursor.prog with
  | .commit _ who _ _ => some who
  | _ => none

/-- Minimal parameter marker for the checked syntax graph. The actual dependent
value type and guard live in the cursor machine action alphabet; this marker is
only structural metadata saying that commit cursors require player input. -/
def syntaxGraphParams
    {g : WFProgram P L} (cursor : ProgramCursor g.prog) : List Unit :=
  match cursor.prog with
  | .commit _ _ _ _ => [()]
  | _ => []

/-- Strict linear order over checked syntax cursors. -/
def syntaxGraphPrecedes
    (g : WFProgram P L)
    (src dst : ProgramCursor g.prog) : Prop :=
  src ∈ syntaxGraphActions g ∧
    dst ∈ syntaxGraphActions g ∧
      syntaxGraphRank g src < syntaxGraphRank g dst

/-- Predecessors of a checked syntax cursor in the linear control graph. -/
noncomputable def syntaxGraphPredecessors
    (g : WFProgram P L)
    (cursor : ProgramCursor g.prog) : Finset (ProgramCursor g.prog) :=
  if cursor ∈ syntaxGraphActions g then
    (syntaxGraphActions g).filter
      (fun src => syntaxGraphRank g src < syntaxGraphRank g cursor)
  else
    ∅

/-- The checked Vegas syntax action graph.

This is the finite IR carrier for the current syntax frontend. It captures
linear control order and commit ownership directly from `ProgramCursor`. Values,
guards, public/private observations, and stochastic samples are supplied by the
checked graph semantics rather than duplicated in graph metadata. -/
noncomputable def syntaxActionGraph
    (g : WFProgram P L) :
    ActionGraph P (ProgramCursor g.prog) Unit Unit Unit Unit where
  actions := syntaxGraphActions g
  initialFields := ∅
  spec := fun cursor =>
    { params := syntaxGraphParams cursor
      join := none
      guard := () }
  actor := syntaxGraphActor
  fieldOwner := fun _ => none
  prereqs := fun cursor => syntaxGraphPredecessors g cursor
  writes := fun _ => ∅
  visibility := fun _ _ => .pub
  guardReads := fun _ => ∅
  rank := syntaxGraphRank g
  precedes := syntaxGraphPrecedes g
  predecessors := syntaxGraphPredecessors g
  prereq_precedes := by
    intro action prereq haction hpre
    have hmem :
        prereq ∈ (syntaxGraphActions g).filter
          (fun src => syntaxGraphRank g src < syntaxGraphRank g action) := by
      simpa [syntaxGraphPredecessors, haction] using hpre
    exact ⟨(Finset.mem_filter.mp hmem).1, haction,
      (Finset.mem_filter.mp hmem).2⟩
  precedes_left_mem := by
    intro src dst h
    exact h.1
  precedes_right_mem := by
    intro src dst h
    exact h.2.1
  precedes_iff_mem_predecessors := by
    intro src dst
    constructor
    · intro h
      simp [syntaxGraphPredecessors, h.2.1, h.1, h.2.2]
    · intro h
      by_cases hdst : dst ∈ syntaxGraphActions g
      · have hmem :
            src ∈ (syntaxGraphActions g).filter
              (fun src => syntaxGraphRank g src < syntaxGraphRank g dst) := by
          simpa [syntaxGraphPredecessors, hdst] using h
        exact ⟨(Finset.mem_filter.mp hmem).1, hdst,
          (Finset.mem_filter.mp hmem).2⟩
      · simp [syntaxGraphPredecessors, hdst] at h
  precedes_rank_lt := by
    intro src dst h
    exact h.2.2
  precedes_trans := by
    intro src mid dst hsm hmd
    exact ⟨hsm.1, hmd.2.1, Nat.lt_trans hsm.2.2 hmd.2.2⟩
  commit_writes_owned := by
    intro action field _haction hwrite _hvis
    simp at hwrite
  guardReads_observable_from_prior := by
    intro action field _haction hread
    simp at hread
  reveal_has_prior_commit := by
    intro action field _haction hwrite _hvis
    simp at hwrite

theorem syntaxActionGraph_frontier_subsingleton
    (g : WFProgram P L) (done : Finset (ProgramCursor g.prog))
    {left right : ProgramCursor g.prog}
    (hleft : left ∈ (syntaxActionGraph g).frontier done)
    (hright : right ∈ (syntaxActionGraph g).frontier done) :
    left = right := by
  let G := syntaxActionGraph g
  have hleftReady := (G.mem_frontier_iff done left).mp hleft
  have hrightReady := (G.mem_frontier_iff done right).mp hright
  by_cases hlt : syntaxGraphRank g left < syntaxGraphRank g right
  · have hpre : G.precedes left right :=
      ⟨hleftReady.1, hrightReady.1, hlt⟩
    have hdone :
        left ∈ done :=
      hrightReady.2.2 ((G.precedes_iff_mem_predecessors).mp hpre)
    exact False.elim (hleftReady.2.1 hdone)
  · by_cases hgt : syntaxGraphRank g right < syntaxGraphRank g left
    · have hpre : G.precedes right left :=
        ⟨hrightReady.1, hleftReady.1, hgt⟩
      have hdone :
          right ∈ done :=
        hleftReady.2.2 ((G.precedes_iff_mem_predecessors).mp hpre)
      exact False.elim (hrightReady.2.1 hdone)
    · have hrank :
          syntaxGraphRank g left = syntaxGraphRank g right := by
        exact Nat.le_antisymm (Nat.le_of_not_gt hgt)
          (Nat.le_of_not_gt hlt)
      exact syntaxGraphRank_injective g hrank

theorem syntaxActionGraph_frontier_card_eq_one_of_not_complete
    (g : WFProgram P L) (done : Finset (ProgramCursor g.prog))
    (hnot : ¬ (syntaxActionGraph g).CompleteAt done) :
    ((syntaxActionGraph g).frontier done).card = 1 := by
  let G := syntaxActionGraph g
  rcases G.frontier_nonempty_of_not_completeAt hnot with ⟨action, haction⟩
  have hfrontier :
      G.frontier done = {action} := by
    apply Finset.Subset.antisymm
    · intro other hother
      have hEq := syntaxActionGraph_frontier_subsingleton
        (g := g) (done := done) hother haction
      simp [hEq]
    · intro other hother
      have hEq : other = action := by
        simpa using hother
      simpa [hEq] using haction
  simp [G, hfrontier]

theorem syntaxActionGraph_card_advance_eq_succ_of_not_complete
    (g : WFProgram P L) (done : Finset (ProgramCursor g.prog))
    (hnot : ¬ (syntaxActionGraph g).CompleteAt done) :
    ((syntaxActionGraph g).advance done).card = done.card + 1 := by
  let G := syntaxActionGraph g
  have hcard :
      (G.frontier done).card = 1 :=
    syntaxActionGraph_frontier_card_eq_one_of_not_complete
      (g := g) (done := done) hnot
  have hdisj : Disjoint done (G.frontier done) :=
    (G.frontier_disjoint_done done).symm
  rw [ActionGraph.advance, Finset.card_union_of_disjoint hdisj]
  omega

/-- Total protocol-machine step for the checked cursor-world implementation.

Legal joint actions take the existing checked cursor transition. Illegal joint
actions stutter; they are unreachable under legal machine strategies, but
the underlying machine step is intentionally total. -/
noncomputable def step
    (g : WFProgram P L)
    (action : ∀ who : P, Option (ProgramAction g.prog who))
    (state : CursorCheckedWorld g) : PMF (CursorCheckedWorld g) := by
  classical
  exact
    if hlegal : CursorProgramJointActionLegal state action then
      cursorProgramTransition state ⟨action, hlegal⟩
    else
      PMF.pure state

/-- A program-local joint action where only `who` submits `action`. -/
def singleProgramJointAction
    (g : WFProgram P L) (who : P)
    (action : ProgramAction g.prog who) :
    ProgramJointAction g :=
  fun other =>
    if h : other = who then
      some (Eq.ndrec action (by cases h; rfl))
    else
      none

@[simp] theorem singleProgramJointAction_self
    (g : WFProgram P L) (who : P)
    (action : ProgramAction g.prog who) :
    singleProgramJointAction g who action who = some action := by
  simp [singleProgramJointAction]

@[simp] theorem singleProgramJointAction_other
    (g : WFProgram P L) {who other : P}
    (action : ProgramAction g.prog who) (hother : other ≠ who) :
    singleProgramJointAction g who action other = none := by
  simp [singleProgramJointAction, hother]

/-- Internal cursor-world events are administrative syntax steps:
`letExpr`, `sample`, and `reveal`. Terminal states may still have a total
selected turn, but no internal event is available there. -/
abbrev InternalEvent := Unit

/-- Internal events are available exactly at nonterminal states with no active
strategic player. -/
def availableInternal (g : WFProgram P L)
    (state : CursorCheckedWorld g) : Set InternalEvent :=
  { _event : InternalEvent | active state.toWorld = ∅ ∧
      ¬ terminal state.toWorld }

/-- Configuration carrier of the checked action-graph semantics. -/
abbrev GraphConfiguration (g : WFProgram P L) : Type :=
  (syntaxActionGraph g).Configuration (CursorCheckedWorld g)

/-- Current checked cursor world stored in a graph configuration.

The checked syntax graph uses one abstract graph field as the cursor-world
register. The initial configuration has not written that field yet, so it
projects to the checked initial cursor world. -/
noncomputable def cursorWorldOfGraphConfiguration
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (cfg : GraphConfiguration g) : CursorCheckedWorld g :=
  match History.lookup cfg.history.stack () with
  | some (.clear w) => w
  | some (.hidden w) => w
  | _ => CursorCheckedWorld.initial g hctx

/-- Advance the syntax frontier and store the next cursor world. -/
noncomputable def graphConfigurationAfterCursorWorld
    (g : WFProgram P L) (cfg : GraphConfiguration g)
    (next : CursorCheckedWorld g) : GraphConfiguration g where
  frontier := cfg.frontier.resolveEnabled
  history :=
    cfg.history.push
      (fun _field : Unit => some (StoredValue.clear next))
  partialFrontierAssignment := fun _field : Unit => none

@[simp] theorem cursorWorldOfGraphConfiguration_initial
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    cursorWorldOfGraphConfiguration g hctx
      (ActionGraph.Configuration.initial (syntaxActionGraph g)) =
      CursorCheckedWorld.initial g hctx := by
  simp [cursorWorldOfGraphConfiguration, ActionGraph.Configuration.initial,
    ActionGraph.BoundedHistory.empty, History.lookup]

@[simp] theorem cursorWorldOfGraphConfiguration_after
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (cfg : GraphConfiguration g) (next : CursorCheckedWorld g) :
    cursorWorldOfGraphConfiguration g hctx
      (graphConfigurationAfterCursorWorld g cfg next) = next := by
  unfold cursorWorldOfGraphConfiguration graphConfigurationAfterCursorWorld
  rw [ActionGraph.BoundedHistory.lookup_push]

@[simp] theorem graphConfigurationAfterCursorWorld_done
    (g : WFProgram P L) (cfg : GraphConfiguration g)
    (next : CursorCheckedWorld g) :
    (graphConfigurationAfterCursorWorld g cfg next).frontier.done =
      (syntaxActionGraph g).advance cfg.frontier.done := rfl

/-- Synchronization invariant for checked syntax graphs: the graph frontier has
resolved exactly the syntax actions strictly before the current cursor. -/
def syntaxGraphDoneBeforeCursor
    (g : WFProgram P L)
    (done : Finset (ProgramCursor g.prog))
    (cursor : ProgramCursor g.prog) : Prop :=
  ∀ action, action ∈ done ↔
    syntaxGraphRank g action < syntaxGraphRank g cursor

theorem syntaxGraphRank_lt_syntaxSteps_of_mem_actions
    (g : WFProgram P L) {cursor : ProgramCursor g.prog}
    (hmem : cursor ∈ syntaxGraphActions g) :
    syntaxGraphRank g cursor < syntaxSteps g.prog := by
  classical
  letI : Fintype (ProgramCursor g.prog) :=
    ProgramCursor.instFintype g.prog
  have hpositive : 0 < syntaxSteps cursor.prog := by
    have hfilter :
        cursor ∈ (Finset.univ.filter
          (fun cursor : ProgramCursor g.prog => 0 < syntaxSteps cursor.prog)) := by
      simpa [syntaxGraphActions] using hmem
    exact (Finset.mem_filter.mp hfilter).2
  unfold syntaxGraphRank
  have hpath := ProgramCursor.path_length_add_syntaxSteps_prog
    (P := P) (L := L) cursor
  omega

theorem syntaxGraphDoneBeforeCursor_initial
    (g : WFProgram P L) :
    syntaxGraphDoneBeforeCursor g ∅ ProgramCursor.here := by
  intro action
  constructor
  · intro h
    simp at h
  · intro hlt
    have hzero :
        syntaxGraphRank g ProgramCursor.here = 0 := by
      unfold syntaxGraphRank
      exact Nat.sub_self (syntaxSteps g.prog)
    rw [hzero] at hlt
    exact False.elim (Nat.not_lt_zero _ hlt)

theorem syntaxGraphDoneBeforeCursor_current_not_done
    (g : WFProgram P L)
    {done : Finset (ProgramCursor g.prog)}
    {cursor : ProgramCursor g.prog}
    (hinv : syntaxGraphDoneBeforeCursor g done cursor) :
    cursor ∉ done := by
  intro hdone
  exact Nat.lt_irrefl _
    ((hinv cursor).mp hdone)

theorem syntaxGraphDoneBeforeCursor_cursor_nonterminal_of_not_complete
    (g : WFProgram P L)
    {done : Finset (ProgramCursor g.prog)}
    {cursor : ProgramCursor g.prog}
    (hinv : syntaxGraphDoneBeforeCursor g done cursor)
    (hnotComplete : ¬ (syntaxActionGraph g).CompleteAt done) :
    0 < syntaxSteps cursor.prog := by
  by_contra hnotPositive
  have hzero : syntaxSteps cursor.prog = 0 := Nat.eq_zero_of_not_pos hnotPositive
  have hcursorRank :
      syntaxGraphRank g cursor = syntaxSteps g.prog := by
    unfold syntaxGraphRank
    simp [hzero]
  have hcomplete : (syntaxActionGraph g).CompleteAt done := by
    intro action haction
    have hrankLt :
        syntaxGraphRank g action < syntaxGraphRank g cursor := by
      rw [hcursorRank]
      exact syntaxGraphRank_lt_syntaxSteps_of_mem_actions
        (g := g) haction
    exact (hinv action).mpr hrankLt
  exact hnotComplete hcomplete

theorem syntaxGraphDoneBeforeCursor_advance
    (g : WFProgram P L)
    {done : Finset (ProgramCursor g.prog)}
    {current next : ProgramCursor g.prog}
    (hcurrent : current ∈ syntaxGraphActions g)
    (hinv : syntaxGraphDoneBeforeCursor g done current)
    (hrankNext :
      syntaxGraphRank g next = syntaxGraphRank g current + 1) :
    syntaxGraphDoneBeforeCursor g
      ((syntaxActionGraph g).advance done) next := by
  intro action
  let G := syntaxActionGraph g
  constructor
  · intro hdone
    rw [G.mem_advance_iff] at hdone
    rcases hdone with hdone | hready
    · have hlt := (hinv action).mp hdone
      omega
    · have hnotDone : action ∉ done := hready.2.1
      have hnotLtCurrent :
          ¬ syntaxGraphRank g action < syntaxGraphRank g current := by
        intro hlt
        exact hnotDone ((hinv action).mpr hlt)
      have hcurrentLe :
          syntaxGraphRank g current ≤ syntaxGraphRank g action :=
        Nat.le_of_not_gt hnotLtCurrent
      have hnotCurrentLt :
          ¬ syntaxGraphRank g current < syntaxGraphRank g action := by
        intro hlt
        have hpre : G.precedes current action :=
          ⟨hcurrent, hready.1, hlt⟩
        have hcurrentDone :
            current ∈ done :=
          hready.2.2 ((G.precedes_iff_mem_predecessors).mp hpre)
        exact syntaxGraphDoneBeforeCursor_current_not_done
          (g := g) hinv hcurrentDone
      have hactionLe :
          syntaxGraphRank g action ≤ syntaxGraphRank g current :=
        Nat.le_of_not_gt hnotCurrentLt
      have hrank :
          syntaxGraphRank g action = syntaxGraphRank g current :=
        Nat.le_antisymm hactionLe hcurrentLe
      omega
  · intro hltNext
    change action ∈ G.advance done
    rw [G.mem_advance_iff]
    have hle :
        syntaxGraphRank g action ≤ syntaxGraphRank g current := by
      omega
    rcases Nat.lt_or_eq_of_le hle with hlt | hrankEq
    · exact Or.inl ((hinv action).mpr hlt)
    · right
      have hEq : action = current :=
        syntaxGraphRank_injective g hrankEq
      subst action
      refine ⟨hcurrent, ?_, ?_⟩
      · exact syntaxGraphDoneBeforeCursor_current_not_done
          (g := g) hinv
      · intro prior hprior
        have hpre : G.precedes prior current :=
          (G.precedes_iff_mem_predecessors).mpr hprior
        exact (hinv prior).mpr (G.precedes_rank_lt hpre)

theorem syntaxGraphRank_cursor_eq_succ_of_remainingSyntaxSteps
    (g : WFProgram P L)
    {current next : CursorCheckedWorld g}
    (hremaining : next.remainingSyntaxSteps + 1 =
      current.remainingSyntaxSteps) :
    syntaxGraphRank g next.1.cursor =
      syntaxGraphRank g current.1.cursor + 1 := by
  have hrem :
      syntaxSteps next.1.cursor.prog + 1 =
        syntaxSteps current.1.cursor.prog := by
    simpa [CursorCheckedWorld.remainingSyntaxSteps, CursorWorldData.prog]
      using hremaining
  have hcurPath := ProgramCursor.path_length_add_syntaxSteps_prog
    (P := P) (L := L) current.1.cursor
  have hnextPath := ProgramCursor.path_length_add_syntaxSteps_prog
    (P := P) (L := L) next.1.cursor
  unfold syntaxGraphRank
  omega

/-- Player choices available in the checked graph machine.

Legality of the concrete dependent value is inherited from the checked cursor
semantics. The graph contributes the frontier-terminal guard. -/
def graphAvailable
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (cfg : GraphConfiguration g) (who : P) :
    Set (ProgramAction g.prog who) :=
  { action |
      ¬ cfg.isTerminal ∧
        action ∈ CursorCheckedWorld.availableProgramActions
          (cursorWorldOfGraphConfiguration g hctx cfg) who }

/-- Internal events available in the checked graph machine.

For well-formed reachable configurations this coincides with the cursor
machine's administrative states. On malformed nonterminal graph configurations
whose stored cursor is already terminal, the event remains available so the
frontier machine can drain to completion instead of blocking a generic FOSG
view over all configurations. -/
def graphAvailableInternal
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (cfg : GraphConfiguration g) : Set InternalEvent :=
  { _event |
      ¬ cfg.isTerminal ∧
        active (cursorWorldOfGraphConfiguration g hctx cfg).toWorld = ∅ }

/-- Player step of the checked action-graph semantics. Unavailable choices
stutter; available choices execute the checked cursor step and then advance the
syntax frontier by one graph layer. -/
noncomputable def graphStepPlay
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (action : ProgramAction g.prog who)
    (cfg : GraphConfiguration g) : PMF (GraphConfiguration g) := by
  classical
  exact
    if action ∈ graphAvailable g hctx cfg who then
      (step g (singleProgramJointAction g who action)
          (cursorWorldOfGraphConfiguration g hctx cfg)).map
        (graphConfigurationAfterCursorWorld g cfg)
    else
      PMF.pure cfg

/-- Internal step of the checked action-graph semantics. Unavailable internal
events stutter; available ones execute the checked administrative cursor step
and then advance the syntax frontier by one graph layer. -/
noncomputable def graphStepInternal
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (event : InternalEvent) (cfg : GraphConfiguration g) :
    PMF (GraphConfiguration g) := by
  classical
  exact
    if event ∈ graphAvailableInternal g hctx cfg then
      (step g (GameTheory.FOSG.noopAction
          (fun who : P => ProgramAction g.prog who))
          (cursorWorldOfGraphConfiguration g hctx cfg)).map
        (graphConfigurationAfterCursorWorld g cfg)
    else
      PMF.pure cfg

theorem graphStepPlay_done_eq_or_advance_of_support
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    {who : P} {action : ProgramAction g.prog who}
    {source target : GraphConfiguration g}
    (hmem : target ∈ (graphStepPlay g hctx who action source).support) :
    target.frontier.done = source.frontier.done ∨
      target.frontier.done =
        (syntaxActionGraph g).advance source.frontier.done := by
  classical
  by_cases havailable : action ∈ graphAvailable g hctx source who
  · right
    have hmap :
        target ∈
          (PMF.map (graphConfigurationAfterCursorWorld g source)
            (step g (singleProgramJointAction g who action)
              (cursorWorldOfGraphConfiguration g hctx source))).support := by
      simpa [graphStepPlay, havailable] using hmem
    rcases (PMF.mem_support_map_iff
        (f := graphConfigurationAfterCursorWorld g source)
        (p := step g (singleProgramJointAction g who action)
          (cursorWorldOfGraphConfiguration g hctx source))
        (b := target)).mp hmap with ⟨next, _hnext, htarget⟩
    rw [← htarget]
    rfl
  · left
    have htarget : target = source := by
      simpa [graphStepPlay, havailable] using hmem
    subst htarget
    rfl

theorem graphStepInternal_done_eq_or_advance_of_support
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    {event : InternalEvent} {source target : GraphConfiguration g}
    (hmem : target ∈ (graphStepInternal g hctx event source).support) :
    target.frontier.done = source.frontier.done ∨
      target.frontier.done =
        (syntaxActionGraph g).advance source.frontier.done := by
  classical
  by_cases havailable : event ∈ graphAvailableInternal g hctx source
  · right
    have hmap :
        target ∈
          (PMF.map (graphConfigurationAfterCursorWorld g source)
            (step g (GameTheory.FOSG.noopAction
                (fun who : P => ProgramAction g.prog who))
              (cursorWorldOfGraphConfiguration g hctx source))).support := by
      simpa [graphStepInternal, havailable] using hmem
    rcases (PMF.mem_support_map_iff
        (f := graphConfigurationAfterCursorWorld g source)
        (p := step g (GameTheory.FOSG.noopAction
            (fun who : P => ProgramAction g.prog who))
          (cursorWorldOfGraphConfiguration g hctx source))
        (b := target)).mp hmap with ⟨next, _hnext, htarget⟩
    rw [← htarget]
    rfl
  · left
    have htarget : target = source := by
      simpa [graphStepInternal, havailable] using hmem
    subst htarget
    rfl

theorem graphStepPlay_done_eq_advance_of_available_of_support
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    {who : P} {action : ProgramAction g.prog who}
    {source target : GraphConfiguration g}
    (havailable : action ∈ graphAvailable g hctx source who)
    (hmem : target ∈ (graphStepPlay g hctx who action source).support) :
    target.frontier.done =
      (syntaxActionGraph g).advance source.frontier.done := by
  have hmap :
      target ∈
        (PMF.map (graphConfigurationAfterCursorWorld g source)
          (step g (singleProgramJointAction g who action)
            (cursorWorldOfGraphConfiguration g hctx source))).support := by
    simpa [graphStepPlay, havailable] using hmem
  rcases (PMF.mem_support_map_iff
      (f := graphConfigurationAfterCursorWorld g source)
      (p := step g (singleProgramJointAction g who action)
        (cursorWorldOfGraphConfiguration g hctx source))
      (b := target)).mp hmap with ⟨next, _hnext, htarget⟩
  rw [← htarget]
  rfl

theorem graphStepInternal_done_eq_advance_of_available_of_support
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    {event : InternalEvent} {source target : GraphConfiguration g}
    (havailable : event ∈ graphAvailableInternal g hctx source)
    (hmem : target ∈ (graphStepInternal g hctx event source).support) :
    target.frontier.done =
      (syntaxActionGraph g).advance source.frontier.done := by
  have hmap :
      target ∈
        (PMF.map (graphConfigurationAfterCursorWorld g source)
          (step g (GameTheory.FOSG.noopAction
              (fun who : P => ProgramAction g.prog who))
            (cursorWorldOfGraphConfiguration g hctx source))).support := by
    simpa [graphStepInternal, havailable] using hmem
  rcases (PMF.mem_support_map_iff
      (f := graphConfigurationAfterCursorWorld g source)
      (p := step g (GameTheory.FOSG.noopAction
          (fun who : P => ProgramAction g.prog who))
        (cursorWorldOfGraphConfiguration g hctx source))
      (b := target)).mp hmap with ⟨next, _hnext, htarget⟩
  rw [← htarget]
  rfl

/-- Canonical checked protocol machine executing the syntax action graph. -/
noncomputable def graphMachine
    (g : WFProgram P L) (hctx : WFCtx g.Γ) : Machine P where
  State := GraphConfiguration g
  Action := fun who => ProgramAction g.prog who
  Internal := InternalEvent
  Public := PublicObs g hctx
  Obs := fun who => PrivateObs g who
  Outcome := Outcome P
  init := ActionGraph.Configuration.initial (syntaxActionGraph g)
  available := graphAvailable g hctx
  availableInternal := graphAvailableInternal g hctx
  stepPlay := graphStepPlay g hctx
  stepInternal := graphStepInternal g hctx
  terminal := ActionGraph.Configuration.isTerminal
  publicView := fun cfg =>
    publicObsOfCursorWorld (hctx := hctx)
      (cursorWorldOfGraphConfiguration g hctx cfg)
  observe := fun who cfg =>
    privateObsOfCursorWorld who
      (cursorWorldOfGraphConfiguration g hctx cfg)
  outcome := fun cfg =>
    cursorWorldOutcome (cursorWorldOfGraphConfiguration g hctx cfg)
  utility := fun outcome who => (outcome who : ℝ)

@[simp] theorem graphMachine_init
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    (graphMachine g hctx).init =
      ActionGraph.Configuration.initial (syntaxActionGraph g) := rfl

@[simp] theorem graphMachine_terminal
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (cfg : (graphMachine g hctx).State) :
    (graphMachine g hctx).terminal cfg = cfg.isTerminal := rfl

/-- Available graph player steps project to the checked cursor step used as
the graph-machine value evaluator. -/
theorem graphStepPlay_project_cursorWorld_of_available
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    {who : P} {action : ProgramAction g.prog who}
    {cfg : GraphConfiguration g}
    (havailable : action ∈ graphAvailable g hctx cfg who) :
    PMF.map (cursorWorldOfGraphConfiguration g hctx)
        (graphStepPlay g hctx who action cfg) =
      step g (singleProgramJointAction g who action)
        (cursorWorldOfGraphConfiguration g hctx cfg) := by
  classical
  rw [graphStepPlay]
  rw [if_pos havailable]
  rw [PMF.map_comp]
  have hfun :
      (cursorWorldOfGraphConfiguration g hctx ∘
          graphConfigurationAfterCursorWorld g cfg) = id := by
    funext next
    simp
  rw [hfun]
  exact PMF.map_id _

/-- Available graph internal steps project to the original checked cursor
administrative step. -/
theorem graphStepInternal_project_cursorWorld_of_available
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    {event : InternalEvent} {cfg : GraphConfiguration g}
    (havailable : event ∈ graphAvailableInternal g hctx cfg) :
    PMF.map (cursorWorldOfGraphConfiguration g hctx)
        (graphStepInternal g hctx event cfg) =
      step g (GameTheory.FOSG.noopAction
          (fun who : P => ProgramAction g.prog who))
        (cursorWorldOfGraphConfiguration g hctx cfg) := by
  classical
  rw [graphStepInternal]
  rw [if_pos havailable]
  rw [PMF.map_comp]
  have hfun :
      (cursorWorldOfGraphConfiguration g hctx ∘
          graphConfigurationAfterCursorWorld g cfg) = id := by
    funext next
    simp
  rw [hfun]
  exact PMF.map_id _

/-- Program joint action represented by one checked graph-machine event. -/
def graphMachineJointAction
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    (graphMachine g hctx).Event → ProgramJointAction g
  | .play who action => singleProgramJointAction g who action
  | .internal _ =>
      GameTheory.FOSG.noopAction (fun who : P => ProgramAction g.prog who)

/-- Turn selected by the graph-machine FOSG view. The graph frontier supplies
terminality; the stored checked cursor world supplies the syntax-local player
or internal event shape. -/
noncomputable def graphMachineTurn
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (pref : (graphMachine g hctx).RunPrefix) :
    (graphMachine g hctx).Turn := by
  classical
  exact
    if pref.lastState.isTerminal then
      .internal ()
    else
      match (cursorWorldOfGraphConfiguration g hctx pref.lastState).1.cursor.prog with
      | .commit _ who _ _ => .play who
      | _ => .internal ()

/-- Direct FOSG view of the checked action-graph machine. -/
noncomputable def fosgView
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    (graphMachine g hctx).FOSGView where
  turn := graphMachineTurn g hctx
  terminal_not_play := by
    intro pref player hterminal hplay
    have hterm : pref.lastState.isTerminal := by
      simpa [graphMachine_terminal] using hterminal
    simp [graphMachineTurn, hterm] at hplay
  turn_available := by
    intro pref hterminal
    have hgraph : ¬ pref.lastState.isTerminal := by
      simpa [graphMachine_terminal] using hterminal
    let w := cursorWorldOfGraphConfiguration g hctx pref.lastState
    cases hprog : w.1.cursor.prog with
    | ret payoffs =>
        have hactive : active w.toWorld = ∅ := by
          simp [w, active, CursorCheckedWorld.toWorld,
            CursorWorldData.prog, hprog]
        have hturn :
            graphMachineTurn g hctx pref = Machine.Turn.internal () := by
          simp [graphMachineTurn, hgraph, w, hprog]
        rw [hturn]
        change () ∈ graphAvailableInternal g hctx pref.lastState
        exact ⟨hgraph, hactive⟩
    | letExpr x e k =>
        have hactive : active w.toWorld = ∅ :=
          cursor_active_eq_empty_of_letExpr
            (by simpa [w, CursorWorldData.prog] using hprog)
        have hturn :
            graphMachineTurn g hctx pref = Machine.Turn.internal () := by
          simp [graphMachineTurn, hgraph, w, hprog]
        rw [hturn]
        change () ∈ graphAvailableInternal g hctx pref.lastState
        exact ⟨hgraph, hactive⟩
    | sample x D k =>
        have hactive : active w.toWorld = ∅ :=
          cursor_active_eq_empty_of_sample
            (by simpa [w, CursorWorldData.prog] using hprog)
        have hturn :
            graphMachineTurn g hctx pref = Machine.Turn.internal () := by
          simp [graphMachineTurn, hgraph, w, hprog]
        rw [hturn]
        change () ∈ graphAvailableInternal g hctx pref.lastState
        exact ⟨hgraph, hactive⟩
    | commit x who R k =>
        have hcursor : ¬ terminal w.toWorld :=
          cursor_not_terminal_of_commit
            (by simpa [w, CursorWorldData.prog] using hprog)
        rcases cursor_nonterminal_exists_program_legal
            (w := w) hcursor with
          ⟨joint, hlegal⟩
        have hlocal := hlegal.2 who
        cases hmove : joint who with
        | none =>
            have hactive : who ∈ active w.toWorld := by
              rw [cursor_active_eq_singleton_of_commit
                (by simpa [w, CursorWorldData.prog] using hprog)]
              simp
            have hnot : who ∉ active w.toWorld := by
              simpa [hmove] using hlocal
            exact False.elim (hnot hactive)
        | some action =>
            have hpair :
                who ∈ active w.toWorld ∧
                  action ∈ CursorCheckedWorld.availableProgramActions w who := by
              simpa [hmove] using hlocal
            have hturn :
                graphMachineTurn g hctx pref = Machine.Turn.play who := by
              simp [graphMachineTurn, hgraph, w, hprog]
            rw [hturn]
            change ∃ action : ProgramAction g.prog who,
              action ∈ graphAvailable g hctx pref.lastState who
            exact ⟨action, ⟨hgraph, by simpa [w] using hpair.2⟩⟩
    | reveal y who x hx k =>
        have hactive : active w.toWorld = ∅ :=
          cursor_active_eq_empty_of_reveal
            (by simpa [w, CursorWorldData.prog] using hprog)
        have hturn :
            graphMachineTurn g hctx pref = Machine.Turn.internal () := by
          simp [graphMachineTurn, hgraph, w, hprog]
        rw [hturn]
        change () ∈ graphAvailableInternal g hctx pref.lastState
        exact ⟨hgraph, hactive⟩
  reward := by
    classical
    exact fun src event dst who =>
      let action := graphMachineJointAction g hctx event
      let srcw := cursorWorldOfGraphConfiguration g hctx src.lastState
      let dstw := cursorWorldOfGraphConfiguration g hctx dst.lastState
      if hlegal : CursorProgramJointActionLegal srcw action then
        rewardOnEnteringRetCursor srcw ⟨action, hlegal⟩ dstw who
      else
        0

/-- Sequential FOSG presentation derived directly from the checked graph
machine. -/
noncomputable def fosg
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    GameTheory.FOSG P (graphMachine g hctx).RunPrefix
      (graphMachine g hctx).Action
      (graphMachine g hctx).Obs
      (graphMachine g hctx).Public :=
  (fosgView g hctx).toFOSG

/-- Horizon-bounded graph-machine FOSG presentation. -/
noncomputable def boundedFOSG
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (horizon : Nat) :
    GameTheory.FOSG P ((graphMachine g hctx).BoundedRunPrefix horizon)
      (graphMachine g hctx).Action
      (graphMachine g hctx).Obs
      (graphMachine g hctx).Public :=
  (fosgView g hctx).toBoundedFOSG horizon

/-- Syntax-horizon graph-machine FOSG presentation. -/
noncomputable def finiteFOSG
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    GameTheory.FOSG P
      ((graphMachine g hctx).BoundedRunPrefix (syntaxSteps g.prog))
      (graphMachine g hctx).Action
      (graphMachine g hctx).Obs
      (graphMachine g hctx).Public :=
  boundedFOSG g hctx (syntaxSteps g.prog)

theorem fosgView_active_eq_cursor_active_of_not_terminal
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (pref : (graphMachine g hctx).RunPrefix)
    (hnot : ¬ pref.lastState.isTerminal) :
    (fosgView g hctx).active pref =
      active (cursorWorldOfGraphConfiguration g hctx pref.lastState).toWorld := by
  let w := cursorWorldOfGraphConfiguration g hctx pref.lastState
  cases hprog : w.1.cursor.prog <;>
    simp [Machine.FOSGView.active, fosgView, graphMachineTurn,
      hnot, w, active, CursorCheckedWorld.toWorld,
      CursorWorldData.prog, active, hprog]

theorem fosgView_availableActions_eq_cursor_availableProgramActions_of_not_terminal
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (pref : (graphMachine g hctx).RunPrefix) (who : P)
    (hnot : ¬ pref.lastState.isTerminal) :
    (fosgView g hctx).availableActions pref who =
      CursorCheckedWorld.availableProgramActions
        (cursorWorldOfGraphConfiguration g hctx pref.lastState) who := by
  ext action
  let w := cursorWorldOfGraphConfiguration g hctx pref.lastState
  cases hprog : w.1.cursor.prog with
  | ret payoffs =>
      constructor
      · intro hleft
        have hfalse := hleft
        simp [Machine.FOSGView.availableActions, fosgView,
          graphMachineTurn, hnot, w, hprog] at hfalse
      · intro hright
        rcases hright with ⟨hbroad, _⟩
        have hfalse := hbroad
        simp [availableActions, CursorCheckedWorld.toWorld,
          CursorWorldData.prog, availableActions, w, hprog] at hfalse
  | letExpr x e k =>
      constructor
      · intro hleft
        have hfalse := hleft
        simp [Machine.FOSGView.availableActions, fosgView,
          graphMachineTurn, hnot, w, hprog] at hfalse
      · intro hright
        rcases hright with ⟨hbroad, _⟩
        have hfalse := hbroad
        simp [availableActions, CursorCheckedWorld.toWorld,
          CursorWorldData.prog, availableActions, w, hprog] at hfalse
  | sample x D k =>
      constructor
      · intro hleft
        have hfalse := hleft
        simp [Machine.FOSGView.availableActions, fosgView,
          graphMachineTurn, hnot, w, hprog] at hfalse
      · intro hright
        rcases hright with ⟨hbroad, _⟩
        have hfalse := hbroad
        simp [availableActions, CursorCheckedWorld.toWorld,
          CursorWorldData.prog, availableActions, w, hprog] at hfalse
  | commit x owner R k =>
      by_cases hwho : who = owner
      · subst who
        unfold Machine.FOSGView.availableActions
        have hturn :
            (fosgView g hctx).turn pref =
              Machine.Turn.play owner := by
          simp [fosgView, graphMachineTurn, hnot, w, hprog]
        rw [hturn]
        simp only [↓reduceIte]
        change
          action ∈ graphAvailable g hctx pref.lastState owner ↔
            action ∈ CursorCheckedWorld.availableProgramActions
              (cursorWorldOfGraphConfiguration g hctx pref.lastState) owner
        constructor
        · intro h
          exact h.2
        · intro h
          exact ⟨hnot, h⟩
      · constructor
        · intro hleft
          have hfalse := hleft
          simp [Machine.FOSGView.availableActions, fosgView,
            graphMachineTurn, hnot, w, hprog, hwho] at hfalse
        · intro hright
          rcases hright with
            ⟨_hbroad, x', owner', b', R', k',
              hprogAction, hownerAction, _hcursor⟩
          unfold CursorWorldData.prog at hprogAction
          rw [hprog] at hprogAction
          cases hprogAction
          exact False.elim (hwho hownerAction.symm)
  | reveal y owner x hx k =>
      constructor
      · intro hleft
        have hfalse := hleft
        simp [Machine.FOSGView.availableActions, fosgView,
          graphMachineTurn, hnot, w, hprog] at hfalse
      · intro hright
        rcases hright with ⟨hbroad, _⟩
        have hfalse := hbroad
        simp [availableActions, CursorCheckedWorld.toWorld,
          CursorWorldData.prog, availableActions, w, hprog] at hfalse

/-- Finite state helper for the checked graph machine. -/
@[reducible] noncomputable instance graphMachine.instFintypeState
    (g : WFProgram P L) (hctx : WFCtx g.Γ) [FiniteDomains g] :
    Fintype (graphMachine g hctx).State := by
  classical
  letI : Fintype (ProgramCursor g.prog) :=
    ProgramCursor.instFintype g.prog
  letI : DecidableEq (CursorCheckedWorld g) := Classical.decEq _
  letI : Fintype (CursorCheckedWorld g) :=
    CursorCheckedWorld.instFintype g
  change Fintype (GraphConfiguration g)
  infer_instance

/-- Finite action helper for the checked graph machine. -/
@[reducible] noncomputable instance graphMachine.instFintypeAction
    (g : WFProgram P L) (hctx : WFCtx g.Γ) [FiniteDomains g]
    (who : P) :
    Fintype ((graphMachine g hctx).Action who) :=
  cursorFOSG.instFintypeAction g hctx who

/-- Finite optional-action helper for the checked graph machine. -/
@[reducible] noncomputable instance graphMachine.instFintypeOptionAction
    (g : WFProgram P L) (hctx : WFCtx g.Γ) [FiniteDomains g]
    (who : P) :
    Fintype (Option ((graphMachine g hctx).Action who)) :=
  cursorFOSG.instFintypeOptionAction g hctx who

/-- Finite primitive-event helper for the checked graph machine. -/
@[reducible] noncomputable instance graphMachine.instFintypeEvent
    (g : WFProgram P L) (hctx : WFCtx g.Γ) [FiniteDomains g]
    [Fintype P] :
    Fintype (graphMachine g hctx).Event := by
  classical
  letI : ∀ who : P, Fintype (ProgramAction g.prog who) :=
    fun who => cursorFOSG.instFintypeAction g hctx who
  letI : Fintype InternalEvent := by
    dsimp [InternalEvent]
    infer_instance
  letI : Fintype (graphMachine g hctx).Internal := by
    change Fintype InternalEvent
    infer_instance
  let playEvents : Finset (graphMachine g hctx).Event :=
    (Finset.univ :
      Finset (Sigma fun who : P => ProgramAction g.prog who)).image
        (fun x => Machine.Event.play x.1 x.2)
  let internalEvents : Finset (graphMachine g hctx).Event :=
    (Finset.univ : Finset (graphMachine g hctx).Internal).image
      (fun event => Machine.Event.internal event)
  refine Fintype.mk (playEvents ∪ internalEvents) ?_
  intro event
  cases event with
  | play who action =>
      exact Finset.mem_union.mpr
        (Or.inl
          (Finset.mem_image.mpr
            ⟨⟨who, action⟩, Finset.mem_univ _, rfl⟩))
  | internal event =>
      exact Finset.mem_union.mpr
        (Or.inr
          (Finset.mem_image.mpr
            ⟨event, Finset.mem_univ _, rfl⟩))

/-- Finite-history helper for bounded graph-machine FOSG views. -/
@[reducible] noncomputable instance boundedFOSG.instFintypeHistory
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (horizon : Nat)
    [Fintype P]
    [Fintype (graphMachine g hctx).State]
    [∀ who : P, Fintype (Option ((graphMachine g hctx).Action who))]
    [Fintype (graphMachine g hctx).Event] :
    Fintype (boundedFOSG g hctx horizon).History := by
  classical
  haveI :
      Fintype ((graphMachine g hctx).BoundedRunPrefix horizon) :=
    Machine.BoundedRunPrefix.instFintype
  exact GameTheory.FOSG.historyFintypeOfBoundedHorizon
    (G := boundedFOSG g hctx horizon)
    ((fosgView g hctx).toBoundedFOSG_boundedHorizon horizon)

/-- Finite-history instance for the bounded FOSG view in its direct view form. -/
@[reducible] noncomputable instance fosgView.instFintypeBoundedHistory
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (horizon : Nat)
    [Fintype P] [FiniteDomains g] :
    Fintype (((fosgView g hctx).toBoundedFOSG horizon).History) := by
  change Fintype (boundedFOSG g hctx horizon).History
  infer_instance

/-- Terminal decidability for the bounded FOSG view in its direct view form. -/
noncomputable instance fosgView.instDecidablePredBoundedTerminal
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (horizon : Nat) :
    DecidablePred (((fosgView g hctx).toBoundedFOSG horizon).terminal) :=
  Classical.decPred _

/-- Finite-history helper for the syntax-horizon graph-machine FOSG. -/
@[reducible] noncomputable instance finiteFOSG.instFintypeHistory
    (g : WFProgram P L) (hctx : WFCtx g.Γ) [FiniteDomains g]
    [Fintype P] :
    Fintype (finiteFOSG g hctx).History := by
  letI : Fintype (graphMachine g hctx).State :=
    graphMachine.instFintypeState g hctx
  letI : ∀ who : P,
      Fintype (Option ((graphMachine g hctx).Action who)) :=
    fun who => graphMachine.instFintypeOptionAction g hctx who
  letI : Fintype (graphMachine g hctx).Event :=
    graphMachine.instFintypeEvent g hctx
  exact boundedFOSG.instFintypeHistory
    g hctx (syntaxSteps g.prog)

/-- Pointwise cursor availability at a nonterminal endpoint packages to the
existing cursor joint-action legality predicate. -/
theorem cursorProgramJointActionLegal_of_mem_availableProgramMovesAt
    (g : WFProgram P L)
    {state : CursorCheckedWorld g}
    {action : ∀ who : P, Option (ProgramAction g.prog who)}
    (hterminal : ¬ terminal state.toWorld)
    (hmove :
      ∀ who : P,
        action who ∈ CursorCheckedWorld.availableProgramMovesAt
          state.1.prog state.1.env state.1.suffix who) :
    CursorProgramJointActionLegal state action := by
  refine ⟨hterminal, ?_⟩
  intro who
  specialize hmove who
  cases haction : action who with
  | none =>
      simpa [CursorProgramJointActionLegal,
        CursorCheckedWorld.availableProgramMovesAt,
        active, CursorWorldData.prog,
        CursorWorldData.suffix, haction] using hmove
  | some ai =>
      simpa [CursorProgramJointActionLegal,
        CursorCheckedWorld.availableProgramMovesAt,
        CursorCheckedWorld.availableProgramActions,
        active, CursorWorldData.prog,
        CursorWorldData.suffix, haction] using hmove

theorem step_eq_cursorProgramTransition_of_legal
    (g : WFProgram P L)
    {state : CursorCheckedWorld g}
    {action : ∀ who : P, Option (ProgramAction g.prog who)}
    (hlegal : CursorProgramJointActionLegal state action) :
    step g action state =
      cursorProgramTransition state ⟨action, hlegal⟩ := by
  simp [step, hlegal]

theorem step_eq_pure_of_not_legal
    (g : WFProgram P L)
    {state : CursorCheckedWorld g}
    {action : ∀ who : P, Option (ProgramAction g.prog who)}
    (hlegal : ¬ CursorProgramJointActionLegal state action) :
    step g action state = PMF.pure state := by
  simp [step, hlegal]

/-- An available graph-machine event determines a legal cursor-world joint
action whenever the projected cursor world is nonterminal.

The nonterminal premise is necessary because the graph FOSG view deliberately
drains malformed graph configurations whose frontier is not complete but whose
stored cursor is already terminal. Reachable checked graph histories satisfy
this premise before the syntax cutoff. -/
theorem cursorProgramJointActionLegal_of_graphMachine_available
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    {state : (graphMachine g hctx).State}
    {event : (graphMachine g hctx).Event}
    (hcursor :
      ¬ terminal (cursorWorldOfGraphConfiguration g hctx state).toWorld)
    (havailable : (graphMachine g hctx).EventAvailable state event) :
    CursorProgramJointActionLegal
      (cursorWorldOfGraphConfiguration g hctx state)
      (graphMachineJointAction g hctx event) := by
  classical
  let w := cursorWorldOfGraphConfiguration g hctx state
  cases event with
  | internal internalEvent =>
      have hinternal :
          internalEvent ∈ graphAvailableInternal g hctx state := by
        simpa [graphMachine] using havailable
      exact cursorProgramJointActionLegal_of_mem_availableProgramMovesAt
        g hcursor (by
          intro who
          have hnot : who ∉ active w.toWorld := by
            rw [hinternal.2]
            simp
          simpa [graphMachineJointAction,
            CursorCheckedWorld.availableProgramMovesAt,
            active, w] using hnot)
  | play who action =>
      have hgraphAvailable :
          action ∈ graphAvailable g hctx state who := by
        simpa [graphMachine] using havailable
      have haction :
          action ∈ CursorCheckedWorld.availableProgramActions w who :=
        hgraphAvailable.2
      cases hprog : w.1.cursor.prog with
      | ret payoffs =>
          rcases haction.2 with
            ⟨x', owner', b', R', k', hprogAction, _hownerAction, _hcursor⟩
          unfold CursorWorldData.prog at hprogAction
          rw [hprog] at hprogAction
          cases hprogAction
      | letExpr x e k =>
          rcases haction.2 with
            ⟨x', owner', b', R', k', hprogAction, _hownerAction, _hcursor⟩
          unfold CursorWorldData.prog at hprogAction
          rw [hprog] at hprogAction
          cases hprogAction
      | sample x D k =>
          rcases haction.2 with
            ⟨x', owner', b', R', k', hprogAction, _hownerAction, _hcursor⟩
          unfold CursorWorldData.prog at hprogAction
          rw [hprog] at hprogAction
          cases hprogAction
      | commit x owner R k =>
          rcases haction.2 with
            ⟨x', owner', b', R', k', hprogAction, hownerAction, _hcursor⟩
          unfold CursorWorldData.prog at hprogAction
          rw [hprog] at hprogAction
          cases hprogAction
          cases hownerAction
          exact cursorProgramJointActionLegal_of_mem_availableProgramMovesAt
            g hcursor (by
              intro other
              by_cases hother : other = who
              · subst other
                have hactive : who ∈ active w.toWorld := by
                  change who ∈ active
                    ({ Γ := w.1.cursor.Γ,
                       prog := w.1.cursor.prog,
                       env := w.1.env } : World P L)
                  rw [hprog]
                  simp [active]
                have hactiveAt :
                    who ∈ active
                      ({ Γ := w.1.cursor.Γ,
                         prog := w.1.prog,
                         env := w.1.env } : World P L) := by
                  simpa [active, CursorCheckedWorld.toWorld,
                    w] using hactive
                have hactionAt :
                    action ∈ CursorCheckedWorld.availableProgramActionsAt
                      w.1.prog w.1.env w.1.suffix who := by
                  simpa [CursorCheckedWorld.availableProgramActions, w]
                    using haction
                simpa [graphMachineJointAction, singleProgramJointAction,
                  CursorCheckedWorld.availableProgramMovesAt] using
                    (And.intro hactiveAt hactionAt)
              · have hnot : other ∉ active w.toWorld := by
                  intro hactive
                  have hwho : other = who := by
                    change other ∈ active w.toWorld at hactive
                    simpa [CursorCheckedWorld.toWorld, CursorWorldData.prog,
                      hprog, active, w] using hactive
                  exact hother hwho
                have hnotAt :
                    other ∉ active
                      ({ Γ := w.1.cursor.Γ,
                         prog := w.1.prog,
                         env := w.1.env } : World P L) := by
                  simpa [active, CursorCheckedWorld.toWorld,
                    w] using hnot
                simpa [graphMachineJointAction, singleProgramJointAction,
                  CursorCheckedWorld.availableProgramMovesAt, hother]
                  using hnotAt)
      | reveal y owner x hx k =>
          rcases haction.2 with
            ⟨x', owner', b', R', k', hprogAction, _hownerAction, _hcursor⟩
          unfold CursorWorldData.prog at hprogAction
          rw [hprog] at hprogAction
          cases hprogAction

/-- Available checked graph-machine events project to the original checked
cursor transition when the projected cursor world is nonterminal. -/
theorem graphMachine_step_map_cursorWorld_eq_cursorProgramTransition_of_available
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    {state : (graphMachine g hctx).State}
    {event : (graphMachine g hctx).Event}
    (hcursor :
      ¬ terminal (cursorWorldOfGraphConfiguration g hctx state).toWorld)
    (havailable : (graphMachine g hctx).EventAvailable state event) :
    PMF.map (cursorWorldOfGraphConfiguration g hctx)
        ((graphMachine g hctx).step event state) =
      cursorProgramTransition
        (cursorWorldOfGraphConfiguration g hctx state)
        ⟨graphMachineJointAction g hctx event,
          cursorProgramJointActionLegal_of_graphMachine_available
            g hctx hcursor havailable⟩ := by
  cases event with
  | play who action =>
      have hgraphAvailable :
          action ∈ graphAvailable g hctx state who := by
        simpa [graphMachine] using havailable
      rw [Machine.step_play]
      change
        PMF.map (cursorWorldOfGraphConfiguration g hctx)
            (graphStepPlay g hctx who action state) =
          cursorProgramTransition
            (cursorWorldOfGraphConfiguration g hctx state)
            ⟨graphMachineJointAction g hctx (Machine.Event.play who action),
              cursorProgramJointActionLegal_of_graphMachine_available
                g hctx hcursor havailable⟩
      rw [graphStepPlay_project_cursorWorld_of_available
        g hctx hgraphAvailable]
      exact step_eq_cursorProgramTransition_of_legal
        g (cursorProgramJointActionLegal_of_graphMachine_available
          g hctx hcursor havailable)
  | internal internalEvent =>
      have hgraphAvailable :
          internalEvent ∈ graphAvailableInternal g hctx state := by
        simpa [graphMachine] using havailable
      rw [Machine.step_internal]
      change
        PMF.map (cursorWorldOfGraphConfiguration g hctx)
            (graphStepInternal g hctx internalEvent state) =
          cursorProgramTransition
            (cursorWorldOfGraphConfiguration g hctx state)
            ⟨graphMachineJointAction g hctx (Machine.Event.internal internalEvent),
              cursorProgramJointActionLegal_of_graphMachine_available
                g hctx hcursor havailable⟩
      rw [graphStepInternal_project_cursorWorld_of_available
        g hctx hgraphAvailable]
      exact step_eq_cursorProgramTransition_of_legal
        g (cursorProgramJointActionLegal_of_graphMachine_available
          g hctx hcursor havailable)

/-- Every positive-probability available graph-machine step consumes exactly
one operational Vegas syntax node, for reachable/nonterminal cursor states. -/
theorem graphMachine_step_support_remainingSyntaxSteps_of_event_available_of_cursor_nonterminal
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    {state next : (graphMachine g hctx).State}
    {event : (graphMachine g hctx).Event}
    (hcursor :
      ¬ terminal (cursorWorldOfGraphConfiguration g hctx state).toWorld)
    (havailable : (graphMachine g hctx).EventAvailable state event)
    (hsupp : (graphMachine g hctx).step event state next ≠ 0) :
    (cursorWorldOfGraphConfiguration g hctx next).remainingSyntaxSteps + 1 =
      (cursorWorldOfGraphConfiguration g hctx state).remainingSyntaxSteps := by
  have hstep :=
    graphMachine_step_map_cursorWorld_eq_cursorProgramTransition_of_available
      g hctx hcursor havailable
  have hmem :
      cursorWorldOfGraphConfiguration g hctx next ∈
        (PMF.map (cursorWorldOfGraphConfiguration g hctx)
          ((graphMachine g hctx).step event state)).support := by
    exact (PMF.mem_support_map_iff _ _ _).2
      ⟨next, (PMF.mem_support_iff _ _).2 hsupp, rfl⟩
  rw [hstep] at hmem
  exact cursorProgramTransition_remainingSyntaxSteps
    (cursorWorldOfGraphConfiguration g hctx state)
    ⟨graphMachineJointAction g hctx event,
      cursorProgramJointActionLegal_of_graphMachine_available
        g hctx hcursor havailable⟩
    (cursorWorldOfGraphConfiguration g hctx next)
    ((PMF.mem_support_iff _ _).1 hmem)

/-- Available checked graph-machine events project to checked-world
transitions after forgetting the graph frontier. -/
theorem graphMachine_step_map_checkedWorld_eq_checkedTransition_of_available
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    {state : (graphMachine g hctx).State}
    {event : (graphMachine g hctx).Event}
    (hcursor :
      ¬ terminal (cursorWorldOfGraphConfiguration g hctx state).toWorld)
    (havailable : (graphMachine g hctx).EventAvailable state event) :
    PMF.map
        (fun next : (graphMachine g hctx).State =>
          CheckedWorld.ofCursorChecked (hctx := hctx)
            (cursorWorldOfGraphConfiguration g hctx next))
        ((graphMachine g hctx).step event state) =
      checkedTransition
        (CheckedWorld.ofCursorChecked (hctx := hctx)
          (cursorWorldOfGraphConfiguration g hctx state))
        ⟨ProgramJointAction.toAction (graphMachineJointAction g hctx event),
          CursorProgramJointActionLegal.toAction
            (cursorProgramJointActionLegal_of_graphMachine_available
              g hctx hcursor havailable)⟩ := by
  have hstep :
      PMF.map (cursorWorldOfGraphConfiguration g hctx)
          ((graphMachine g hctx).step event state) =
        cursorProgramTransition
          (cursorWorldOfGraphConfiguration g hctx state)
          ⟨graphMachineJointAction g hctx event,
            cursorProgramJointActionLegal_of_graphMachine_available
              g hctx hcursor havailable⟩ := by
    exact
      graphMachine_step_map_cursorWorld_eq_cursorProgramTransition_of_available
        g hctx hcursor havailable
  calc
    PMF.map
        (fun next : (graphMachine g hctx).State =>
          CheckedWorld.ofCursorChecked (hctx := hctx)
            (cursorWorldOfGraphConfiguration g hctx next))
        ((graphMachine g hctx).step event state)
        =
      PMF.map
        (fun next : CursorCheckedWorld g =>
          CheckedWorld.ofCursorChecked (hctx := hctx) next)
        (cursorProgramTransition
          (cursorWorldOfGraphConfiguration g hctx state)
          ⟨graphMachineJointAction g hctx event,
            cursorProgramJointActionLegal_of_graphMachine_available
              g hctx hcursor havailable⟩) := by
          rw [← hstep]
          rw [PMF.map_comp]
          rfl
    _ =
      checkedTransition
        (CheckedWorld.ofCursorChecked (hctx := hctx)
          (cursorWorldOfGraphConfiguration g hctx state))
        ⟨ProgramJointAction.toAction (graphMachineJointAction g hctx event),
          CursorProgramJointActionLegal.toAction
            (cursorProgramJointActionLegal_of_graphMachine_available
              g hctx hcursor havailable)⟩ := by
          convert cursorProgramTransition_map_checkedWorld
            (hctx := hctx)
            (cursorWorldOfGraphConfiguration g hctx state)
            ⟨graphMachineJointAction g hctx event,
              cursorProgramJointActionLegal_of_graphMachine_available
                g hctx hcursor havailable⟩ using 1

theorem graphMachine_step_support_done_eq_advance_of_event_available
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    {state next : (graphMachine g hctx).State}
    {event : (graphMachine g hctx).Event}
    (havailable : (graphMachine g hctx).EventAvailable state event)
    (hsupp : (graphMachine g hctx).step event state next ≠ 0) :
    next.frontier.done =
      (syntaxActionGraph g).advance state.frontier.done := by
  have hmem :
      next ∈ ((graphMachine g hctx).step event state).support :=
    (PMF.mem_support_iff _ _).2 hsupp
  cases event with
  | play who action =>
      have hgraphAvailable :
          action ∈ graphAvailable g hctx state who := by
        simpa [graphMachine] using havailable
      simpa [Machine.step_play, graphMachine] using
        graphStepPlay_done_eq_advance_of_available_of_support
          g hctx hgraphAvailable (by
            simpa [Machine.step_play, graphMachine] using hmem)
  | internal internalEvent =>
      have hgraphAvailable :
          internalEvent ∈ graphAvailableInternal g hctx state := by
        simpa [graphMachine] using havailable
      simpa [Machine.step_internal, graphMachine] using
        graphStepInternal_done_eq_advance_of_available_of_support
          g hctx hgraphAvailable (by
            simpa [Machine.step_internal, graphMachine] using hmem)

/-- The bounded graph-machine FOSG transition is the checked transition for
the primitive event selected by the FOSG legal action, after projecting graph
configuration endpoints to cursor checked worlds.

The cursor-nonterminal premise is discharged by reachable finite graph
histories before the syntax cutoff. -/
theorem boundedFOSG_transition_map_checkedWorld_eq_checkedTransition
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (horizon : Nat)
    (pref : (graphMachine g hctx).BoundedRunPrefix horizon)
    (action : (boundedFOSG g hctx horizon).LegalAction pref)
    (hcursor :
      ¬ terminal (cursorWorldOfGraphConfiguration g hctx pref.lastState).toWorld) :
    let selected :=
      (fosgView g hctx).boundedEventOfLegalJointAction
        horizon pref action
    PMF.map
        (fun dst : (graphMachine g hctx).BoundedRunPrefix horizon =>
          CheckedWorld.ofCursorChecked (hctx := hctx)
            (cursorWorldOfGraphConfiguration g hctx dst.lastState))
        ((boundedFOSG g hctx horizon).transition pref action) =
      checkedTransition
        (CheckedWorld.ofCursorChecked (hctx := hctx)
          (cursorWorldOfGraphConfiguration g hctx pref.lastState))
        ⟨ProgramJointAction.toAction
            (graphMachineJointAction g hctx selected),
          CursorProgramJointActionLegal.toAction
            (cursorProgramJointActionLegal_of_graphMachine_available
              g hctx hcursor
              ((fosgView g hctx)
                |>.boundedEventOfLegalJointAction_available
                  horizon pref action))⟩ := by
  classical
  let selected :=
    (fosgView g hctx).boundedEventOfLegalJointAction
      horizon pref action
  have havailable :
      (graphMachine g hctx).EventAvailable pref.lastState selected := by
    simpa [selected] using
      (fosgView g hctx)
        |>.boundedEventOfLegalJointAction_available horizon pref action
  have hstep :
      PMF.map (cursorWorldOfGraphConfiguration g hctx)
          ((graphMachine g hctx).step selected pref.lastState) =
        cursorProgramTransition
          (cursorWorldOfGraphConfiguration g hctx pref.lastState)
          ⟨graphMachineJointAction g hctx selected,
            cursorProgramJointActionLegal_of_graphMachine_available
              g hctx hcursor havailable⟩ := by
    exact
      graphMachine_step_map_cursorWorld_eq_cursorProgramTransition_of_available
        g hctx hcursor havailable
  calc
    PMF.map
        (fun dst : (graphMachine g hctx).BoundedRunPrefix horizon =>
          CheckedWorld.ofCursorChecked (hctx := hctx)
            (cursorWorldOfGraphConfiguration g hctx dst.lastState))
        ((boundedFOSG g hctx horizon).transition pref action)
        =
      PMF.map
        (fun next : (graphMachine g hctx).State =>
          CheckedWorld.ofCursorChecked (hctx := hctx)
            (cursorWorldOfGraphConfiguration g hctx next))
        ((graphMachine g hctx).step selected pref.lastState) := by
          change
            PMF.map
                (fun dst : (graphMachine g hctx).BoundedRunPrefix horizon =>
                  CheckedWorld.ofCursorChecked (hctx := hctx)
                    (cursorWorldOfGraphConfiguration g hctx dst.lastState))
                (((fosgView g hctx).toBoundedFOSG horizon).transition
                  pref action) =
              PMF.map
                (fun next : (graphMachine g hctx).State =>
                  CheckedWorld.ofCursorChecked (hctx := hctx)
                    (cursorWorldOfGraphConfiguration g hctx next))
                ((graphMachine g hctx).step selected pref.lastState)
          rw [Machine.FOSGView.toBoundedFOSG_transition]
          rw [PMF.map_comp]
          change
            PMF.map
                (fun next : (graphMachine g hctx).State =>
                  CheckedWorld.ofCursorChecked (hctx := hctx)
                    (cursorWorldOfGraphConfiguration g hctx
                      ((pref.snoc
                        (by
                          have hnot :
                              ¬ horizon ≤ pref.pref.events.length := by
                            intro hle
                            exact action.2.1 (Or.inr hle)
                          exact Nat.lt_of_not_ge hnot)
                        selected next).lastState)))
                ((graphMachine g hctx).step selected pref.lastState) =
              PMF.map
                (fun next : (graphMachine g hctx).State =>
                  CheckedWorld.ofCursorChecked (hctx := hctx)
                    (cursorWorldOfGraphConfiguration g hctx next))
                ((graphMachine g hctx).step selected pref.lastState)
          simp [selected, Machine.BoundedRunPrefix.lastState,
            Machine.BoundedRunPrefix.snoc, Machine.RunPrefix.lastState]
    _ =
      PMF.map
        (fun next : CursorCheckedWorld g =>
          CheckedWorld.ofCursorChecked (hctx := hctx) next)
        (cursorProgramTransition
          (cursorWorldOfGraphConfiguration g hctx pref.lastState)
          ⟨graphMachineJointAction g hctx selected,
            cursorProgramJointActionLegal_of_graphMachine_available
              g hctx hcursor havailable⟩) := by
          rw [← hstep]
          rw [PMF.map_comp]
          rfl
    _ =
      checkedTransition
        (CheckedWorld.ofCursorChecked (hctx := hctx)
          (cursorWorldOfGraphConfiguration g hctx pref.lastState))
        ⟨ProgramJointAction.toAction
            (graphMachineJointAction g hctx selected),
          CursorProgramJointActionLegal.toAction
            (cursorProgramJointActionLegal_of_graphMachine_available
              g hctx hcursor havailable)⟩ := by
          convert cursorProgramTransition_map_checkedWorld
            (hctx := hctx)
            (cursorWorldOfGraphConfiguration g hctx pref.lastState)
            ⟨graphMachineJointAction g hctx selected,
              cursorProgramJointActionLegal_of_graphMachine_available
                g hctx hcursor havailable⟩ using 1

/-- Every supported bounded graph-machine FOSG transition consumes exactly one
operational Vegas syntax node at the projected cursor state, for nonterminal
projected cursor states. -/
theorem boundedFOSG_transition_support_remainingSyntaxSteps
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (horizon : Nat)
    (pref : (graphMachine g hctx).BoundedRunPrefix horizon)
    (action : (boundedFOSG g hctx horizon).LegalAction pref)
    {dst : (graphMachine g hctx).BoundedRunPrefix horizon}
    (hsupp :
      (boundedFOSG g hctx horizon).transition pref action dst ≠ 0)
    (hcursor :
      ¬ terminal (cursorWorldOfGraphConfiguration g hctx pref.lastState).toWorld) :
    (cursorWorldOfGraphConfiguration g hctx dst.lastState).remainingSyntaxSteps + 1 =
      (cursorWorldOfGraphConfiguration g hctx pref.lastState).remainingSyntaxSteps := by
  classical
  let selected :=
    (fosgView g hctx).boundedEventOfLegalJointAction
      horizon pref action
  have hmem :
      dst ∈ ((boundedFOSG g hctx horizon).transition
        pref action).support := by
    exact (PMF.mem_support_iff _ _).2 hsupp
  have hmemMap :
      dst ∈
        (PMF.map
          (fun next =>
            pref.snoc
              (by
                have hnot :
                    ¬ horizon ≤ pref.pref.events.length := by
                  intro hle
                  exact action.2.1 (Or.inr hle)
                exact Nat.lt_of_not_ge hnot)
              selected next)
          ((graphMachine g hctx).step selected pref.lastState)).support := by
    simpa [boundedFOSG,
      Machine.FOSGView.toBoundedFOSG_transition, selected]
      using hmem
  rcases (PMF.mem_support_map_iff _ _ _).mp hmemMap with
    ⟨next, hnext, hdst⟩
  have havailable :
      (graphMachine g hctx).EventAvailable pref.lastState selected := by
    simpa [selected] using
      (fosgView g hctx)
        |>.boundedEventOfLegalJointAction_available horizon pref action
  have hnextStep :
      (graphMachine g hctx).step selected pref.lastState next ≠ 0 :=
    (PMF.mem_support_iff _ _).1 hnext
  have hremaining :=
    graphMachine_step_support_remainingSyntaxSteps_of_event_available_of_cursor_nonterminal
      g hctx hcursor havailable hnextStep
  rw [← hdst]
  simpa [Machine.BoundedRunPrefix.lastState,
    Machine.BoundedRunPrefix.snoc, Machine.RunPrefix.lastState] using hremaining

theorem boundedFOSG_transition_support_done_eq_advance
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (horizon : Nat)
    (pref : (graphMachine g hctx).BoundedRunPrefix horizon)
    (action : (boundedFOSG g hctx horizon).LegalAction pref)
    {dst : (graphMachine g hctx).BoundedRunPrefix horizon}
    (hsupp :
      (boundedFOSG g hctx horizon).transition pref action dst ≠ 0) :
    dst.lastState.frontier.done =
      (syntaxActionGraph g).advance pref.lastState.frontier.done := by
  classical
  let selected :=
    (fosgView g hctx).boundedEventOfLegalJointAction
      horizon pref action
  have hmem :
      dst ∈ ((boundedFOSG g hctx horizon).transition
        pref action).support := by
    exact (PMF.mem_support_iff _ _).2 hsupp
  have hmemMap :
      dst ∈
        (PMF.map
          (fun next =>
            pref.snoc
              (by
                have hnot :
                    ¬ horizon ≤ pref.pref.events.length := by
                  intro hle
                  exact action.2.1 (Or.inr hle)
                exact Nat.lt_of_not_ge hnot)
              selected next)
          ((graphMachine g hctx).step selected pref.lastState)).support := by
    simpa [boundedFOSG,
      Machine.FOSGView.toBoundedFOSG_transition, selected]
      using hmem
  rcases (PMF.mem_support_map_iff _ _ _).mp hmemMap with
    ⟨next, hnext, hdst⟩
  have havailable :
      (graphMachine g hctx).EventAvailable pref.lastState selected := by
    simpa [selected] using
      (fosgView g hctx)
        |>.boundedEventOfLegalJointAction_available horizon pref action
  have hnextStep :
      (graphMachine g hctx).step selected pref.lastState next ≠ 0 :=
    (PMF.mem_support_iff _ _).1 hnext
  have hdone :=
    graphMachine_step_support_done_eq_advance_of_event_available
      g hctx havailable hnextStep
  rw [← hdst]
  simpa [Machine.BoundedRunPrefix.lastState,
    Machine.BoundedRunPrefix.snoc, Machine.RunPrefix.lastState] using hdone

/-- Along a finite graph-machine FOSG chain, graph frontier completion remains
synchronized with the projected checked cursor. -/
theorem finiteFOSG_stepChain_doneBeforeCursor_from
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    ∀ {start : (graphMachine g hctx).BoundedRunPrefix (syntaxSteps g.prog)}
      {steps : List (finiteFOSG g hctx).Step},
      (finiteFOSG g hctx).StepChainFrom start steps →
      syntaxGraphDoneBeforeCursor g start.lastState.frontier.done
        (cursorWorldOfGraphConfiguration g hctx start.lastState).1.cursor →
      syntaxGraphDoneBeforeCursor g
        ((finiteFOSG g hctx).lastStateFrom start steps
          ).lastState.frontier.done
        (cursorWorldOfGraphConfiguration g hctx
          ((finiteFOSG g hctx).lastStateFrom start steps
            ).lastState).1.cursor
  | start, [], _hchain, hinv => by
      simpa [GameTheory.FOSG.lastStateFrom] using hinv
  | start, step :: steps, hchain, hinv => by
      rcases hchain with ⟨hsrc, htail⟩
      let action : (finiteFOSG g hctx).LegalAction start :=
        hsrc ▸ step.act
      have hsupp :
          (finiteFOSG g hctx).transition start action step.dst ≠ 0 := by
        subst hsrc
        simpa [action] using step.support
      have hnotGraphTerminal :
          ¬ (graphMachine g hctx).terminal start.lastState := by
        intro hterminal
        exact action.2.1 (Or.inl hterminal)
      have hnotComplete :
          ¬ (syntaxActionGraph g).CompleteAt start.lastState.frontier.done := by
        simpa [graphMachine_terminal, ActionGraph.Configuration.isTerminal,
          ActionGraph.FrontierMachine.isComplete] using hnotGraphTerminal
      let currentW := cursorWorldOfGraphConfiguration g hctx start.lastState
      let nextW :=
        cursorWorldOfGraphConfiguration g hctx step.dst.lastState
      have hpositive :
          0 < syntaxSteps currentW.1.cursor.prog :=
        syntaxGraphDoneBeforeCursor_cursor_nonterminal_of_not_complete
          (g := g) hinv hnotComplete
      have hcursor :
          ¬ terminal currentW.toWorld := by
        intro hterminal
        have hzero :
            syntaxSteps currentW.1.cursor.prog = 0 := by
          have hz :=
            (CursorCheckedWorld.terminal_iff_remainingSyntaxSteps_eq_zero
              (g := g) (w := currentW)).1 hterminal
          simpa [CursorCheckedWorld.remainingSyntaxSteps,
            CursorWorldData.prog, currentW] using hz
        omega
      have hremaining :
          nextW.remainingSyntaxSteps + 1 =
            currentW.remainingSyntaxSteps := by
        exact
          boundedFOSG_transition_support_remainingSyntaxSteps
            g hctx (syntaxSteps g.prog) start action
            (by simpa [finiteFOSG] using hsupp)
            (by simpa [currentW] using hcursor)
      have hrankNext :
          syntaxGraphRank g nextW.1.cursor =
            syntaxGraphRank g currentW.1.cursor + 1 := by
        exact syntaxGraphRank_cursor_eq_succ_of_remainingSyntaxSteps
          (g := g) hremaining
      have hcurrentMem :
          currentW.1.cursor ∈ syntaxGraphActions g := by
        classical
        letI : Fintype (ProgramCursor g.prog) :=
          ProgramCursor.instFintype g.prog
        simp [syntaxGraphActions, hpositive]
      have hdone :
          step.dst.lastState.frontier.done =
            (syntaxActionGraph g).advance
              start.lastState.frontier.done := by
        exact
          boundedFOSG_transition_support_done_eq_advance
            g hctx (syntaxSteps g.prog) start action
            (by simpa [finiteFOSG] using hsupp)
      have hinvStep :
          syntaxGraphDoneBeforeCursor g step.dst.lastState.frontier.done
            nextW.1.cursor := by
        rw [hdone]
        exact syntaxGraphDoneBeforeCursor_advance
          (g := g) hcurrentMem (by simpa [currentW] using hinv)
          (by simpa [currentW, nextW] using hrankNext)
      exact
        finiteFOSG_stepChain_doneBeforeCursor_from
          (g := g) (hctx := hctx) (start := step.dst)
          (steps := steps) htail hinvStep

/-- Every finite graph-machine FOSG history satisfies the graph/cursor
synchronization invariant. -/
theorem finiteFOSG_history_doneBeforeCursor
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (h : (finiteFOSG g hctx).History) :
    syntaxGraphDoneBeforeCursor g h.lastState.lastState.frontier.done
      (cursorWorldOfGraphConfiguration g hctx
        h.lastState.lastState).1.cursor := by
  have hinv :=
    finiteFOSG_stepChain_doneBeforeCursor_from
      (g := g) (hctx := hctx)
      (start := Machine.BoundedRunPrefix.init
        (graphMachine g hctx) (syntaxSteps g.prog))
      h.chain
      (by
        change
          syntaxGraphDoneBeforeCursor g
            (ActionGraph.Configuration.initial
              (syntaxActionGraph g)).frontier.done
            (cursorWorldOfGraphConfiguration g hctx
              (ActionGraph.Configuration.initial
                (syntaxActionGraph g))).1.cursor
        simpa [ActionGraph.Configuration.initial,
          ActionGraph.FrontierMachine.initial,
          cursorWorldOfGraphConfiguration_initial] using
          syntaxGraphDoneBeforeCursor_initial g)
  simpa [GameTheory.FOSG.History.lastState, finiteFOSG,
    boundedFOSG] using hinv

/-- Along a finite graph-machine FOSG chain, the projected endpoint cursor
state and the bounded prefix length maintain the source syntax-step budget. -/
theorem finiteFOSG_stepChain_remainingSyntaxSteps_from
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    ∀ {start : (graphMachine g hctx).BoundedRunPrefix (syntaxSteps g.prog)}
      {steps : List (finiteFOSG g hctx).Step},
      (finiteFOSG g hctx).StepChainFrom start steps →
      (cursorWorldOfGraphConfiguration g hctx start.lastState).remainingSyntaxSteps +
          start.pref.events.length = syntaxSteps g.prog →
      (cursorWorldOfGraphConfiguration g hctx
          ((finiteFOSG g hctx).lastStateFrom start steps).lastState
        ).remainingSyntaxSteps +
          ((finiteFOSG g hctx).lastStateFrom start steps).pref.events.length =
        syntaxSteps g.prog
  | start, [], _hchain, hstart => by
      simpa [GameTheory.FOSG.lastStateFrom] using hstart
  | start, step :: steps, hchain, hstart => by
      rcases hchain with ⟨hsrc, htail⟩
      let action : (finiteFOSG g hctx).LegalAction start :=
        hsrc ▸ step.act
      have hsupp :
          (finiteFOSG g hctx).transition start action step.dst ≠ 0 := by
        subst hsrc
        simpa [action] using step.support
      have hnotCut :
          ¬ syntaxSteps g.prog ≤ start.pref.events.length := by
        intro hle
        exact action.2.1 (Or.inr hle)
      have hcursor :
          ¬ terminal (cursorWorldOfGraphConfiguration g hctx start.lastState).toWorld := by
        intro hterm
        have hzero :
            (cursorWorldOfGraphConfiguration g hctx
              start.lastState).remainingSyntaxSteps = 0 :=
          (CursorCheckedWorld.terminal_iff_remainingSyntaxSteps_eq_zero
            (g := g)
            (w := cursorWorldOfGraphConfiguration g hctx start.lastState)).1 hterm
        omega
      have hstep :
          (cursorWorldOfGraphConfiguration g hctx
              step.dst.lastState).remainingSyntaxSteps + 1 =
            (cursorWorldOfGraphConfiguration g hctx
              start.lastState).remainingSyntaxSteps := by
        exact
          boundedFOSG_transition_support_remainingSyntaxSteps
            g hctx (syntaxSteps g.prog) start action (by
              simpa [finiteFOSG] using hsupp) hcursor
      have hevents :
          step.dst.pref.events.length = start.pref.events.length + 1 := by
        have hsuppView :
            (((fosgView g hctx).toBoundedFOSG
                (syntaxSteps g.prog)).transition start action step.dst) ≠ 0 := by
          change
            (finiteFOSG g hctx).transition start action step.dst ≠ 0
          exact hsupp
        exact
          (fosgView g hctx).toBoundedFOSG_transition_support_events_length
            (syntaxSteps g.prog) start action
            hsuppView
      have htailStart :
          (cursorWorldOfGraphConfiguration g hctx
              step.dst.lastState).remainingSyntaxSteps +
              step.dst.pref.events.length =
            syntaxSteps g.prog := by
        omega
      exact
        finiteFOSG_stepChain_remainingSyntaxSteps_from
          (g := g) (hctx := hctx) (start := step.dst)
          (steps := steps) htail htailStart

/-- A finite graph-machine FOSG history preserves syntax-step accounting after
projecting its endpoint graph configuration to the checked cursor world. -/
theorem finiteFOSG_history_remainingSyntaxSteps
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (h : (finiteFOSG g hctx).History) :
    (cursorWorldOfGraphConfiguration g hctx h.lastState.lastState).remainingSyntaxSteps +
        h.steps.length = syntaxSteps g.prog := by
  have hinv :=
    finiteFOSG_stepChain_remainingSyntaxSteps_from
      (g := g) (hctx := hctx)
      (start := Machine.BoundedRunPrefix.init
        (graphMachine g hctx) (syntaxSteps g.prog))
      h.chain
      (by
        change
          (cursorWorldOfGraphConfiguration g hctx
              (ActionGraph.Configuration.initial (syntaxActionGraph g))).remainingSyntaxSteps +
              0 =
            syntaxSteps g.prog
        simp [cursorWorldOfGraphConfiguration,
          ActionGraph.Configuration.initial,
          ActionGraph.BoundedHistory.empty,
          History.lookup,
          CursorCheckedWorld.remainingSyntaxSteps,
          CursorCheckedWorld.initial,
          CursorWorldData.prog,
          ProgramCursor.prog]
        rfl)
  have hlen :=
    (fosgView g hctx).toBoundedFOSG_history_events_length
      (syntaxSteps g.prog) h
  have hlen' : h.lastState.pref.events.length = h.steps.length := by
    simpa [GameTheory.FOSG.History.lastState, finiteFOSG,
      boundedFOSG] using hlen
  change
    (cursorWorldOfGraphConfiguration g hctx h.lastState.lastState).remainingSyntaxSteps +
        h.lastState.pref.events.length = syntaxSteps g.prog at hinv
  omega

/-- At the syntax cutoff, a finite graph-machine FOSG history projects to a
terminal checked cursor state. -/
theorem finiteFOSG_terminal_endpoint_of_cutoff
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (h : (finiteFOSG g hctx).History)
    (hcut : syntaxSteps g.prog ≤ h.lastState.pref.events.length) :
    terminal (cursorWorldOfGraphConfiguration g hctx h.lastState.lastState).toWorld := by
  have hlen :=
    (fosgView g hctx).toBoundedFOSG_history_events_length
      (syntaxSteps g.prog) h
  have hlen' : h.lastState.pref.events.length = h.steps.length := by
    simpa [GameTheory.FOSG.History.lastState, finiteFOSG,
      boundedFOSG] using hlen
  have hsteps : h.steps.length = syntaxSteps g.prog := by
    have hle₁ : h.steps.length ≤ syntaxSteps g.prog := by
      calc
        h.steps.length = h.lastState.pref.events.length := hlen'.symm
        _ ≤ syntaxSteps g.prog := h.lastState.length_le
    have hle₂ : syntaxSteps g.prog ≤ h.steps.length := by
      calc
        syntaxSteps g.prog ≤ h.lastState.pref.events.length := hcut
        _ = h.steps.length := hlen'
    exact Nat.le_antisymm hle₁ hle₂
  have hinv := finiteFOSG_history_remainingSyntaxSteps g hctx h
  rw [hsteps] at hinv
  have hzero :
      (cursorWorldOfGraphConfiguration g hctx
        h.lastState.lastState).remainingSyntaxSteps = 0 := by
    omega
  exact (CursorCheckedWorld.terminal_iff_remainingSyntaxSteps_eq_zero
    (g := g)
    (w := cursorWorldOfGraphConfiguration g hctx h.lastState.lastState)).2 hzero

/-- A graph-terminal finite graph-machine FOSG history projects to a terminal
checked cursor state. -/
theorem finiteFOSG_cursor_terminal_of_graph_terminal
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (h : (finiteFOSG g hctx).History)
    (hgraph : (graphMachine g hctx).terminal h.lastState.lastState) :
    terminal (cursorWorldOfGraphConfiguration g hctx h.lastState.lastState).toWorld := by
  rw [(CursorCheckedWorld.terminal_iff_remainingSyntaxSteps_eq_zero
    (w := cursorWorldOfGraphConfiguration g hctx h.lastState.lastState))]
  by_contra hnotZero
  have hpositive :
      0 <
        (cursorWorldOfGraphConfiguration g hctx
          h.lastState.lastState).remainingSyntaxSteps :=
    Nat.pos_of_ne_zero hnotZero
  have hcursorPositive :
      0 < syntaxSteps
        (cursorWorldOfGraphConfiguration g hctx
          h.lastState.lastState).1.cursor.prog := by
    simpa [CursorCheckedWorld.remainingSyntaxSteps, CursorWorldData.prog]
      using hpositive
  have hcurrentMem :
      (cursorWorldOfGraphConfiguration g hctx
        h.lastState.lastState).1.cursor ∈ syntaxGraphActions g := by
    classical
    letI : Fintype (ProgramCursor g.prog) :=
      ProgramCursor.instFintype g.prog
    simp [syntaxGraphActions, hcursorPositive]
  have hdoneBefore :=
    finiteFOSG_history_doneBeforeCursor g hctx h
  have hnotDone :
      (cursorWorldOfGraphConfiguration g hctx
        h.lastState.lastState).1.cursor ∉
          h.lastState.lastState.frontier.done :=
    syntaxGraphDoneBeforeCursor_current_not_done
      (g := g) hdoneBefore
  have hcomplete :
      (syntaxActionGraph g).CompleteAt
        h.lastState.lastState.frontier.done := by
    simpa [graphMachine_terminal, ActionGraph.Configuration.isTerminal,
      ActionGraph.FrontierMachine.isComplete] using hgraph
  exact hnotDone (hcomplete hcurrentMem)

/-- A finite graph-machine FOSG terminal history projects to a terminal checked
cursor state. -/
theorem finiteFOSG_cursor_terminal_of_terminal
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (h : (finiteFOSG g hctx).History)
    (hterm : (finiteFOSG g hctx).terminal h.lastState) :
    terminal (cursorWorldOfGraphConfiguration g hctx h.lastState.lastState).toWorld := by
  rcases hterm with hgraph | hcut
  · exact finiteFOSG_cursor_terminal_of_graph_terminal
      g hctx h hgraph
  · exact finiteFOSG_terminal_endpoint_of_cutoff
      g hctx h hcut

theorem finiteFOSG_not_graph_terminal_of_not_cutoff
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (h : (finiteFOSG g hctx).History)
    (hcut : ¬ syntaxSteps g.prog ≤ h.lastState.pref.events.length) :
    ¬ (graphMachine g hctx).terminal h.lastState.lastState := by
  have hlen :=
    (fosgView g hctx).toBoundedFOSG_history_events_length
      (syntaxSteps g.prog) h
  have hlen' : h.lastState.pref.events.length = h.steps.length := by
    simpa [GameTheory.FOSG.History.lastState, finiteFOSG,
      boundedFOSG] using hlen
  have hinvSteps := finiteFOSG_history_remainingSyntaxSteps
    g hctx h
  have hremainingPositive :
      0 <
        (cursorWorldOfGraphConfiguration g hctx
          h.lastState.lastState).remainingSyntaxSteps := by
    have hlt : h.steps.length < syntaxSteps g.prog := by
      rw [← hlen']
      exact Nat.lt_of_not_ge hcut
    omega
  have hcursorPositive :
      0 < syntaxSteps
        (cursorWorldOfGraphConfiguration g hctx
          h.lastState.lastState).1.cursor.prog := by
    simpa [CursorCheckedWorld.remainingSyntaxSteps, CursorWorldData.prog]
      using hremainingPositive
  have hcurrentMem :
      (cursorWorldOfGraphConfiguration g hctx
        h.lastState.lastState).1.cursor ∈ syntaxGraphActions g := by
    classical
    letI : Fintype (ProgramCursor g.prog) :=
      ProgramCursor.instFintype g.prog
    simp [syntaxGraphActions, hcursorPositive]
  have hdoneBefore :=
    finiteFOSG_history_doneBeforeCursor g hctx h
  have hnotDone :
      (cursorWorldOfGraphConfiguration g hctx
        h.lastState.lastState).1.cursor ∉
          h.lastState.lastState.frontier.done :=
    syntaxGraphDoneBeforeCursor_current_not_done
      (g := g) hdoneBefore
  intro hterminal
  have hcomplete :
      (syntaxActionGraph g).CompleteAt
        h.lastState.lastState.frontier.done := by
    simpa [graphMachine_terminal, ActionGraph.Configuration.isTerminal,
      ActionGraph.FrontierMachine.isComplete] using hterminal
  exact hnotDone (hcomplete hcurrentMem)

/-- Away from the syntax cutoff, finite graph-machine FOSG available moves are
exactly the observed cursor-world moves at the projected endpoint. -/
theorem finiteFOSG_availableMoves_eq_observedProgram_of_not_cutoff
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P)
    (h : (finiteFOSG g hctx).History)
    (hcut : ¬ syntaxSteps g.prog ≤ h.lastState.pref.events.length) :
    (finiteFOSG g hctx).availableMoves h who =
      (cursorFOSG g hctx).availableMovesAtState
        (cursorWorldOfGraphConfiguration g hctx h.lastState.lastState) who := by
  have hnotGraph :=
    finiteFOSG_not_graph_terminal_of_not_cutoff
      g hctx h hcut
  ext move
  cases move with
  | none =>
      change
        who ∉
            Machine.FOSGView.boundedActive
              (fosgView g hctx) (syntaxSteps g.prog)
              h.lastState ↔
          who ∉ active (cursorWorldOfGraphConfiguration g hctx h.lastState.lastState).toWorld
      rw [Machine.FOSGView.boundedActive]
      rw [if_neg hcut]
      rw [fosgView_active_eq_cursor_active_of_not_terminal
        g hctx h.lastState.pref hnotGraph]
      simp [Machine.BoundedRunPrefix.lastState]
  | some action =>
      change
        (who ∈
              (if syntaxSteps g.prog ≤ h.lastState.pref.events.length then ∅
               else Machine.FOSGView.active (fosgView g hctx)
                 h.lastState.pref) ∧
            action ∈
              (if syntaxSteps g.prog ≤ h.lastState.pref.events.length then ∅
               else Machine.FOSGView.availableActions
                 (fosgView g hctx) h.lastState.pref who)) ↔
          (who ∈ active
              (cursorWorldOfGraphConfiguration g hctx
                h.lastState.pref.lastState).toWorld ∧
            action ∈
              CursorCheckedWorld.availableProgramActions
                (cursorWorldOfGraphConfiguration g hctx
                  h.lastState.pref.lastState) who)
      rw [if_neg hcut, if_neg hcut]
      rw [fosgView_active_eq_cursor_active_of_not_terminal
        g hctx h.lastState.pref hnotGraph,
        fosgView_availableActions_eq_cursor_availableProgramActions_of_not_terminal
          g hctx h.lastState.pref who hnotGraph]
      rfl

theorem finiteFOSG_cursor_nonterminal_of_not_terminal
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (h : (finiteFOSG g hctx).History)
    (hterm : ¬ (finiteFOSG g hctx).terminal h.lastState) :
    ¬ terminal (cursorWorldOfGraphConfiguration g hctx h.lastState.lastState).toWorld := by
  have hnotCut :
      ¬ syntaxSteps g.prog ≤ h.lastState.pref.events.length := by
    intro hcut
    exact hterm (Or.inr hcut)
  have hnotGraph :=
    finiteFOSG_not_graph_terminal_of_not_cutoff
      g hctx h hnotCut
  have hnotComplete :
      ¬ (syntaxActionGraph g).CompleteAt
        h.lastState.lastState.frontier.done := by
    simpa [graphMachine_terminal, ActionGraph.Configuration.isTerminal,
      ActionGraph.FrontierMachine.isComplete] using hnotGraph
  have hdoneBefore :=
    finiteFOSG_history_doneBeforeCursor g hctx h
  have hpositive :
      0 < syntaxSteps
        (cursorWorldOfGraphConfiguration g hctx
          h.lastState.lastState).1.cursor.prog :=
    syntaxGraphDoneBeforeCursor_cursor_nonterminal_of_not_complete
      (g := g) hdoneBefore hnotComplete
  intro hcursor
  have hzero :
      syntaxSteps
        (cursorWorldOfGraphConfiguration g hctx
          h.lastState.lastState).1.cursor.prog = 0 := by
    have hz :=
      (CursorCheckedWorld.terminal_iff_remainingSyntaxSteps_eq_zero
        (g := g)
        (w := cursorWorldOfGraphConfiguration g hctx
          h.lastState.lastState)).1 hcursor
    simpa [CursorCheckedWorld.remainingSyntaxSteps,
      CursorWorldData.prog] using hz
  omega

theorem graphMachineJointAction_selected_eq_of_active
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (horizon : Nat)
    {pref : (graphMachine g hctx).BoundedRunPrefix horizon}
    (action : (boundedFOSG g hctx horizon).LegalAction pref)
    {who : P}
    (hactive :
      who ∈ (boundedFOSG g hctx horizon).active pref) :
    graphMachineJointAction g hctx
        ((fosgView g hctx).boundedEventOfLegalJointAction
          horizon pref action) who =
      action.1 who := by
  classical
  cases hturn : (fosgView g hctx).turn pref.pref with
  | internal event =>
      have hfalse := hactive
      simp [boundedFOSG, Machine.FOSGView.boundedActive,
        Machine.FOSGView.active, hturn] at hfalse
  | play player =>
      have hcut : ¬ horizon ≤ pref.pref.events.length := by
        intro hle
        exact action.2.1 (Or.inr hle)
      have hwho : who = player := by
        have hmem : who ∈ ({player} : Finset P) := by
          simpa [boundedFOSG, Machine.FOSGView.boundedActive,
            Machine.FOSGView.active, hcut, hturn] using hactive
        simpa using hmem
      subst who
      cases hmove : action.1 player with
      | none =>
          have hlocal := action.2.2 player
          have hnot :
              player ∉
                (fosgView g hctx).boundedActive horizon pref := by
            simpa [hmove] using hlocal
          have hmem :
              player ∈
                (fosgView g hctx).boundedActive horizon pref := by
            simp [Machine.FOSGView.boundedActive,
              Machine.FOSGView.active, hcut, hturn]
          exact False.elim (hnot hmem)
      | some choice =>
          have hevent :=
            (fosgView g hctx)
              |>.boundedEventOfLegalJointAction_eq_play_of_turn_action
                horizon pref action hturn hmove
          rw [hevent]
          simp [graphMachineJointAction]
          rfl

/-- The finite graph-machine FOSG for a checked Vegas program satisfies the
FOSG legality-observability side condition needed by Kuhn's theorem. -/
theorem finiteFOSG_legalObservable
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    (finiteFOSG g hctx).LegalObservable := by
  intro who h h' hInfo
  let G := finiteFOSG g hctx
  have hobsLen :
      (GameTheory.FOSG.InfoState.observationEvents
        (G := G) (i := who) (h.playerView who)).length =
        h.steps.length := by
    simpa [G, finiteFOSG, boundedFOSG] using
      (fosgView g hctx)
        |>.toBoundedFOSG_history_playerView_observationEvents_length
          (syntaxSteps g.prog) h who
  have hobsLen' :
      (GameTheory.FOSG.InfoState.observationEvents
        (G := G) (i := who) (h'.playerView who)).length =
        h'.steps.length := by
    simpa [G, finiteFOSG, boundedFOSG] using
      (fosgView g hctx)
        |>.toBoundedFOSG_history_playerView_observationEvents_length
          (syntaxSteps g.prog) h' who
  have hlenEq : h.steps.length = h'.steps.length := by
    have hlen :=
      congrArg
        (fun s =>
          (GameTheory.FOSG.InfoState.observationEvents
            (G := G) (i := who) s).length)
        hInfo
    change
      (GameTheory.FOSG.InfoState.observationEvents
        (G := G) (i := who) (h.playerView who)).length =
        (GameTheory.FOSG.InfoState.observationEvents
          (G := G) (i := who) (h'.playerView who)).length at hlen
    rw [hobsLen, hobsLen'] at hlen
    exact hlen
  by_cases hnil : h.steps = []
  · have hnil' : h'.steps = [] := by
      have hlen0 : h'.steps.length = 0 := by
        rw [← hlenEq, hnil]
        rfl
      exact List.eq_nil_of_length_eq_zero hlen0
    have hh : h = GameTheory.FOSG.History.nil G := by
      cases h with
      | mk steps chain =>
          cases hnil
          rfl
    have hh' : h' = GameTheory.FOSG.History.nil G := by
      cases h' with
      | mk steps chain =>
          cases hnil'
          rfl
    subst hh
    subst hh'
    rfl
  · have hnil' : h'.steps ≠ [] := by
      intro hnil'
      have hlen0 : h.steps.length = 0 := by
        rw [hlenEq, hnil']
        rfl
      exact hnil (List.eq_nil_of_length_eq_zero hlen0)
    have heventLen :=
      (fosgView g hctx)
        |>.toBoundedFOSG_history_events_length (syntaxSteps g.prog) h
    have heventLen' :=
      (fosgView g hctx)
        |>.toBoundedFOSG_history_events_length (syntaxSteps g.prog) h'
    have hcutEq :
        (syntaxSteps g.prog ≤ h.lastState.pref.events.length) ↔
          (syntaxSteps g.prog ≤ h'.lastState.pref.events.length) := by
      have heqEvents :
          h.lastState.pref.events.length =
            h'.lastState.pref.events.length := by
        calc
          h.lastState.pref.events.length = h.steps.length := heventLen
          _ = h'.steps.length := hlenEq
          _ = h'.lastState.pref.events.length := heventLen'.symm
      constructor
      · intro hle
        exact heqEvents ▸ hle
      · intro hle
        exact heqEvents.symm ▸ hle
    by_cases hcut : syntaxSteps g.prog ≤ h.lastState.pref.events.length
    · have hcut' : syntaxSteps g.prog ≤ h'.lastState.pref.events.length :=
        hcutEq.mp hcut
      have hInactive : who ∉ G.active h.lastState := by
        change who ∉
          (if syntaxSteps g.prog ≤ h.lastState.pref.events.length then ∅
           else (fosgView g hctx).active h.lastState.pref)
        rw [if_pos hcut]
        simp
      have hInactive' : who ∉ G.active h'.lastState := by
        change who ∉
          (if syntaxSteps g.prog ≤ h'.lastState.pref.events.length then ∅
           else (fosgView g hctx).active h'.lastState.pref)
        rw [if_pos hcut']
        simp
      rw [G.availableMoves_eq_singleton_none_of_not_mem_active h hInactive,
        G.availableMoves_eq_singleton_none_of_not_mem_active h' hInactive']
    · have hcut' : ¬ syntaxSteps g.prog ≤ h'.lastState.pref.events.length := by
        intro hle
        exact hcut (hcutEq.mpr hle)
      have hlatest :=
        congrArg
          (GameTheory.FOSG.InfoState.latestObservation?
            (G := G) (i := who))
          hInfo
      have hlatest₁ :
          GameTheory.FOSG.InfoState.latestObservation?
              (G := G) (i := who) (h.playerView who) =
            some (privateObsOfCursorWorld who
                (cursorWorldOfGraphConfiguration g hctx
                  h.lastState.lastState),
              publicObsOfCursorWorld (hctx := hctx)
                (cursorWorldOfGraphConfiguration g hctx
                  h.lastState.lastState)) := by
        simpa [G, finiteFOSG, boundedFOSG,
          graphMachine] using
          (fosgView g hctx)
            |>.toBoundedFOSG_latestObservation?_history_of_ne_nil
              (syntaxSteps g.prog) who h hnil
      have hlatest₂ :
          GameTheory.FOSG.InfoState.latestObservation?
              (G := G) (i := who) (h'.playerView who) =
            some (privateObsOfCursorWorld who
                (cursorWorldOfGraphConfiguration g hctx
                  h'.lastState.lastState),
              publicObsOfCursorWorld (hctx := hctx)
                (cursorWorldOfGraphConfiguration g hctx
                  h'.lastState.lastState)) := by
        simpa [G, finiteFOSG, boundedFOSG,
          graphMachine] using
          (fosgView g hctx)
            |>.toBoundedFOSG_latestObservation?_history_of_ne_nil
              (syntaxSteps g.prog) who h' hnil'
      rw [hlatest₁, hlatest₂] at hlatest
      injection hlatest with hobs
      have hpriv :
          privateObsOfCursorWorld who
              (cursorWorldOfGraphConfiguration g hctx
                h.lastState.lastState) =
            privateObsOfCursorWorld who
              (cursorWorldOfGraphConfiguration g hctx
                h'.lastState.lastState) :=
        congrArg Prod.fst hobs
      rw [
        finiteFOSG_availableMoves_eq_observedProgram_of_not_cutoff
          g hctx who h hcut,
        finiteFOSG_availableMoves_eq_observedProgram_of_not_cutoff
          g hctx who h' hcut']
      exact cursorFOSG_availableMovesAtState_eq_of_privateObs_eq
        g hctx who
        (cursorWorldOfGraphConfiguration g hctx h.lastState.lastState)
        (cursorWorldOfGraphConfiguration g hctx h'.lastState.lastState)
        hpriv

end Vegas
