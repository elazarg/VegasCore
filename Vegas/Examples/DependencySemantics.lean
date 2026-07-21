import Vegas.Frontier
import Vegas.EventGraph.Validate
import Vegas.Export.KernelGame
import Vegas.Export.FOSG
import Vegas.Export.EFG
import Vegas.Presentation.FOSG.FromCore
import Vegas.Presentation.EFG.FromCore
import Vegas.Language.Basic
import Vegas.Core.ExprSimple
import GameTheory.Concepts.Equilibrium.SolutionConcepts

/-!
# Event-graph compiler checks

Small checks for dependency construction, schedule-free readiness, and
graph-causal commit views.
-/

namespace Vegas
namespace Examples

open GameTheory
open ToEventGraph

inductive Player where
  | alice
  | bob
deriving DecidableEq, Repr, Fintype

abbrev L := simpleExpr

def boolRef (field : Nat) : EventGraph.FieldRef L where
  field := field
  ty := .bool

@[simp] theorem boolRef_field (field : Nat) :
    (boolRef field).field = field := rfl

def sealedChoice : EventGraph.EventGuard L where
  ty := .bool
  choiceReads := ∅
  eval := fun _ _ => true

def revealedChoice : EventGraph.EventGuard L where
  ty := .bool
  choiceReads := {boolRef 1}
  eval := fun _ _ => true

def sealedReadChoice : EventGraph.EventGuard L where
  ty := .bool
  choiceReads := {boolRef 0}
  eval := fun _ _ => true

def ownHistoryChoice : EventGraph.EventGuard L where
  ty := .bool
  choiceReads := {boolRef 0}
  eval := fun _ _ => true

def boolValue (value : Bool) : EventGraph.TypedValue L where
  ty := .bool
  value := value

def boolInitialField (owner : Option Player) (value : Bool) :
    EventGraph.InitialField Player L where
  ty := .bool
  owner := owner
  value := value

def boolEvent (owner : Option Player)
    (sem : EventGraph.NodeSem Player L) : EventGraph.EventNode Player L where
  ty := .bool
  owner := owner
  sem := sem

noncomputable def constGraphDist
    (reads : Finset (EventGraph.FieldRef L)) (value : Bool) :
    EventGraph.EventDist L where
  ty := .bool
  reads := reads
  eval := fun _ => PMF.pure value

def twoHiddenCommitNodes : List (EventGraph.EventNode Player L) :=
  [boolEvent (some .alice) (.commit .alice sealedChoice),
   boolEvent (some .bob) (.commit .bob sealedChoice)]

def twoHiddenCommitGraph : EventGraph.Graph Player L where
  initialFields := []
  nodes := twoHiddenCommitNodes

def twoHiddenCommitNode0 : Fin twoHiddenCommitGraph.nodeCount :=
  ⟨0, by
    simp [twoHiddenCommitGraph, twoHiddenCommitNodes,
      EventGraph.Graph.nodeCount]⟩

def twoHiddenCommitNode1 : Fin twoHiddenCommitGraph.nodeCount :=
  ⟨1, by
    simp [twoHiddenCommitGraph, twoHiddenCommitNodes,
      EventGraph.Graph.nodeCount]⟩

def wrongCommitOwnerGraph : EventGraph.Graph Player L where
  initialFields := []
  nodes := [boolEvent none (.commit .alice sealedChoice)]

example :
    wrongCommitOwnerGraph.valid = false := by
  rfl

def sealedReadLeakGraph : EventGraph.Graph Player L where
  initialFields := [boolInitialField (some .alice) false]
  nodes := [boolEvent (some .bob) (.commit .bob sealedReadChoice)]

example :
    sealedReadLeakGraph.valid = false := by
  decide

noncomputable def sealedPublicSampleGraph : EventGraph.Graph Player L where
  initialFields := [boolInitialField (some .alice) false]
  nodes := [boolEvent none (.sample (constGraphDist {boolRef 0} true))]

example :
    sealedPublicSampleGraph.valid = false := by
  decide

noncomputable def futureReadGraph : EventGraph.Graph Player L where
  initialFields := []
  nodes :=
    [boolEvent none (.sample (constGraphDist {boolRef 1} true)),
     boolEvent none (.sample (constGraphDist ∅ false))]

example :
    futureReadGraph.valid = false := by
  rfl

def publicRevealSourceGraph : EventGraph.Graph Player L where
  initialFields := [boolInitialField none false]
  nodes := [boolEvent none (.reveal 0)]

example :
    publicRevealSourceGraph.valid = false := by
  rfl

def twoHiddenCommitInit : EventGraph.Config twoHiddenCommitGraph :=
  EventGraph.Config.initial twoHiddenCommitGraph

example :
    twoHiddenCommitGraph.prereqs twoHiddenCommitNode0 = ∅ := by
  decide

example :
    twoHiddenCommitGraph.prereqs twoHiddenCommitNode1 = ∅ := by
  decide

example :
    EventGraph.Ready twoHiddenCommitGraph twoHiddenCommitInit
      twoHiddenCommitNode0 := by
  rw [EventGraph.Ready]
  constructor
  · change twoHiddenCommitNode0 ∉
      (∅ : Finset (Fin twoHiddenCommitGraph.nodeCount))
    simp
  · have hpr : twoHiddenCommitGraph.prereqs twoHiddenCommitNode0 = ∅ := by
      decide
    rw [hpr]
    simp

example :
    EventGraph.Ready twoHiddenCommitGraph twoHiddenCommitInit
      twoHiddenCommitNode1 := by
  rw [EventGraph.Ready]
  constructor
  · change twoHiddenCommitNode1 ∉
      (∅ : Finset (Fin twoHiddenCommitGraph.nodeCount))
    simp
  · have hpr : twoHiddenCommitGraph.prereqs twoHiddenCommitNode1 = ∅ := by
      decide
    rw [hpr]
    simp

noncomputable def publicSampleAfterHiddenCommitNodes :
    List (EventGraph.EventNode Player L) :=
  [boolEvent (some .alice) (.commit .alice sealedChoice),
   boolEvent none (.sample (constGraphDist ∅ true))]

noncomputable def publicSampleAfterHiddenCommitGraph :
    EventGraph.Graph Player L where
  initialFields := []
  nodes := publicSampleAfterHiddenCommitNodes

def publicSampleAfterHiddenCommitNode1 :
    Fin publicSampleAfterHiddenCommitGraph.nodeCount :=
  ⟨1, by
    simp [publicSampleAfterHiddenCommitGraph,
      publicSampleAfterHiddenCommitNodes, boolEvent,
      EventGraph.Graph.nodeCount]⟩

/-- A public computation with an empty declared footprint is not ordered after
an unrelated sealed commit. -/
example :
    publicSampleAfterHiddenCommitGraph.prereqs
      publicSampleAfterHiddenCommitNode1 = ∅ := by
  decide

def samePlayerCommitNodes : List (EventGraph.EventNode Player L) :=
  [boolEvent (some .alice) (.commit .alice sealedChoice),
   boolEvent (some .alice) (.commit .alice ownHistoryChoice)]

def samePlayerCommitGraph : EventGraph.Graph Player L where
  initialFields := []
  nodes := samePlayerCommitNodes

def samePlayerCommitNode0 : Fin samePlayerCommitGraph.nodeCount :=
  ⟨0, by
    simp [samePlayerCommitGraph, samePlayerCommitNodes, boolEvent,
      EventGraph.Graph.nodeCount]⟩

def samePlayerCommitNode1 : Fin samePlayerCommitGraph.nodeCount :=
  ⟨1, by
    simp [samePlayerCommitGraph, samePlayerCommitNodes, boolEvent,
      EventGraph.Graph.nodeCount]⟩

/-- Same-player later commits can be ordered by the player's own visible
history. -/
example :
    samePlayerCommitGraph.prereqs samePlayerCommitNode1 =
      {samePlayerCommitNode0} := by
  decide

def afterAliceCommit : EventGraph.Config twoHiddenCommitGraph :=
  twoHiddenCommitInit.completeNode twoHiddenCommitNode0 (boolValue true)

def aliceTrueAction : EventGraph.CommitAction twoHiddenCommitGraph .alice where
  node := twoHiddenCommitNode0
  value := boolValue true

example :
    EventGraph.CommitAvailable twoHiddenCommitGraph twoHiddenCommitInit
      .alice aliceTrueAction := by
  let row := boolEvent (some .alice) (.commit .alice sealedChoice)
  have henv :
      ∃ env : EventGraph.ReadEnv L sealedChoice.choiceReads,
        EventGraph.ReadEnv.ofStore? twoHiddenCommitInit.store
          sealedChoice.choiceReads = some env := by
    simp [sealedChoice, EventGraph.ReadEnv.ofStore?]
  refine
    ⟨{ row := row
       guard := sealedChoice
       row_get := ?_
       sem_eq := ?_
       ready := ?_
       value := true
       value_ok := ?_
       env := Classical.choose henv
       env_ok := Classical.choose_spec henv
       guard_ok := ?_ }⟩
  · change twoHiddenCommitNodes[0]? = some row
    simp [row, twoHiddenCommitNodes,
      boolEvent]
  · simp [row, boolEvent]
  · change EventGraph.Ready twoHiddenCommitGraph twoHiddenCommitInit
      twoHiddenCommitNode0
    rw [EventGraph.Ready]
    constructor
    · change twoHiddenCommitNode0 ∉
        (∅ : Finset (Fin twoHiddenCommitGraph.nodeCount))
      simp
    · have hpr : twoHiddenCommitGraph.prereqs twoHiddenCommitNode0 = ∅ := by
        decide
      rw [hpr]
      simp
  · simp [aliceTrueAction, boolValue, sealedChoice, EventGraph.TypedValue.as?]
  · simp [sealedChoice]

/-- Bob's independent commit has an empty choice footprint, so Alice's
scheduled commit does not enter Bob's graph-causal view. -/
example :
    (EventGraph.observe twoHiddenCommitGraph afterAliceCommit .bob).value?
      twoHiddenCommitNode1
      (boolRef 0) = none := by
  simp [EventGraph.Observation.value?, EventGraph.observe,
    EventGraph.Graph.fieldRow, afterAliceCommit, twoHiddenCommitInit,
    twoHiddenCommitNode1, twoHiddenCommitGraph, twoHiddenCommitNodes,
    boolEvent, sealedChoice, EventGraph.Config.initial, EventGraph.Config.completeNode,
    EventGraph.Ready, EventGraph.Graph.node?, EventGraph.Graph.nodeCount,
    EventGraph.Graph.prereqs]

def revealThenCommitNodes : List (EventGraph.EventNode Player L) :=
  [boolEvent (some .alice) (.commit .alice sealedChoice),
   boolEvent none (.reveal 0),
   boolEvent (some .bob) (.commit .bob revealedChoice)]

def twoRevealNodes : List (EventGraph.EventNode Player L) :=
  [boolEvent (some .alice) (.commit .alice sealedChoice),
   boolEvent (some .bob) (.commit .bob sealedChoice),
   boolEvent none (.reveal 0),
   boolEvent none (.reveal 1)]

def revealThenCommitGraph : EventGraph.Graph Player L where
  initialFields := []
  nodes := revealThenCommitNodes

def revealThenCommitNode0 : Fin revealThenCommitGraph.nodeCount :=
  ⟨0, by
    simp [revealThenCommitGraph, revealThenCommitNodes, boolEvent,
      EventGraph.Graph.nodeCount]⟩

def revealThenCommitNode1 : Fin revealThenCommitGraph.nodeCount :=
  ⟨1, by
    simp [revealThenCommitGraph, revealThenCommitNodes, boolEvent,
      EventGraph.Graph.nodeCount]⟩

def revealThenCommitNode2 : Fin revealThenCommitGraph.nodeCount :=
  ⟨2, by
    simp [revealThenCommitGraph, revealThenCommitNodes, boolEvent,
      EventGraph.Graph.nodeCount]⟩

/-- The reveal depends on the commit it opens. -/
example :
    revealThenCommitGraph.prereqs revealThenCommitNode1 =
      {revealThenCommitNode0} := by
  decide

/-- Bob's later commit can condition on the public reveal. -/
theorem revealThenCommitNode2_prereqs :
    revealThenCommitGraph.prereqs revealThenCommitNode2 =
      {revealThenCommitNode1} := by
  decide

def twoRevealGraph : EventGraph.Graph Player L where
  initialFields := []
  nodes := twoRevealNodes

def twoRevealNode2 : Fin twoRevealGraph.nodeCount :=
  ⟨2, by
    simp [twoRevealGraph, twoRevealNodes, boolEvent,
      EventGraph.Graph.nodeCount]⟩

def twoRevealNode3 : Fin twoRevealGraph.nodeCount :=
  ⟨3, by
    simp [twoRevealGraph, twoRevealNodes, boolEvent,
      EventGraph.Graph.nodeCount]⟩

def twoRevealNode0 : Fin twoRevealGraph.nodeCount :=
  ⟨0, by
    simp [twoRevealGraph, twoRevealNodes, boolEvent,
      EventGraph.Graph.nodeCount]⟩

def twoRevealNode1 : Fin twoRevealGraph.nodeCount :=
  ⟨1, by
    simp [twoRevealGraph, twoRevealNodes, boolEvent,
      EventGraph.Graph.nodeCount]⟩

/-- The source-order reveal barrier fixes all earlier commitments before the
first reveal, including commitments that the reveal does not read directly. -/
example :
    twoRevealGraph.prereqs twoRevealNode2 =
      {twoRevealNode0, twoRevealNode1} := by
  decide

/-- A later reveal also waits for earlier commits, but reveal/reveal pairs are
not ordered just because a reveal is earlier in source order. -/
example :
    twoRevealGraph.prereqs twoRevealNode3 =
      {twoRevealNode0, twoRevealNode1} := by
  decide

/-- Reveals wait for prior commits, but not for prior reveals. -/
example :
    twoRevealNode2 ∉ twoRevealGraph.prereqs twoRevealNode3 := by
  decide

def revealThenCommitInit : EventGraph.Config revealThenCommitGraph :=
  EventGraph.Config.initial revealThenCommitGraph

example :
    ¬ EventGraph.Ready revealThenCommitGraph revealThenCommitInit
      revealThenCommitNode2 := by
  have hnot :
      ¬ revealThenCommitGraph.prereqs revealThenCommitNode2 ⊆
        revealThenCommitInit.done := by
    rw [revealThenCommitNode2_prereqs]
    simp [revealThenCommitInit, EventGraph.Config.initial]
  intro hready
  rw [EventGraph.Ready] at hready
  exact hnot hready.2

def afterRelevantReveal : EventGraph.Config revealThenCommitGraph :=
  { done := {revealThenCommitNode0, revealThenCommitNode1}
    store := EventGraph.Store.set
      (EventGraph.Store.set revealThenCommitInit.store 0 (boolValue true))
      1 (boolValue true) }

/-- Once the relevant reveal is complete, Bob's commit view contains the
revealed field because that field is in the commit choice footprint. -/
example :
    (EventGraph.observe revealThenCommitGraph afterRelevantReveal .bob).value?
      revealThenCommitNode2
      (boolRef 1) = some true := by
  have hready :
      EventGraph.Ready revealThenCommitGraph afterRelevantReveal
        revealThenCommitNode2 := by
    rw [EventGraph.Ready]
    refine ⟨?_, ?_⟩
    · change revealThenCommitNode2 ∉
        ({revealThenCommitNode0, revealThenCommitNode1} :
          Finset (Fin revealThenCommitGraph.nodeCount))
      decide
    · rw [revealThenCommitNode2_prereqs]
      simp [afterRelevantReveal, revealThenCommitNode1]
  have hnode :
      revealThenCommitGraph.node? (revealThenCommitNode2 : Nat) =
        some (EventGraph.NodeSem.commit Player.bob revealedChoice) := by
    change revealThenCommitGraph.node? 2 =
      some (EventGraph.NodeSem.commit Player.bob revealedChoice)
    simp [revealThenCommitGraph, revealThenCommitNodes, boolEvent,
      EventGraph.Graph.node?]
  have hstore :
      EventGraph.Store.getAs afterRelevantReveal.store 1 BaseTy.bool =
        some true := by
    simp [afterRelevantReveal, EventGraph.Store.set, EventGraph.Store.getAs,
      boolValue, EventGraph.TypedValue.as?]
    rfl
  have hrowSem :
      (revealThenCommitGraph.nodeRow revealThenCommitNode2).sem =
        EventGraph.NodeSem.commit Player.bob revealedChoice := by
    have hcanonical :=
      revealThenCommitGraph.node?_nodeRow revealThenCommitNode2
    rw [hnode] at hcanonical
    exact Option.some.inj hcanonical
  simp [EventGraph.Observation.value?, EventGraph.observe,
    EventGraph.Graph.fieldRow, hrowSem, hready, revealedChoice, boolRef]
  cases afterRelevantReveal.store.getAs 1 BaseTy.bool <;> rfl

def revealThenUnrelatedCommitGraph : EventGraph.Graph Player L where
  initialFields := []
  nodes :=
    [boolEvent (some .alice) (.commit .alice sealedChoice),
     boolEvent none (.reveal 0),
     boolEvent (some .bob) (.commit .bob sealedChoice)]

def revealThenUnrelatedCommitNode2 :
    Fin revealThenUnrelatedCommitGraph.nodeCount :=
  ⟨2, by
    simp [revealThenUnrelatedCommitGraph, boolEvent,
      EventGraph.Graph.nodeCount]⟩

def revealThenUnrelatedCommitNode0 :
    Fin revealThenUnrelatedCommitGraph.nodeCount :=
  ⟨0, by
    simp [revealThenUnrelatedCommitGraph, boolEvent,
      EventGraph.Graph.nodeCount]⟩

def revealThenUnrelatedCommitNode1 :
    Fin revealThenUnrelatedCommitGraph.nodeCount :=
  ⟨1, by
    simp [revealThenUnrelatedCommitGraph, boolEvent,
      EventGraph.Graph.nodeCount]⟩

def afterUnrelatedReveal : EventGraph.Config revealThenUnrelatedCommitGraph :=
  { done := {revealThenUnrelatedCommitNode0, revealThenUnrelatedCommitNode1}
    store := EventGraph.Store.set
      (EventGraph.Store.set
        (EventGraph.Config.initial revealThenUnrelatedCommitGraph).store
        0 (boolValue true))
      1 (boolValue true) }

/-- An unrelated reveal scheduled before a commit is not visible to that commit
unless the commit choice footprint contains the revealed field. -/
example :
    (EventGraph.observe revealThenUnrelatedCommitGraph
      afterUnrelatedReveal .bob).value? revealThenUnrelatedCommitNode2
      (boolRef 1) = none := by
  simp [EventGraph.Observation.value?, EventGraph.observe,
    EventGraph.Graph.fieldRow, afterUnrelatedReveal,
    revealThenUnrelatedCommitNode2, revealThenUnrelatedCommitGraph, boolEvent,
    sealedChoice, EventGraph.Ready, EventGraph.Graph.node?, EventGraph.Graph.nodeCount,
    EventGraph.Graph.prereqs]

/-! ## Compiler-path regressions -/

def surfaceLetOnly : VegasLang Player [] :=
  .letExpr 0 (.constBool true) (.ret [])

def coreLetOnly : VegasCore Player L [] :=
  VegasLang.lower surfaceLetOnly

/-- Surface `let` is erased before core/event-graph compilation. -/
example :
    coreLetOnly = .ret [] := by
  rfl

noncomputable def graphLetOnly : GraphProgram Player L where
  Γ := []
  prog := coreLetOnly
  env := VEnv.empty L
  wctx := WFCtx_nil
  fresh := by
    trivial
  normalized := by
    trivial

/-- Surface `let` emits no event-graph node. -/
example :
    (compile graphLetOnly).graph.nodeCount = 0 := by
  simp [compile, graphLetOnly, coreLetOnly, surfaceLetOnly, VegasLang.lower,
    VegasLang.lowerWith, VegasLang.LowerEnv.expr, VegasLang.LowerEnv.aliasPublic,
    compileCore, EventGraph.Graph.nodeCount]

def sampleThenRetCore : VegasCore Player L [] :=
  .sample 0 (b := .bool) (DistExpr.point true) (.ret [])

noncomputable def sampleThenRetProgram : GraphProgram Player L where
  Γ := []
  prog := sampleThenRetCore
  env := VEnv.empty L
  wctx := WFCtx_nil
  fresh := by
    simp [sampleThenRetCore, FreshBindings, Fresh]
  normalized := by
    simp only [sampleThenRetCore, NormalizedDists]
    constructor
    · intro depEnv
      change
        FWeight.totalWeight
          (FWeight.ofList [(true, (1 : ℚ≥0))]) = 1
      rw [FWeight.ofList_cons, FWeight.ofList_nil]
      simp [FWeight.totalWeight, FWeight.zero]
    · trivial

noncomputable def sampleThenRetCompiled : CompiledProgram Player L :=
  compile sampleThenRetProgram

/-- A source sample followed by return compiles to exactly one graph event. -/
example :
    sampleThenRetCompiled.graph.nodeCount = 1 := by
  simp [sampleThenRetCompiled, compile, sampleThenRetProgram,
    sampleThenRetCore, compileCore, EventGraph.Graph.nodeCount]

/-- Returning after the sample adds no payoff projection. -/
example :
    sampleThenRetCompiled.payoffs.length = 0 := by
  simp [sampleThenRetCompiled, compile, sampleThenRetProgram,
    sampleThenRetCore, compileCore]

def trueGuard {Γ : CtxSimple} {x : VarId} :
    Expr ((x, .bool) :: Γ) .bool :=
  .constBool true

def independentCommitCore : VegasCore Player L [] :=
  .commit 0 .alice (trueGuard (x := 0))
    (.commit 1 .bob (trueGuard (x := 1))
      (.ret []))

noncomputable def independentCommitProgram : GraphProgram Player L where
  Γ := []
  prog := independentCommitCore
  env := VEnv.empty L
  wctx := WFCtx_nil
  fresh := by
    simp [independentCommitCore, FreshBindings, Fresh]
  normalized := by
    simp [independentCommitCore, NormalizedDists]

noncomputable def independentCommitCompiled : CompiledProgram Player L :=
  compile independentCommitProgram

noncomputable def independentCommitCompiledNode1 :
    Fin independentCommitCompiled.graph.nodeCount :=
  ⟨1, by
    simp [independentCommitCompiled, compile, independentCommitProgram,
      independentCommitCore, trueGuard, compileCore,
      EventGraph.Graph.nodeCount]⟩

/-- Independent initial commits compile to two protocol graph nodes. -/
example :
    (compile independentCommitProgram).graph.nodeCount = 2 := by
  simp [compile, independentCommitProgram, independentCommitCore, trueGuard,
    compileCore, EventGraph.Graph.nodeCount]

/-- The second independent initial commit has no choice footprint in the
compiled graph. -/
example :
    (match (compile independentCommitProgram).graph.node? 1 with
     | some sem => sem.reads
     | none => ∅) = ∅ := by
  simp [compile, independentCommitProgram, independentCommitCore, trueGuard,
    compileCore, eventGuardOf, visibleFieldRefs, initialState,
    viewVCtx, canSee, Visibility.canSee, EventGraph.Graph.node?,
    EventGraph.NodeSem.reads]

/-- Independent initial commits stay unordered after source compilation. -/
example :
    independentCommitCompiled.graph.prereqs independentCommitCompiledNode1 =
      ∅ := by
  decide

def samePlayerCommitCore : VegasCore Player L [] :=
  .commit 0 .alice (trueGuard (x := 0))
    (.commit 1 .alice (trueGuard (x := 1))
      (.ret []))

noncomputable def samePlayerCommitProgram : GraphProgram Player L where
  Γ := []
  prog := samePlayerCommitCore
  env := VEnv.empty L
  wctx := WFCtx_nil
  fresh := by
    simp [samePlayerCommitCore, FreshBindings, Fresh]
  normalized := by
    simp [samePlayerCommitCore, NormalizedDists]

/-- Same-player commit chains compile without administrative nodes. -/
example :
    (compile samePlayerCommitProgram).graph.nodeCount = 2 := by
  simp [compile, samePlayerCommitProgram, samePlayerCommitCore, trueGuard,
    compileCore, EventGraph.Graph.nodeCount]

/-- A later same-player commit choice footprint contains the player's prior
sealed field in the compiled graph. -/
example :
    (match (compile samePlayerCommitProgram).graph.node? 1 with
     | some sem => sem.reads
     | none => ∅) = {0} := by
  simp only [EventGraph.Graph.node?, compile, samePlayerCommitProgram,
    samePlayerCommitCore, viewVCtx, eraseVCtx_nil, trueGuard, canSee,
    Visibility.canSee, decide_true, ↓dreduceIte, eraseVCtx_cons,
    erasePubVCtx_cons_sealed, erasePubVCtx_nil, initialState, compileCore,
    eventGuardOf, visibleFieldRefs, fieldRefsOfCtx_nil, fieldRefsOfCtx_cons,
    Finset.insert_empty, BuildState.addEvent_initialFields,
    BuildState.fromInitial_initialFields, BuildState.addEvent_nodes,
    BuildState.fromInitial_nodes, BindTy.owner_sealed, List.nil_append,
    List.cons_append, List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Order.lt_two_iff, Std.le_refl, getElem?_pos,
    List.getElem_cons_succ, List.getElem_cons_zero,
    EventGraph.NodeSem.reads, EventGraph.FieldRef.fields,
    Finset.image_singleton, Finset.singleton_inj]
  rw [BuildState.fieldOf_eq_of_nodup _ _
    (VHasVar.here :
      VHasVar
        [(0, BindTy.sealed (L := L) Player.alice BaseTy.bool)]
        0 (BindTy.sealed (L := L) Player.alice BaseTy.bool))]
  rw [BuildState.addCommitEvent_fieldOf_here]
  rfl

def revealBarrierCore : VegasCore Player L [] :=
  .commit 0 .alice (trueGuard (x := 0))
    (.reveal 1 .alice 0 VHasVar.here
      (.ret []))

noncomputable def revealBarrierProgram : GraphProgram Player L where
  Γ := []
  prog := revealBarrierCore
  env := VEnv.empty L
  wctx := WFCtx_nil
  fresh := by
    simp [revealBarrierCore, FreshBindings, Fresh]
  normalized := by
    simp [revealBarrierCore, NormalizedDists]

noncomputable def revealBarrierCompiled : CompiledProgram Player L :=
  compile revealBarrierProgram

noncomputable def revealBarrierCompiledNode0 :
    Fin revealBarrierCompiled.graph.nodeCount :=
  ⟨0, by
    simp [revealBarrierCompiled, compile, revealBarrierProgram,
      revealBarrierCore, trueGuard, compileCore, EventGraph.Graph.nodeCount]⟩

noncomputable def revealBarrierCompiledNode1 :
    Fin revealBarrierCompiled.graph.nodeCount :=
  ⟨1, by
    simp [revealBarrierCompiled, compile, revealBarrierProgram,
      revealBarrierCore, trueGuard, compileCore, EventGraph.Graph.nodeCount]⟩

/-- A commit followed by reveal compiles to two protocol graph nodes. -/
example :
    (compile revealBarrierProgram).graph.nodeCount = 2 := by
  simp [compile, revealBarrierProgram, revealBarrierCore, trueGuard,
    compileCore, EventGraph.Graph.nodeCount]

/-- A compiled reveal waits for the commitment it opens. -/
example :
    revealBarrierCompiled.graph.prereqs revealBarrierCompiledNode1 =
      {revealBarrierCompiledNode0} := by
  decide

def relevantRevealCore : VegasCore Player L [] :=
  .commit 0 .alice (trueGuard (x := 0))
    (.reveal 1 .alice 0 VHasVar.here
      (.commit 2 .bob (trueGuard (x := 2))
        (.ret [])))

noncomputable def relevantRevealProgram : GraphProgram Player L where
  Γ := []
  prog := relevantRevealCore
  env := VEnv.empty L
  wctx := WFCtx_nil
  fresh := by
    simp [relevantRevealCore, FreshBindings, Fresh]
  normalized := by
    simp [relevantRevealCore, NormalizedDists]

/-- A commit after a public reveal compiles to the expected three protocol
nodes. -/
example :
    (compile relevantRevealProgram).graph.nodeCount = 3 := by
  simp [compile, relevantRevealProgram, relevantRevealCore, trueGuard,
    compileCore, EventGraph.Graph.nodeCount]

/-- A commit after a relevant reveal has exactly the revealed public field in
its compiled choice footprint. -/
example :
    (match (compile relevantRevealProgram).graph.node? 2 with
     | some sem => sem.reads
     | none => ∅) = {1} := by
  simp only [EventGraph.Graph.node?, compile, relevantRevealProgram,
    relevantRevealCore, viewVCtx, eraseVCtx_nil, trueGuard, canSee,
    Visibility.canSee, ↓dreduceIte, reduceCtorEq, decide_false,
    Bool.false_eq_true, eraseVCtx_cons, erasePubVCtx_cons_sealed,
    erasePubVCtx_cons_pub, erasePubVCtx_nil, initialState, compileCore,
    eventGuardOf, visibleFieldRefs, fieldRefsOfCtx_nil,
    fieldRefsOfCtx_cons,
    Finset.insert_empty, BuildState.addEvent_initialFields,
    BuildState.fromInitial_initialFields, BuildState.addEvent_nodes,
    BuildState.fromInitial_nodes, BindTy.owner_sealed, List.nil_append,
    BindTy.owner_public, List.cons_append, List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.lt_add_one,
    getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero,
    EventGraph.NodeSem.reads, EventGraph.FieldRef.fields,
    Finset.image_singleton, Finset.singleton_inj]
  rw [BuildState.fieldOf_eq_of_nodup _ _
    (VHasVar.here :
      VHasVar
        [(1, BindTy.pub (Player := Player) (L := L) BaseTy.bool),
          (0, BindTy.sealed (L := L) Player.alice BaseTy.bool)]
        1 (BindTy.pub (Player := Player) (L := L) BaseTy.bool))]
  rw [BuildState.addRevealEvent_fieldOf_here]
  simp only [BuildState.nextField, BuildState.nextNode,
    BuildState.addEvent_nodes, BuildState.fromInitial_nodes,
    BuildState.addEvent_initialFields, BuildState.fromInitial_initialFields,
    InitialState.empty, List.nil_append, List.length_singleton,
    List.length_nil, zero_add]

def missingPayoff : EventGraph.EventPayoff L where
  reads := {boolRef 0}
  eval := fun _ => 0

example :
    EventGraph.evalPayoffs?
      [(Player.alice, missingPayoff)] (fun _ => none) = none := by
  have hmissing :
      ¬ (∀ ref, ref ∈ ({boolRef 0} : Finset (EventGraph.FieldRef L)) →
          ∃ value, EventGraph.Store.getAs (fun _ => none) ref.field ref.ty = some value) := by
    intro h
    rcases h (boolRef 0) (by simp) with ⟨value, hvalue⟩
    simp [EventGraph.Store.getAs] at hvalue
  have henv :
      EventGraph.ReadEnv.ofStore? (L := L) (fun _ => none)
        ({boolRef 0} : Finset (EventGraph.FieldRef L)) = none := by
    unfold EventGraph.ReadEnv.ofStore?
    rw [dif_neg hmissing]
  have hentries :
      EventGraph.evalPayoffEntries?
      [(Player.alice, missingPayoff)] (fun _ => none) = none := by
    simp [EventGraph.evalPayoffEntries?, missingPayoff, henv]
  simp [EventGraph.evalPayoffs?, hentries]


end Examples
end Vegas
