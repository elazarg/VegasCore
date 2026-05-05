import Vegas.Protocol.SyntaxGraph

/-!
# State sufficiency for the syntax graph machine

The graph-native Vegas machine stores an extensional protocol configuration.
For this machine, the current public transcript and a player's current private
observation are sufficient to determine that player's currently available
bounded FOSG moves. Full FOSG history is not needed for move availability.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Dynamic commit legality transfers across syntax-graph configurations that
agree on the visible reads of the guard attached to the node. The frontier
hypothesis supplies availability of the guard reads in the target
configuration. -/
theorem syntaxGraph_actionLegal_of_guardVisibleValue_eq
    (g : WFProgram P L)
    {left right : (syntaxProtocolGraph g).Configuration}
    {node : ProgramNode g.prog}
    {slice : ProgramField.WriteSlice g.prog}
    (hfrontierRight : node ∈ right.frontier)
    (hvisible :
      ∀ {owner : P} {target : ProgramField g.prog}
        {guard : ProtocolGraph.GraphGuard L (ProgramField g.prog)
          (fun field => field.ty) target},
        ProgramNode.sem g.wctx g.wf.1 g.wf.2.2 g.legal g.normalized node =
            .commit owner target guard →
          ∀ read, read ∈ guard.visibleReads →
            ProgramField.value? g.env left.result read =
              ProgramField.value? g.env right.result read)
    (haction :
      (syntaxProtocolGraph g).actionLegal left.result node slice) :
    (syntaxProtocolGraph g).actionLegal right.result node slice := by
  classical
  change
    ProgramNode.actionLegal g.env g.wctx g.wf.1 g.wf.2.2
      g.legal g.normalized left.result node slice at haction
  change
    ProgramNode.actionLegal g.env g.wctx g.wf.1 g.wf.2.2
      g.legal g.normalized right.result node slice
  cases hsem :
      ProgramNode.sem g.wctx g.wf.1 g.wf.2.2
        g.legal g.normalized node with
  | assign field expr =>
      simp [ProgramNode.actionLegal, hsem] at haction
  | sample field dist =>
      simp [ProgramNode.actionLegal, hsem] at haction
  | reveal source target hty =>
      simp [ProgramNode.actionLegal, hsem] at haction
  | commit owner field guard =>
      rw [ProgramNode.actionLegal, hsem] at haction ⊢
      rcases haction with
        ⟨availableLeft, value, hguardEval, hslice⟩
      have availableRight :
          ∀ read, read ∈ guard.reads →
            (ProgramField.value? g.env right.result read).isSome := by
        intro read hread
        exact syntaxReadsAvailableAtFrontier_of_wfProgram g
          right hfrontierRight read
          (by simpa [ProtocolGraph.NodeSem.reads, hsem] using hread)
      refine ⟨availableRight, value, ?_, hslice⟩
      let ρleft :=
        ProgramField.readEnvOfResult g.env left.result
          guard.reads availableLeft
      let ρright :=
        ProgramField.readEnvOfResult g.env right.result
          guard.reads availableRight
      have hguardEq :
          guard.eval value ρleft = guard.eval value ρright := by
        apply guard.eval_eq_of_visible_eq
        intro read hleft hright hreadVisible
        have hvalueEq :
            ProgramField.value? g.env left.result read =
              ProgramField.value? g.env right.result read := by
          exact hvisible (owner := owner) (target := field) (guard := guard)
            hsem read hreadVisible
        simpa [ρleft, ρright] using
          (ProgramField.readEnvOfResult_value_eq_of_value?_eq
            g.env (left := left.result) (right := right.result)
            (availableLeft := availableLeft)
            (availableRight := availableRight)
            (field := read) (hleft := hleft) (hright := hright)
            hvalueEq)
      rw [← hguardEq]
      exact hguardEval

/-- Player action availability in the syntax graph is determined by the public
transcript plus the values of the generated guard-visible reads. This is the
machine-level invariant underlying the coarser observation-sufficiency theorem:
private observation equality is one way to prove equality of these guard-visible
values. -/
theorem syntaxGraph_available_eq_of_publicView_eq_of_guardVisibleValue_eq
    (g : WFProgram P L) (who : P)
    {left right : (syntaxProtocolGraph g).Configuration}
    (hpub : syntaxGraphPublicView g left = syntaxGraphPublicView g right)
    (hvisible :
      ∀ {node : ProgramNode g.prog} {owner : P}
        {target : ProgramField g.prog}
        {guard : ProtocolGraph.GraphGuard L (ProgramField g.prog)
          (fun field => field.ty) target},
        ProgramNode.sem g.wctx g.wf.1 g.wf.2.2 g.legal g.normalized node =
            .commit owner target guard →
          ∀ read, read ∈ guard.visibleReads →
            ProgramField.value? g.env left.result read =
              ProgramField.value? g.env right.result read) :
    ProtocolGraph.available (syntaxProtocolGraph g) left who =
      ProtocolGraph.available (syntaxProtocolGraph g) right who := by
  classical
  ext action
  constructor
  · intro haction
    rcases haction with ⟨hfrontier, hactor, hslice, hlegal⟩
    have hfrontierRight : action.node ∈ right.frontier := by
      simpa [syntaxGraphPublicView_frontier_eq_of_eq g hpub] using hfrontier
    exact ⟨hfrontierRight, hactor, hslice,
      syntaxGraph_actionLegal_of_guardVisibleValue_eq g hfrontierRight
        (fun hsem read hread => hvisible hsem read hread) hlegal⟩
  · intro haction
    rcases haction with ⟨hfrontier, hactor, hslice, hlegal⟩
    have hfrontierLeft : action.node ∈ left.frontier := by
      simpa [syntaxGraphPublicView_frontier_eq_of_eq g hpub] using hfrontier
    exact ⟨hfrontierLeft, hactor, hslice,
      syntaxGraph_actionLegal_of_guardVisibleValue_eq g hfrontierLeft
        (fun hsem read hread => (hvisible hsem read hread).symm) hlegal⟩

/-- Current machine observations determine the bounded FOSG optional moves at
the endpoint of two syntax-graph histories, provided neither endpoint is past
the bounded presentation cutoff. -/
theorem syntaxGraph_availableMoves_eq_of_currentObservation_eq
    (g : WFProgram P L) (horizon : Nat) (who : P)
    {h h' : (((syntaxGraphFOSGView g).toBoundedFOSG horizon).History)}
    (hcut : ¬ horizon ≤ h.lastState.pref.events.length)
    (hcut' : ¬ horizon ≤ h'.lastState.pref.events.length)
    (hpriv :
      syntaxGraphObserve g who h.lastState.lastState =
        syntaxGraphObserve g who h'.lastState.lastState)
    (hpub :
      syntaxGraphPublicView g h.lastState.lastState =
        syntaxGraphPublicView g h'.lastState.lastState) :
    ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableMoves h who =
      ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableMoves h' who := by
  simpa [GameTheory.FOSG.availableMoves] using
    syntaxGraph_boundedAvailableMovesAtState_eq_of_observation_eq
      g horizon who hcut hcut' hpriv hpub

/-- On nonempty bounded syntax-graph histories before the presentation cutoff,
equality of the latest FOSG private/public observation already determines the
current optional move set. -/
theorem syntaxGraph_availableMoves_eq_of_latestObservation_eq
    (g : WFProgram P L) (horizon : Nat) (who : P)
    {h h' : (((syntaxGraphFOSGView g).toBoundedFOSG horizon).History)}
    (hcut : ¬ horizon ≤ h.lastState.pref.events.length)
    (hcut' : ¬ horizon ≤ h'.lastState.pref.events.length)
    (hne : h.steps ≠ [])
    (hne' : h'.steps ≠ [])
    (hlatest :
      GameTheory.FOSG.InfoState.latestObservation?
          (G := (syntaxGraphFOSGView g).toBoundedFOSG horizon)
          (i := who) (h.playerView who) =
        GameTheory.FOSG.InfoState.latestObservation?
          (G := (syntaxGraphFOSGView g).toBoundedFOSG horizon)
          (i := who) (h'.playerView who)) :
    ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableMoves h who =
      ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableMoves h' who := by
  let G := (syntaxGraphFOSGView g).toBoundedFOSG horizon
  have hlatest₁ :
      GameTheory.FOSG.InfoState.latestObservation?
          (G := G) (i := who) (h.playerView who) =
        some
          (syntaxGraphObserve g who h.lastState.lastState,
            syntaxGraphPublicView g h.lastState.lastState) := by
    simpa [G, syntaxGraphMachine, ProtocolGraph.toMachine,
      syntaxGraphMachineInterface] using
      (syntaxGraphFOSGView g)
        |>.toBoundedFOSG_latestObservation?_history_of_ne_nil
          horizon who h hne
  have hlatest₂ :
      GameTheory.FOSG.InfoState.latestObservation?
          (G := G) (i := who) (h'.playerView who) =
        some
          (syntaxGraphObserve g who h'.lastState.lastState,
            syntaxGraphPublicView g h'.lastState.lastState) := by
    simpa [G, syntaxGraphMachine, ProtocolGraph.toMachine,
      syntaxGraphMachineInterface] using
      (syntaxGraphFOSGView g)
        |>.toBoundedFOSG_latestObservation?_history_of_ne_nil
          horizon who h' hne'
  have hlatestG :
      GameTheory.FOSG.InfoState.latestObservation?
          (G := G) (i := who) (h.playerView who) =
        GameTheory.FOSG.InfoState.latestObservation?
          (G := G) (i := who) (h'.playerView who) := by
    simpa [G] using hlatest
  rw [hlatest₁, hlatest₂] at hlatestG
  injection hlatestG with hobs
  have hpriv :
      syntaxGraphObserve g who h.lastState.lastState =
        syntaxGraphObserve g who h'.lastState.lastState :=
    congrArg Prod.fst hobs
  have hpub :
      syntaxGraphPublicView g h.lastState.lastState =
        syntaxGraphPublicView g h'.lastState.lastState :=
    congrArg Prod.snd hobs
  exact
    syntaxGraph_availableMoves_eq_of_currentObservation_eq
      g horizon who hcut hcut' hpriv hpub

end Vegas
