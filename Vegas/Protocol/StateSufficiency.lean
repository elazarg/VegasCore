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
      ∀ node, AgreeOnGuardVisibleReads g left right node) :
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
        (hvisible action.node) hlegal⟩
  · intro haction
    rcases haction with ⟨hfrontier, hactor, hslice, hlegal⟩
    have hfrontierLeft : action.node ∈ left.frontier := by
      simpa [syntaxGraphPublicView_frontier_eq_of_eq g hpub] using hfrontier
    exact ⟨hfrontierLeft, hactor, hslice,
      syntaxGraph_actionLegal_of_guardVisibleValue_eq g hfrontierLeft
        (AgreeOnGuardVisibleReads.symm (hvisible action.node)) hlegal⟩

/-- Current machine observations determine the bounded FOSG optional moves at
the endpoint of two syntax-graph histories, provided neither endpoint is past
the bounded presentation cutoff. -/
theorem syntaxGraph_availableMoves_eq_of_currentObservation_eq
    (g : WFProgram P L) (horizon : Nat) (who : P)
    {h h' : (((syntaxGraphFOSGView g).toBoundedFOSG horizon).History)}
    (hcut : ¬ horizon ≤ h.lastState.depth)
    (hcut' : ¬ horizon ≤ h'.lastState.depth)
    (hpriv :
      syntaxGraphObserve g who h.lastState.state =
        syntaxGraphObserve g who h'.lastState.state)
    (hpub :
      syntaxGraphPublicView g h.lastState.state =
        syntaxGraphPublicView g h'.lastState.state) :
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
    (hcut : ¬ horizon ≤ h.lastState.depth)
    (hcut' : ¬ horizon ≤ h'.lastState.depth)
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
          (syntaxGraphObserve g who h.lastState.state,
            syntaxGraphPublicView g h.lastState.state) := by
    simpa [G, syntaxGraphMachine, ProtocolGraph.toMachine,
      syntaxGraphMachineInterface] using
      (syntaxGraphFOSGView g)
        |>.toBoundedFOSG_latestObservation?_history_of_ne_nil
          horizon who h hne
  have hlatest₂ :
      GameTheory.FOSG.InfoState.latestObservation?
          (G := G) (i := who) (h'.playerView who) =
        some
          (syntaxGraphObserve g who h'.lastState.state,
            syntaxGraphPublicView g h'.lastState.state) := by
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
      syntaxGraphObserve g who h.lastState.state =
        syntaxGraphObserve g who h'.lastState.state :=
    congrArg Prod.fst hobs
  have hpub :
      syntaxGraphPublicView g h.lastState.state =
        syntaxGraphPublicView g h'.lastState.state :=
    congrArg Prod.snd hobs
  exact
    syntaxGraph_availableMoves_eq_of_currentObservation_eq
      g horizon who hcut hcut' hpriv hpub

end Vegas
