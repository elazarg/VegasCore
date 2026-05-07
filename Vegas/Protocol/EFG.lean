import GameTheory.Languages.FOSG.Theorems
import Vegas.Protocol.Strategic

/-!
# Extensive-form presentation of checked programs

The native Vegas execution path is event graph -> machine -> FOSG -> kernel
game.  GameTheory also provides a canonical FOSG-to-augmented-EFG bridge. This
file packages that bridge for checked Vegas programs and proves that the EFG
presentation preserves the generated behavioral outcome distribution.

The generated EFG is intentionally not a hand-drawn textbook tree: each FOSG
round is serialized as one EFG decision opportunity per player followed by a
chance transition.
-/

namespace EFG

/-- A tree has `players` sequential decision nodes at the root, followed by a
chance node.

This is a structural predicate for the canonical FOSG-to-EFG bridge. It avoids
committing to the exact generated infoset and continuation terms while still
checking the tree spine, not merely its induced distribution. -/
def GameTree.HasDecisionChainThenChance
    {S : InfoStructure} {Outcome : Type} :
    Nat → GameTree S Outcome → Prop
  | 0, .chance _ _ _ _ => True
  | 0, _ => False
  | n + 1, .decision _ next =>
      ∀ action, HasDecisionChainThenChance n (next action)
  | _ + 1, _ => False

@[simp] theorem GameTree.hasDecisionChainThenChance_chance
    {S : InfoStructure} {Outcome : Type}
    (k : Nat) (μ : PMF (Fin k)) (hk : 0 < k)
    (next : Fin k → GameTree S Outcome) :
    HasDecisionChainThenChance 0 (GameTree.chance k μ hk next) := by
  change True
  trivial

@[simp] theorem GameTree.hasDecisionChainThenChance_decision
    {S : InfoStructure} {Outcome : Type}
    {p : S.Player} (I : S.Infoset p)
    (next : S.Act I → GameTree S Outcome) (n : Nat) :
    HasDecisionChainThenChance (n + 1) (GameTree.decision I next) ↔
      ∀ action, HasDecisionChainThenChance n (next action) := by
  change (∀ action, HasDecisionChainThenChance n (next action)) ↔
    ∀ action, HasDecisionChainThenChance n (next action)
  rfl

end EFG

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Finite private observations for the program event-graph machine. -/
@[reducible] noncomputable instance eventGraphMachine.instFintypeObs
    (g : WFProgram P L) [FiniteDomains g] (who : P) :
    Fintype ((eventGraphMachine g).Obs who) := by
  classical
  letI : Fintype (ProgramField g.prog) :=
    ProgramField.instFintype g.prog
  letI :
      ∀ field : ProgramField g.prog, Fintype (L.Val field.ty) :=
    fun field => ProgramField.instFintypeValue g field
  change Fintype (ProgramPrivateObs g who)
  exact Fintype.ofEquiv
    ((field : ProgramField g.prog) → Option (L.Val field.ty))
    { toFun := fun values => { value? := values }
      invFun := fun obs => obs.value?
      left_inv := by
        intro values
        rfl
      right_inv := by
        intro obs
        cases obs
        rfl }

/-- Decidable equality for private observations of the program event-graph
machine. -/
noncomputable instance eventGraphMachine.instDecidableEqObs
    (g : WFProgram P L) (who : P) :
    DecidableEq ((eventGraphMachine g).Obs who) :=
  Classical.decEq _

/-- Finite public observations for the program event-graph machine. -/
@[reducible] noncomputable instance eventGraphMachine.instFintypePublic
    (g : WFProgram P L) [FiniteDomains g] :
    Fintype (eventGraphMachine g).Public := by
  classical
  letI : Fintype (ProgramNode g.prog) :=
    ProgramNode.instFintype g.prog
  letI : Fintype (ProgramField g.prog) :=
    ProgramField.instFintype g.prog
  letI :
      ∀ field : ProgramField g.prog, Fintype (L.Val field.ty) :=
    fun field => ProgramField.instFintypeValue g field
  change Fintype (ProgramPublicObs g)
  exact Fintype.ofEquiv
    ((ProgramNode g.prog → Bool) ×
      ((field : ProgramField g.prog) → Option (L.Val field.ty)))
    { toFun := fun values => { done := values.1, value? := values.2 }
      invFun := fun obs => (obs.done, obs.value?)
      left_inv := by
        intro values
        cases values
        rfl
      right_inv := by
        intro obs
        cases obs
        rfl }

/-- Decidable equality for public observations of the program event-graph
machine. -/
noncomputable instance eventGraphMachine.instDecidableEqPublic
    (g : WFProgram P L) :
    DecidableEq (eventGraphMachine g).Public :=
  Classical.decEq _

/-- Decidable equality for event-graph FOSG round actions. -/
noncomputable instance eventGraphFOSGView.instDecidableEqAct
    (g : WFProgram P L) [FiniteDomains g] (who : P) :
    DecidableEq ((eventGraphFOSGView g).Act who) :=
  Classical.decEq _

/-- Bounded event-graph FOSG used by the EFG bridge for a checked program. -/
noncomputable abbrev eventGraphBoundedFOSGAt
    (g : WFProgram P L) :=
  (eventGraphFOSGView g).toBoundedFOSG (syntaxSteps g.prog)

/-- Canonical augmented EFG presentation of a checked Vegas program.

This is obtained by applying the GameTheory FOSG-to-EFG bridge to the bounded
event-graph FOSG at the program's source horizon. -/
noncomputable abbrev eventGraphEFGAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :=
  GameTheory.FOSG.AugmentedEFGBridge.toPlainEFGOfBoundedHorizon
    (G := eventGraphBoundedFOSGAt g)
    ((eventGraphFOSGView g).toBoundedFOSG_boundedHorizon
      (syntaxSteps g.prog))

/-- Translate a generated Vegas behavioral profile to the canonical EFG
behavioral profile. -/
noncomputable def eventGraphEFGBehavioralProfileAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (β : behavioralProfilePMFAt g) :=
  GameTheory.FOSG.AugmentedEFGBridge.translateBehavioralProfile
    (G := eventGraphBoundedFOSGAt g)
    (k := syntaxSteps g.prog)
    β.extend

/-- Project a canonical EFG history outcome back to the public Vegas outcome. -/
noncomputable def eventGraphEFGPublicOutcomeAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    (eventGraphBoundedFOSGAt g).History → Outcome P :=
  fun h => (eventGraphFOSGView g).boundedHistoryOutcome
    (syntaxSteps g.prog) h

/-- Player translation from the canonical EFG's finite player indices back to
the original Vegas players. -/
noncomputable def eventGraphEFGOrigPlayerAt
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] :
    GameTheory.FOSG.AugmentedEFGBridge.PlayerIx (ι := P) → P := by
  classical
  intro p
  exact
    GameTheory.FOSG.AugmentedEFGBridge.origPlayer
      (ι := P)
      p

/-- The root bounded event-graph FOSG history is nonterminal when the source
program has at least one protocol node and the presentation horizon is
positive. -/
theorem eventGraphBoundedFOSGAt_root_not_terminal_of_node
    (g : WFProgram P L) [FiniteDomains g]
    (node : ProgramNode g.prog)
    (hsteps : 0 < syntaxSteps g.prog) :
    ¬ (eventGraphBoundedFOSGAt g).terminal
        (GameTheory.FOSG.AugmentedEFGBridge.SerialExec.root
          (eventGraphBoundedFOSGAt g)).lastState := by
  intro hterminal
  rcases hterminal with hmachine | hcut
  · have hnode : node ∈ (programEventGraph g).nodes := by
      exact ProgramNode.mem_finset g.prog node
    have hdone := hmachine hnode
    simp [eventGraphMachine, EventGraph.toMachine,
      EventGraph.Configuration.done, EventGraph.done,
      EventGraph.Configuration.initial] at hdone
  · simp [GameTheory.FOSG.AugmentedEFGBridge.SerialExec.root] at hcut
    omega

/-- The canonical EFG presentation has the same public outcome distribution as
the generated PMF behavioral kernel game, after translating the profile and
projecting EFG histories to public outcomes.

This is the example-facing "translated to the expected EFG" theorem: the EFG
tree is the canonical serialization of the generated FOSG, and its public
outcome law is exactly the Vegas strategic semantics. -/
theorem eventGraphEFGAt_outcomeKernel_map_publicOutcome
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (β : behavioralProfilePMFAt g) :
    PMF.map (eventGraphEFGPublicOutcomeAt g)
        ((eventGraphEFGAt g).toKernelGame.outcomeKernel
          (eventGraphEFGBehavioralProfileAt g β)) =
      (pmfBehavioralKernelGameAt g).outcomeKernel β := by
  classical
  have hbridge :
      (eventGraphEFGAt g).toKernelGame.outcomeKernel
          (eventGraphEFGBehavioralProfileAt g β) =
        (eventGraphBoundedFOSGAt g).runDist
          (syntaxSteps g.prog) β.extend := by
    simpa [eventGraphEFGAt, eventGraphEFGBehavioralProfileAt,
      eventGraphBoundedFOSGAt] using
      (GameTheory.FOSG.AugmentedEFGBridge.toPlainEFGOfBoundedHorizon_outcomeKernel_eq_runDist
          (G := eventGraphBoundedFOSGAt g)
          ((eventGraphFOSGView g).toBoundedFOSG_boundedHorizon
            (syntaxSteps g.prog))
          β.extend)
  rw [hbridge]
  rfl

end Vegas
