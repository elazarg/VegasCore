import Vegas.Examples.PrisonersDilemma
import Vegas.Examples.MatchingPennies
import Vegas.Examples.BattleOfTheSexes
import Vegas.Examples.MontyHall
import Vegas.GameBridge.EFG.FromRoundView

/-!
# EFG translation examples

Concrete checks for the canonical FOSG-to-EFG presentation of checked
frontier games. The strategic denotation is the native frontier/FOSG game; the
plain EFG is the serialized presentation used when an extensive-form tree is
needed.
-/

namespace Vegas
namespace Examples

open GameTheory

namespace PrisonersDilemma

open GameTheory
open EFGBridge

theorem plainEFG_player_count :
    plainEFG.inf.n = Fintype.card Player := rfl

/-- The serialized Prisoner's Dilemma EFG starts with two player decision
opportunities and then the bridge chance node for the first frontier round. -/
theorem plainEFG_first_round_shape :
    DecisionSpineThenChance (Fintype.card Player) plainEFG.tree := by
  classical
  letI :=
    ToEventGraph.FrontierGameSemantics.EFGInstances.primitiveStateFintype
      checkedProgram.frontierSemantics
  letI :=
    ToEventGraph.FrontierGameSemantics.EFGInstances.actFintype
      checkedProgram.frontierSemantics
  letI :
      ∀ player,
        DecidableEq
          (checkedProgram.frontierSemantics.behavioral.view.Act player) :=
    fun _ => Classical.decEq _
  letI :=
    ToEventGraph.FrontierGameSemantics.EFGInstances.obsFintype
      checkedProgram.frontierSemantics
  letI :
      ∀ player,
        DecidableEq
          ((ToEventGraph.PrimitiveMachine
            (ToEventGraph.compile checkedProgram.core)).Obs player) :=
    fun _ => Classical.decEq _
  letI :=
    ToEventGraph.FrontierGameSemantics.EFGInstances.publicFintype
      checkedProgram.frontierSemantics
  letI :
      DecidableEq
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile checkedProgram.core)).Public :=
    Classical.decEq _
  change DecisionSpineThenChance (Fintype.card Player)
    (GameTheory.FOSG.AugmentedEFGBridge.Tree.fromHistory
        (G := checkedProgram.frontierSemantics.behavioral.view.toFOSG
          4 (fun _ => 0))
        4 (3 + 1)
        (GameTheory.FOSG.AugmentedEFGBridge.SerialExec.root
          (checkedProgram.frontierSemantics.behavioral.view.toFOSG
            4 (fun _ => 0))))
  apply DecisionSpineThenChance.fromHistory_succ_nonterminal
  intro hterminal
  simp [Machine.RoundView.toFOSG, Machine.RoundView.boundedTerminal,
    Machine.BoundedState.init] at hterminal
  simpa [ToEventGraph.PrimitiveMachine, EventGraph.PrimitiveMachineOf,
    EventGraph.ToMachine.primitiveMachine, EventGraph.Config.initial] using
    hterminal ⟨0, by decide⟩

theorem plainEFG_full_tree_shape :
    FullTreeShape (Fintype.card Player) plainEFG.tree := by
  classical
  letI :=
    ToEventGraph.FrontierGameSemantics.EFGInstances.primitiveStateFintype
      checkedProgram.frontierSemantics
  letI :=
    ToEventGraph.FrontierGameSemantics.EFGInstances.actFintype
      checkedProgram.frontierSemantics
  letI :
      ∀ player,
        DecidableEq
          (checkedProgram.frontierSemantics.behavioral.view.Act player) :=
    fun _ => Classical.decEq _
  letI :=
    ToEventGraph.FrontierGameSemantics.EFGInstances.obsFintype
      checkedProgram.frontierSemantics
  letI :
      ∀ player,
        DecidableEq
          ((ToEventGraph.PrimitiveMachine
            (ToEventGraph.compile checkedProgram.core)).Obs player) :=
    fun _ => Classical.decEq _
  letI :=
    ToEventGraph.FrontierGameSemantics.EFGInstances.publicFintype
      checkedProgram.frontierSemantics
  letI :
      DecidableEq
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile checkedProgram.core)).Public :=
    Classical.decEq _
  change FullTreeShape (Fintype.card Player)
    (GameTheory.FOSG.AugmentedEFGBridge.Tree.fromHistory
        (G := checkedProgram.frontierSemantics.behavioral.view.toFOSG
          4 (fun _ => 0))
        4 4
        (GameTheory.FOSG.AugmentedEFGBridge.SerialExec.root
          (checkedProgram.frontierSemantics.behavioral.view.toFOSG
            4 (fun _ => 0))))
  exact FullTreeShape.fromHistory _ _ _ _

end PrisonersDilemma

namespace MatchingPenniesEFG

open GameTheory
open EFGBridge

theorem plainEFG_player_count :
    matchingPenniesPlainEFG.inf.n = Fintype.card Player := rfl

/-- The serialized Matching Pennies EFG exposes the first simultaneous
frontier round as Alice's and Bob's decision opportunities followed by chance. -/
theorem plainEFG_first_round_shape :
    DecisionSpineThenChance
      (Fintype.card Player) matchingPenniesPlainEFG.tree := by
  classical
  letI :=
    ToEventGraph.FrontierGameSemantics.EFGInstances.primitiveStateFintype
      matchingPenniesChecked.frontierSemantics
  letI :=
    ToEventGraph.FrontierGameSemantics.EFGInstances.actFintype
      matchingPenniesChecked.frontierSemantics
  letI :
      ∀ player,
        DecidableEq
          (matchingPenniesChecked.frontierSemantics.behavioral.view.Act
            player) :=
    fun _ => Classical.decEq _
  letI :=
    ToEventGraph.FrontierGameSemantics.EFGInstances.obsFintype
      matchingPenniesChecked.frontierSemantics
  letI :
      ∀ player,
        DecidableEq
          ((ToEventGraph.PrimitiveMachine
            (ToEventGraph.compile matchingPenniesChecked.core)).Obs
              player) :=
    fun _ => Classical.decEq _
  letI :=
    ToEventGraph.FrontierGameSemantics.EFGInstances.publicFintype
      matchingPenniesChecked.frontierSemantics
  letI :
      DecidableEq
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile matchingPenniesChecked.core)).Public :=
    Classical.decEq _
  change DecisionSpineThenChance (Fintype.card Player)
    (GameTheory.FOSG.AugmentedEFGBridge.Tree.fromHistory
        (G := matchingPenniesChecked.frontierSemantics.behavioral.view.toFOSG
          4 (fun _ => 0))
        4 (3 + 1)
        (GameTheory.FOSG.AugmentedEFGBridge.SerialExec.root
          (matchingPenniesChecked.frontierSemantics.behavioral.view.toFOSG
            4 (fun _ => 0))))
  apply DecisionSpineThenChance.fromHistory_succ_nonterminal
  intro hterminal
  simp [Machine.RoundView.toFOSG, Machine.RoundView.boundedTerminal,
    Machine.BoundedState.init] at hterminal
  simpa [ToEventGraph.PrimitiveMachine, EventGraph.PrimitiveMachineOf,
    EventGraph.ToMachine.primitiveMachine, EventGraph.Config.initial] using
    hterminal ⟨0, by decide⟩

theorem plainEFG_full_tree_shape :
    FullTreeShape
      (Fintype.card Player) matchingPenniesPlainEFG.tree := by
  classical
  letI :=
    ToEventGraph.FrontierGameSemantics.EFGInstances.primitiveStateFintype
      matchingPenniesChecked.frontierSemantics
  letI :=
    ToEventGraph.FrontierGameSemantics.EFGInstances.actFintype
      matchingPenniesChecked.frontierSemantics
  letI :
      ∀ player,
        DecidableEq
          (matchingPenniesChecked.frontierSemantics.behavioral.view.Act
            player) :=
    fun _ => Classical.decEq _
  letI :=
    ToEventGraph.FrontierGameSemantics.EFGInstances.obsFintype
      matchingPenniesChecked.frontierSemantics
  letI :
      ∀ player,
        DecidableEq
          ((ToEventGraph.PrimitiveMachine
            (ToEventGraph.compile matchingPenniesChecked.core)).Obs
              player) :=
    fun _ => Classical.decEq _
  letI :=
    ToEventGraph.FrontierGameSemantics.EFGInstances.publicFintype
      matchingPenniesChecked.frontierSemantics
  letI :
      DecidableEq
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile matchingPenniesChecked.core)).Public :=
    Classical.decEq _
  change FullTreeShape (Fintype.card Player)
    (GameTheory.FOSG.AugmentedEFGBridge.Tree.fromHistory
        (G := matchingPenniesChecked.frontierSemantics.behavioral.view.toFOSG
          4 (fun _ => 0))
        4 4
        (GameTheory.FOSG.AugmentedEFGBridge.SerialExec.root
          (matchingPenniesChecked.frontierSemantics.behavioral.view.toFOSG
            4 (fun _ => 0))))
  exact FullTreeShape.fromHistory _ _ _ _

end MatchingPenniesEFG

namespace BattleOfTheSexes

open GameTheory
open EFGBridge

theorem plainEFG_player_count :
    checkedProgram.frontierPlainEFG.inf.n = Fintype.card Player := rfl

/-- The serialized Battle of the Sexes EFG starts with one decision
opportunity per player and then the bridge chance node. -/
theorem plainEFG_first_round_shape :
    DecisionSpineThenChance
      (Fintype.card Player) checkedProgram.frontierPlainEFG.tree := by
  classical
  letI :=
    ToEventGraph.FrontierGameSemantics.EFGInstances.primitiveStateFintype
      checkedProgram.frontierSemantics
  letI :=
    ToEventGraph.FrontierGameSemantics.EFGInstances.actFintype
      checkedProgram.frontierSemantics
  letI :
      ∀ player,
        DecidableEq
          (checkedProgram.frontierSemantics.behavioral.view.Act player) :=
    fun _ => Classical.decEq _
  letI :=
    ToEventGraph.FrontierGameSemantics.EFGInstances.obsFintype
      checkedProgram.frontierSemantics
  letI :
      ∀ player,
        DecidableEq
          ((ToEventGraph.PrimitiveMachine
            (ToEventGraph.compile checkedProgram.core)).Obs player) :=
    fun _ => Classical.decEq _
  letI :=
    ToEventGraph.FrontierGameSemantics.EFGInstances.publicFintype
      checkedProgram.frontierSemantics
  letI :
      DecidableEq
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile checkedProgram.core)).Public :=
    Classical.decEq _
  change DecisionSpineThenChance (Fintype.card Player)
    (GameTheory.FOSG.AugmentedEFGBridge.Tree.fromHistory
        (G := checkedProgram.frontierSemantics.behavioral.view.toFOSG
          4 (fun _ => 0))
        4 (3 + 1)
        (GameTheory.FOSG.AugmentedEFGBridge.SerialExec.root
          (checkedProgram.frontierSemantics.behavioral.view.toFOSG
            4 (fun _ => 0))))
  apply DecisionSpineThenChance.fromHistory_succ_nonterminal
  intro hterminal
  simp [Machine.RoundView.toFOSG, Machine.RoundView.boundedTerminal,
    Machine.BoundedState.init] at hterminal
  simpa [ToEventGraph.PrimitiveMachine, EventGraph.PrimitiveMachineOf,
    EventGraph.ToMachine.primitiveMachine, EventGraph.Config.initial] using
    hterminal ⟨0, by decide⟩

theorem plainEFG_full_tree_shape :
    FullTreeShape
      (Fintype.card Player) checkedProgram.frontierPlainEFG.tree := by
  classical
  letI :=
    ToEventGraph.FrontierGameSemantics.EFGInstances.primitiveStateFintype
      checkedProgram.frontierSemantics
  letI :=
    ToEventGraph.FrontierGameSemantics.EFGInstances.actFintype
      checkedProgram.frontierSemantics
  letI :
      ∀ player,
        DecidableEq
          (checkedProgram.frontierSemantics.behavioral.view.Act player) :=
    fun _ => Classical.decEq _
  letI :=
    ToEventGraph.FrontierGameSemantics.EFGInstances.obsFintype
      checkedProgram.frontierSemantics
  letI :
      ∀ player,
        DecidableEq
          ((ToEventGraph.PrimitiveMachine
            (ToEventGraph.compile checkedProgram.core)).Obs player) :=
    fun _ => Classical.decEq _
  letI :=
    ToEventGraph.FrontierGameSemantics.EFGInstances.publicFintype
      checkedProgram.frontierSemantics
  letI :
      DecidableEq
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile checkedProgram.core)).Public :=
    Classical.decEq _
  change FullTreeShape (Fintype.card Player)
    (GameTheory.FOSG.AugmentedEFGBridge.Tree.fromHistory
        (G := checkedProgram.frontierSemantics.behavioral.view.toFOSG
          4 (fun _ => 0))
        4 4
        (GameTheory.FOSG.AugmentedEFGBridge.SerialExec.root
          (checkedProgram.frontierSemantics.behavioral.view.toFOSG
            4 (fun _ => 0))))
  exact FullTreeShape.fromHistory _ _ _ _

end BattleOfTheSexes

namespace MontyHall

open GameTheory
open EFGBridge

theorem plainEFG_player_count :
    plainEFG.inf.n = Fintype.card Player := rfl

/-- The serialized Monty Hall EFG also begins with one decision opportunity
per player before chance resolves the first frontier transition. The first
active move support is determined by the frontier legality relation. -/
theorem plainEFG_first_round_shape :
    DecisionSpineThenChance (Fintype.card Player) plainEFG.tree := by
  classical
  letI :=
    ToEventGraph.FrontierGameSemantics.EFGInstances.primitiveStateFintype
      checkedProgram.frontierSemantics
  letI :=
    ToEventGraph.FrontierGameSemantics.EFGInstances.actFintype
      checkedProgram.frontierSemantics
  letI :
      ∀ player,
        DecidableEq
          (checkedProgram.frontierSemantics.behavioral.view.Act player) :=
    fun _ => Classical.decEq _
  letI :=
    ToEventGraph.FrontierGameSemantics.EFGInstances.obsFintype
      checkedProgram.frontierSemantics
  letI :
      ∀ player,
        DecidableEq
          ((ToEventGraph.PrimitiveMachine
            (ToEventGraph.compile checkedProgram.core)).Obs player) :=
    fun _ => Classical.decEq _
  letI :=
    ToEventGraph.FrontierGameSemantics.EFGInstances.publicFintype
      checkedProgram.frontierSemantics
  letI :
      DecidableEq
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile checkedProgram.core)).Public :=
    Classical.decEq _
  change DecisionSpineThenChance (Fintype.card Player)
    (GameTheory.FOSG.AugmentedEFGBridge.Tree.fromHistory
        (G := checkedProgram.frontierSemantics.behavioral.view.toFOSG
          8 (fun _ => 0))
        8 (7 + 1)
        (GameTheory.FOSG.AugmentedEFGBridge.SerialExec.root
          (checkedProgram.frontierSemantics.behavioral.view.toFOSG
            8 (fun _ => 0))))
  apply DecisionSpineThenChance.fromHistory_succ_nonterminal
  intro hterminal
  simp [Machine.RoundView.toFOSG, Machine.RoundView.boundedTerminal,
    Machine.BoundedState.init] at hterminal
  simpa [ToEventGraph.PrimitiveMachine, EventGraph.PrimitiveMachineOf,
    EventGraph.ToMachine.primitiveMachine, EventGraph.Config.initial] using
    hterminal ⟨0, by decide⟩

theorem plainEFG_full_tree_shape :
    FullTreeShape (Fintype.card Player) plainEFG.tree := by
  classical
  letI :=
    ToEventGraph.FrontierGameSemantics.EFGInstances.primitiveStateFintype
      checkedProgram.frontierSemantics
  letI :=
    ToEventGraph.FrontierGameSemantics.EFGInstances.actFintype
      checkedProgram.frontierSemantics
  letI :
      ∀ player,
        DecidableEq
          (checkedProgram.frontierSemantics.behavioral.view.Act player) :=
    fun _ => Classical.decEq _
  letI :=
    ToEventGraph.FrontierGameSemantics.EFGInstances.obsFintype
      checkedProgram.frontierSemantics
  letI :
      ∀ player,
        DecidableEq
          ((ToEventGraph.PrimitiveMachine
            (ToEventGraph.compile checkedProgram.core)).Obs player) :=
    fun _ => Classical.decEq _
  letI :=
    ToEventGraph.FrontierGameSemantics.EFGInstances.publicFintype
      checkedProgram.frontierSemantics
  letI :
      DecidableEq
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile checkedProgram.core)).Public :=
    Classical.decEq _
  change FullTreeShape (Fintype.card Player)
    (GameTheory.FOSG.AugmentedEFGBridge.Tree.fromHistory
        (G := checkedProgram.frontierSemantics.behavioral.view.toFOSG
          8 (fun _ => 0))
        8 8
        (GameTheory.FOSG.AugmentedEFGBridge.SerialExec.root
          (checkedProgram.frontierSemantics.behavioral.view.toFOSG
            8 (fun _ => 0))))
  exact FullTreeShape.fromHistory _ _ _ _

end MontyHall

end Examples
end Vegas
