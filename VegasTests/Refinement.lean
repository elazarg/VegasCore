import Vegas.Examples.Refinement

/-!
# Refinement test imports

This module keeps the refinement smoke examples in the default test target.
-/

namespace VegasTests

example :
    Vegas.Examples.Refinement.matchingPenniesIdentity.projectState
        Vegas.Examples.Refinement.matchingPenniesMachine.init =
      Vegas.Examples.Refinement.matchingPenniesMachine.init := by
  rfl

end VegasTests
