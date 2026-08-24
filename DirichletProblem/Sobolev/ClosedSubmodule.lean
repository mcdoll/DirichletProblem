/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Analysis.InnerProductSpace.Orthogonal

public section

variable {𝕜 E F : Type*}
  [RCLike 𝕜]

section NormedSpace

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

instance ClosedSubmodule.normedAddCommGroup (W : ClosedSubmodule 𝕜 E) : NormedAddCommGroup W :=
  fast_instance% W.toSubmodule.normedAddCommGroup

instance ClosedSubmodule.normedSpace (W : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 W :=
  fast_instance% W.toSubmodule.normedSpace

end NormedSpace

section InnerProductspace

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

instance ClosedSubmodule.innerProductSpace (W : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 W :=
  fast_instance% W.toSubmodule.innerProductSpace

end InnerProductspace
