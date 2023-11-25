import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Data.Finset.Basic

import Rubin.Support

namespace Rubin

def OrbitClosure {G α : Type _} [Group G] [MulAction G α] (U : Set α) :=
  { g : G | Support α g ⊆ U}

end Rubin
