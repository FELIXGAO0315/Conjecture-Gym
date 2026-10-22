import Lake
open Lake DSL

package "graphlib" where
  name := "graphlib"

require "leanprover-community" / "mathlib" @ git "v4.34.0"

lean_lib GraphLemmas where
  roots := #[`GraphLemmas]
