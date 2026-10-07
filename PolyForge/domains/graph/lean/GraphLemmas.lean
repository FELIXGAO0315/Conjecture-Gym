/-
PolyForge — graph domain Lean library.

This file is the graph analogue of HexLemmas.lean: a small, self-proved lemma
base built on top of Mathlib's graph theory, used to verify that the graph Lean
project (recent Mathlib, pinned to v4.34.0) is wired up and usable.

For now it contains a single self-proved sanity lemma; later versions grow the
graph Inventory here.  No `sorry`, no axioms.
-/
import Mathlib

open Finset

namespace PolyForge.Graph

variable {V : Type*} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]

/-- The maximum degree of a finite simple graph is at most its number of edges.
Immediate from Mathlib's `SimpleGraph.degree_le_card_edgeFinset` (every vertex
degree is at most the edge count) together with
`SimpleGraph.maxDegree_le_of_forall_degree_le`. -/
theorem maxDegree_le_card_edgeFinset :
    G.maxDegree ≤ G.edgeFinset.card :=
  G.maxDegree_le_of_forall_degree_le _ (fun v => G.degree_le_card_edgeFinset v)

end PolyForge.Graph
