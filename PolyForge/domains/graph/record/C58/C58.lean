import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C58 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hn1 : (G.diam : ℤ) ≥ 3) :
    (G.radius.toNat : ℤ) ≥ 2 := by
  have s1 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := diam_le_two_radius_int G (isTree_connected G hp1)
    try push_cast at hw
    linarith [hw]
  have s2 : (G.diam : ℤ) ≥ 3 := by linarith [hn1]
  have s3 : 2 * (G.radius.toNat : ℤ) ≥ 3 := by linarith [s1, s2]
  have s4 : (G.radius.toNat : ℤ) ≥ 2 := by have hr := s3; omega
  have heq_gallai := gallai_int G
  have heq_tree := tree_edges_int G hp1
  try push_cast at heq_gallai heq_tree
  linarith [s4, heq_gallai, heq_tree]
