import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C144 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hn1 : (Fintype.card V : ℤ) ≥ 6) :
    (Fintype.card V : ℤ) ≥ 2 * (G.diam : ℤ) - 3 * (G.radius.toNat : ℤ) + 4 := by
  have s1 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := diam_le_two_radius_int G (isTree_connected G hp1)
    try push_cast at hw
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) ≥ 6 := by linarith [hn1]
  have s3 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
    have hw := diam_le_card_sub_one_int G (isTree_connected G hp1)
    try push_cast at hw
    linarith [hw]
  have s4 : 2 * (Fintype.card V : ℤ) - 4 * (G.diam : ℤ) + 6 * (G.radius.toNat : ℤ) ≥ 7 := by linarith [s1, s2, s3]
  have s5 : (Fintype.card V : ℤ) - 2 * (G.diam : ℤ) + 3 * (G.radius.toNat : ℤ) ≥ 4 := by have hr := s4; omega
  have heq_gallai := gallai_int G
  have heq_tree := tree_edges_int G hp1
  try push_cast at heq_gallai heq_tree
  linarith [s5, heq_gallai, heq_tree]
