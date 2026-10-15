import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C48 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hn1 : (G.cliqueNum : ℤ) ≥ 2) :
    (G.radius.toNat : ℤ) ≥ -3 * (Fintype.card V : ℤ) + 3 * (G.diam : ℤ) + 4 := by
  have s1 : (G.cliqueNum : ℤ) ≥ 2 := by linarith [hn1]
  have s2 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := diam_le_two_radius_int G (isTree_connected G hp1)
    try push_cast at hw
    linarith [hw]
  have s3 : (Fintype.card V : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
    have hw := omega_le_card_int G
    try push_cast at hw
    linarith [hw]
  have s4 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
    have hw := diam_le_card_sub_one_int G (isTree_connected G hp1)
    try push_cast at hw
    linarith [hw]
  have s5 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
    have hw := tree_edges_int G hp1
    try push_cast at hw
    linarith [hw]
  have s6 : 6 * (G.edgeFinset.card : ℤ) - 6 * (G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 1 := by linarith [s1, s2, s3, s4, s5]
  have s7 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.diam : ℤ) + (G.radius.toNat : ℤ) ≥ 1 := by have hr := s6; omega
  have heq_gallai := gallai_int G
  have heq_tree := tree_edges_int G hp1
  try push_cast at heq_gallai heq_tree
  linarith [s7, heq_gallai, heq_tree]
