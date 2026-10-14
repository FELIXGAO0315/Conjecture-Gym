import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C62 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hn1 : (G.indepNum : ℤ) ≥ 2) :
    (G.diam : ℤ) ≤ (Fintype.card V : ℤ) + (G.radius.toNat : ℤ) - 2 := by
  have s1 : (G.indepNum : ℤ) ≥ 2 := by linarith [hn1]
  have s2 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := diam_le_two_radius_int G (isTree_connected G hp1)
    try push_cast at hw
    linarith [hw]
  have s3 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
    have hw := diam_le_card_sub_one_int G (isTree_connected G hp1)
    try push_cast at hw
    linarith [hw]
  have s4 : (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by positivity
  have s5 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s6 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
    have hw := tree_edges_int G hp1
    try push_cast at hw
    linarith [hw]
  have s7 : 2 * (G.edgeFinset.card : ℤ) - 2 * (G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 1 := by linarith [s1, s2, s3, s4, s5, s6]
  have s8 : (G.edgeFinset.card : ℤ) - (G.diam : ℤ) + (G.radius.toNat : ℤ) ≥ 1 := by have hr := s7; omega
  have heq_gallai := gallai_int G
  have heq_tree := tree_edges_int G hp1
  try push_cast at heq_gallai heq_tree
  linarith [s8, heq_gallai, heq_tree]
