import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C207 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hn1 : (G.vertexCoverNum.toNat : ℤ) ≤ 2 * (G.indepNum : ℤ)) :
    (Fintype.card V : ℤ) ≤ (G.edgeFinset.card : ℤ) + 2 * (G.indepNum : ℤ) - 2 := by
  have s1 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
    have hw := tau_le_edges_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.edgeFinset.card : ℤ) ≥ 3 := by
    have hw := three_le_edges_int G hp1
    try push_cast at hw
    linarith [hw]
  have s3 : 2 * (G.indepNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s4 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s5 : 2 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) - 4 * (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by linarith [s1, s2, s3, s4]
  have s6 : (Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by have hr := s5; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s6, heq_gallai]
