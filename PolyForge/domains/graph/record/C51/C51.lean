import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C51 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hn1 : (Fintype.card V : ℤ) ≥ 2 * (G.indepNum : ℤ)) :
    (G.indepNum : ℤ) ≤ 2 * (Fintype.card V : ℤ) - 5 := by
  have s1 : (Fintype.card V : ℤ) ≥ 3 := by
    have hw := three_le_card_of_cycle_int G hp1
    try push_cast at hw
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) - 2 * (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
  have s3 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s4 : 2 * (G.indepNum : ℤ) + 4 * (G.vertexCoverNum.toNat : ℤ) ≥ 9 := by linarith [s1, s2, s3]
  have s5 : (G.indepNum : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 5 := by have hr := s4; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s5, heq_gallai]
