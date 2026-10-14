import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C57 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.indepNum : ℤ) ≥ 2 * (G.vertexCoverNum.toNat : ℤ)) (hn2 : (G.maxDegree : ℤ) ≤ 4) :
    (G.maxDegree : ℤ) ≤ -2 * (Fintype.card V : ℤ) + 4 * (G.indepNum : ℤ) := by
  have s1 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.indepNum : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s3 : -(G.maxDegree : ℤ) ≥ -4 := by linarith [hn2]
  have s4 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s5 : -3 * (G.maxDegree : ℤ) + 6 * (G.indepNum : ℤ) - 6 * (G.vertexCoverNum.toNat : ℤ) ≥ -2 := by linarith [s1, s2, s3, s4]
  have s6 : -(G.maxDegree : ℤ) + 2 * (G.indepNum : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by have hr := s5; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s6, heq_gallai]
