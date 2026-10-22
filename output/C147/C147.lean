import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C147 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.indepNum : ℤ) ≥ 2 * (G.vertexCoverNum.toNat : ℤ)) (hn2 : (G.maxDegree : ℤ) ≥ 1) :
    (G.indepNum : ℤ) ≥ 2 := by
  have s1 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.maxDegree : ℤ) ≥ 1 := by linarith [hn2]
  have s3 : (G.indepNum : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s4 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s5 : 3 * (G.indepNum : ℤ) ≥ 4 := by linarith [s1, s2, s3, s4]
  have s6 : (G.indepNum : ℤ) ≥ 2 := by have hr := s5; omega
  have s7 : 3 * (Fintype.card V : ℤ) + 2 * (G.indepNum : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 10 := by linarith [s6, s4]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s7, heq_gallai]
