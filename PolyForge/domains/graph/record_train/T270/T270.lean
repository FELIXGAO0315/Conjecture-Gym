import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem T270 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.indepNum : ℤ) ≥ (G.vertexCoverNum.toNat : ℤ)) (hn2 : (G.maxDegree : ℤ) ≤ 6) :
    (G.maxDegree : ℤ) ≤ (G.indepNum : ℤ) + 2 := by
  have s1 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.indepNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s3 : -(G.maxDegree : ℤ) ≥ -6 := by linarith [hn2]
  have s4 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s5 : -2 * (G.maxDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ -5 := by linarith [s1, s2, s3, s4]
  have s6 : -(G.maxDegree : ℤ) + (G.indepNum : ℤ) ≥ -2 := by have hr := s5; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s6, heq_gallai]
