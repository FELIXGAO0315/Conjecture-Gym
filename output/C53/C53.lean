import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C53 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.maxDegree : ℤ) ≥ 2 * (G.minDegree : ℤ)) (hn2 : (Fintype.card V : ℤ) ≥ 2) :
    (Fintype.card V : ℤ) ≥ (G.minDegree : ℤ) + 2 := by
  have s1 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) ≥ 2 := by linarith [hn2]
  have s3 : (G.maxDegree : ℤ) - 2 * (G.minDegree : ℤ) ≥ 0 := by linarith [hn1]
  have s4 : 2 * (Fintype.card V : ℤ) - 2 * (G.minDegree : ℤ) ≥ 3 := by linarith [s1, s2, s3]
  have s5 : (Fintype.card V : ℤ) - (G.minDegree : ℤ) ≥ 2 := by have hr := s4; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s5, heq_gallai]
