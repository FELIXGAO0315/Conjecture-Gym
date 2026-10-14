import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C67 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≥ 2 * (G.edgeFinset.card : ℤ)) :
    (Fintype.card V : ℤ) ≥ (G.edgeFinset.card : ℤ) + 1 := by
  have s1 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by positivity
  have s3 : (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) ≥ 0 := by linarith [hn1]
  have s4 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s5 : -2 * (G.edgeFinset.card : ℤ) + 2 * (G.indepNum : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by linarith [s1, s2, s3, s4]
  have s6 : -(G.edgeFinset.card : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by have hr := s5; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s6, heq_gallai]
