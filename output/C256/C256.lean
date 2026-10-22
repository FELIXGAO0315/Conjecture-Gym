import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C256 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.indepNum : ℤ) ≤ 2 * (G.vertexCoverNum.toNat : ℤ)) :
    2 * (G.indepNum : ℤ) ≤ 3 * (Fintype.card V : ℤ) - 4 := by
  have s1 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : -(G.indepNum : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s3 : 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by linarith [s1, s2]
  have s4 : (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by have hr := s3; omega
  have s5 : (G.indepNum : ℤ) + 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 4 := by linarith [s1, s4]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s5, heq_gallai]
