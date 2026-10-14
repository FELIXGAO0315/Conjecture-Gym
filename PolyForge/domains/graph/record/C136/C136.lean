import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C136 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.indepNum : ℤ) ≥ 2 * (G.vertexCoverNum.toNat : ℤ)) :
    (Fintype.card V : ℤ) ≤ 2 * (G.indepNum : ℤ) - 1 := by
  have s1 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.indepNum : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s3 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s4 : 2 * (Fintype.card V : ℤ) - 4 * (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by linarith [s1, s2, s3]
  have s5 : (Fintype.card V : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by have hr := s4; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s5, heq_gallai]
