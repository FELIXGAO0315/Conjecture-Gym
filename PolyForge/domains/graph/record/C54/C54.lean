import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C54 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.maxDegree : ℤ) ≥ (G.cliqueNum : ℤ)) (hn2 : (G.indepNum : ℤ) ≤ 2 * (G.vertexCoverNum.toNat : ℤ)) :
    (G.cliqueNum : ℤ) ≤ 3 * (Fintype.card V : ℤ) - 2 * (G.indepNum : ℤ) - 3 := by
  have s1 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.cliqueNum : ℤ) ≥ 1 := by
    have hw := omega_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s3 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
  have s4 : -(G.indepNum : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn2]
  have s5 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s6 : -3 * (G.cliqueNum : ℤ) + 3 * (G.indepNum : ℤ) + 9 * (G.vertexCoverNum.toNat : ℤ) ≥ 7 := by linarith [s1, s2, s3, s4, s5]
  have s7 : -(G.cliqueNum : ℤ) + (G.indepNum : ℤ) + 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by have hr := s6; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s7, heq_gallai]
