import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C213 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.maxDegree : ℤ) ≤ 2 * (G.chromaticNumber.toNat : ℤ)) (hn2 : (G.indepNum : ℤ) ≥ 4) :
    (Fintype.card V : ℤ) ≥ (G.maxDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) + 3 := by
  have s1 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.indepNum : ℤ) ≥ 4 := by linarith [hn2]
  have s3 : (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by positivity
  have s4 : -(G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s5 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s6 : 2 * (Fintype.card V : ℤ) - 2 * (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 5 := by linarith [s1, s2, s3, s4, s5]
  have s7 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hr := s6; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s7, heq_gallai]
