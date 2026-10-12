import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C84 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≤ 2 * (G.chromaticNumber.toNat : ℤ)) (hn2 : (G.minDegree : ℤ) ≥ 2) :
    (Fintype.card V : ℤ) ≤ 3 * (G.chromaticNumber.toNat : ℤ) - 2 := by
  have s1 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s3 : (G.minDegree : ℤ) ≥ 2 := by linarith [hn2]
  have s4 : -(Fintype.card V : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s5 : -2 * (Fintype.card V : ℤ) + 6 * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by linarith [s1, s2, s3, s4]
  have s6 : -(Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hr := s5; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s6, heq_gallai]
