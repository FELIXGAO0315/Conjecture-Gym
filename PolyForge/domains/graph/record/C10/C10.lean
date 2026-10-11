import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C10 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : 2 ≤ Fintype.card V) (hn1 : (G.minDegree : ℤ) ≤ 1) (hn2 : (G.chromaticNumber.toNat : ℤ) ≤ 2 * (G.maxDegree : ℤ)) :
    (G.maxDegree : ℤ) ≤ 3 * (Fintype.card V : ℤ) - 5 := by
  have s1 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
    have hw := chi_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s3 : 2 * (G.maxDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn2]
  have s4 : 2 * (G.maxDegree : ℤ) ≥ 1 := by linarith [s2, s3]
  have s5 : (G.maxDegree : ℤ) ≥ 1 := by have hr := s4; omega
  have s6 : 3 * (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 5 := by linarith [s1, s5]
  linarith [s6]
