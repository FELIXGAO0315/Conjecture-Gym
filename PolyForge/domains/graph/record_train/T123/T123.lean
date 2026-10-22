import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem T123 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsBipartite) (hn1 : (G.maxDegree : ℤ) ≥ 2 * (G.minDegree : ℤ)) :
    (G.edgeFinset.card : ℤ) ≥ 3 * (G.minDegree : ℤ) - (G.indepNum : ℤ) + 1 := by
  have s1 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
    have hw := max_le_edges_int G
    try push_cast at hw
    linarith [hw]
  have s3 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
    have hw := bipartite_chi_int G hp1
    try push_cast at hw
    linarith [hw]
  have s4 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := card_le_alpha_chi_int G
    try push_cast at hw
    linarith [hw]
  have s5 : (G.maxDegree : ℤ) - 2 * (G.minDegree : ℤ) ≥ 0 := by linarith [hn1]
  have s6 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s7 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
    have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
      mul_nonneg (by linarith [s6]) (by linarith [s3])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s8 : 2 * (G.edgeFinset.card : ℤ) - 6 * (G.minDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ 1 := by linarith [s1, s2, s3, s4, s5, s7]
  have s9 : (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + (G.indepNum : ℤ) ≥ 1 := by have hr := s8; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s9, heq_gallai]
