import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C87 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsBipartite) (hn1 : (G.maxDegree : ℤ) ≤ 5) :
    (G.edgeFinset.card : ℤ) ≤ 3 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - 8 := by
  have s1 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hw := handshake_max_int G
    try push_cast at hw
    linarith [hw]
  have s3 : -(G.maxDegree : ℤ) ≥ -5 := by linarith [hn1]
  have s4 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    try push_cast at hw
    linarith [hw]
  have s5 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    have hw := not_bipartite_chi_int G hp1
    try push_cast at hw
    linarith [hw]
  have s6 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s4, s5]
  have s7 : 5 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 15 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (5 - (G.maxDegree : ℤ)) :=
      mul_nonneg (by linarith [s6]) (by linarith [s3])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s8 : 3 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + (G.maxDegree : ℤ) ≥ 8 := by linarith [s1, s2, s7]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s8, heq_gallai]
