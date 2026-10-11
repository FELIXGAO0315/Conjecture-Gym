import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C61 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsBipartite) (hn1 : (G.maxDegree : ℤ) ≤ 4) :
    (G.edgeFinset.card : ℤ) ≤ 3 * (Fintype.card V : ℤ) - 5 := by
  have s1 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hw := handshake_max_int G
    try push_cast at hw
    linarith [hw]
  have s3 : (Fintype.card V : ℤ) ≥ 1 := by
    have hw := card_ge_one_int (V := V)
    try push_cast at hw
    linarith [hw]
  have s4 : -(G.maxDegree : ℤ) ≥ -4 := by linarith [hn1]
  have s5 : 4 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 4 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (4 - (G.maxDegree : ℤ)) :=
      mul_nonneg (by linarith [s3]) (by linarith [s4])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s6 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    try push_cast at hw
    linarith [hw]
  have s7 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    have hw := not_bipartite_chi_int G hp1
    try push_cast at hw
    linarith [hw]
  have s8 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s6, s7]
  have s9 : 4 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 12 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (4 - (G.maxDegree : ℤ)) :=
      mul_nonneg (by linarith [s8]) (by linarith [s4])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s10 : 3 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) ≥ 5 := by linarith [s1, s2, s5, s9]
  linarith [s10]
