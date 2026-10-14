import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C238 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsBipartite) (hn1 : (G.maxDegree : ℤ) ≤ 4) :
    (G.maxDegree : ℤ) ≥ -2 * (Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) + 4 := by
  have s1 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hw := handshake_max_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) ≥ 1 := by
    have hw := card_ge_one_int (V := V)
    try push_cast at hw
    linarith [hw]
  have s3 : -(G.maxDegree : ℤ) ≥ -4 := by linarith [hn1]
  have s4 : 4 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 4 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (4 - (G.maxDegree : ℤ)) :=
      mul_nonneg (by linarith [s2]) (by linarith [s3])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s5 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    try push_cast at hw
    linarith [hw]
  have s6 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    have hw := not_bipartite_chi_int G hp1
    try push_cast at hw
    linarith [hw]
  have s7 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s5, s6]
  have s8 : 4 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 12 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (4 - (G.maxDegree : ℤ)) :=
      mul_nonneg (by linarith [s7]) (by linarith [s3])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s9 : 2 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + (G.maxDegree : ℤ) ≥ 4 := by linarith [s1, s4, s8]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s9, heq_gallai]
