import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C44 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsBipartite) (hn1 : (G.cliqueNum : ℤ) ≥ 2) :
    2 * (G.minDegree : ℤ) ≤ 2 * (Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) - 5 := by
  have s1 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    have hw := not_bipartite_chi_int G hp1
    try push_cast at hw
    linarith [hw]
  have s3 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s1, s2]
  have s4 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s5 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    try push_cast at hw
    linarith [hw]
  have s6 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s7 : 2 * (Fintype.card V : ℤ) - 2 * (G.minDegree : ℤ) ≥ 2 := by linarith [s5, s6]
  have s8 : (G.minDegree : ℤ) ≥ 0 := by positivity
  have s9 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s3]) (by linarith [s8])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s10 : 2 * (Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) ≥ 5 := by linarith [s3, s4, s7, s9]
  linarith [s10]
