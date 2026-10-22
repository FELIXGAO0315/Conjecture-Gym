import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C155 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsBipartite) (hn1 : (G.maxDegree : ℤ) ≤ 4) :
    (G.chromaticNumber.toNat : ℤ) ≤ 3 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) - 2 := by
  have s1 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s3 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
    have hw := bipartite_chi_int G hp1
    try push_cast at hw
    linarith [hw]
  have s4 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hw := handshake_max_int G
    try push_cast at hw
    linarith [hw]
  have s5 : (Fintype.card V : ℤ) ≥ 1 := by
    have hw := card_ge_one_int (V := V)
    try push_cast at hw
    linarith [hw]
  have s6 : -(G.maxDegree : ℤ) ≥ -4 := by linarith [hn1]
  have s7 : 4 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 4 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (4 - (G.maxDegree : ℤ)) :=
      mul_nonneg (by linarith [s5]) (by linarith [s6])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s8 : 6 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) - 2 * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by linarith [s1, s2, s3, s4, s7]
  have s9 : 3 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hr := s8; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s9, heq_gallai]
