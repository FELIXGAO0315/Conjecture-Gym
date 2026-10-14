import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C115 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.minDegree : ℤ) ≥ 3) :
    (G.cliqueNum : ℤ) ≤ (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + 4 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
    have hw := omega_le_chi_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    try push_cast at hw
    linarith [hw]
  have s3 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s4 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    try push_cast at hw
    linarith [hw]
  have s5 : (G.minDegree : ℤ) ≥ 3 := by linarith [hn1]
  have s6 : (G.maxDegree : ℤ) ≥ 3 := by linarith [s4, s5]
  have s7 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s8 : (Fintype.card V : ℤ) ≥ 4 := by linarith [s4, s3, s5]
  have s9 : -3 * (Fintype.card V : ℤ) - 4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -12 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * ((G.minDegree : ℤ) - 3) :=
      mul_nonneg (by linarith [s8]) (by linarith [s5])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s10 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -4 := by linarith [s1, s2, s3, s6, s7, s9]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s10, heq_gallai]
