import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem T333 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsBipartite) :
    2 * (G.edgeFinset.card : ℤ) ≥ 3 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) + 3 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    have hw := not_bipartite_chi_int G hp1
    try push_cast at hw
    linarith [hw]
  have s2 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s3 : (G.minDegree : ℤ) ≥ 0 := by positivity
  have s4 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    try push_cast at hw
    linarith [hw]
  have s5 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s4, s1]
  have s6 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s5]) (by linarith [s3])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s7 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 3 := by linarith [s1, s2, s6]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s7, heq_gallai]
