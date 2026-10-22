import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C314 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsAcyclic) (hn1 : (Fintype.card V : ℤ) ≥ 5) :
    (G.cliqueNum : ℤ) ≤ 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + 1 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
    have hw := omega_le_chi_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
    have hw := max_le_edges_int G
    try push_cast at hw
    linarith [hw]
  have s3 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
    have hw := acyclic_chi_int G hp1
    try push_cast at hw
    linarith [hw]
  have s4 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
    have hw := omega_le_maxdeg_add_one_int G
    try push_cast at hw
    linarith [hw]
  have s5 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s6 : (G.minDegree : ℤ) ≥ 0 := by positivity
  have s7 : (Fintype.card V : ℤ) ≥ 5 := by linarith [hn1]
  have s8 : -5 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 5) * ((G.minDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s7]) (by linarith [s6])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s9 : 10 * (G.edgeFinset.card : ℤ) - 15 * (G.minDegree : ℤ) - 5 * (G.cliqueNum : ℤ) ≥ -6 := by linarith [s1, s2, s3, s4, s5, s8]
  have s10 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by have hr := s9; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s10, heq_gallai]
