import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C56 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.edgeFinset.card : ℤ) ≥ 5) (hn2 : (G.maxDegree : ℤ) ≤ 2 * (G.cliqueNum : ℤ)) :
    (G.edgeFinset.card : ℤ) ≥ (G.maxDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) + 3 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
    have hw := omega_le_chi_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
    have hw := max_le_edges_int G
    try push_cast at hw
    linarith [hw]
  have s3 : (G.edgeFinset.card : ℤ) ≥ 5 := by linarith [hn1]
  have s4 : -(G.maxDegree : ℤ) + 2 * (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn2]
  have s5 : 2 * (G.edgeFinset.card : ℤ) - 2 * (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 5 := by linarith [s1, s2, s3, s4]
  have s6 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hr := s5; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s6, heq_gallai]
