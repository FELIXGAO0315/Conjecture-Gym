import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C220 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.chromaticNumber.toNat : ℤ) ≥ 2 * (G.maxDegree : ℤ)) :
    (G.edgeFinset.card : ℤ) ≥ 2 * (G.maxDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) + 1 := by
  have s1 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
    have hw := max_le_edges_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
    have hw := chi_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s3 : -2 * (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s4 : 2 * (G.edgeFinset.card : ℤ) - 4 * (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by linarith [s1, s2, s3]
  have s5 : (G.edgeFinset.card : ℤ) - 2 * (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 1 := by have hr := s4; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s5, heq_gallai]
