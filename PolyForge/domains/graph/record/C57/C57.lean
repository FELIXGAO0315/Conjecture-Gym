import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C57 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.cliqueNum : ℤ) ≤ 2 * (G.maxDegree : ℤ)) :
    (G.maxDegree : ℤ) ≥ 1 := by
  have s1 : (G.cliqueNum : ℤ) ≥ 1 := by
    have hw := omega_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : 2 * (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
  have s3 : 2 * (G.maxDegree : ℤ) ≥ 1 := by linarith [s1, s2]
  have s4 : (G.maxDegree : ℤ) ≥ 1 := by have hr := s3; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s4, heq_gallai]
