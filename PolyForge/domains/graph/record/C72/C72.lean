import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C72 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.chromaticNumber.toNat : ℤ) ≥ 5) (hn2 : (Fintype.card V : ℤ) ≥ 2 * (G.minDegree : ℤ)) :
    (G.minDegree : ℤ) ≤ (Fintype.card V : ℤ) - 3 := by
  have s1 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 5 := by linarith [hn1]
  have s3 : (Fintype.card V : ℤ) - 2 * (G.minDegree : ℤ) ≥ 0 := by linarith [hn2]
  have s4 : 2 * (Fintype.card V : ℤ) - 2 * (G.minDegree : ℤ) ≥ 5 := by linarith [s1, s2, s3]
  have s5 : (Fintype.card V : ℤ) - (G.minDegree : ℤ) ≥ 3 := by have hr := s4; omega
  linarith [s5]
