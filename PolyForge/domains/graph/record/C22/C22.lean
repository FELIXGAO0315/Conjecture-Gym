import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C22 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.chromaticNumber.toNat : ℤ) ≥ 5) (hn2 : (Fintype.card V : ℤ) - 2 * (G.minDegree : ℤ) ≥ 0) :
    2 * (G.minDegree : ℤ) ≤ 2 * (Fintype.card V : ℤ) + (G.chromaticNumber.toNat : ℤ) - 11 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) ≥ 5 := by linarith [hn1]
  have s2 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    linarith [hw]
  have s3 : (Fintype.card V : ℤ) - 2 * (G.minDegree : ℤ) ≥ 0 := by linarith [hn2]
  have s4 : 2 * (Fintype.card V : ℤ) - 2 * (G.minDegree : ℤ) ≥ 5 := by linarith [s2, s1, s3]
  have s5 : (Fintype.card V : ℤ) - (G.minDegree : ℤ) ≥ 3 := by have hr := s4; omega
  have s6 : 2 * (Fintype.card V : ℤ) - 2 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 11 := by linarith [s1, s5]
  linarith [s6]
