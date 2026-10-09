import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C56 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hn1 : (G.diam : ℤ) ≥ 1) (hn2 : -2 * (G.edgeFinset.card : ℤ) + (G.chromaticNumber.toNat : ℤ) ≤ 0) :
    (G.chromaticNumber.toNat : ℤ) ≤ 2 * (G.edgeFinset.card : ℤ) + 2 * (G.radius.toNat : ℤ) - 2 := by
  have s1 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := diam_le_two_radius_int G hp1
    linarith [hw]
  have s2 : (G.diam : ℤ) ≥ 1 := by linarith [hn1]
  have s3 : 2 * (G.radius.toNat : ℤ) ≥ 1 := by linarith [s1, s2]
  have s4 : (G.radius.toNat : ℤ) ≥ 1 := by have hr := s3; omega
  have s5 : 2 * (G.edgeFinset.card : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn2]
  have s6 : 2 * (G.edgeFinset.card : ℤ) - (G.chromaticNumber.toNat : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 2 := by linarith [s4, s5]
  linarith [s6]
