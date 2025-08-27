import SigFigs.Interval.Field
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic

--TODO:
-- Simplifying lemmas for
--  abs
--  Real.sin, Real.cos, Real.tan

--Defining rpow
-- Simplifying when power is `pure`
-- Simplifying when base is `pure`
-- Simplifying when power is strictly positive
-- Simplifying when base is nonnegative
--Make sure these happen _after_ appropriate NatCast/IntCast handling in the power

namespace ℝRange

variable (r : ℝRange) {x y : ℝ} (hxy : x ≤ y)

theorem map_sqrt : map Real.sqrt r = ⟨⟨r.fst.sqrt, r.snd.sqrt⟩, Real.sqrt_monotone r.2⟩ := by
  simp [Real.sqrt_monotone]

@[simp]
theorem map_sqrt_mk : map Real.sqrt ⟨⟨x, y⟩, hxy⟩ = ⟨⟨x.sqrt, y.sqrt⟩, Real.sqrt_monotone hxy⟩ :=
  map_sqrt _

@[simp]
theorem map_sqrt_toProd : (map Real.sqrt r).toProd = ⟨r.fst.sqrt, r.snd.sqrt⟩ :=
  congrArg NonemptyInterval.toProd (map_sqrt _)

theorem map_exp : map Real.exp r = ⟨⟨r.fst.exp, r.snd.exp⟩, Real.exp_monotone r.2⟩ := by
  simp [Real.exp_monotone]

@[simp]
theorem map_exp_mk : map Real.exp ⟨⟨x, y⟩, hxy⟩ = ⟨⟨x.exp, y.exp⟩, Real.exp_monotone hxy⟩ :=
  map_exp _

@[simp]
theorem map_exp_toProd : (map Real.exp r).toProd = ⟨r.fst.exp, r.snd.exp⟩ :=
  congrArg NonemptyInterval.toProd (map_exp _)

theorem map_log_pos {r} (hr : 0 < r.fst) : map Real.log r = ⟨⟨r.fst.log, r.snd.log⟩,
      Real.strictMonoOn_log.monotoneOn hr (lt_of_lt_of_le hr r.2) r.2⟩ := by
  rw [map_monotoneOn]
  · congr
  · apply Real.strictMonoOn_log.monotoneOn.mono
    intro x hx
    exact lt_of_lt_of_le hr hx.1

@[simp]
theorem map_log_mk_pos (hx : 0 < x) : map Real.log ⟨⟨x, y⟩, hxy⟩ =
    ⟨⟨x.log, y.log⟩, Real.strictMonoOn_log.monotoneOn hx (lt_of_lt_of_le hx hxy) hxy⟩ :=
  map_log_pos hx

@[simp]
theorem map_log_toProd {r} (hr : 0 < r.fst) :
    (map Real.log r).toProd = ⟨r.fst.log, r.snd.log⟩ :=
  congrArg NonemptyInterval.toProd (map_log_pos hr)

end ℝRange
