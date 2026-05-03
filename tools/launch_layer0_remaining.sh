#!/bin/bash
# Layer-0 remaining: 7 parallel dispatchers, each on a single-node blueprint.
# Each writes to its own tracker so they don't race.

set -u
cd "$(dirname "$0")/.."

mkdir -p runs/logs runs/dispatcher_logs

# Helper: build a single-node TeX file by extracting one lemma from the
# combined remaining.tex blueprint, then dispatch on it.
extract_one() {
  local label="$1"
  local out="$2"
  awk -v lbl="$label" '
    /^\\begin\{(lemma|theorem|proposition|corollary|definition|fact)\}/ {capture=0; buf=""}
    /\\label\{/ {if (index($0, "{" lbl "}")) capture=1}
    {if (capture) buf = buf $0 "\n"}
    /^\\end\{(lemma|theorem|proposition|corollary|definition|fact)\}/ {if (capture) {print buf; exit}}
  ' blueprint/src/davis_l0_remaining.tex > "$out"
}

dispatch_one() {
  local label="$1"
  local hints="$2"
  local safe=$(echo "$label" | sed 's/[^a-zA-Z0-9]/_/g')
  local bp="blueprint/src/single_${safe}.tex"
  local tracker="runs/single_${safe}_tracker.json"
  echo "% single-node extraction of ${label}" > "$bp"
  echo "\\chapter{${label}}\\label{chap:${safe}}" >> "$bp"
  extract_one "$label" /tmp/${safe}.body
  cat /tmp/${safe}.body >> "$bp"

  echo "  launching $label (hints: $(echo $hints | wc -w | tr -d ' ') terms)"
  nohup python3 tools/dispatcher.py \
    --blueprint "$bp" \
    --lake-root "$(pwd)" \
    --lea-root /home/chinmay-gcp/lea-prover \
    --tracker "$tracker" \
    --target-module LeaHadamard.Hadamard \
    --model claude-opus-4-7 \
    --max-turns 200 \
    --hints "$hints" \
    --limit 1 \
    > "runs/dispatcher_logs/${safe}.dispatcher.log" 2>&1 &
  echo "$! $label" >> runs/dispatcher_logs/pids_remaining.txt
}

> runs/dispatcher_logs/pids_remaining.txt

# 1. lem:gaussian-quadratic (retry, expanded hints from Lea's diagnosis)
dispatch_one "lem:gaussian-quadratic-2" \
  "integral_gaussian_complex,integral_gaussian,integral_gaussian_sq_complex,Matrix.PosDef,IsHermitian,Matrix.det_diagonal,LinearMap.det_pos,Matrix.diagonalize,Matrix.IsHermitian.eigenvalues,Real.sqrt_eq_rpow,Complex.cpow"

# 2. lem:hc
dispatch_one "lem:hc" \
  "MeasureTheory.eLpNorm,MeasureTheory.snorm,MeasureTheory.snorm_le_snorm_of_exponent_le,Polynomial,MeasureTheory.Integrable,MeasureTheory.eLpNorm_lt_top_iff,Real.rpow_le_rpow"

# 3. lem:weak-comparison
dispatch_one "lem:weak-comparison" \
  "MeasureTheory.integral_sub,Real.taylor_mean_remainder,Asymptotics.IsLittleO,ContDiff,Polynomial.derivative,deriv_pow,iteratedDeriv,MeasureTheory.integral_pi"

# 4. lem:triangle
dispatch_one "lem:triangle" \
  "Finset.sum_pow,Finset.sum_mul_sum,Finset.expectation,uniformOn,MeasureTheory.integral_dirac,MeasureTheory.integral_finset_sum,Finset.prod_range_succ"

# 5. fact:psi-sq
dispatch_one "fact:psi-sq" \
  "Complex.abs_sq,Complex.norm_eq_abs,Complex.exp_im,Complex.cos,Real.cos_le_one,Finset.prod_le_prod,Finset.expectation,uniformOn"

# 6. lem:realpart
dispatch_one "lem:realpart" \
  "Real.cos_le_one,Real.one_sub_sq_div_two_le_cos,Real.cos_lt_one,Complex.exp_re,Complex.exp_im,Real.cos_pi_div_three,Real.cos_zero,MeasureTheory.integral_cos"

# 7. fact:fixed-n
dispatch_one "fact:fixed-n" \
  "Asymptotics.IsLittleO,Filter.Tendsto,Real.exp_neg,integral_gaussian,Filter.Tendsto.div,Real.tendsto_exp_atTop,Filter.eventually_atTop"

echo ""
echo "Launched $(wc -l < runs/dispatcher_logs/pids_remaining.txt) parallel dispatchers."
echo ""
echo "Live logs:"
ls runs/logs/lem_*.lea.log runs/logs/fact_*.lea.log 2>/dev/null
echo ""
echo "Stop all early:  pkill -9 -f 'lea --max-turns 200'"
