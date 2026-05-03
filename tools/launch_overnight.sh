#!/bin/bash
# Overnight launch: 2 parallel layer-0 leaf dispatches, nohup'd.
# Each runs Opus 4.7 with curated Mathlib hints, max-turns 200, 4h wall cap.

set -u
cd "$(dirname "$0")/.."

mkdir -p runs/logs runs/dispatcher_logs

# --- lem:gaussian-quadratic (Fresnel) ---
nohup python3 tools/dispatcher.py \
  --blueprint blueprint/src/davis_l0_quadratic.tex \
  --lake-root "$(pwd)" \
  --lea-root /home/chinmay-gcp/lea-prover \
  --tracker runs/davis_l0_quadratic_tracker.json \
  --target-module LeaHadamard.Hadamard \
  --model claude-opus-4-7 \
  --max-turns 200 \
  --hints "integral_gaussian_complex,integral_gaussian,integral_gaussian_sq_complex,continuousAt_gaussian_integral,integral_gaussian_complex_Ioi,integral_pi,Matrix.det_isHermitian,IsHermitian.det_eq_prod_eigenvalues" \
  --limit 1 \
  > runs/dispatcher_logs/quadratic.dispatcher.log 2>&1 &
echo "$! gaussian-quadratic" > runs/dispatcher_logs/pids.txt

# --- lem:inner-core ---
nohup python3 tools/dispatcher.py \
  --blueprint blueprint/src/davis_l0_innercore.tex \
  --lake-root "$(pwd)" \
  --lea-root /home/chinmay-gcp/lea-prover \
  --tracker runs/davis_l0_innercore_tracker.json \
  --target-module LeaHadamard.Hadamard \
  --model claude-opus-4-7 \
  --max-turns 200 \
  --hints "integral_gaussian,integrable_exp_neg_mul_sq,exp_neg_mul_sq_isLittleO_exp_neg,integral_pi,setIntegral_le_integral,integrable_rpow_mul_exp_neg_mul_sq,integral_mono_of_nonneg" \
  --limit 1 \
  > runs/dispatcher_logs/innercore.dispatcher.log 2>&1 &
echo "$! inner-core" >> runs/dispatcher_logs/pids.txt

echo "Launched 2 parallel dispatchers."
echo "PIDs:"
cat runs/dispatcher_logs/pids.txt
echo ""
echo "Live progress (logs stream as Lea works):"
echo "  tail -f runs/logs/lem_gaussian-quadratic.lea.log"
echo "  tail -f runs/logs/lem_inner-core.lea.log"
