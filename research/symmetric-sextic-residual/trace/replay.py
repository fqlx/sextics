from pathlib import Path
import subprocess, sys
root=Path(__file__).resolve().parent
checks=['raw73_units_seed.py', 'audit_cauchy_first_integral.py', 'audit_cauchy_source_matched.py', 'audit_cauchy_Efree.py', 'audit_cauchy_Efree_t5.py', 'cauchy_remove_E_exact.py']
for check in checks:
    print(f"\n== {check} ==", flush=True)
    subprocess.run([sys.executable, str(root / check)], check=True)
print("\nAll trace checkpoint checks passed.")
