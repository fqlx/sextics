from pathlib import Path
import subprocess, sys
root=Path(__file__).resolve().parent
checks=['audit_relative_first_variation', 'audit_complete_mixed_flint', 'audit_full_first_transport', 'audit_second_radials', 'audit_second_residual_currents', 'audit_full_second_transport', 'audit_generic_first_certificate']
for check in checks:
    print(f"\n== {check} ==", flush=True)
    subprocess.run([sys.executable, str(root / (check + ".py"))], check=True)
print("\nAll exact checkpoint checks passed.")
