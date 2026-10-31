# Sandbox executable path compatibility

This shim is only for the current execution sandbox. It is not required on an ordinary Linux host with elan.

The sandbox exposes `/proc/self/exe` but not `/proc/<getpid()>/exe`. Lean 4.19.0's official runtime queries the latter, resulting in `failed to locate application`. The C shim redirects only numeric `/proc/*/exe` `readlink` requests to `/proc/self/exe`. It does not change the Lean binary, kernel, imported declarations, or proof checking.

Build with:

```sh
gcc -shared -fPIC -O2 -o proc_exe_compat.so proc_exe_compat.c -ldl
```

Then set `LD_PRELOAD` to the absolute path of the resulting `.so` while running the unmodified official Lean and Lake binaries. See `evidence/ENVIRONMENT.txt` for actual commands and outcomes. Do not commit the compiled `.so`.
