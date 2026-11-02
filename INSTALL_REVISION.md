# Add the 2 November 2026 extension

The extension ZIP contains added and updated files at repository-relative
paths. Extract it **inside the root of your existing repository**; it replaces
the listed documentation and PDFs and adds four Lean modules. It does not
delete your repository or its Git history. The original manuscript is retained.

For GitHub Codespaces, upload `PSPrimes_Revision_Extension_2026-11-02.zip` to
the repository root, then paste this in the Codespaces terminal:

```sh
python3 -m zipfile -e PSPrimes_Revision_Extension_2026-11-02.zip .
git status --short
```

The new main proof is `PSPrimes/LongVariation.lean`. Read
`docs/REVISION_2026_11_02.md` for the exact scope and the two manuscript edits.
The root PDFs are `Compact_Blueprint.pdf` and `Full_Expository_Blueprint.pdf`.

After reviewing the changes, save them to GitHub:

```sh
git add PSPrimes.lean PSPrimes README.md RECOVERY_STATUS.md INSTALL_REVISION.md blueprint docs evidence history manuscript scripts
git add Compact_Blueprint.pdf Full_Expository_Blueprint.pdf
git commit -m "Formalize revised lacunary variation corollary"
git push origin main
```

The ZIP itself is not staged by these commands. Do not paste the surrounding
Markdown fences into the terminal. A normal Linux/macOS Lean installation can
reproduce the checks with `lake exe cache get` and `bash scripts/check.sh`.
The executable-path shim recorded in the evidence is specific to the build
sandbox and is not required on an ordinary computer.

The complete project ZIP is an alternative containing the entire updated
project in a `PSPrimes/` folder. Use one installation route; the extension ZIP
is designed for the existing repository at base commit
`d523ab623a07a1969cae0f6386d08a7e28f09c28`.
