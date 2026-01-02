# Vendored Submodule SHAs

These SHAs are the original gitlink targets from commit 557ef89 (before vendoring).

| Repo | SHA | Upstream |
| --- | --- | --- |
| Bend | d184863f03e796d1d657958a51dd6dd331ade92d | https://github.com/HigherOrderCO/Bend |
| HVM | 654276018084b8f44a22b562dd68ab18583bfb5b | https://github.com/HigherOrderCO/HVM |
| hvm4 | 2b3f16a4bc34baed2182a8299888bd6d21e23273 | https://github.com/HigherOrderCO/hvm4 |

Use these when converting the folders back into submodules later.

## Re-Submodule Recipe (Pinned)

```bash
# from repo root
git rm -r Bend HVM hvm4
git submodule add https://github.com/HigherOrderCO/Bend Bend
git submodule add https://github.com/HigherOrderCO/HVM HVM
git submodule add https://github.com/HigherOrderCO/hvm4 hvm4

(cd Bend && git checkout d184863f03e796d1d657958a51dd6dd331ade92d)
(cd HVM && git checkout 654276018084b8f44a22b562dd68ab18583bfb5b)
(cd hvm4 && git checkout 2b3f16a4bc34baed2182a8299888bd6d21e23273)

git add .gitmodules Bend HVM hvm4
git commit -m "Restore Bend, HVM, and hvm4 as submodules"
```
