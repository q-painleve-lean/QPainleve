# CI cache transport

Main CI, PR/merge-group builds and full lint restore one GitHub Actions cache
archive containing QPainleve's standard Lake output records and compressed `.ltar`
artifacts. `services.cache.ci_bundle = true` preserves the PR setting when Tools
regenerates the wrapper. The customized main/full-lint workflows use the same
pinned restore action.

Only successful main builds save this cache; candidate builds only read it.
Keys include OS, architecture, Lean toolchain and the publishing revision.
Prefix restoration supplies older artifacts; Lake's input hashes determine
which are reusable. Changed or missing modules compile locally. There is no
fallback to per-module downloads or revision-history searches.
This is one archive transfer, not a promise of one HTTP request to GitHub.

The transport helper rejects unsafe paths, mismatched toolchains and corrupted
files before installing records. The archive is limited to 64 MiB. A separate
job retains eight generations (at most 512 MiB, plus one transient generation).
Saving is skipped when the repository's measured total plus the new archive
would exceed 8 GiB. This is an operational bound, not an account-wide billing
cap; other workflows and repositories have their own usage.

CI makes no requests to a project cache server for restoration. Mathlib and
TauCeti continue using their independently operated upstream caches. QPainleve
has no public R2 reader (Mei's `infra/mei-cache-reader` was not ported); add one
only if host workers need QPainleve artifacts they cannot build quickly.

Validation requires both a cold main run that saves the bundle and a subsequent
run that reports a GitHub cache hit and Lake unpacking unchanged modules. A
cache miss may take one full compilation. Unit tests alone do not prove CI
integration or account-wide daily request usage.
