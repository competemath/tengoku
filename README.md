<p align="center"><img src="logo.png" alt="Tengoku" width="200"></p>
<h1 align="center">Tengoku (天国)</h1>
<p align="center"><em>An AI-first formal mathematics library for Lean 4.</em></p>
<p align="center">
<a href="lean-toolchain"><img src="https://img.shields.io/badge/dynamic/regex?url=https%3A%2F%2Fraw.githubusercontent.com%2Fcompetemath%2Ftengoku%2Fmain%2Flean-toolchain&search=v%5B0-9.%5D%2B%28-rc%5B0-9%5D%2B%29%3F&label=Lean%204&color=blue" alt="Lean 4 toolchain"></a>
<a href="https://competemath.com/tengoku"><img src="https://img.shields.io/badge/dynamic/json?url=https%3A%2F%2Fraw.githubusercontent.com%2Fcompetemath%2Ftengoku%2Fmain%2Fdata%2Fstats.json&query=%24.totals.trusted&label=trusted%20theorems&color=2e7d32" alt="Trusted theorems"></a>
<a href="https://doi.org/10.5281/zenodo.23050400"><img src="https://zenodo.org/badge/DOI/10.5281/zenodo.23050400.svg" alt="DOI"></a>
<a href="https://scorecard.dev/viewer/?uri=github.com/competemath/tengoku"><img src="https://api.scorecard.dev/projects/github.com/competemath/tengoku/badge" alt="OpenSSF Scorecard"></a>
<a href="https://www.bestpractices.dev/projects/15102"><img src="https://www.bestpractices.dev/projects/15102/badge" alt="OpenSSF Best Practices"></a>
<a href="LICENSE"><img src="https://img.shields.io/badge/licence-Apache--2.0-blue" alt="Licence: Apache-2.0"></a>
<a href="https://app.fossa.com/projects/git%2Bgithub.com%2Fcompetemath%2Ftengoku?ref=badge_small"><img src="https://app.fossa.com/api/projects/git%2Bgithub.com%2Fcompetemath%2Ftengoku.svg?type=small" alt="FOSSA Status"></a>
<a href="https://sonarcloud.io/summary/new_code?id=competemath_tengoku"><img src="https://sonarcloud.io/api/project_badges/measure?project=competemath_tengoku&amp;metric=alert_status" alt="SonarQube Cloud quality gate"></a>
<a href="https://codecov.io/gh/competemath/tengoku"><img src="https://codecov.io/gh/competemath/tengoku/graph/badge.svg" alt="Codecov"></a>
</p>

## About
Significant formal math projects are fragmented across hundreds of different sources. We pull them
into one unified, verified tree, under the same toolchain. Tengoku aims to provide continuously improving,
reliable context for automated theorem provers.

## Developers
Tengoku hosts **Leak I**, a free MCP service that lets an LLM or agent query
formal theorems by meaning or by type, here: https://barkingtree-leak-i.hf.space/sse (no auth configurations required).

Search the whole library right now [here](https://competemath.com/tengoku).

Prefer HTTP? Endpoint, input and output shapes: [API](docs/api.md).

Want to host your own infrastructure? The code for those who want to self-serve is
[here](https://github.com/mikael-bashir/leak-services).

## Contributors
Anyone can contribute, by hand or with AI. Before you submit:

- **Verification is automatic.** Leak checks every submission: if it compiles
  cleanly and isn't just a longer route to something the tree already reaches,
  it's in.
- **Credit is permanent, and shared.** Put a docstring above your theorem naming
  the human author, any AI used, and a link to you (GitHub, LinkedIn, ORCID, or
  your [CompeteMath ID](https://competemath.com/whoami)). It stays in the tree.

  ```lean
  /-- The sum of the first `n` odd numbers is `n ^ 2`.

  Author: Ada Lovelace (https://github.com/ada), with Claude Fable 5.1. -/
  theorem sum_range_odd (n : ℕ) : ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by
    ...
  ```

  One sentence on what it says, then one line starting with `Author:`. That word
  is what the checks key on: no pull request can remove or edit the line once it
  is in.
- **Submitting a whole project?** Point the
  [bulk attribution tool](tools/attribute/README.md) at the directory with your
  credit string once; it writes the docstrings for you.
- **Tiers.** Submissions start in `tentative` or `staging` and are promoted to
  `trusted` only once Leak's own toolchain has compiled them from scratch.

## Get it, report a problem, contribute
- **Get it:** clone this repository; `scripts/cache.sh get` downloads the newest compiled tree, so only what changed
  since that cache is built. Each numbered release (`vX.Y.Z`, not the `cache-*` ones) carries the dataset of all
  trusted theorems, also on Zenodo ([DOI 10.5281/zenodo.23050400](https://doi.org/10.5281/zenodo.23050400)).
- **Report a bug or ask for a feature:** [open an issue](https://github.com/competemath/tengoku/issues/new). Security
  problems go through [SECURITY.md](SECURITY.md) instead, never a public issue.
- **Contribute:** [CONTRIBUTING.md](CONTRIBUTING.md); every change is a pull request, discussed in the open.

## How to cite
Cite the version you used. [10.5281/zenodo.23050400](https://doi.org/10.5281/zenodo.23050400) stands for every
version (it resolves to the newest); each release also has its own DOI, on its release page. GitHub's *Cite this
repository* button gives the same reference, from [CITATION.cff](CITATION.cff).

```bibtex
@misc{tengoku,
  author       = {{Tengoku contributors} and Bashir, Mikael},
  title        = {Tengoku: one verified Lean 4 tree of formal mathematics, with provenance},
  publisher    = {Zenodo},
  year         = {2026},
  doi          = {10.5281/zenodo.23050400},
  url          = {https://doi.org/10.5281/zenodo.23050400}
}
```

## Full documentation
- [How a theorem gets into Tengoku](docs/how-a-pr-flows.md): the pull request, step by step.
- [What Tengoku guarantees, and how to use and cite it](docs/why-tengoku.md).
- [Goals](GOALS.md): what people would like the library to have next.

Security issues: see [SECURITY.md](SECURITY.md) (private reporting, never a public issue).

Security and licence-compliance programme (OpenChain ISO/IEC 18974 and 5230): [docs/openchain](docs/openchain/README.md).

This is the quick start. The full manual — merge queue, tiers, toolchain, every
seeded library — is at [competemath.com/about/tengoku](https://competemath.com/about/tengoku).

## Tech

[Lean 4](https://lean-lang.org) · [Mathlib](https://github.com/leanprover-community/mathlib4) · [GitHub](https://github.com/features/actions) · [Claude Code](https://www.anthropic.com/claude-code) · [CodeRabbit](https://www.coderabbit.ai) · [Hugging Face](https://huggingface.co/spaces) · [FastMCP](https://gofastmcp.com) · [Loogle](https://github.com/nomeata/loogle) · [Pantograph](https://github.com/lenianiva/Pantograph) · [lean4export](https://github.com/leanprover/lean4export) · [lean4checker](https://github.com/leanprover/lean4checker) · [nanoda](https://github.com/ammkrn/nanoda_lib) · [Next.js](https://nextjs.org) · [Vercel](https://vercel.com) · [Neon](https://neon.com) · [zizmor](https://github.com/zizmorcore/zizmor) · [Harden-Runner](https://github.com/step-security/harden-runner) · [TruffleHog](https://github.com/trufflesecurity/trufflehog) · [detect-secrets](https://github.com/Yelp/detect-secrets)

Tengoku stands on these projects, and on the authors of every library in it: thank you. How each one shaped
Tengoku, and the full list of the technology, tools and writing behind it (security, infrastructure, design, AI,
review and CI), is in [docs/acknowledgements.md](docs/acknowledgements.md). The mathematics comes from the
libraries listed in [schemas/sources.json](schemas/sources.json) and [LICENSE-THIRD-PARTY.md](LICENSE-THIRD-PARTY.md).
