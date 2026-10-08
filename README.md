<p align="center"><img src="logo.png" alt="Tengoku" width="200"></p>
<h1 align="center">Tengoku (天国)</h1>
<p align="center"><em>An AI-first formal mathematics library for Lean 4 agentic theorem provers.</em></p>
<p align="center">
<a href="lean-toolchain"><img src="https://img.shields.io/badge/dynamic/regex?url=https%3A%2F%2Fraw.githubusercontent.com%2Fcompetemath%2Ftengoku%2Fmain%2Flean-toolchain&search=v%5B0-9.%5D%2B%28-rc%5B0-9%5D%2B%29%3F&label=Lean%204&color=blue" alt="Lean 4 toolchain"></a>
<a href="https://competemath.com/tengoku"><img src="https://img.shields.io/badge/dynamic/json?url=https%3A%2F%2Fraw.githubusercontent.com%2Fcompetemath%2Ftengoku%2Fmain%2Fdata%2Fstats.json&query=%24.totals.trusted&label=trusted%20theorems&color=2e7d32" alt="Trusted theorems"></a>
</p>

## About
Formal mathematics is mathematics a computer can check, step by step. It is scattered across hundreds of separate
projects, written for different versions of the language, Lean. Tengoku brings them together in one verified library
on one version, so that agentic theorem provers can use all of it at once.

Tengoku aims to provide continuously improving, reliable context for automated theorem provers. By reliable, we mean
that our systems are designed to be exceptionally cynical of all dependencies, even the Lean 4 kernel and elaboration
ecosystem. [How we do that](docs/reliability.md).

## Try it
[Leak](https://competemath.com/about/leak) is the intended interface to Tengoku.

- **Add the MCP tool to your agent** (free, no sign-up):
  `claude mcp add --transport sse tengoku-search https://barkingtree-leak-i.hf.space/sse`
- **Search it on the web:** [competemath.com/tengoku](https://competemath.com/tengoku), in plain English or by name.
- **Run your own:** the [service code](https://github.com/mikael-bashir/leak-services).
- **HTTP API:** [docs/api.md](docs/api.md).
- **Download it:** clone this repository and run `scripts/cache.sh get` to download the compiled library.

## Contributors
Anyone can contribute, by hand or with AI. Every theorem keeps its author's credit: put a docstring above it with one
line starting `Author:` that names you, and any AI you used. [How credit works](docs/credit.md) ·
[Contributing](CONTRIBUTING.md) · [How a theorem gets in](docs/how-a-pr-flows.md) · [What we would like next](GOALS.md)

Found a bug, or have an idea? [Open an issue](https://github.com/competemath/tengoku/issues/new). Security problems go
through [SECURITY.md](SECURITY.md), never a public issue.

## Learn more
- [How Tengoku stays reliable](docs/reliability.md)
- [What Tengoku guarantees](docs/why-tengoku.md)
- [The full manual](https://competemath.com/about/tengoku)
- [Security and licence compliance](docs/openchain/README.md) (OpenChain ISO/IEC 18974 and 5230)
- [Acknowledgements](docs/acknowledgements.md): the projects and people Tengoku stands on
- Cite it: [10.5281/zenodo.23050400](https://doi.org/10.5281/zenodo.23050400), or the *Cite this repository* button

## Dedication

This project is founded for the sake of God (فِي سَبِيلِ ٱللَّٰهِ) - the prophet PBUH said:

> "Whoever takes a path in which he seeks knowledge, Allah will make easy for him, by it, a path to Paradise."
>
> «ومن سلك طريقا يلتمس فيه علما سهل الله له به طريقا إلى الجنة»
>
> — Ṣaḥīḥ Muslim, no. 2699 (narrated by Abū Hurayrah), Kitāb al-Dhikr wa-l-Duʿāʾ. Manuscript copy of 1164 CE: [Princeton University Library, Garrett MS 104Y, fol. 167a](https://dpul.princeton.edu/islamicmss/catalog/cr56n359w), [exact page](https://iiif-cloud.princeton.edu/iiif/2/4b%2F29%2F26%2F4b2926c452bf475ba690d038a6577e8b%2Fintermediate_file/full/full/0/default.jpg).

## Thanks
Tengoku stands on Lean, Mathlib and the authors of every library in it. Thank you.

<a href="https://snyk.io"><img src="https://cdn.simpleicons.org/snyk" height="18" alt="Snyk"></a>&nbsp;**Security, with [Snyk](https://snyk.io).** Tengoku is a proud member of Snyk's [Secure Developer Program](https://snyk.io/open-source/), which equips open-source maintainers with its developer-security platform.

## Funding and affiliation

Tengoku is one of the services of [CompeteMath](https://competemath.com). CompeteMath has no intention of generating income with any of its projects. CompeteMath is not affiliated with Lean, Mathlib or the authors of the libraries in Tengoku; their names credit their work and imply no endorsement.

## Badges

<p align="center">
<a href="https://doi.org/10.5281/zenodo.23050400"><img src="https://zenodo.org/badge/DOI/10.5281/zenodo.23050400.svg" alt="DOI"></a>
<a href="https://scorecard.dev/viewer/?uri=github.com/competemath/tengoku"><img src="https://api.scorecard.dev/projects/github.com/competemath/tengoku/badge" alt="OpenSSF Scorecard"></a>
<a href="https://www.bestpractices.dev/projects/15102"><img src="https://www.bestpractices.dev/projects/15102/badge" alt="OpenSSF Best Practices"></a>
<a href="LICENSE"><img src="https://img.shields.io/badge/licence-Apache--2.0-blue" alt="Licence: Apache-2.0"></a>
<a href="https://app.fossa.com/projects/git%2Bgithub.com%2Fcompetemath%2Ftengoku?ref=badge_small"><img src="https://app.fossa.com/api/projects/git%2Bgithub.com%2Fcompetemath%2Ftengoku.svg?type=small" alt="FOSSA Status"></a>
<a href="https://sonarcloud.io/summary/new_code?id=competemath_tengoku"><img src="https://sonarcloud.io/api/project_badges/measure?project=competemath_tengoku&amp;metric=alert_status" alt="SonarQube Cloud quality gate"></a>
<a href="https://codecov.io/gh/competemath/tengoku"><img src="https://codecov.io/gh/competemath/tengoku/graph/badge.svg" alt="Codecov"></a>
</p>
