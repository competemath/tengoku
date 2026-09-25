<p align="center"><img src="logo.png" alt="Tengoku" width="200"></p>
<h1 align="center">Tengoku (天国)</h1>
<p align="center"><em>An AI-first formal mathematics library for Lean 4.</em></p>

## About
Formal math projects are fragmented across hundreds of different sources. We pull them
into one unified, verified tree, under up-to-date toolchains tracked by Tengoku. Our aim is to provide continuously improving,
reliable context for automated theorem provers.

Tengoku is in its early stages. Now, the focus is translating as much current open-source work as possible, to 
the same toolchain Tengoku tracks. We estimate this will seed the library with ~600,000 theorems.

In the future, Tengoku will focus on growing high-quality theorem content via automated audits, thorough automated testing
of PRs, and contributions from the community, with and without AI-assistance.

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

## Full documentation
This is the quick start. The full manual — merge queue, tiers, toolchain, every
seeded library — is at [competemath.com/about/tengoku](https://competemath.com/about/tengoku).
