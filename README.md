<p align="center"><img src="logo.png" alt="Tengoku" width="200"></p>
<h1 align="center">Tengoku (天国)</h1>
<p align="center"><em>An AI-first formal mathematics library for Lean 4.</em></p>

## About
Significant formal math projects are fragmented across hundreds of different sources. We pull them
into one unified, verified tree, under the same toolchain. Tengoku aims to provide continuously improving,
Formal math projects are fragmented across hundreds of different sources. We pull them
into one unified, verified tree, under up-to-date toolchains tracked by Tengoku. Our aim is to provide continuously improving,
reliable context for automated theorem provers.

Tengoku is in its early stages. Now, the focus is on translating as much current open-source work as possible, to 
the same toolchain Tengoku tracks. We estimate this will seed the library with ~600,000 theorems, before 2027.

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
