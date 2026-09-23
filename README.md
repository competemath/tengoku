<p align="center"><img src="logo.png" alt="Tengoku" width="200"></p>
<h1 align="center">Tengoku (天国)</h1>
<p align="center"><em>An AI-first formal mathematics library for Lean 4.</em></p>

## About
Significant formal math projects are fragmented across hundreds of different sources. We pull them
into one unified, verified tree, under the same toolchain. Tengoku aims to provide continuously improving,
reliable context for automated theorem provers.

## Developers
Tengoku hosts **Leak I**, a free MCP service that lets an LLM or agent query
formal theorems by meaning or by type, here: https://barkingtree-leak-i.hf.space/sse (no auth configurations required).

Search the whole library right now [here](https://competemath.com/tengoku).

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
- **Submitting a whole project?** Point the bulk attribution tool at the
  directory with your credit string once; it writes the docstrings for you.
- **Tiers.** Submissions start in `tentative` or `staging` and are promoted to
  `trusted` only once Leak's own toolchain has compiled them from scratch.

## Full documentation
This is the quick start. The full manual — merge queue, tiers, toolchain, every
seeded library — is at [competemath.com/about/tengoku](https://competemath.com/about/tengoku).
