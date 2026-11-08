module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Upstream.Attribution.Trilemma

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Explainability / attribution limits

Thin wrappers over the attribution trilemma (Caraker et al.; Apache-2.0).
Landscape `LAND-ATTR-001` — not survey headline coverage. No AI-system bridge.

## Primary surface

| Role | Declaration | One-line |
|---|---|---|
| **Law** | `attribution_impossibility` | Faithful + stable ranking impossible under Rashomon |
| **Law** | `attribution_impossibility_weak` | Weaker packaging of the same core |
-/

namespace AISafetyAtlas.Explainability

/-- Feature index type (collinearity groups).-/
public abbrev FeatureIndex := AISafetyAtlas.Upstream.Attribution.FeatureIndex

/-- Group membership.-/
public abbrev inGroup := AISafetyAtlas.Upstream.Attribution.inGroup

/-- Rashomon property for an attribution map.-/
public abbrev RashomonProperty := AISafetyAtlas.Upstream.Attribution.RashomonProperty

end AISafetyAtlas.Explainability
