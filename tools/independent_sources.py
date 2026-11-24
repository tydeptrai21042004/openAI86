"""Independent source inventory; retain two legacy adapted files without counting them."""
from pathlib import Path

LEGACY = ("OpenAI086/Lemma33Reviewed.lean", "OpenAI086/Lemma33Check.lean")
LEGACY_MODULES = frozenset(p.removesuffix(".lean").replace("/", ".") for p in LEGACY)

def core_sources(root: Path):
    return sorted(p for p in (root / "OpenAI086").rglob("*.lean")
                  if p.relative_to(root).as_posix() not in LEGACY)

def independent_sources(root: Path):
    return core_sources(root) + [root / "OpenAI086.lean", root / "OpenAI086Whole.lean"]
