"""Parse `review-cone.toml`: the roots and the section layout of a review
document.

Its own module because two tools read it for two reasons — `review-cone`
renders the layout, `dep-tree` only wants the roots — and the latter should not
drag in an HTML renderer to read a config file.
"""

from __future__ import annotations

import sys
import tomllib
from pathlib import Path
from typing import TypedDict

from . import cli

DEFAULT_CONFIG_NAME = "review-cone.toml"

# A project may keep several configs, one per review document.
CONE_CONFIG_GLOB = "review-cone*.toml"


class SectionConfig(TypedDict):
    title: str
    decls: list[str]
    titles: dict[str, str]


class SupportConfig(TypedDict):
    title: str
    toc: bool


class ReviewConeConfig(TypedDict):
    sections: list[SectionConfig]
    support: SupportConfig
    roots: list[str]
    title: str | None
    out: str | None


class ConfigError(SystemExit):
    """A malformed review-cone.toml — reported with the cli.red convention."""

    def __init__(self, msg: str) -> None:
        super().__init__(cli.red("✗ review-cone.toml: ") + msg)


def load_config(path: Path) -> ReviewConeConfig:
    """Parse and validate `review-cone.toml`. Returns
        {"sections": [{"title": str, "decls": [name], "titles": {name: str}}],
         "support": {"title": str, "toc": bool},
         "roots": [name],          # union of all section decls, order-preserving
         "title": str | None,      # document title (CLI --title overrides)
         "out": str | None}        # output path, relative to the project root
    Every named decl is a root. Enforced invariants (each a hard error):
      * each `[[section]]` has a non-empty string `title` and a `decls` list of
        strings;
      * no decl appears in two sections;
      * every `[section.titles]` key is one of that section's decls, with a
        string value (a value that parsed to a dict means an *unquoted* dotted
        key — Lean names contain dots — which TOML silently nests)."""
    if not path.is_file():
        raise ConfigError(f"not found at {path} (pass --config to point elsewhere)")
    try:
        raw = tomllib.loads(path.read_text(encoding="utf-8"))
    except tomllib.TOMLDecodeError as e:
        raise ConfigError(f"parse error — {e}") from e

    raw_sections = raw.get("section")
    if not isinstance(raw_sections, list) or not raw_sections:
        raise ConfigError("needs at least one [[section]] with a `decls` list")

    sections: list[SectionConfig] = []
    seen: dict[str, str] = {}  # decl name -> section title that claimed it
    roots: list[str] = []
    for i, sec in enumerate(raw_sections):
        if not isinstance(sec, dict):
            raise ConfigError(f"section #{i + 1} must be a [[section]] table")
        title = sec.get("title")
        if not isinstance(title, str) or not title.strip():
            raise ConfigError(f"section #{i + 1} needs a non-empty string `title`")
        raw_decls = sec.get("decls", [])
        if not isinstance(raw_decls, list) or not all(isinstance(d, str) for d in raw_decls):
            raise ConfigError(f"section '{title}': `decls` must be a list of strings")
        decls: list[str] = [d for d in raw_decls if isinstance(d, str)]
        for d in decls:
            if d in seen:
                raise ConfigError(f"decl '{d}' is listed in both '{seen[d]}' and '{title}'")
            seen[d] = title
            roots.append(d)
        raw_titles = sec.get("titles", {})
        if not isinstance(raw_titles, dict):
            raise ConfigError(f"section '{title}': `[section.titles]` must be a table")
        titles: dict[str, str] = {}
        for k, v in raw_titles.items():
            if not isinstance(k, str):
                continue  # TOML keys are always strings; this only narrows for the type checker
            if not isinstance(v, str):
                raise ConfigError(
                    f"section '{title}': title for '{k}' is not a string — "
                    'a dotted Lean name must be quoted ("CountColorings.branch")'
                )
            if k not in decls:
                raise ConfigError(f"section '{title}': title for '{k}', which is not one of its decls")
            titles[k] = v
        sections.append({"title": title, "decls": decls, "titles": titles})

    sup = raw.get("support", {})
    if not isinstance(sup, dict):
        raise ConfigError("`[support]` must be a table")
    support: SupportConfig = {
        "title": sup.get("title", "Supporting declarations"),
        "toc": bool(sup.get("toc", False)),
    }
    if not isinstance(support["title"], str) or not support["title"].strip():
        raise ConfigError("`support.title` must be a non-empty string")
    doc_title = raw.get("title")
    if doc_title is not None and not isinstance(doc_title, str):
        raise ConfigError("`title` must be a string")
    out = raw.get("out")
    if out is not None and not isinstance(out, str):
        raise ConfigError("`out` must be a string path")
    return {"sections": sections, "support": support, "roots": roots, "title": doc_title, "out": out}


def roots_from_configs(root: Path) -> set[str]:
    """Root decl names from every `review-cone*.toml` in `root` — the union of
    each config's roots, via the one authoritative parser. Empty (with a note)
    if none is found; an invalid config is skipped with a note."""
    paths = sorted(root.glob(CONE_CONFIG_GLOB))
    if not paths:
        print(f"note: no {CONE_CONFIG_GLOB} in {root}", file=sys.stderr)
        return set()
    out: set[str] = set()
    for path in paths:
        try:
            out.update(load_config(path)["roots"])
        except ConfigError as e:
            print(f"note: {path.name} skipped — {e.code}", file=sys.stderr)
    return out
