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
    labels: dict[str, str]
    summaries: dict[str, str]
    toc: bool


class SupportConfig(TypedDict):
    title: str
    toc: bool


class InfoConfig(TypedDict):
    heading: str
    text: str
    url: str


class ReviewConeConfig(TypedDict):
    sections: list[SectionConfig]
    support: SupportConfig
    info: InfoConfig | None
    roots: list[str]
    title: str | None
    out: str | None
    imports: list[str] | None


DEFAULT_INFO_HEADING = "Full source code"
DEFAULT_INFO_TEXT = "Complete Lean sources, including all proofs, are hosted at"


class ConfigError(SystemExit):
    """A malformed review-cone.toml — reported with the cli.red convention."""

    def __init__(self, msg: str) -> None:
        super().__init__(cli.red("✗ review-cone.toml: ") + msg)


def _read_name_table(
    sec: dict[str, object], key: str, what: str, section_title: str, decls: list[str]
) -> dict[str, str]:
    """One `[section.<key>]` table, checked: every key is one of `decls` and
    every value is a string. `what` names the entry in error messages."""
    raw = sec.get(key, {})
    if not isinstance(raw, dict):
        raise ConfigError(f"section '{section_title}': `[section.{key}]` must be a table")
    out: dict[str, str] = {}
    for k, v in raw.items():
        if not isinstance(k, str):
            continue  # TOML keys are always strings; this only narrows for the type checker
        if not isinstance(v, str):
            raise ConfigError(
                f"section '{section_title}': {what} for '{k}' is not a string — "
                'a dotted Lean name must be quoted ("CountColorings.branch")'
            )
        if k not in decls:
            raise ConfigError(f"section '{section_title}': {what} for '{k}', which is not one of its decls")
        out[k] = v
    return out


def _read_info(raw: dict[str, object]) -> InfoConfig | None:
    """The optional `[info]` table: a panel naming where the full sources live.
    Absent means no panel at all, so a config that never mentions it renders
    exactly as before. `url` is the only required key."""
    info = raw.get("info")
    if info is None:
        return None
    if not isinstance(info, dict):
        raise ConfigError("`[info]` must be a table")
    fields: dict[str, str] = {}
    for key, default in (("heading", DEFAULT_INFO_HEADING), ("text", DEFAULT_INFO_TEXT), ("url", None)):
        value = info.get(key, default)
        if not isinstance(value, str) or not value.strip():
            what = "is required" if default is None else "must be a non-empty string"
            raise ConfigError(f"`info.{key}` {what}")
        fields[key] = value
    return {"heading": fields["heading"], "text": fields["text"], "url": fields["url"]}


def load_config(path: Path) -> ReviewConeConfig:
    """Parse and validate `review-cone.toml`. Returns
        {"sections": [{"title": str, "decls": [name], "titles": {name: str},
          "labels": {name: str}, "summaries": {name: str}, "toc": bool}],
         "support": {"title": str, "toc": bool},
         "info": {"heading": str, "text": str, "url": str} | None,
         "roots": [name],          # union of all section decls, order-preserving
         "title": str | None,      # document title (CLI --title overrides)
         "out": str | None}        # output path, relative to the project root
    Every named decl is a root. Enforced invariants (each a hard error):
      * each `[[section]]` has a non-empty string `title` and a `decls` list of
        strings, and an optional `toc` flag (default true) that lists it in the
        table of contents;
      * no decl appears in two sections;
      * every `[section.titles]`, `[section.labels]` and `[section.summaries]`
        key is one of that section's decls, with a string value (a value that parsed to a dict
        means an *unquoted* dotted key — Lean names contain dots — which TOML
        silently nests). A label ("Theorem 1") replaces the kind and the Lean
        name in the entry's heading; a summary is a prose paragraph shown
        above the entry's source;
      * the optional `[info]` table, when present, has a non-empty string
        `url` (plus optional `heading`/`text`) — it renders the panel that
        points a reader at the full sources."""
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
        titles = _read_name_table(sec, "titles", "title", title, decls)
        labels = _read_name_table(sec, "labels", "label", title, decls)
        summaries = _read_name_table(sec, "summaries", "summary", title, decls)
        sections.append(
            {
                "title": title,
                "decls": decls,
                "titles": titles,
                "labels": labels,
                "summaries": summaries,
                "toc": bool(sec.get("toc", True)),
            }
        )

    sup = raw.get("support", {})
    if not isinstance(sup, dict):
        raise ConfigError("`[support]` must be a table")
    support: SupportConfig = {
        "title": sup.get("title", "Supporting declarations"),
        "toc": bool(sup.get("toc", True)),
    }
    if not isinstance(support["title"], str) or not support["title"].strip():
        raise ConfigError("`support.title` must be a non-empty string")
    doc_title = raw.get("title")
    if doc_title is not None and not isinstance(doc_title, str):
        raise ConfigError("`title` must be a string")
    out = raw.get("out")
    if out is not None and not isinstance(out, str):
        raise ConfigError("`out` must be a string path")
    imports = raw.get("imports")
    if imports is not None and (
        not isinstance(imports, list)
        or not imports
        or any(not isinstance(m, str) or not m.strip() or "," in m for m in imports)
    ):
        raise ConfigError("`imports` must be a non-empty list of module names")
    return {
        "imports": imports,
        "sections": sections,
        "support": support,
        "info": _read_info(raw),
        "roots": roots,
        "title": doc_title,
        "out": out,
    }


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
