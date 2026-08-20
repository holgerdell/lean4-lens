"""Lean declaration keywords and the regex fragments that recognise them in source text."""

# `noncomputable def` needs no entry of its own: `MODIFIERS` consumes the
# `noncomputable` prefix before the keyword is matched.
DECL_KEYWORDS = [
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "structure",
    "class abbrev",
    "class inductive",
    "class",
    "instance",
    "inductive",
    "axiom",
]

ATTR_PREFIX = r"(?:@\[[^\]]*\]\s*)*"
MODIFIERS = r"(?:(?:private|protected|noncomputable|scoped|local|partial|unsafe|public|nonrec|meta)\s+)*"
