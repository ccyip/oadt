var coqdocjs = coqdocjs || {};

coqdocjs.project_page = "../";

coqdocjs.repl = {
    "forall": "∀",
    "exists": "∃",
    "~": "¬",
    "/\\": "∧",
    "\\/": "∨",
    "->": "→",
    "<-": "←",
    "<->": "↔",
    "=>": "⇒",
    "<>": "≠",
    "<=": "≤",
    ">=": "≥",
    "el": "∈",
    "nel": "∉",
    "<<=": "⊆",
    "|-": "⊢",
    ">>": "»",
    "<<": "⊆",
    "++": "⧺",
    "===": "≡",
    "=/=": "≢",
    "=~=": "≅",
    "==>": "⟹",
    "lhd": "⊲",
    "rhd": "⊳",
    "nat": "ℕ",
    "alpha": "α",
    "beta": "β",
    "gamma": "γ",
    "delta": "δ",
    "epsilon": "ε",
    "eta": "η",
    "iota": "ι",
    "kappa": "κ",
    "lambda": "λ",
    "mu": "μ",
    "nu": "ν",
    "omega": "ω",
    "phi": "ϕ",
    "pi": "π",
    "psi": "ψ",
    "rho": "ρ",
    "sigma": "σ",
    "tau": "τ",
    "theta": "θ",
    "xi": "ξ",
    "zeta": "ζ",
    "Delta": "Δ",
    "Gamma": "Γ",
    "Pi": "Π",
    "Sigma": "Σ",
    "Omega": "Ω",
    "Xi": "Ξ"
};

coqdocjs.subscr = {
  "0" : "₀",
  "1" : "₁",
  "2" : "₂",
  "3" : "₃",
  "4" : "₄",
  "5" : "₅",
  "6" : "₆",
  "7" : "₇",
  "8" : "₈",
  "9" : "₉",
};

coqdocjs.replInText = ["==>","<=>", "=>", "->", "<-", ":="];

// Update with user config
Object.assign(coqdocjs, coqdocjs_conf);
if (coqdocjs_conf.more_repl) {
    Object.assign(coqdocjs.repl, coqdocjs_conf.more_repl);
}
if (coqdocjs_conf.more_replInText) {
    coqdocjs.replInText = coqdocjs_conf.more_replInText.concat(coqdocjs.replInText);
}
