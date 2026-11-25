#!/usr/bin/env python3
"""Send the attack-plan question to the frontier model, with every Lean source attached."""
import json, os, sys, urllib.request

ROOT = "/root/work/cpnf-lean"
Q = os.path.join(ROOT, "frontier/question-minfac.md")
OUT = os.path.join(ROOT, "frontier/answer-minfac.md")

key = os.environ["LITELLM_MASTER_KEY"]

files = ["CpnfLean.lean"] + sorted(
    "CpnfLean/" + f for f in os.listdir(os.path.join(ROOT, "CpnfLean")) if f.endswith(".lean")
)
# Head last, Correspondence last-but-one: the layers the question is about.
files = [f for f in files if not f.endswith("Head.lean") and not f.endswith("Correspondence.lean")]
files += ["CpnfLean/Head.lean", "CpnfLean/Correspondence.lean"]

parts = [open(Q).read(), "\n\n# Attached Lean sources\n"]
total = 0
for rel in files:
    src = open(os.path.join(ROOT, rel)).read()
    total += src.count("\n")
    parts.append(f"\n## `{rel}`\n\n```lean\n{src.rstrip()}\n```\n")
prompt = "".join(parts)
print(f"attaching {len(files)} files, {total} lines, {len(prompt)} chars", flush=True)

body = {
    "model": "gpt-6.2-astra",
    "messages": [
        {"role": "system", "content":
            "You are a research mathematician attacking the twin prime conjecture through a "
            "computational framework (CPNF) whose code is formally verified in Lean 4. You "
            "reason rigorously and never claim a result stronger than what follows from the "
            "given definitions. When asked for a plan, you give one plainly, in order, with the "
            "first step stated as a Lean-checkable lemma."},
        {"role": "user", "content": prompt},
    ],
    "max_tokens": 8000,
}

req = urllib.request.Request(
    "http://127.0.0.1:4000/v1/chat/completions",
    data=json.dumps(body).encode(),
    headers={"Content-Type": "application/json", "Authorization": f"Bearer {key}"},
)
with urllib.request.urlopen(req, timeout=1200) as r:
    data = json.load(r)

msg = data["choices"][0]["message"]
text = msg.get("content") or ""
usage = data.get("usage", {})
reasoning = usage.get("completion_tokens_details", {}).get("reasoning_tokens")

open(OUT, "w").write(text + "\n")
print(f"model={data.get('model')} chars={len(text)} "
      f"prompt_tokens={usage.get('prompt_tokens')} completion_tokens={usage.get('completion_tokens')} "
      f"reasoning_tokens={reasoning}", flush=True)
if not text.strip():
    print("EMPTY ANSWER — all budget went to reasoning", flush=True)
    sys.exit(3)
