#!/usr/bin/env python3
"""Send the new-mathematics design question, with the paper and all Lean sources attached."""
import json, os, urllib.request

ROOT = "/root/work/cpnf-lean"
Q = os.path.join(ROOT, "frontier/question-lean-blocker.md")
PAPER = os.path.join(ROOT, "frontier/paper.txt")
OUT = os.path.join(ROOT, "frontier/answer-lean-blocker.md")

key = os.environ["LITELLM_MASTER_KEY"]

files = ["CpnfLean.lean"] + sorted(
    "CpnfLean/" + f for f in os.listdir(os.path.join(ROOT, "CpnfLean")) if f.endswith(".lean")
)
files = [f for f in files if not f.endswith("Head.lean") and not f.endswith("Correspondence.lean")]
files += ["CpnfLean/Head.lean", "CpnfLean/Correspondence.lean"]

paper = open(PAPER).read()
parts = [open(Q).read(), "\n\n# The paper (full text)\n\n```\n", paper.rstrip(), "\n```\n"]

parts.append("\n# Attached Lean sources\n")
total = 0
for rel in files:
    src = open(os.path.join(ROOT, rel)).read()
    total += src.count("\n")
    parts.append(f"\n## `{rel}`\n\n```lean\n{src.rstrip()}\n```\n")
prompt = "".join(parts)
print(f"paper={len(paper)} chars; {len(files)} files, {total} lines; total {len(prompt)} chars", flush=True)

body = {
    "model": "gpt-6.2-astra",
    "messages": [
        {"role": "system", "content":
            "You are a mathematician and logician designing a new foundation of mathematics "
            "at the request of a researcher. You are maximally creative but rigorous: every "
            "notion you introduce must be defined, every proof obligation real, and every "
            "tool nameable or constructible. You never relabel a conjecture as a definition."},
        {"role": "user", "content": prompt},
    ],
    "max_tokens": 12000,
}

req = urllib.request.Request(
    "http://127.0.0.1:4000/v1/chat/completions",
    data=json.dumps(body).encode(),
    headers={"Content-Type": "application/json", "Authorization": f"Bearer {key}"},
)
with urllib.request.urlopen(req, timeout=1800) as r:
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
