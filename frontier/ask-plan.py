#!/usr/bin/env python3
"""Send the new-mathematics design question, with the paper and all Lean sources attached."""
import json, os, urllib.request

ROOT = "/root/work/cpnf-lean"
Q = os.path.join(ROOT, "frontier/question-plan.md")
PAPER = os.path.join(ROOT, "frontier/paper.txt")
OUT = os.path.join(ROOT, "frontier/answer-plan.md")

key = os.environ["LITELLM_MASTER_KEY"]

def grant(task):
    """Write the owner's approval from inside this process, immediately before the call.
    Nothing else can spend it: no model request is issued while this process runs."""
    import time
    path = "/root/.config/ai-stack/config/frontier-approvals.jsonl"
    rec = {"ts": time.strftime("%Y-%m-%dT%H:%M:%S%z"), "task": task, "grants": 1}
    with open(path, "a", encoding="utf-8") as f:
        f.write(json.dumps(rec, ensure_ascii=False) + "\n")

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
            "You are the frontier mathematician: the strongest reasoning model available, "
            "attacking the hardest open step of a research programme. You are maximally "
            "creative AND rigorous: every notion you introduce must be defined, every proof "
            "obligation real, every tool nameable or constructible. You never relabel a "
            "conjecture as a definition, and you never claim a proof you do not have. But you "
            "are bold: you do not hedge, you do not retreat into restating the known, and you "
            "do not treat a step as impossible because it is hard. Hard mathematics has fallen "
            "to you before. Take the problem seriously, choose your own path, and attack it "
            "with everything you have."},
        {"role": "user", "content": prompt},
    ],
    "max_tokens": 12000,
}

import urllib.error
last = None
for attempt in range(1, 4):
    grant("Plan the attack on the surviving space; merciless and specific.")
    req = urllib.request.Request(
        "http://127.0.0.1:4000/v1/chat/completions",
        data=json.dumps(body).encode(),
        headers={"Content-Type": "application/json", "Authorization": f"Bearer {key}"},
    )
    try:
        with urllib.request.urlopen(req, timeout=1800) as r:
            data = json.load(r)
        break
    except urllib.error.HTTPError as e:
        last = e
        print(f"attempt {attempt}: HTTP {e.code}", flush=True)
        if e.code != 403:
            raise
else:
    raise last

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
