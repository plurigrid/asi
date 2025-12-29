#!/usr/bin/env python3
"""
L-Space Token Novelty Sensor - P1 Implementation
Measures token surprise via logprobs from local/remote LLMs

Usage:
    python token_novelty.py "text to analyze" --backend ollama
    python token_novelty.py -f file.txt --backend openai
    
Backends: ollama (default), openai, mlx
"""

import argparse
import json
import math
import sys
from dataclasses import dataclass
from typing import Iterator, Optional

@dataclass
class TokenNovelty:
    token: str
    logprob: float
    novelty: float  # -logprob (surprise in nats)
    poincare_r: float  # position on manifold
    
    def to_dict(self):
        return {
            "token": self.token,
            "logprob": round(self.logprob, 4),
            "novelty": round(self.novelty, 4),
            "poincare_r": round(self.poincare_r, 4)
        }

def novelty_to_poincare(novelty: float, baseline: float = 2.0) -> float:
    """Map novelty to Poincaré ball radius [0, 1)"""
    # Higher novelty → closer to boundary
    r = 0.5 + (novelty - baseline) / 20.0
    return max(0.01, min(0.99, r))

# --- Backend: Ollama ---
def stream_ollama(text: str, model: str = "llama3.2") -> Iterator[TokenNovelty]:
    """Stream logprobs from Ollama"""
    try:
        import requests
    except ImportError:
        print("pip install requests", file=sys.stderr)
        sys.exit(1)
    
    resp = requests.post(
        "http://localhost:11434/api/generate",
        json={
            "model": model,
            "prompt": text,
            "stream": True,
            "options": {"num_predict": 1}  # We want logprobs of input, not generation
        },
        stream=True
    )
    
    # Ollama doesn't expose logprobs directly in generate
    # Use /api/embed or estimate from context
    # For now, use frequency-based estimation
    print("Warning: Ollama doesn't expose logprobs; using frequency estimation", file=sys.stderr)
    yield from estimate_novelty(text)

# --- Backend: OpenAI ---
def stream_openai(text: str, model: str = "gpt-4o-mini") -> Iterator[TokenNovelty]:
    """Stream logprobs from OpenAI API"""
    try:
        from openai import OpenAI
    except ImportError:
        print("pip install openai", file=sys.stderr)
        sys.exit(1)
    
    client = OpenAI()
    
    # Get logprobs by asking model to repeat the text
    response = client.chat.completions.create(
        model=model,
        messages=[
            {"role": "system", "content": "Repeat the following text exactly, word by word."},
            {"role": "user", "content": text}
        ],
        logprobs=True,
        top_logprobs=5,
        max_tokens=len(text.split()) + 10
    )
    
    if response.choices[0].logprobs:
        for content in response.choices[0].logprobs.content:
            logprob = content.logprob
            novelty = -logprob
            yield TokenNovelty(
                token=content.token,
                logprob=logprob,
                novelty=novelty,
                poincare_r=novelty_to_poincare(novelty)
            )

# --- Backend: MLX ---
def stream_mlx(text: str, model: str = "mlx-community/gemma-3-1b-it-qat-4bit") -> Iterator[TokenNovelty]:
    """Get logprobs from MLX-LM server"""
    try:
        import requests
    except ImportError:
        print("pip install requests", file=sys.stderr)
        sys.exit(1)
    
    # Assumes mlx_lm.server running on :8080
    resp = requests.post(
        "http://localhost:8080/v1/completions",
        json={
            "model": model,
            "prompt": text,
            "max_tokens": 1,
            "logprobs": 5,
            "echo": True  # Return logprobs for prompt tokens
        }
    )
    
    data = resp.json()
    if "choices" in data and data["choices"]:
        logprobs_data = data["choices"][0].get("logprobs", {})
        tokens = logprobs_data.get("tokens", [])
        logprobs = logprobs_data.get("token_logprobs", [])
        
        for tok, lp in zip(tokens, logprobs):
            if lp is not None:
                novelty = -lp
                yield TokenNovelty(
                    token=tok,
                    logprob=lp,
                    novelty=novelty,
                    poincare_r=novelty_to_poincare(novelty)
                )

# --- Fallback: Frequency Estimation ---
def estimate_novelty(text: str) -> Iterator[TokenNovelty]:
    """Estimate novelty from unigram frequency (no LLM required)"""
    import re
    from collections import Counter
    
    tokens = re.findall(r'\b\w+\b', text.lower())
    freqs = Counter(tokens)
    total = len(tokens)
    
    for tok in tokens:
        freq = freqs[tok]
        logprob = math.log(freq / total)  # Estimated
        novelty = -logprob
        yield TokenNovelty(
            token=tok,
            logprob=round(logprob, 4),
            novelty=round(novelty, 4),
            poincare_r=novelty_to_poincare(novelty)
        )

# --- Main ---
def analyze(text: str, backend: str, model: Optional[str] = None) -> dict:
    """Full novelty analysis"""
    backends = {
        "ollama": stream_ollama,
        "openai": stream_openai,
        "mlx": stream_mlx,
        "estimate": estimate_novelty
    }
    
    if backend not in backends:
        print(f"Unknown backend: {backend}. Use: {list(backends.keys())}", file=sys.stderr)
        sys.exit(1)
    
    stream_fn = backends[backend]
    tokens = list(stream_fn(text, model) if model else stream_fn(text))
    
    if not tokens:
        tokens = list(estimate_novelty(text))
    
    novelties = [t.novelty for t in tokens]
    mean_nov = sum(novelties) / len(novelties) if novelties else 0
    max_nov = max(novelties) if novelties else 0
    
    # Octavo territory detection
    octavo_tokens = [t for t in tokens if t.poincare_r > 0.95]
    
    return {
        "backend": backend,
        "total_tokens": len(tokens),
        "mean_novelty": round(mean_nov, 4),
        "max_novelty": round(max_nov, 4),
        "octavo_territory": len(octavo_tokens) > 0,
        "octavo_tokens": [t.to_dict() for t in octavo_tokens],
        "tokens": [t.to_dict() for t in tokens],
        "gf3": gf3_check(tokens)
    }

def gf3_check(tokens: list[TokenNovelty]) -> dict:
    """GF(3) balance: categorize by manifold region"""
    trits = []
    for t in tokens:
        if t.poincare_r < 0.33:
            trits.append(-1)  # Center
        elif t.poincare_r > 0.66:
            trits.append(1)   # Boundary
        else:
            trits.append(0)   # Interior
    
    return {
        "distribution": {"minus": trits.count(-1), "ergodic": trits.count(0), "plus": trits.count(1)},
        "sum": sum(trits),
        "balanced": sum(trits) % 3 == 0
    }

def main():
    parser = argparse.ArgumentParser(description="L-Space Token Novelty Sensor")
    parser.add_argument("text", nargs="?", help="Text to analyze")
    parser.add_argument("-f", "--file", help="Read text from file")
    parser.add_argument("-b", "--backend", default="estimate", 
                        choices=["ollama", "openai", "mlx", "estimate"])
    parser.add_argument("-m", "--model", help="Model name for backend")
    parser.add_argument("--json", action="store_true", help="Output JSON")
    
    args = parser.parse_args()
    
    if args.file:
        with open(args.file) as f:
            text = f.read()
    elif args.text:
        text = args.text
    elif not sys.stdin.isatty():
        text = sys.stdin.read()
    else:
        parser.print_help()
        sys.exit(1)
    
    result = analyze(text, args.backend, args.model)
    
    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print(f"Backend: {result['backend']}")
        print(f"Tokens: {result['total_tokens']}")
        print(f"Mean novelty: {result['mean_novelty']:.2f} nats")
        print(f"Max novelty: {result['max_novelty']:.2f} nats")
        print(f"Octavo territory: {'YES' if result['octavo_territory'] else 'no'}")
        print(f"GF(3) balanced: {result['gf3']['balanced']}")
        
        if result['octavo_tokens']:
            print("\nHigh-novelty tokens (r > 0.95):")
            for t in result['octavo_tokens'][:5]:
                print(f"  '{t['token']}': novelty={t['novelty']:.2f}, r={t['poincare_r']:.3f}")

if __name__ == "__main__":
    main()
