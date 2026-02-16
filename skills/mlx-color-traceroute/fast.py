#!/usr/bin/env python3
"""Minimal fast traceroute - no deps"""
import sys
S = int(sys.argv[1], 16) if len(sys.argv) > 1 else 0x42D
def sm(z): z=((z^(z>>30))*0xBF58476D1CE4E5B9)&0xFFFFFFFFFFFFFFFF; z=((z^(z>>27))*0x94D049BB133111EB)&0xFFFFFFFFFFFFFFFF; return z^(z>>31)
for i,s in enumerate(["sRGB","clj-mcp","nrepl","grain","modex","fastmlx","Gay.jl","∞"]):
    st=sm(S^i); h=(st%65536)/65536*360; t=st%3-1; r,g,b=int(128+127*__import__('math').cos((h-0)*3.14159/180)),int(128+127*__import__('math').cos((h-120)*3.14159/180)),int(128+127*__import__('math').cos((h-240)*3.14159/180))
    print(f"\033[48;2;{r};{g};{b}m  \033[0m {i} {s:12} {'−○+'[t+1]}")
print(f"sum={sum(sm(S^i)%3-1 for i in range(8))}mod3")
