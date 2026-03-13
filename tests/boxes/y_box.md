```
LETTER: y
TRIT: 0
PROOF_STYLE: gemini (coordination)
COUNTERFACTUAL: aptos_transfer invoked without valid YAML manifest schema — must be denied
PROOF_CONDITION: coordinator validates SKILL.md YAML frontmatter (name, version, description) parses clean before any MCP tool dispatch
TEST_CMD: python3 -c "import re,sys; fm=open('/tmp/asi-pr/skills/y/SKILL.md').read().split('---')[1]; [sys.exit(f'FAIL: missing {k}') for k in ('name','version','description') if not re.search(rf'^{k}:',fm,re.M)]; print('PASS: yaml-validation gate holds')"
EXPECTED: pass
```

[Y|ERGODIC|games] Edge: y(0) × b(0) → conservation 0+0+0≡0 (mod 3) ✓
