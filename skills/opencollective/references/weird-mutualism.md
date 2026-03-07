# Weird Mutualism

From the Open Mutualism Guild: mutualism where **infrastructure participates in the mutualism it enables**.

## Five Strange Loops in OC

1. **Self-referential platform** — OC is a collective on its own platform (ID 845576), funded by tips through its own mechanism
2. **Host ↔ Collective** — Hosts provide legal standing, collectives provide purpose and fees. Neither exists without the other
3. **Circular funding** — Collectives fund other collectives via `CONNECTED_COLLECTIVE` role, creating dataflow cycles
4. **Code-money-code** — npm postinstall → donation → maintainer payment → better code → more installs
5. **Fractal cooperativism** — Co-ops hosting co-ops (Platform 6), funded by co-ops (social.coop)

## Exploring Mutualism via API

```graphql
# Mutual aid collectives
query {
  accounts(searchTerm: "mutual aid", type: COLLECTIVE, isActive: true, limit: 20) {
    totalCount
    nodes { name slug description tags stats { balance { valueInCents currency } contributorsCount } }
  }
}

# Cooperative fiscal hosts
query {
  hosts(limit: 20) {
    nodes { name slug totalHostedCollectives hostFeePercent description }
  }
}

# Tag ecosystem
query {
  tagStats(searchTerm: "mutual", limit: 20) { nodes { tag count } }
}

# Connected collectives (symbiotic links)
query {
  account(slug: "opensource") {
    members(role: [CONNECTED_COLLECTIVE], limit: 20) {
      nodes { account { name slug } }
    }
  }
}
```

## Key Ecosystem Tags

Run `tagStats` queries for current counts. Major clusters: `mutual aid`, `solidarity`, `solidarity economy`, `cooperative`, `commons`, `community`.

## Sources

- Open Mutualism Guild: https://hackmd.io/@exeuntdoteth/Hku0b5xyJg
- Benkler, "Practical Anarchism: Peer Mutualism" (2013)
- OC blog, "Emergent Practices from the Decentralized Co-operative Web" (2021)
