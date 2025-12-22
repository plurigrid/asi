# Tim Roughgarden Educational Content - Comprehensive Index

**Last Updated:** December 21, 2025
**Purpose:** Knowledge indexing for mechanism design, replicated state machines, distributed systems, and game theory research

---

## Table of Contents
1. [Stanford Course Series (2004-2018)](#stanford-courses)
2. [Columbia Course Series (2019-Present)](#columbia-courses)
3. [YouTube Lecture Playlists](#youtube-playlists)
4. [Online MOOCs](#moocs)
5. [Conference Talks & Tutorials](#conference-talks)
6. [Key Papers by Topic](#key-papers)
7. [Lecture Notes Repository](#lecture-notes)

---

## Stanford Courses

### CS364A: Algorithmic Game Theory (Fall 2013)
- **Platform:** YouTube + Course Website
- **URL (Playlist):** https://www.youtube.com/playlist?list=PLEGCF-WLh2RJBqmxvZ0_ie-mleCFhi2N4
- **URL (Notes):** https://timroughgarden.org/f13/f13.html
- **Lectures:** 20 videos + comprehensive lecture notes
- **Duration:** ~60-70 minutes per lecture
- **Key Topics:**
  - Mechanism design basics (Vickrey auctions, Myerson's Lemma)
  - Algorithmic mechanism design
  - Revenue-maximizing auctions
  - VCG mechanism and multi-parameter mechanism design
  - Combinatorial auctions and spectrum auctions
  - Price of anarchy in selfish routing
  - No-regret dynamics and learning in games
  - Computational complexity (PLS-completeness, PPAD-completeness)
  - Smooth games and robust equilibrium analysis
- **Textbook:** "Twenty Lectures on Algorithmic Game Theory" (Cambridge, 2016)
- **Relevance:** ⭐⭐⭐⭐⭐ - Foundational for mechanism design and game theory

### CS364B: Advanced Mechanism Design (Winter 2014)
- **Platform:** YouTube + Course Website
- **URL (Playlist):** https://www.youtube.com/playlist?list=PLEGCF-WLh2RI77PL4gwLld_OU9Zh3TCX9
- **URL (Notes):** https://timroughgarden.org/w14/w14.html
- **Lectures:** 20 videos
- **Key Topics:**
  - Ascending and ex post incentive compatible mechanisms
  - Walrasian equilibria and gross substitutes condition
  - Crawford-Knoer and Clinching auctions
  - Submodular valuations
  - MIR and MIDR mechanisms
  - Bayesian incentive-compatibility
  - Price of anarchy in simple auctions
  - Border's theorem
  - Multi-parameter revenue maximization
  - Truthful approximation mechanisms
- **Relevance:** ⭐⭐⭐⭐⭐ - Advanced techniques for combinatorial auctions

### CS261: A Second Course in Algorithms (Winter 2016)
- **Platform:** YouTube + Course Website
- **URL (Playlist):** https://www.youtube.com/playlist?list=PLEGCF-WLh2RJh2yDxlJJjnKswWdoO8gAc
- **URL (Notes):** https://timroughgarden.org/w16/w16.html
- **Lectures:** 20 videos
- **Key Topics:**
  - Maximum flow algorithms (augmenting paths, push-relabel)
  - Bipartite matching and generalizations
  - Linear programming and duality
  - Multiplicative weights algorithm
  - Online algorithms and competitive analysis
  - Approximation algorithms
  - TSP problem
  - Beating brute-force search for NP-hard problems
- **Relevance:** ⭐⭐⭐ - Algorithmic foundations supporting mechanism design

### CS168: Modern Algorithmic Toolbox (Spring 2017, with Greg Valiant)
- **Platform:** Course Website (lecture notes)
- **URL:** https://web.stanford.edu/class/cs168/
- **URL (Notes):** https://timroughgarden.org/notes.html
- **Lectures:** 19 lecture note sets
- **Key Topics:**
  - Consistent hashing
  - Count-Min sketch and heavy hitters
  - Dimensionality reduction
  - PCA and SVD
  - Spectral graph theory
  - Markov Chain Monte Carlo
  - Fourier transform and convolution
  - Compressive sensing
  - Expander codes
- **Relevance:** ⭐⭐⭐ - Modern data structures and probabilistic methods

### CS264/CS369N: Beyond Worst-Case Analysis (Fall 2014, Winter 2017)
- **Platform:** YouTube + Course Website
- **URL (Playlist):** https://www.youtube.com/playlist?list=PLEGCF-WLh2RL8jsZpaf2tLHa5LotFEt5b
- **URL (Notes):** https://timroughgarden.org/f14/f14.html
- **Lectures:** 20 videos
- **Key Topics:**
  - Smoothed analysis
  - Parameterized analysis
  - Instance optimality
  - Stable clustering
  - Planted and semi-random graph models
  - LP decoding
  - Pseudorandom data models
  - Self-improving algorithms
- **Relevance:** ⭐⭐⭐ - Alternative analytical frameworks

### CS269I: Incentives in Computer Science (Fall 2016, Fall 2018)
- **Platform:** YouTube + Course Website
- **URL (Playlist):** https://www.youtube.com/playlist?list=PLEGCF-WLh2RJdrKZ431SidRX_T4VmAKx8
- **URL (Notes):** https://timroughgarden.org/f16/f16.html
- **Lectures:** Short course (accessible introduction)
- **Key Topics:**
  - Markets in computer science
  - Prisoner's Dilemma and BitTorrent
  - Asymmetric information (adverse selection, moral hazard)
  - eBay reputation systems
  - Auctions and sponsored search
  - Voting and participatory budgeting
  - Game theory in Bitcoin mining
- **Relevance:** ⭐⭐⭐⭐ - Applied game theory in systems

---

## Columbia Courses

### COMS 6998: Foundations of Blockchains (Fall 2020, Fall 2021)
- **Platform:** YouTube + GitHub Pages
- **URL (Playlist):** https://www.youtube.com/playlist?list=PLEGCF-WLh2RLOHv_xUGLqRts_9JxrckiA
- **URL (Course Site):** https://timroughgarden.github.io/fob21/
- **URL (GitHub):** https://github.com/timroughgarden/fob21
- **Lectures:** Complete video series + lecture notes
- **Key Topics:**
  - **Byzantine Fault Tolerance:**
    - Dolev-Strong protocol for Byzantine broadcast
    - FLP impossibility theorem
    - Partially synchronous model
    - Tendermint protocol
  - **Consensus Protocols:**
    - State machine replication (SMR)
    - Longest-chain consensus
    - Permissionless vs permissioned consensus
  - **Proof Systems:**
    - Proof-of-work and Nakamoto consensus
    - Proof-of-stake protocols
    - Selfish mining attacks
  - **Blockchain Economics:**
    - Transaction fee mechanism design
    - EIP-1559 analysis
    - Economic security limits
  - **DeFi and Applications:**
    - Automated market makers
    - MEV (miner extractable value)
    - Layer-2 scaling (optimistic and zk-rollups)
- **Lecture Notes Available:**
  - L1: Introduction and Overview
  - L2: Dolev-Strong Protocol (Byzantine broadcast in synchronous model)
  - L3: Simulation and Indistinguishability
  - L4-5: FLP Impossibility Theorem
  - L6: Partially Synchronous Model and CAP Principle
  - L7: Tendermint Protocol
  - L8: Longest-Chain Consensus
  - L9: Permissionless Consensus and Proof-of-Work
  - L10: Selfish Mining (partial)
- **Relevance:** ⭐⭐⭐⭐⭐ - Essential for RSM, BFT, and distributed consensus

### COMS 4995: The Science of Blockchains (Spring 2025 - Current)
- **Platform:** Course Website
- **URL:** https://timroughgarden.org/s25/
- **Lectures:** Ongoing (lecture slides available)
- **Key Topics:**
  - **Part I: Building a Shared Global Virtual Machine**
    - SMR problem definition
    - Consensus, consistency, liveness
    - Crash faults vs Byzantine faults
    - Paxos/Raft for crash fault tolerance
    - Tendermint for Byzantine fault tolerance
    - Longest-chain consensus
  - **Part II: Scaling**
    - Cryptographic hash functions
    - Merkle and Merkle-Patricia trees
    - KZG commitments
    - Data availability and light clients
    - Optimistic rollups (fraud proofs)
    - Validity rollups (SNARKs)
    - Cross-chain bridges
  - **Part III: Permissionless Validation**
    - Proof-of-work and Nakamoto consensus
    - Difficulty adjustment
    - Proof-of-stake design
    - VRFs and randomness beacons
    - Mempools and gossip protocols
    - Transaction fees and gas
    - MEV and proposer-builder separation
- **Lecture Materials:** Slides and outlines for all 28 lectures available
- **Relevance:** ⭐⭐⭐⭐⭐ - Most current treatment of blockchain consensus

---

## YouTube Playlists

### Foundations of Blockchains (Primary Series)
- **URL:** https://www.youtube.com/playlist?list=PLEGCF-WLh2RLOHv_xUGLqRts_9JxrckiA
- **Videos:** Complete lecture series
- **Key Lecture Examples:**
  - 1.1: Focus of Lecture Series
  - 1.4: State Machine Replication
  - 2.1-2.4: Dolev-Strong Protocol
  - 3.1: PSL-FLM Impossibility Result
  - 4.3: Byzantine Agreement
  - 8.1-8.8: Longest-Chain Consensus
  - 9.1: Permissionless Consensus
  - 12.1-12.2: Review of Consensus

### Algorithmic Game Theory (Stanford CS364A)
- **URL:** https://www.youtube.com/playlist?list=PLEGCF-WLh2RJBqmxvZ0_ie-mleCFhi2N4
- **Videos:** 20 complete lectures
- **Popular Lectures:**
  - L1: Introduction and Examples (245K views)
  - L2: Mechanism Design Basics (36K views)
  - L4: Algorithmic Mechanism Design (20K views)
  - L7: VCG Mechanism (10K views)

### Advanced Mechanism Design (Stanford CS364B)
- **URL:** https://www.youtube.com/playlist?list=PLEGCF-WLh2RI77PL4gwLld_OU9Zh3TCX9
- **Videos:** 20 lectures on advanced topics

### A Second Course in Algorithms (Stanford CS261)
- **URL:** https://www.youtube.com/playlist?list=PLEGCF-WLh2RJh2yDxlJJjnKswWdoO8gAc
- **Videos:** 20 lectures

### Beyond Worst-Case Analysis (Stanford CS264)
- **URL:** https://www.youtube.com/playlist?list=PLEGCF-WLh2RL8jsZpaf2tLHa5LotFEt5b
- **Videos:** 20 lectures

### Incentives in Computer Science (Short Course)
- **URL:** https://www.youtube.com/playlist?list=PLEGCF-WLh2RJdrKZ431SidRX_T4VmAKx8
- **Videos:** Accessible introduction series

### Tim Roughgarden Lectures (Main Channel)
- **URL:** https://www.youtube.com/channel/UCcH4Ga14Y4ELFKrEYM1vXCg
- **Content:** All course playlists plus additional talks

---

## MOOCs

### Algorithms Specialization (Coursera)
- **URL:** https://www.coursera.org/specializations/algorithms
- **Institution:** Stanford University
- **Format:** 4-course series (4 weeks each)
- **Courses:**
  1. **Divide and Conquer, Sorting and Searching**
     - Asymptotic notation, sorting, randomized algorithms
  2. **Graph Search, Shortest Paths, Data Structures**
     - Heaps, BSTs, hash tables, BFS/DFS, shortest paths
  3. **Greedy Algorithms, MST, Dynamic Programming**
     - Scheduling, MST, clustering, Huffman, knapsack
  4. **Shortest Paths Revisited, NP-Complete Problems**
     - Bellman-Ford, Floyd-Warshall, NP-completeness, heuristics
- **Book Series:** "Algorithms Illuminated" (4 volumes)
- **Recognition:** Multiple "top MOOCs of all time" lists
- **Relevance:** ⭐⭐⭐ - Foundational algorithms

---

## Conference Talks & Tutorials

### Mechanism Design Focus

**How To Think About Algorithmic Mechanism Design**
- **Conference:** FOCS 2010 (Tutorial)
- **URL:** Video available on YouTube
- **Slides:** https://timroughgarden.org/talks/focs10.pdf
- **Topics:** Survey of mechanism design fundamentals

**Approximately Optimal Mechanism Design**
- **Conference:** EC 2014
- **URL:** https://timroughgarden.org/talks/ec14talk.pdf (slides)
- **Paper:** https://arxiv.org/abs/1406.6773
- **Topics:** Motivation and lessons learned from approximate mechanisms

**Learning Near-Optimal Auctions**
- **Conference:** WINE 2017 (Keynote)
- **URL:** https://www.youtube.com/watch?v=zgbq4j8SDKE
- **Slides:** https://timroughgarden.org/talks/wine17public.pdf
- **Topics:** Statistical, computational, and strategic challenges

### Byzantine Fault Tolerance & Consensus

**Permissionless Consensus**
- **Conference:** ICDCN 2022 (Keynote)
- **URL:** https://timroughgarden.org/tldr/icdcn22.pdf
- **Topics:** Proof-of-work, longest-chain, permissionless vs permissioned

**Tutorial Series on Permissionless Consensus**
- **Format:** 13-part YouTube series
- **URL:** Search "Permissionless Consensus Tutorial Tim Roughgarden"
- **Topics:** Complete treatment from classical to permissionless consensus

**Blockchain Protocols and Web3: A Glimpse Under the Hood**
- **Format:** Public lecture
- **URL:** https://www.youtube.com/watch?v=-mWjDgVWl20
- **Topics:** Accessible overview of consensus and protocol design

### Price of Anarchy

**Extension Theorems for the Price of Anarchy**
- **Conference:** Texas A&M Fish Bowl Seminar (2013)
- **URL:** https://www.youtube.com/watch?v=e3O_tMsN2t8
- **Slides:** https://timroughgarden.org/talks/nytheoryday13.pdf
- **Papers:** STOC '09, EC '12

**Barriers to Near-Optimal Equilibria**
- **Conference:** Twenty Years of Price of Anarchy (2019)
- **URL:** https://www.youtube.com/watch?v=pl4vaS7xnts
- **Paper:** FOCS '14

**Intrinsic Robustness of the Price of Anarchy**
- **Event:** Kalai Prize Lecture (2016)
- **Slides:** https://timroughgarden.org/talks/kalai.pdf
- **Topics:** Connection between worst-case and Bayesian price of anarchy

### Additional Surveys

**Game Theory Through the Computational Lens**
- **Venue:** London School of Economics Public Lecture (2017)
- **URL:** https://www.youtube.com/watch?v=7HYJ2oJtLZk
- **Slides:** https://timroughgarden.org/talks/lse_public17public.pdf

**How Computer Science Informs Modern Auction Design**
- **Venue:** Simons Foundation Public Lecture (2018)
- **URL:** https://www.youtube.com/watch?v=mSekp5ctcQw
- **Slides:** https://timroughgarden.org/talks/simonsfoundation18public.pdf

---

## Key Papers by Topic

### Transaction Fee Mechanism Design

**Transaction Fee Mechanism Design for the Ethereum Blockchain: An Economic Analysis of EIP-1559**
- **Authors:** Tim Roughgarden
- **Venue:** ACM Conference on Economics and Computation (EC), 2021
- **URL:** https://timroughgarden.org/papers/eip1559.pdf
- **Abstract:** Economic analysis of Ethereum's EIP-1559 transaction fee mechanism, including variable-size blocks, history-dependent reserve price, and base fee burning
- **Related Talk:** https://www.youtube.com/watch?v=ndNyx-Oj9Wk
- **Relevance:** ⭐⭐⭐⭐⭐ - Essential for blockchain fee market design

**Transaction Fee Mechanism Design**
- **Authors:** Tim Roughgarden
- **Venue:** ACM SIGecom Exchanges, 2021
- **URL:** https://arxiv.org/abs/2106.01340
- **Abstract:** Broader treatment of transaction fee mechanism design principles

### Byzantine Fault Tolerance

**Byzantine Generals in the Permissionless Setting**
- **Authors:** Andrew Lewis-Pye, Tim Roughgarden
- **Year:** 2021
- **URL:** https://arxiv.org/pdf/2101.07095.pdf
- **Abstract:** Characterization of permissionless consensus and its relationship to classical Byzantine agreement

**Permissionless Consensus**
- **Authors:** Andrew Lewis-Pye, Tim Roughgarden
- **Year:** 2023
- **URL:** https://arxiv.org/pdf/2304.14701
- **Abstract:** Comprehensive treatment of permissionless consensus protocols

**The Economic Limits of Permissionless Consensus**
- **Authors:** Eric Budish, Andrew Lewis-Pye, Tim Roughgarden
- **Year:** 2024
- **URL:** Check author websites
- **Abstract:** Economic analysis of security bounds in permissionless systems

### Mechanism Design - Combinatorial Auctions

**Combinatorial Auctions with Restricted Complements**
- **Authors:** Ittai Abraham, Moshe Babaioff, Shaddin Dughmi, Tim Roughgarden
- **Venue:** EC 2012
- **URL:** https://arxiv.org/abs/1205.4104
- **Abstract:** Model for valuations with complements that enables mechanism design inroads

**Optimal Mechanisms for Combinatorial Auctions**
- **Authors:** Ittai Abraham, Moshe Babaioff, Shaddin Dughmi, Tim Roughgarden
- **Venue:** Journal of the ACM, 2016
- **URL:** https://dl.acm.org/doi/10.1145/2908735
- **Abstract:** Convex rounding framework for computationally tractable truthful mechanisms

**Lectures on Combinatorial Auctions**
- **Author:** Tim Roughgarden
- **Year:** 2008
- **URL:** https://timroughgarden.org/f05/ca.pdf
- **Type:** Comprehensive lecture notes

### Price of Anarchy

**The Price of Anarchy in Games of Incomplete Information**
- **Author:** Tim Roughgarden
- **Venue:** Multiple (STOC, EC)
- **URL:** http://www.timroughgarden.org/papers/inc.pdf
- **Abstract:** General theory for bounding price of anarchy in Bayesian games

**The Price of Anarchy is Independent of the Network Topology**
- **Authors:** Multiple including Tim Roughgarden
- **URL:** https://theory.stanford.edu/~tim/papers/indep.pdf
- **Abstract:** Fundamental result on robustness of price of anarchy bounds

**Intrinsic Robustness of the Price of Anarchy**
- **Authors:** Tim Roughgarden
- **Venue:** STOC 2009, JACM 2015
- **URL:** https://www.timroughgarden.org/papers/robust_cacm.pdf
- **Abstract:** Connection between worst-case and smoothed/Bayesian price of anarchy

**Weighted Congestion Games: Price of Anarchy and Universal Worst-Case Examples**
- **URL:** https://timroughgarden.org/papers/wcg.pdf
- **Abstract:** Characterization of price of anarchy as function of cost functions

### Proof-of-Stake and Blockchain Security

**On the Instability of Bitcoin Without the Block Reward**
- **Authors:** Miles Carlsten, Harry Kalodner, S. Matthew Weinberg, Arvind Narayanan
- **Venue:** CCS 2016
- **URL:** https://www.cs.princeton.edu/~arvindn/publications/mining_CCS.pdf
- **Abstract:** Analysis of Bitcoin security when block rewards diminish

**Majority is not Enough: Bitcoin Mining is Vulnerable**
- **Authors:** Ittay Eyal, Emin Gün Sirer
- **Venue:** Financial Cryptography 2014
- **URL:** https://www.cs.cornell.edu/~ie53/publications/btcProcFC.pdf
- **Abstract:** Selfish mining attack on Bitcoin

### Historical/Foundational Papers Referenced

**The Byzantine Generals Problem**
- **Authors:** Lamport, Shostak, Pease
- **Venue:** TOPLAS, 1982
- **URL:** https://lamport.azurewebsites.net/pubs/byz.pdf

**Impossibility of Distributed Consensus with One Faulty Process**
- **Authors:** Fischer, Lynch, Paterson
- **Venue:** JACM, 1985 (FLP Theorem)
- **URL:** https://groups.csail.mit.edu/tds/papers/Lynch/jacm85.pdf

**Consensus in the Presence of Partial Synchrony**
- **Authors:** Dwork, Lynch, Stockmeyer
- **Venue:** JACM, 1988
- **URL:** https://groups.csail.mit.edu/tds/papers/Lynch/jacm88.pdf

**The latest gossip on BFT consensus (Tendermint)**
- **Authors:** Buchman, Kwon, Milosevic
- **Year:** 2018
- **URL:** https://arxiv.org/abs/1807.04938

---

## Lecture Notes Repository

### Complete Course Notes Available at: https://timroughgarden.org/notes.html

#### Foundations of Blockchains (COMS 6998, 2021)
- **Format:** PDF lecture notes (rough drafts)
- **Status:** Lectures 1-9 available, L10 partial
- **Topics Covered:**
  - L1: Introduction and Overview
  - L2: Dolev-Strong Protocol
  - L3: Simulation and Indistinguishability
  - L4-5: FLP Impossibility Theorem
  - L6: Partially Synchronous Model and CAP Principle
  - L7: Tendermint Protocol
  - L8: Longest-Chain Consensus
  - L9: Permissionless Consensus and Proof-of-Work
  - L10: Selfish Mining (incomplete)

#### Algorithmic Game Theory (CS364A, 2013)
- **Format:** Complete PDF set
- **URL:** https://timroughgarden.org/f13/f13.pdf
- **Also Available:** As book "Twenty Lectures on Algorithmic Game Theory"
- **All 20 Lectures:** Fully documented with proofs and examples

#### Advanced Mechanism Design (CS364B, 2014)
- **Format:** Individual lecture PDFs
- **URL Base:** https://timroughgarden.org/w14/l/
- **Lectures:** l21.pdf through l40.pdf
- **Topics:** Ex post mechanisms, Walrasian equilibria, gross substitutes, etc.

#### Modern Algorithmic Toolbox (CS168, 2017)
- **Format:** Individual lecture PDFs
- **URL Base:** https://timroughgarden.org/s17/l/
- **19 Lectures:** Consistent hashing through expander codes

#### A Second Course in Algorithms (CS261, 2016)
- **Format:** Individual lecture PDFs
- **URL Base:** https://timroughgarden.org/w16/l/
- **20 Lectures:** Maximum flow through beating brute-force search

#### Beyond Worst-Case Analysis (CS264, 2014/2017)
- **Format:** Individual lecture PDFs
- **Two Versions:** 2014 full set, 2017 updated lectures
- **URL Base:** https://timroughgarden.org/f14/l/ and https://timroughgarden.org/w17/l/

#### Incentives in Computer Science (CS269I, 2016)
- **Format:** Individual lecture PDFs
- **URL Base:** https://timroughgarden.org/f16/l/
- **Topics:** Stable matching, voting, auctions, VCG, asymmetric information

#### Communication Complexity (CS369E, 2015)
- **Format:** Combined and individual lecture PDFs
- **URL:** https://timroughgarden.org/w15/l/w15.pdf
- **8 Lectures:** Data streams through property testing

---

## Quick Access: Most Relevant for Mechanism Design & RSM

### Top Priority Resources:

1. **Foundations of Blockchains (Columbia 2021)**
   - YouTube: https://www.youtube.com/playlist?list=PLEGCF-WLh2RLOHv_xUGLqRts_9JxrckiA
   - Course: https://timroughgarden.github.io/fob21/
   - **Why:** Most comprehensive treatment of RSM, BFT, and consensus

2. **Algorithmic Game Theory (Stanford 2013)**
   - YouTube: https://www.youtube.com/playlist?list=PLEGCF-WLh2RJBqmxvZ0_ie-mleCFhi2N4
   - Notes: https://timroughgarden.org/f13/f13.html
   - **Why:** Foundational mechanism design theory

3. **Advanced Mechanism Design (Stanford 2014)**
   - YouTube: https://www.youtube.com/playlist?list=PLEGCF-WLh2RI77PL4gwLld_OU9Zh3TCX9
   - Notes: https://timroughgarden.org/w14/w14.html
   - **Why:** Advanced techniques for combinatorial auctions

4. **Science of Blockchains (Columbia 2025 - Current)**
   - Course: https://timroughgarden.org/s25/
   - **Why:** Most up-to-date consensus protocol coverage

5. **Transaction Fee Mechanism Design Paper**
   - PDF: https://timroughgarden.org/papers/eip1559.pdf
   - **Why:** Applied mechanism design in blockchain context

### Key Lecture Sequences:

**For Byzantine Fault Tolerance:**
- Foundations of Blockchains L1-L7 (Dolev-Strong → Tendermint)
- L8-L9 (Longest-chain and permissionless consensus)

**For Mechanism Design:**
- CS364A L1-L9 (Mechanism design basics through VCG)
- CS364B L1-L6 (Ascending auctions through gross substitutes)

**For Price of Anarchy:**
- CS364A L11-L15 (Selfish routing through equilibrium concepts)

---

## Additional Resources

### Supplementary Reading
- **Decentralized Thoughts Blog:** https://decentralizedthoughts.github.io/
- **Elaine Shi's Book:** "Foundations of Distributed Consensus and Blockchains"
- **Andrew Lewis-Pye:** "Consensus in 50 pages" (rough draft)
- **James Aspnes:** "Notes on Theory of Distributed Systems"

### Related Courses (Other Instructors)
- **David Tse (Stanford):** Internet-Scale Consensus in the Blockchain Era
- **Jason Hartline (Northwestern):** "Lectures on Optimal Mechanism Design"

### Tools for Further Exploration
- **GitHub Repository:** https://github.com/timroughgarden/fob21
- **Course Website Archive:** https://timroughgarden.org/teaching.html
- **Complete Papers List:** https://timroughgarden.org/ (homepage)

---

## Citation Information

**Author:** Tim Roughgarden
- **Current Position:** Professor, Computer Science Department, Columbia University
- **Previous Position:** Professor, Stanford University (2004-2018)
- **Email:** tr@cs.columbia.edu
- **Homepage:** https://timroughgarden.org/
- **YouTube Channel:** https://www.youtube.com/channel/UCcH4Ga14Y4ELFKrEYM1vXCg

**Areas of Expertise:**
- Algorithmic game theory
- Mechanism design
- Byzantine fault tolerance and distributed consensus
- Blockchain protocol design
- Price of anarchy
- Computational complexity in economics

---

## Usage Notes for Knowledge Indexing

**Video Duration Patterns:**
- Most lectures: 60-75 minutes
- Tutorial talks: 90-120 minutes
- Short course videos: 15-30 minutes

**Content Difficulty Levels:**
- **Accessible:** Incentives in CS, Public lectures
- **Intermediate:** CS364A (Algorithmic Game Theory)
- **Advanced:** CS364B (Advanced Mechanism Design), Foundations of Blockchains
- **Specialized:** Beyond Worst-Case Analysis, Communication Complexity

**Lecture Note Quality:**
- **Complete/Published:** CS364A (as book), CS261, CS364B
- **Draft/In Progress:** Foundations of Blockchains (L1-9)
- **Comprehensive:** CS168, CS264, CS269I

**Update Frequency:**
- Historical courses: Content stable (2013-2018)
- Current course (S25): Active updates weekly
- Papers: Check https://timroughgarden.org/ for latest publications

---

## Index Compiled By
Agent: Claude (Anthropic)
Date: December 21, 2025
Source: Comprehensive web search and analysis of Tim Roughgarden's educational materials
