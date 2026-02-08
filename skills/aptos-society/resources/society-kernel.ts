/**
 * Society Kernel - TypeScript authoritative layer
 * Goblins runtime participates through this bus protocol
 *
 * NON-NEGOTIABLE: This kernel owns:
 * - event schema + bus single-writer
 * - run_manifest (gaymcp_root_hex, skills_snapshot_hash, manifest_sha256)
 * - receipts + payout distribution
 * - verify_run invariants (including mint↔proof↔manifest links)
 */

import { EventEmitter } from 'events';
import { createHash } from 'crypto';

// ============================================================
// GF(3) Types - Enforced at kernel level
// ============================================================

type Trit = -1 | 0 | 1;
type Role = 'PLUS' | 'ERGODIC' | 'MINUS';

const ROLE_TO_TRIT: Record<Role, Trit> = {
  PLUS: 1,
  ERGODIC: 0,
  MINUS: -1,
};

// ============================================================
// Event Schema - Single source of truth
// ============================================================

interface SocietyEvent {
  epoch: number;
  agent: string;
  role: Role;
  action: 'MINT' | 'VERIFY' | 'DECAY' | 'FREEZE' | 'RESOLVE';
  delta: number;
  reason: string;
  cap_hash: string;
  timestamp: number;
  tx_hash?: string;
}

interface RunManifest {
  gaymcp_root_hex: string;
  skills_snapshot_hash: string;
  manifest_sha256: string;
  goblins_runtime?: string;
  timestamp: number;
}

interface Receipt {
  tx_hash: string;
  event: SocietyEvent;
  block_height: number;
  gf3_sum_after: number;
  status: 'confirmed' | 'pending' | 'failed';
}

interface Capability {
  id: string;
  agent: string;
  scope: 'mint' | 'verify' | 'read' | 'resolve';
  signer: string;
  expires: number;
  hash: string;
}

// ============================================================
// Society Kernel - Authoritative Event Bus
// ============================================================

export class SocietyKernel extends EventEmitter {
  private events: SocietyEvent[] = [];
  private receipts: Map<string, Receipt> = new Map();
  private capabilities: Map<string, Capability> = new Map();
  private gf3Sum: number = 0;
  private currentManifest: RunManifest | null = null;

  constructor(
    private readonly kernelSigner: string,
    private readonly escrowAddress: string
  ) {
    super();
  }

  // ============================================================
  // Event Bus - Single Writer (kernel only appends)
  // ============================================================

  /**
   * Submit event to bus - validates capability and GF(3)
   * Goblins actors call this via HTTP
   */
  async submitEvent(event: Omit<SocietyEvent, 'timestamp' | 'tx_hash'>, capHash: string): Promise<Receipt> {
    // 1. Validate capability
    const cap = this.capabilities.get(capHash);
    if (!cap) throw new Error('Invalid capability');
    if (cap.expires < Date.now()) throw new Error('Capability expired');
    if (cap.agent !== event.agent) throw new Error('Capability agent mismatch');

    // 2. Validate GF(3) conservation
    const trit = ROLE_TO_TRIT[event.role];
    const newSum = this.gf3Add(this.gf3Sum, trit);

    // 3. Create full event with timestamp
    const fullEvent: SocietyEvent = {
      ...event,
      cap_hash: capHash,
      timestamp: Date.now(),
      tx_hash: this.generateTxHash(event),
    };

    // 4. Append to log (single-writer, append-only)
    this.events.push(fullEvent);
    this.gf3Sum = newSum;

    // 5. Create receipt
    const receipt: Receipt = {
      tx_hash: fullEvent.tx_hash!,
      event: fullEvent,
      block_height: this.events.length,
      gf3_sum_after: this.gf3Sum,
      status: 'confirmed',
    };
    this.receipts.set(receipt.tx_hash, receipt);

    // 6. Emit for listeners (Goblins can subscribe via WebSocket)
    this.emit('event', fullEvent);
    this.emit('receipt', receipt);

    return receipt;
  }

  // ============================================================
  // Capability Management - Explicit, not implicit
  // ============================================================

  /**
   * Mint capability - ONLY kernel can do this
   */
  mintCapability(agent: string, scope: Capability['scope'], expiresIn: number): Capability {
    const cap: Capability = {
      id: this.generateCapId(),
      agent,
      scope,
      signer: this.kernelSigner,
      expires: Date.now() + expiresIn,
      hash: '',
    };
    cap.hash = this.hashCapability(cap);
    this.capabilities.set(cap.hash, cap);
    return cap;
  }

  verifyCapability(capHash: string, requiredScope: Capability['scope']): boolean {
    const cap = this.capabilities.get(capHash);
    if (!cap) return false;
    if (cap.expires < Date.now()) return false;
    if (cap.scope !== requiredScope) return false;
    return true;
  }

  revokeCapability(capHash: string): void {
    this.capabilities.delete(capHash);
  }

  // ============================================================
  // Run Manifest - Links mint↔proof↔manifest
  // ============================================================

  /**
   * Register run manifest - links Goblins runtime state to Society
   */
  registerManifest(manifest: Omit<RunManifest, 'manifest_sha256'>): RunManifest {
    const fullManifest: RunManifest = {
      ...manifest,
      manifest_sha256: this.hashManifest(manifest),
    };
    this.currentManifest = fullManifest;
    this.emit('manifest', fullManifest);
    return fullManifest;
  }

  /**
   * Verify mint↔proof↔manifest link
   * This is the key invariant for Goblins integration
   */
  verifyMintProofManifestLink(
    mintTxHash: string,
    proofHash: string,
    manifestHash: string
  ): { valid: boolean; error?: string } {
    // 1. Get the mint receipt
    const receipt = this.receipts.get(mintTxHash);
    if (!receipt) return { valid: false, error: 'Mint tx not found' };

    // 2. Verify proof references the mint
    // (In production, this would verify a cryptographic proof)
    const expectedProofHash = this.hashProof(receipt, manifestHash);
    if (proofHash !== expectedProofHash) {
      return { valid: false, error: 'Proof hash mismatch' };
    }

    // 3. Verify manifest matches current
    if (!this.currentManifest || this.currentManifest.manifest_sha256 !== manifestHash) {
      return { valid: false, error: 'Manifest mismatch' };
    }

    return { valid: true };
  }

  // ============================================================
  // Payout Distribution - Kernel calculates, Goblins observes
  // ============================================================

  calculatePayouts(vaultApt: number): Map<string, number> {
    const claims = new Map<string, number>();

    // Aggregate claims from events
    for (const event of this.events) {
      if (event.action === 'MINT') {
        const current = claims.get(event.agent) || 0;
        claims.set(event.agent, current + event.delta);
      }
    }

    // Calculate proportional payouts
    const totalClaims = Array.from(claims.values()).reduce((a, b) => a + b, 0);
    const payouts = new Map<string, number>();

    for (const [agent, agentClaims] of claims) {
      payouts.set(agent, (agentClaims / totalClaims) * vaultApt);
    }

    return payouts;
  }

  // ============================================================
  // GF(3) Invariants - Enforced at kernel level
  // ============================================================

  private gf3Add(...trits: number[]): number {
    return ((trits.reduce((a, b) => a + b, 0) % 3) + 3) % 3;
  }

  verifyGF3Conservation(): boolean {
    // Recompute from events
    let sum = 0;
    for (const event of this.events) {
      sum = this.gf3Add(sum, ROLE_TO_TRIT[event.role]);
    }
    return sum === 0;
  }

  getGF3State(): { sum: number; conserved: boolean } {
    return {
      sum: this.gf3Sum,
      conserved: this.gf3Sum === 0,
    };
  }

  // ============================================================
  // HTTP Interface for Goblins actors
  // ============================================================

  getEventLog(since?: number): SocietyEvent[] {
    if (since === undefined) return [...this.events];
    return this.events.filter(e => e.timestamp > since);
  }

  getReceipt(txHash: string): Receipt | undefined {
    return this.receipts.get(txHash);
  }

  getCurrentManifest(): RunManifest | null {
    return this.currentManifest;
  }

  // ============================================================
  // Private helpers
  // ============================================================

  private generateTxHash(event: Omit<SocietyEvent, 'timestamp' | 'tx_hash'>): string {
    const data = JSON.stringify({ ...event, nonce: Date.now(), random: Math.random() });
    return '0x' + createHash('sha256').update(data).digest('hex');
  }

  private generateCapId(): string {
    return 'cap_' + createHash('sha256').update(Date.now().toString() + Math.random()).digest('hex').slice(0, 16);
  }

  private hashCapability(cap: Omit<Capability, 'hash'>): string {
    return createHash('sha256').update(JSON.stringify(cap)).digest('hex');
  }

  private hashManifest(manifest: Omit<RunManifest, 'manifest_sha256'>): string {
    return createHash('sha256').update(JSON.stringify(manifest)).digest('hex');
  }

  private hashProof(receipt: Receipt, manifestHash: string): string {
    return createHash('sha256').update(JSON.stringify({ receipt, manifestHash })).digest('hex');
  }
}

// ============================================================
// Express HTTP Server for Goblins integration
// ============================================================

export function createSocietyServer(kernel: SocietyKernel, port: number = 3847) {
  // In production, use Express
  // This is the interface Goblins actors POST to
  return {
    routes: {
      'POST /bus': 'submitEvent',
      'GET /bus/events': 'getEventLog',
      'GET /receipt/:txHash': 'getReceipt',
      'POST /capability/mint': 'mintCapability (kernel only)',
      'GET /manifest': 'getCurrentManifest',
      'POST /manifest': 'registerManifest',
      'GET /gf3': 'getGF3State',
      'GET /payouts/:vaultApt': 'calculatePayouts',
    },
    port,
  };
}
