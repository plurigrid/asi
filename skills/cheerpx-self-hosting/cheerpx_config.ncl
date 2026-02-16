# ═══════════════════════════════════════════════════════════════════════════
# CheerpX Self-Hosting Configuration
# x86 → WebAssembly virtualization with SPI guarantees
# ═══════════════════════════════════════════════════════════════════════════

let GAMMA = 137.5077640500378 in  # Golden angle for SPI

# ═══════════════════════════════════════════════════════════════════════════
# Core CheerpX Configuration
# ═══════════════════════════════════════════════════════════════════════════

let MemoryConfig = {
  initial_mb | std.number.Nat | default = 512,
  max_mb | std.number.Nat | default = 4096,
  wasm_pages | std.number.Nat | default = 8192,  # 512MB in WASM pages
} in

let FilesystemMount = {
  type | [| 'ext2, 'overlay, 'devs, 'proc, 'tmp |],
  path | String,
  url | optional | String,  # For ext2 mounts
  size_mb | optional | std.number.Nat,  # For tmp mounts
} in

let NetworkConfig = {
  enabled | Bool | default = true,
  tailscale | Bool | default = false,
  headscale_server | optional | String,
  cors_proxy | optional | String,
} in

let CheerpXConfig = {
  # Versioning
  version | String | default = "1.0.6",
  cdn_url | String | default = "https://cxrtnc.leaningtech.com",

  # Memory
  memory | MemoryConfig | default = {},

  # Filesystem mounts
  mounts | Array FilesystemMount | default = [
    { type = 'ext2, path = "/", url = "https://example.com/rootfs.ext2" },
    { type = 'devs, path = "/dev" },
    { type = 'proc, path = "/proc" },
    { type = 'tmp, path = "/tmp", size_mb = 256 },
  ],

  # Networking
  network | NetworkConfig | default = {},

  # SPI seed for deterministic behavior
  spi_seed | std.number.Nat,
} in

# ═══════════════════════════════════════════════════════════════════════════
# GF(3) Execution Tiers
# ═══════════════════════════════════════════════════════════════════════════

let ExecutionTier = {
  browser = {
    name = "browser",
    trit = -1,
    description = "CheerpX/WASM - Untrusted, sandboxed",
    latency_ms = 100,
    throughput = 0.1,  # Relative to native
  },

  edge = {
    name = "edge",
    trit = 0,
    description = "BrowserPod/Cloudflare - Semi-trusted",
    latency_ms = 20,
    throughput = 0.5,
  },

  server = {
    name = "server",
    trit = 1,
    description = "Native x86 - Trusted, full speed",
    latency_ms = 5,
    throughput = 1.0,
  },

  # GF(3) conservation check
  sum = browser.trit + edge.trit + server.trit,  # = 0
} in

# ═══════════════════════════════════════════════════════════════════════════
# Self-Hosting Profiles
# ═══════════════════════════════════════════════════════════════════════════

let Profiles = {
  # Minimal: Just enough to run Nickel
  minimal = CheerpXConfig & {
    memory = { initial_mb = 256, max_mb = 512 },
    mounts = [
      { type = 'ext2, path = "/", url = "./rootfs-minimal.ext2" },
      { type = 'devs, path = "/dev" },
    ],
    spi_seed = 0x4D494E49,  # "MINI"
  },

  # Development: Full toolchain
  development = CheerpXConfig & {
    memory = { initial_mb = 1024, max_mb = 4096 },
    mounts = [
      { type = 'ext2, path = "/", url = "./rootfs-dev.ext2" },
      { type = 'devs, path = "/dev" },
      { type = 'proc, path = "/proc" },
      { type = 'tmp, path = "/tmp", size_mb = 512 },
      { type = 'overlay, path = "/home", url = "./home-overlay.ext2" },
    ],
    network = { enabled = true, tailscale = true },
    spi_seed = 0x44455620,  # "DEV "
  },

  # Goblins: Scheme + capability actors
  goblins = CheerpXConfig & {
    memory = { initial_mb = 512, max_mb = 2048 },
    mounts = [
      { type = 'ext2, path = "/", url = "./rootfs-guile.ext2" },
      { type = 'devs, path = "/dev" },
      { type = 'overlay, path = "/goblins", url = "./goblins-modules.ext2" },
    ],
    spi_seed = 0x474F424C,  # "GOBL"
  },

  # Julia: Gay.jl SPI verification
  julia_spi = CheerpXConfig & {
    memory = { initial_mb = 2048, max_mb = 8192 },
    mounts = [
      { type = 'ext2, path = "/", url = "./rootfs-julia.ext2" },
      { type = 'devs, path = "/dev" },
      { type = 'proc, path = "/proc" },
    ],
    spi_seed = 20251226,  # Standard Gay.jl seed
  },
} in

# ═══════════════════════════════════════════════════════════════════════════
# HTML/JS Generation
# ═══════════════════════════════════════════════════════════════════════════

let generate_mount_js = fun mount =>
  let type_str = std.string.from_enum mount.type in
  if mount.type == 'ext2 then
    "{ type: \"ext2\", path: \"" ++ mount.path ++ "\", url: \"" ++ (mount.url) ++ "\" }"
  else if mount.type == 'tmp then
    "{ type: \"tmpfs\", path: \"" ++ mount.path ++ "\" }"
  else
    "{ type: \"" ++ type_str ++ "\", path: \"" ++ mount.path ++ "\" }"
in

let generate_js = fun config =>
  let mounts_js = std.array.map generate_mount_js config.mounts in
  "const cx = await CheerpX.Linux.create({\n"
  ++ "  mounts: [\n    "
  ++ std.string.join ",\n    " mounts_js
  ++ "\n  ],\n"
  ++ "});\n"
  ++ "// SPI seed: " ++ std.string.from_number config.spi_seed ++ "\n"
in

# ═══════════════════════════════════════════════════════════════════════════
# SPI Color for Build Artifacts
# ═══════════════════════════════════════════════════════════════════════════

let spi_color = fun seed index =>
  let phi = 1.6180339887498949 in
  let base = (seed * phi) - std.number.floor (seed * phi) in
  let hue = (base * 360 + (index - 1) * GAMMA) in
  hue - 360 * std.number.floor (hue / 360)
in

# ═══════════════════════════════════════════════════════════════════════════
# Export
# ═══════════════════════════════════════════════════════════════════════════

{
  # Types
  CheerpXConfig,
  MemoryConfig,
  FilesystemMount,
  NetworkConfig,
  ExecutionTier,

  # Profiles
  profiles = Profiles,

  # Code generation
  generate_js,

  # SPI
  spi_color,
  GAMMA,

  # Verification
  test = {
    gf3_conserved = ExecutionTier.sum == 0,
    dev_js = generate_js Profiles.development,
    dev_color = spi_color Profiles.development.spi_seed 1,
    goblins_color = spi_color Profiles.goblins.spi_seed 1,
  },
}
