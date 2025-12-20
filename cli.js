#!/usr/bin/env node

const fs = require('fs');
const path = require('path');
const os = require('os');

// Version check
const NODE_VERSION = process.versions.node.split('.')[0];
if (parseInt(NODE_VERSION) < 14) {
  console.error(`Error: Node.js 14+ required (you have ${process.versions.node})`);
  process.exit(1);
}

const SKILLS_DIR = path.join(__dirname, 'skills');
const CONFIG_FILE = path.join(os.homedir(), '.agent-skills.json');
const MAX_SKILL_SIZE = 50 * 1024 * 1024; // 50MB limit

// Agent-specific skill directories
const AGENT_PATHS = {
  claude: path.join(os.homedir(), '.claude', 'skills'),
  cursor: path.join(process.cwd(), '.cursor', 'skills'),
  amp: path.join(os.homedir(), '.amp', 'skills'),
  vscode: path.join(process.cwd(), '.github', 'skills'),
  copilot: path.join(process.cwd(), '.github', 'skills'),
  project: path.join(process.cwd(), '.skills'),
  goose: path.join(os.homedir(), '.config', 'goose', 'skills'),
  opencode: path.join(os.homedir(), '.opencode', 'skills'),
  codex: path.join(os.homedir(), '.codex', 'skills'),
  letta: path.join(os.homedir(), '.letta', 'skills'),
};

const colors = {
  reset: '\x1b[0m',
  bold: '\x1b[1m',
  dim: '\x1b[2m',
  green: '\x1b[32m',
  yellow: '\x1b[33m',
  blue: '\x1b[34m',
  cyan: '\x1b[36m',
  red: '\x1b[31m',
  magenta: '\x1b[35m'
};

function log(msg) { console.log(msg); }
function success(msg) { console.log(`${colors.green}${colors.bold}${msg}${colors.reset}`); }
function info(msg) { console.log(`${colors.cyan}${msg}${colors.reset}`); }
function warn(msg) { console.log(`${colors.yellow}${msg}${colors.reset}`); }
function error(msg) { console.log(`${colors.red}${msg}${colors.reset}`); }

// ============ CONFIG FILE SUPPORT ============

function loadConfig() {
  try {
    if (fs.existsSync(CONFIG_FILE)) {
      return JSON.parse(fs.readFileSync(CONFIG_FILE, 'utf8'));
    }
  } catch (e) {
    warn(`Warning: Could not load config file: ${e.message}`);
  }
  return { defaultAgent: 'claude', autoUpdate: false };
}

function saveConfig(config) {
  try {
    fs.writeFileSync(CONFIG_FILE, JSON.stringify(config, null, 2));
    return true;
  } catch (e) {
    error(`Failed to save config: ${e.message}`);
    return false;
  }
}

// ============ SECURITY VALIDATION ============

function validateSkillName(name) {
  if (!name || typeof name !== 'string') {
    throw new Error('Skill name is required');
  }

  // Check for path traversal attacks
  if (name.includes('..') || name.includes('/') || name.includes('\\')) {
    throw new Error(`Invalid skill name: "${name}" contains path characters`);
  }

  // Check for valid characters (lowercase, numbers, hyphens)
  if (!/^[a-z0-9][a-z0-9-]*[a-z0-9]$|^[a-z0-9]$/.test(name)) {
    throw new Error(`Invalid skill name: "${name}" must be lowercase alphanumeric with hyphens`);
  }

  // Check length
  if (name.length > 64) {
    throw new Error(`Skill name too long: ${name.length} > 64 characters`);
  }

  return true;
}

// ============ ERROR-SAFE JSON LOADING ============

function loadSkillsJson() {
  const skillsJsonPath = path.join(__dirname, 'skills.json');

  if (!fs.existsSync(skillsJsonPath)) {
    warn('skills.json not found, using empty list');
    return { skills: [] };
  }

  try {
    const content = fs.readFileSync(skillsJsonPath, 'utf8');
    const data = JSON.parse(content);

    if (!data.skills || !Array.isArray(data.skills)) {
      throw new Error('Invalid skills.json: missing skills array');
    }

    return data;
  } catch (e) {
    if (e instanceof SyntaxError) {
      error(`Failed to parse skills.json: ${e.message}`);
    } else {
      error(`Failed to load skills.json: ${e.message}`);
    }
    process.exit(1);
  }
}

function getAvailableSkills() {
  if (!fs.existsSync(SKILLS_DIR)) return [];

  try {
    return fs.readdirSync(SKILLS_DIR).filter(name => {
      const skillPath = path.join(SKILLS_DIR, name);
      return fs.statSync(skillPath).isDirectory() &&
             fs.existsSync(path.join(skillPath, 'SKILL.md'));
    });
  } catch (e) {
    error(`Failed to read skills directory: ${e.message}`);
    return [];
  }
}

// ============ ARGUMENT PARSING ============

function parseArgs(args) {
  const config = loadConfig();
  const result = {
    command: null,
    param: null,
    agent: config.defaultAgent || 'claude',
    installed: false,
    all: false,
    dryRun: false,
    tags: null,
    category: null
  };

  const validAgents = Object.keys(AGENT_PATHS);

  for (let i = 0; i < args.length; i++) {
    const arg = args[i];

    if (arg === '--agent' || arg === '-a') {
      let agentValue = args[i + 1] || 'claude';
      agentValue = agentValue.replace(/^-+/, '');
      result.agent = validAgents.includes(agentValue) ? agentValue : 'claude';
      i++;
    }
    else if (arg === '--installed' || arg === '-i') {
      result.installed = true;
    }
    else if (arg === '--all') {
      result.all = true;
    }
    else if (arg === '--dry-run' || arg === '-n') {
      result.dryRun = true;
    }
    else if (arg === '--tag' || arg === '-t') {
      result.tags = args[i + 1];
      i++;
    }
    else if (arg === '--category' || arg === '-c') {
      result.category = args[i + 1];
      i++;
    }
    else if (arg.startsWith('--')) {
      const potentialAgent = arg.replace(/^--/, '');
      if (validAgents.includes(potentialAgent)) {
        result.agent = potentialAgent;
      } else if (!result.command) {
        result.command = arg;
      }
    }
    else if (!result.command) {
      result.command = args[i];
    } else if (!result.param) {
      result.param = args[i];
    }
  }

  return result;
}

// ============ SAFE FILE OPERATIONS ============

function copyDir(src, dest, currentSize = { total: 0 }) {
  try {
    if (fs.existsSync(dest)) {
      fs.rmSync(dest, { recursive: true });
    }
    fs.mkdirSync(dest, { recursive: true });

    const entries = fs.readdirSync(src, { withFileTypes: true });

    for (const entry of entries) {
      const srcPath = path.join(src, entry.name);
      const destPath = path.join(dest, entry.name);

      if (entry.isDirectory()) {
        copyDir(srcPath, destPath, currentSize);
      } else {
        const stat = fs.statSync(srcPath);
        currentSize.total += stat.size;

        if (currentSize.total > MAX_SKILL_SIZE) {
          throw new Error(`Skill exceeds maximum size of ${MAX_SKILL_SIZE / 1024 / 1024}MB`);
        }

        fs.copyFileSync(srcPath, destPath);
      }
    }
  } catch (e) {
    // Clean up partial install on failure
    if (fs.existsSync(dest)) {
      try { fs.rmSync(dest, { recursive: true }); } catch {}
    }
    throw e;
  }
}

function getDirectorySize(dir) {
  let size = 0;
  try {
    const entries = fs.readdirSync(dir, { withFileTypes: true });
    for (const entry of entries) {
      const fullPath = path.join(dir, entry.name);
      if (entry.isDirectory()) {
        size += getDirectorySize(fullPath);
      } else {
        size += fs.statSync(fullPath).size;
      }
    }
  } catch {}
  return size;
}

// ============ CORE COMMANDS ============

function installSkill(skillName, agent = 'claude', dryRun = false) {
  try {
    validateSkillName(skillName);
  } catch (e) {
    error(e.message);
    return false;
  }

  const sourcePath = path.join(SKILLS_DIR, skillName);

  if (!fs.existsSync(sourcePath)) {
    error(`Skill "${skillName}" not found.`);

    // Suggest similar skills
    const available = getAvailableSkills();
    const similar = available.filter(s =>
      s.includes(skillName) || skillName.includes(s) ||
      levenshteinDistance(s, skillName) <= 3
    ).slice(0, 3);

    if (similar.length > 0) {
      log(`\n${colors.dim}Did you mean: ${similar.join(', ')}?${colors.reset}`);
    }
    return false;
  }

  const destDir = AGENT_PATHS[agent] || AGENT_PATHS.claude;
  const destPath = path.join(destDir, skillName);
  const skillSize = getDirectorySize(sourcePath);

  if (dryRun) {
    log(`\n${colors.bold}Dry Run${colors.reset} (no changes made)\n`);
    info(`Would install: ${skillName}`);
    info(`Agent: ${agent}`);
    info(`Source: ${sourcePath}`);
    info(`Destination: ${destPath}`);
    info(`Size: ${(skillSize / 1024).toFixed(1)} KB`);

    if (fs.existsSync(destPath)) {
      warn(`Note: Would overwrite existing installation`);
    }
    return true;
  }

  try {
    if (!fs.existsSync(destDir)) {
      fs.mkdirSync(destDir, { recursive: true });
    }

    copyDir(sourcePath, destPath);

    success(`\nInstalled: ${skillName}`);
    info(`Agent: ${agent}`);
    info(`Location: ${destPath}`);
    info(`Size: ${(skillSize / 1024).toFixed(1)} KB`);

    log('');
    showAgentInstructions(agent, skillName, destPath);

    return true;
  } catch (e) {
    error(`Failed to install skill: ${e.message}`);
    return false;
  }
}

function showAgentInstructions(agent, skillName, destPath) {
  const instructions = {
    claude: `The skill is now available in Claude Code.\nJust mention "${skillName}" in your prompt and Claude will use it.`,
    cursor: `The skill is installed in your project's .cursor/skills/ folder.\nCursor will automatically detect and use it.`,
    amp: `The skill is now available in Amp.`,
    codex: `The skill is now available in Codex.`,
    vscode: `The skill is installed in your project's .github/skills/ folder.`,
    copilot: `The skill is installed in your project's .github/skills/ folder.`,
    project: `The skill is installed in .skills/ in your current directory.\nThis makes it portable across all compatible agents.`,
    letta: `The skill is now available in Letta.`,
    goose: `The skill is now available in Goose.`,
    opencode: `The skill is now available in OpenCode.`
  };

  log(`${colors.dim}${instructions[agent] || `The skill is ready to use with ${agent}.`}${colors.reset}`);
}

function uninstallSkill(skillName, agent = 'claude', dryRun = false) {
  try {
    validateSkillName(skillName);
  } catch (e) {
    error(e.message);
    return false;
  }

  const destDir = AGENT_PATHS[agent] || AGENT_PATHS.claude;
  const skillPath = path.join(destDir, skillName);

  if (!fs.existsSync(skillPath)) {
    error(`Skill "${skillName}" is not installed for ${agent}.`);
    log(`\nInstalled skills for ${agent}:`);
    listInstalledSkills(agent);
    return false;
  }

  if (dryRun) {
    log(`\n${colors.bold}Dry Run${colors.reset} (no changes made)\n`);
    info(`Would uninstall: ${skillName}`);
    info(`Agent: ${agent}`);
    info(`Path: ${skillPath}`);
    return true;
  }

  try {
    fs.rmSync(skillPath, { recursive: true });
    success(`\nUninstalled: ${skillName}`);
    info(`Agent: ${agent}`);
    info(`Removed from: ${skillPath}`);
    return true;
  } catch (e) {
    error(`Failed to uninstall skill: ${e.message}`);
    return false;
  }
}

function getInstalledSkills(agent = 'claude') {
  const destDir = AGENT_PATHS[agent] || AGENT_PATHS.claude;

  if (!fs.existsSync(destDir)) return [];

  try {
    return fs.readdirSync(destDir).filter(name => {
      const skillPath = path.join(destDir, name);
      return fs.statSync(skillPath).isDirectory() &&
             fs.existsSync(path.join(skillPath, 'SKILL.md'));
    });
  } catch (e) {
    return [];
  }
}

function listInstalledSkills(agent = 'claude') {
  const installed = getInstalledSkills(agent);
  const destDir = AGENT_PATHS[agent] || AGENT_PATHS.claude;
  const data = loadSkillsJson();

  if (installed.length === 0) {
    warn(`No skills installed for ${agent}`);
    info(`Location: ${destDir}`);
    return;
  }

  log(`\n${colors.bold}Installed Skills${colors.reset} (${installed.length} for ${agent})\n`);
  log(`${colors.dim}Location: ${destDir}${colors.reset}\n`);

  // Check for updates
  let updatesAvailable = 0;

  installed.forEach(name => {
    const skill = data.skills.find(s => s.name === name);
    const hasUpdate = skill && skill.lastUpdated && isUpdateAvailable(name, agent, skill.lastUpdated);

    if (hasUpdate) {
      updatesAvailable++;
      log(`  ${colors.green}${name}${colors.reset} ${colors.yellow}(update available)${colors.reset}`);
    } else {
      log(`  ${colors.green}${name}${colors.reset}`);
    }
  });

  if (updatesAvailable > 0) {
    log(`\n${colors.yellow}${updatesAvailable} update(s) available.${colors.reset}`);
    log(`${colors.dim}Run: npx ai-agent-skills update <name> --agent ${agent}${colors.reset}`);
  }

  log(`\n${colors.dim}Uninstall: npx ai-agent-skills uninstall <name> --agent ${agent}${colors.reset}`);
}

function isUpdateAvailable(skillName, agent, repoLastUpdated) {
  // Simple check based on file modification time
  const destDir = AGENT_PATHS[agent] || AGENT_PATHS.claude;
  const skillPath = path.join(destDir, skillName, 'SKILL.md');

  try {
    if (!fs.existsSync(skillPath)) return false;
    const stat = fs.statSync(skillPath);
    const installedTime = stat.mtime.getTime();
    const repoTime = new Date(repoLastUpdated).getTime();
    return repoTime > installedTime;
  } catch {
    return false;
  }
}

function updateSkill(skillName, agent = 'claude', dryRun = false) {
  try {
    validateSkillName(skillName);
  } catch (e) {
    error(e.message);
    return false;
  }

  const sourcePath = path.join(SKILLS_DIR, skillName);
  const destDir = AGENT_PATHS[agent] || AGENT_PATHS.claude;
  const destPath = path.join(destDir, skillName);

  if (!fs.existsSync(sourcePath)) {
    error(`Skill "${skillName}" not found in repository.`);
    return false;
  }

  if (!fs.existsSync(destPath)) {
    error(`Skill "${skillName}" is not installed for ${agent}.`);
    log(`\nUse 'install' to add it first.`);
    return false;
  }

  if (dryRun) {
    log(`\n${colors.bold}Dry Run${colors.reset} (no changes made)\n`);
    info(`Would update: ${skillName}`);
    info(`Agent: ${agent}`);
    info(`Path: ${destPath}`);
    return true;
  }

  try {
    fs.rmSync(destPath, { recursive: true });
    copyDir(sourcePath, destPath);

    success(`\nUpdated: ${skillName}`);
    info(`Agent: ${agent}`);
    info(`Location: ${destPath}`);
    return true;
  } catch (e) {
    error(`Failed to update skill: ${e.message}`);
    return false;
  }
}

function updateAllSkills(agent = 'claude', dryRun = false) {
  const installed = getInstalledSkills(agent);

  if (installed.length === 0) {
    warn(`No skills installed for ${agent}`);
    return;
  }

  log(`\n${colors.bold}Updating ${installed.length} skill(s)...${colors.reset}\n`);

  let updated = 0;
  let failed = 0;

  for (const skillName of installed) {
    if (updateSkill(skillName, agent, dryRun)) {
      updated++;
    } else {
      failed++;
    }
  }

  log(`\n${colors.bold}Summary:${colors.reset} ${updated} updated, ${failed} failed`);
}

// ============ LISTING AND SEARCH ============

function listSkills(category = null, tags = null) {
  const data = loadSkillsJson();
  let skills = data.skills || [];

  // Filter by category
  if (category) {
    skills = skills.filter(s => s.category === category.toLowerCase());
  }

  // Filter by tags
  if (tags) {
    const tagList = tags.split(',').map(t => t.trim().toLowerCase());
    skills = skills.filter(s =>
      s.tags && tagList.some(t => s.tags.includes(t))
    );
  }

  if (skills.length === 0) {
    if (category || tags) {
      warn(`No skills found matching filters`);
      log(`\n${colors.dim}Try: npx ai-agent-skills list${colors.reset}`);
    } else {
      warn('No skills found in skills.json');
    }
    return;
  }

  // Group by category
  const byCategory = {};
  skills.forEach(skill => {
    const cat = skill.category || 'other';
    if (!byCategory[cat]) byCategory[cat] = [];
    byCategory[cat].push(skill);
  });

  log(`\n${colors.bold}Available Skills${colors.reset} (${skills.length} total)\n`);

  Object.keys(byCategory).sort().forEach(cat => {
    log(`${colors.blue}${colors.bold}${cat.toUpperCase()}${colors.reset}`);
    byCategory[cat].forEach(skill => {
      const featured = skill.featured ? ` ${colors.yellow}*${colors.reset}` : '';
      const verified = skill.verified ? ` ${colors.green}✓${colors.reset}` : '';
      const tagStr = skill.tags && skill.tags.length > 0
        ? ` ${colors.dim}[${skill.tags.slice(0, 3).join(', ')}]${colors.reset}`
        : '';

      log(`  ${colors.green}${skill.name}${colors.reset}${featured}${verified}${tagStr}`);

      const desc = skill.description.length > 65
        ? skill.description.slice(0, 65) + '...'
        : skill.description;
      log(`    ${colors.dim}${desc}${colors.reset}`);
    });
    log('');
  });

  log(`${colors.dim}* = featured  ✓ = verified${colors.reset}`);
  log(`\nInstall: ${colors.cyan}npx ai-agent-skills install <skill-name>${colors.reset}`);
  log(`Filter:  ${colors.cyan}npx ai-agent-skills list --category development${colors.reset}`);
}

function searchSkills(query, category = null) {
  const data = loadSkillsJson();
  let skills = data.skills || [];
  const q = query.toLowerCase();

  // Filter by category first
  if (category) {
    skills = skills.filter(s => s.category === category.toLowerCase());
  }

  // Search in name, description, and tags
  const matches = skills.filter(s =>
    s.name.toLowerCase().includes(q) ||
    s.description.toLowerCase().includes(q) ||
    (s.category && s.category.toLowerCase().includes(q)) ||
    (s.tags && s.tags.some(t => t.toLowerCase().includes(q)))
  );

  if (matches.length === 0) {
    warn(`No skills found matching "${query}"`);

    // Suggest similar
    const allSkills = data.skills || [];
    const similar = allSkills
      .map(s => ({ name: s.name, dist: levenshteinDistance(s.name, query) }))
      .filter(s => s.dist <= 4)
      .sort((a, b) => a.dist - b.dist)
      .slice(0, 3);

    if (similar.length > 0) {
      log(`\n${colors.dim}Did you mean: ${similar.map(s => s.name).join(', ')}?${colors.reset}`);
    }
    return;
  }

  log(`\n${colors.bold}Search Results${colors.reset} (${matches.length} matches)\n`);

  matches.forEach(skill => {
    const tagStr = skill.tags && skill.tags.length > 0
      ? ` ${colors.magenta}[${skill.tags.slice(0, 3).join(', ')}]${colors.reset}`
      : '';

    log(`${colors.green}${skill.name}${colors.reset} ${colors.dim}[${skill.category}]${colors.reset}${tagStr}`);

    const desc = skill.description.length > 75
      ? skill.description.slice(0, 75) + '...'
      : skill.description;
    log(`  ${desc}`);
    log('');
  });
}

// Simple Levenshtein distance for "did you mean" suggestions
function levenshteinDistance(a, b) {
  if (!a.length) return b.length;
  if (!b.length) return a.length;

  const matrix = [];
  for (let i = 0; i <= b.length; i++) {
    matrix[i] = [i];
  }
  for (let j = 0; j <= a.length; j++) {
    matrix[0][j] = j;
  }

  for (let i = 1; i <= b.length; i++) {
    for (let j = 1; j <= a.length; j++) {
      if (b.charAt(i - 1) === a.charAt(j - 1)) {
        matrix[i][j] = matrix[i - 1][j - 1];
      } else {
        matrix[i][j] = Math.min(
          matrix[i - 1][j - 1] + 1,
          matrix[i][j - 1] + 1,
          matrix[i - 1][j] + 1
        );
      }
    }
  }

  return matrix[b.length][a.length];
}

// ============ INFO AND HELP ============

function showHelp() {
  log(`
${colors.bold}AI Agent Skills${colors.reset}
The universal skill repository for AI agents.

${colors.bold}Usage:${colors.reset}
  npx ai-agent-skills <command> [options]

${colors.bold}Commands:${colors.reset}
  ${colors.green}list${colors.reset}                             List all available skills
  ${colors.green}list --installed${colors.reset}                 List installed skills for an agent
  ${colors.green}list --category <cat>${colors.reset}            Filter by category
  ${colors.green}install <name>${colors.reset}                   Install a skill
  ${colors.green}install <name> --dry-run${colors.reset}         Preview installation without changes
  ${colors.green}uninstall <name>${colors.reset}                 Remove an installed skill
  ${colors.green}update <name>${colors.reset}                    Update an installed skill to latest
  ${colors.green}update --all${colors.reset}                     Update all installed skills
  ${colors.green}search <query>${colors.reset}                   Search skills by name, description, or tags
  ${colors.green}info <name>${colors.reset}                      Show skill details
  ${colors.green}config${colors.reset}                           Show/edit configuration
  ${colors.green}help${colors.reset}                             Show this help

${colors.bold}Options:${colors.reset}
  ${colors.cyan}--agent <name>${colors.reset}   Target agent (default: claude)
  ${colors.cyan}--installed${colors.reset}      Show only installed skills (with list)
  ${colors.cyan}--dry-run, -n${colors.reset}    Preview changes without applying
  ${colors.cyan}--category <c>${colors.reset}   Filter by category
  ${colors.cyan}--all${colors.reset}            Apply to all (with update)

${colors.bold}Agents:${colors.reset}
  ${colors.cyan}claude${colors.reset}   (default) ~/.claude/skills/
  ${colors.cyan}cursor${colors.reset}   .cursor/skills/ in current project
  ${colors.cyan}amp${colors.reset}      ~/.amp/skills/
  ${colors.cyan}vscode${colors.reset}   .github/skills/ in current project
  ${colors.cyan}copilot${colors.reset}  .github/skills/ (alias for vscode)
  ${colors.cyan}goose${colors.reset}    ~/.config/goose/skills/
  ${colors.cyan}opencode${colors.reset} ~/.opencode/skills/
  ${colors.cyan}codex${colors.reset}    ~/.codex/skills/
  ${colors.cyan}letta${colors.reset}    ~/.letta/skills/
  ${colors.cyan}project${colors.reset}  .skills/ in current directory (portable)

${colors.bold}Categories:${colors.reset}
  development, document, creative, business, productivity

${colors.bold}Examples:${colors.reset}
  npx ai-agent-skills install frontend-design
  npx ai-agent-skills install pdf --dry-run
  npx ai-agent-skills install frontend-design --cursor
  npx ai-agent-skills list --category development
  npx ai-agent-skills list --installed --agent cursor
  npx ai-agent-skills search testing
  npx ai-agent-skills update --all

${colors.bold}Config:${colors.reset}
  Config file: ~/.agent-skills.json
  Set default agent: npx ai-agent-skills config --default-agent cursor

${colors.bold}More info:${colors.reset}
  https://skillcreator.ai/discover
  https://github.com/skillcreatorai/Ai-Agent-Skills
`);
}

function showInfo(skillName) {
  const data = loadSkillsJson();
  const skill = data.skills.find(s => s.name === skillName);

  if (!skill) {
    error(`Skill "${skillName}" not found.`);

    // Suggest similar
    const similar = data.skills
      .filter(s => s.name.includes(skillName) || skillName.includes(s.name))
      .slice(0, 3);

    if (similar.length > 0) {
      log(`\n${colors.dim}Did you mean: ${similar.map(s => s.name).join(', ')}?${colors.reset}`);
    }
    return;
  }

  const tagStr = skill.tags && skill.tags.length > 0
    ? skill.tags.join(', ')
    : 'none';

  log(`
${colors.bold}${skill.name}${colors.reset}${skill.featured ? ` ${colors.yellow}(featured)${colors.reset}` : ''}${skill.verified ? ` ${colors.green}(verified)${colors.reset}` : ''}

${colors.dim}${skill.description}${colors.reset}

${colors.bold}Category:${colors.reset}    ${skill.category}
${colors.bold}Tags:${colors.reset}        ${tagStr}
${colors.bold}Author:${colors.reset}      ${skill.author}
${colors.bold}License:${colors.reset}     ${skill.license}
${colors.bold}Source:${colors.reset}      ${skill.source}
${skill.lastUpdated ? `${colors.bold}Updated:${colors.reset}     ${skill.lastUpdated}\n` : ''}
${colors.bold}Install:${colors.reset}
  npx ai-agent-skills install ${skill.name}
  npx ai-agent-skills install ${skill.name} --agent cursor
  npx ai-agent-skills install ${skill.name} --dry-run
`);
}

function showConfig() {
  const config = loadConfig();

  log(`\n${colors.bold}Configuration${colors.reset}`);
  log(`${colors.dim}File: ${CONFIG_FILE}${colors.reset}\n`);

  log(`${colors.bold}defaultAgent:${colors.reset} ${config.defaultAgent || 'claude'}`);
  log(`${colors.bold}autoUpdate:${colors.reset}   ${config.autoUpdate || false}`);

  log(`\n${colors.dim}Edit with: npx ai-agent-skills config --default-agent <agent>${colors.reset}`);
}

function setConfig(key, value) {
  const config = loadConfig();

  if (key === 'default-agent' || key === 'defaultAgent') {
    if (!AGENT_PATHS[value]) {
      error(`Invalid agent: ${value}`);
      log(`Valid agents: ${Object.keys(AGENT_PATHS).join(', ')}`);
      return false;
    }
    config.defaultAgent = value;
  } else if (key === 'auto-update' || key === 'autoUpdate') {
    config.autoUpdate = value === 'true' || value === true;
  } else {
    error(`Unknown config key: ${key}`);
    return false;
  }

  if (saveConfig(config)) {
    success(`Config updated: ${key} = ${value}`);
    return true;
  }
  return false;
}

// ============ MAIN CLI ============

const args = process.argv.slice(2);
const { command, param, agent, installed, dryRun, category, tags, all } = parseArgs(args);

// Handle config commands specially
if (command === 'config') {
  const configArgs = args.slice(1);
  if (configArgs.length === 0) {
    showConfig();
  } else {
    for (let i = 0; i < configArgs.length; i++) {
      if (configArgs[i].startsWith('--')) {
        const key = configArgs[i].replace('--', '');
        const value = configArgs[i + 1];
        if (value) {
          setConfig(key, value);
          i++;
        }
      }
    }
  }
  process.exit(0);
}

switch (command || 'help') {
  case 'list':
  case 'ls':
    if (installed) {
      listInstalledSkills(agent);
    } else {
      listSkills(category, tags);
    }
    break;

  case 'install':
  case 'i':
  case 'add':
    if (!param) {
      error('Please specify a skill name.');
      log('Usage: npx ai-agent-skills install <skill-name> [--agent <agent>] [--dry-run]');
      process.exit(1);
    }
    installSkill(param, agent, dryRun);
    break;

  case 'uninstall':
  case 'remove':
  case 'rm':
    if (!param) {
      error('Please specify a skill name.');
      log('Usage: npx ai-agent-skills uninstall <skill-name> [--agent <agent>]');
      process.exit(1);
    }
    uninstallSkill(param, agent, dryRun);
    break;

  case 'update':
  case 'upgrade':
    if (all) {
      updateAllSkills(agent, dryRun);
    } else if (!param) {
      error('Please specify a skill name or use --all.');
      log('Usage: npx ai-agent-skills update <skill-name> [--agent <agent>]');
      log('       npx ai-agent-skills update --all [--agent <agent>]');
      process.exit(1);
    } else {
      updateSkill(param, agent, dryRun);
    }
    break;

  case 'search':
  case 's':
  case 'find':
    if (!param) {
      error('Please specify a search query.');
      log('Usage: npx ai-agent-skills search <query>');
      process.exit(1);
    }
    searchSkills(param, category);
    break;

  case 'info':
  case 'show':
    if (!param) {
      error('Please specify a skill name.');
      log('Usage: npx ai-agent-skills info <skill-name>');
      process.exit(1);
    }
    showInfo(param);
    break;

  case 'help':
  case '--help':
  case '-h':
    showHelp();
    break;

  default:
    // If command looks like a skill name, try to install it
    if (getAvailableSkills().includes(command)) {
      installSkill(command, agent, dryRun);
    } else {
      error(`Unknown command: ${command}`);
      showHelp();
      process.exit(1);
    }
}
