#!/usr/bin/env node

const fs = require('fs');
const path = require('path');
const os = require('os');

const SKILLS_DIR = path.join(__dirname, 'skills');

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
  red: '\x1b[31m'
};

function log(msg) { console.log(msg); }
function success(msg) { console.log(`${colors.green}${colors.bold}${msg}${colors.reset}`); }
function info(msg) { console.log(`${colors.cyan}${msg}${colors.reset}`); }
function warn(msg) { console.log(`${colors.yellow}${msg}${colors.reset}`); }
function error(msg) { console.log(`${colors.red}${msg}${colors.reset}`); }

function loadSkillsJson() {
  const skillsJsonPath = path.join(__dirname, 'skills.json');
  if (fs.existsSync(skillsJsonPath)) {
    return JSON.parse(fs.readFileSync(skillsJsonPath, 'utf8'));
  }
  return { skills: [] };
}

function getAvailableSkills() {
  if (!fs.existsSync(SKILLS_DIR)) return [];
  return fs.readdirSync(SKILLS_DIR).filter(name => {
    const skillPath = path.join(SKILLS_DIR, name);
    return fs.statSync(skillPath).isDirectory() &&
           fs.existsSync(path.join(skillPath, 'SKILL.md'));
  });
}

function parseArgs(args) {
  const result = { command: null, param: null, agent: 'claude', installed: false, all: false };

  // List of valid agents for shorthand flags
  const validAgents = Object.keys(AGENT_PATHS);

  for (let i = 0; i < args.length; i++) {
    const arg = args[i];

    // Handle --agent <name> or -a <name>
    if (arg === '--agent' || arg === '-a') {
      let agentValue = args[i + 1] || 'claude';
      // Strip leading dashes if user passed --cursor instead of cursor
      agentValue = agentValue.replace(/^-+/, '');
      result.agent = validAgents.includes(agentValue) ? agentValue : 'claude';
      i++;
    }
    // Handle --installed flag
    else if (arg === '--installed' || arg === '-i') {
      result.installed = true;
    }
    // Handle --all flag for uninstall
    else if (arg === '--all') {
      result.all = true;
    }
    // Handle shorthand flags like --cursor, --amp, --vscode, etc.
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

function installSkill(skillName, agent = 'claude') {
  const sourcePath = path.join(SKILLS_DIR, skillName);

  if (!fs.existsSync(sourcePath)) {
    error(`Skill "${skillName}" not found.`);
    log(`\nAvailable skills:`);
    listSkills();
    return false;
  }

  // Get the appropriate destination path for the agent
  const destDir = AGENT_PATHS[agent] || AGENT_PATHS.claude;
  const destPath = path.join(destDir, skillName);

  // Create skills directory if it doesn't exist
  if (!fs.existsSync(destDir)) {
    fs.mkdirSync(destDir, { recursive: true });
  }

  // Copy skill directory
  copyDir(sourcePath, destPath);

  success(`\nInstalled: ${skillName}`);
  info(`Agent: ${agent}`);
  info(`Location: ${destPath}`);

  // Show agent-specific instructions
  log('');
  showAgentInstructions(agent, skillName, destPath);

  return true;
}

function showAgentInstructions(agent, skillName, destPath) {
  switch (agent) {
    case 'claude':
      log(`${colors.dim}The skill is now available in Claude Code.${colors.reset}`);
      log(`${colors.dim}Just mention "${skillName}" in your prompt and Claude will use it.${colors.reset}`);
      break;
    case 'cursor':
      log(`${colors.dim}The skill is installed in your project's .cursor/skills/ folder.${colors.reset}`);
      log(`${colors.dim}Cursor will automatically detect and use it.${colors.reset}`);
      break;
    case 'amp':
      log(`${colors.dim}The skill is now available in Amp.${colors.reset}`);
      break;
    case 'codex':
      log(`${colors.dim}The skill is now available in Codex.${colors.reset}`);
      break;
    case 'vscode':
    case 'copilot':
      log(`${colors.dim}The skill is installed in your project's .github/skills/ folder.${colors.reset}`);
      break;
    case 'project':
      log(`${colors.dim}The skill is installed in .skills/ in your current directory.${colors.reset}`);
      log(`${colors.dim}This makes it portable across all compatible agents.${colors.reset}`);
      break;
    default:
      log(`${colors.dim}The skill is ready to use with ${agent}.${colors.reset}`);
  }
}

function copyDir(src, dest) {
  if (fs.existsSync(dest)) {
    fs.rmSync(dest, { recursive: true });
  }
  fs.mkdirSync(dest, { recursive: true });

  const entries = fs.readdirSync(src, { withFileTypes: true });
  for (const entry of entries) {
    const srcPath = path.join(src, entry.name);
    const destPath = path.join(dest, entry.name);
    if (entry.isDirectory()) {
      copyDir(srcPath, destPath);
    } else {
      fs.copyFileSync(srcPath, destPath);
    }
  }
}

function uninstallSkill(skillName, agent = 'claude') {
  const destDir = AGENT_PATHS[agent] || AGENT_PATHS.claude;
  const skillPath = path.join(destDir, skillName);

  if (!fs.existsSync(skillPath)) {
    error(`Skill "${skillName}" is not installed for ${agent}.`);
    log(`\nInstalled skills for ${agent}:`);
    listInstalledSkills(agent);
    return false;
  }

  fs.rmSync(skillPath, { recursive: true });
  success(`\nUninstalled: ${skillName}`);
  info(`Agent: ${agent}`);
  info(`Removed from: ${skillPath}`);
  return true;
}

function getInstalledSkills(agent = 'claude') {
  const destDir = AGENT_PATHS[agent] || AGENT_PATHS.claude;

  if (!fs.existsSync(destDir)) return [];

  return fs.readdirSync(destDir).filter(name => {
    const skillPath = path.join(destDir, name);
    return fs.statSync(skillPath).isDirectory() &&
           fs.existsSync(path.join(skillPath, 'SKILL.md'));
  });
}

function listInstalledSkills(agent = 'claude') {
  const installed = getInstalledSkills(agent);
  const destDir = AGENT_PATHS[agent] || AGENT_PATHS.claude;

  if (installed.length === 0) {
    warn(`No skills installed for ${agent}`);
    info(`Location: ${destDir}`);
    return;
  }

  log(`\n${colors.bold}Installed Skills${colors.reset} (${installed.length} for ${agent})\n`);
  log(`${colors.dim}Location: ${destDir}${colors.reset}\n`);

  installed.forEach(name => {
    log(`  ${colors.green}${name}${colors.reset}`);
  });

  log(`\n${colors.dim}Uninstall: npx ai-agent-skills uninstall <name> --agent ${agent}${colors.reset}`);
}

function updateSkill(skillName, agent = 'claude') {
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

  // Remove old and copy new
  fs.rmSync(destPath, { recursive: true });
  copyDir(sourcePath, destPath);

  success(`\nUpdated: ${skillName}`);
  info(`Agent: ${agent}`);
  info(`Location: ${destPath}`);
  return true;
}

function listSkills() {
  const data = loadSkillsJson();
  const skills = data.skills || [];

  if (skills.length === 0) {
    warn('No skills found in skills.json');
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

  Object.keys(byCategory).sort().forEach(category => {
    log(`${colors.blue}${colors.bold}${category.toUpperCase()}${colors.reset}`);
    byCategory[category].forEach(skill => {
      const featured = skill.featured ? ` ${colors.yellow}*${colors.reset}` : '';
      log(`  ${colors.green}${skill.name}${colors.reset}${featured}`);
      const desc = skill.description.length > 70
        ? skill.description.slice(0, 70) + '...'
        : skill.description;
      log(`    ${colors.dim}${desc}${colors.reset}`);
    });
    log('');
  });

  log(`${colors.dim}* = featured skill${colors.reset}`);
  log(`\nInstall: ${colors.cyan}npx ai-agent-skills install <skill-name> [--agent <agent>]${colors.reset}`);
}

function searchSkills(query) {
  const data = loadSkillsJson();
  const skills = data.skills || [];
  const q = query.toLowerCase();

  const matches = skills.filter(s =>
    s.name.toLowerCase().includes(q) ||
    s.description.toLowerCase().includes(q) ||
    (s.category && s.category.toLowerCase().includes(q))
  );

  if (matches.length === 0) {
    warn(`No skills found matching "${query}"`);
    return;
  }

  log(`\n${colors.bold}Search Results${colors.reset} (${matches.length} matches)\n`);
  matches.forEach(skill => {
    log(`${colors.green}${skill.name}${colors.reset} ${colors.dim}[${skill.category}]${colors.reset}`);
    log(`  ${skill.description.slice(0, 80)}...`);
    log('');
  });
}

function showHelp() {
  log(`
${colors.bold}AI Agent Skills${colors.reset}
The universal skill repository for AI agents.

${colors.bold}Usage:${colors.reset}
  npx ai-agent-skills <command> [options]

${colors.bold}Commands:${colors.reset}
  ${colors.green}list${colors.reset}                             List all available skills
  ${colors.green}list --installed${colors.reset}                 List installed skills for an agent
  ${colors.green}install <name>${colors.reset}                   Install a skill
  ${colors.green}uninstall <name>${colors.reset}                 Remove an installed skill
  ${colors.green}update <name>${colors.reset}                    Update an installed skill to latest
  ${colors.green}search <query>${colors.reset}                   Search skills by name or description
  ${colors.green}info <name>${colors.reset}                      Show skill details
  ${colors.green}help${colors.reset}                             Show this help

${colors.bold}Options:${colors.reset}
  ${colors.cyan}--agent <name>${colors.reset}  Target agent (default: claude)
  ${colors.cyan}--installed${colors.reset}     Show only installed skills (with list)

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

${colors.bold}Examples:${colors.reset}
  npx ai-agent-skills install frontend-design
  npx ai-agent-skills install frontend-design --cursor
  npx ai-agent-skills list --installed --agent cursor
  npx ai-agent-skills uninstall pdf --claude
  npx ai-agent-skills update frontend-design
  npx ai-agent-skills search excel

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
    return;
  }

  log(`
${colors.bold}${skill.name}${colors.reset}${skill.featured ? ` ${colors.yellow}(featured)${colors.reset}` : ''}

${colors.dim}${skill.description}${colors.reset}

${colors.bold}Category:${colors.reset}  ${skill.category}
${colors.bold}Author:${colors.reset}    ${skill.author}
${colors.bold}License:${colors.reset}   ${skill.license}
${colors.bold}Source:${colors.reset}    ${skill.source}
${colors.bold}Stars:${colors.reset}     ${skill.stars.toLocaleString()}
${colors.bold}Downloads:${colors.reset} ${skill.downloads.toLocaleString()}

${colors.bold}Install:${colors.reset}
  npx ai-agent-skills install ${skill.name}
  npx ai-agent-skills install ${skill.name} --agent cursor
`);
}

// Main CLI
const args = process.argv.slice(2);
const { command, param, agent, installed } = parseArgs(args);

switch (command || 'help') {
  case 'list':
  case 'ls':
    if (installed) {
      listInstalledSkills(agent);
    } else {
      listSkills();
    }
    break;
  case 'install':
  case 'i':
  case 'add':
    if (!param) {
      error('Please specify a skill name.');
      log('Usage: npx ai-agent-skills install <skill-name> [--agent <agent>]');
      process.exit(1);
    }
    installSkill(param, agent);
    break;
  case 'uninstall':
  case 'remove':
  case 'rm':
    if (!param) {
      error('Please specify a skill name.');
      log('Usage: npx ai-agent-skills uninstall <skill-name> [--agent <agent>]');
      process.exit(1);
    }
    uninstallSkill(param, agent);
    break;
  case 'update':
  case 'upgrade':
    if (!param) {
      error('Please specify a skill name.');
      log('Usage: npx ai-agent-skills update <skill-name> [--agent <agent>]');
      process.exit(1);
    }
    updateSkill(param, agent);
    break;
  case 'search':
  case 's':
  case 'find':
    if (!param) {
      error('Please specify a search query.');
      log('Usage: npx ai-agent-skills search <query>');
      process.exit(1);
    }
    searchSkills(param);
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
      installSkill(command, agent);
    } else {
      error(`Unknown command: ${command}`);
      showHelp();
      process.exit(1);
    }
}
