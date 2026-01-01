# Zig Version Differences

## Major Version Changes

### 0.15.x (Current Stable)
- Latest stable release
- No async/await (removed in 0.11)
- Modern build.zig API
- Current for loop syntax

### 0.11.x - 0.14.x
- Async/await removed (being redesigned)
- Build system API evolution
- Error set syntax changes
- For loop syntax changes in 0.13

### 0.9.x - 0.10.x
- Last versions with async/await
- Older build.zig API
- Different error handling syntax

### 0.2.x - 0.8.x
- Early language versions
- Significant syntax differences
- Limited standard library
- Different build system

## Breaking Changes

### Async/Await
- **0.10.x and earlier**: Full async/await support
- **0.11.x - 0.15.x**: Removed, use threads or event loops
- **0.16.x (planned)**: New async implementation

### Build System API
- **0.10.x**: `build.zig` uses older API
- **0.11.x**: Major build API overhaul
- **0.12.x+**: Incremental improvements

### For Loop Syntax
- **Pre-0.13**: Different iterator syntax
- **0.13+**: Modern for loop with captures

### Error Handling
- **Pre-0.11**: Different error set syntax
- **0.11+**: Current error union syntax

## Migration Guides

### From 0.10.x to 0.11.x+
1. Remove all async/await code
2. Update build.zig to new API
3. Fix error set syntax
4. Update for loop syntax

### From Pre-0.9 to Modern
1. Major syntax overhaul needed
2. Rewrite build system
3. Update all error handling
4. Modernize type syntax

## Feature Availability by Version

| Feature | 0.2-0.8 | 0.9-0.10 | 0.11-0.15 | 0.16+ |
|---------|---------|----------|-----------|-------|
| async/await | ❌ | ✅ | ❌ | 🔄 |
| comptime | ✅ | ✅ | ✅ | ✅ |
| error unions | ⚠️ | ✅ | ✅ | ✅ |
| build.zig | ⚠️ | ⚠️ | ✅ | ✅ |
| std library | ⚠️ | ✅ | ✅ | ✅ |

Legend: ✅ Full support, ⚠️ Limited/different, ❌ Not available, 🔄 Planned
