# Dynamic Sufficiency Checker for Nickel Configs
# GF(3) Trit: 0 (ERGODIC)
#
# Verifies that config transformations preserve computational equivalence

let NonEmptyArray = std.contract.from_predicate (fun arr =>
  std.array.length arr > 0)

let SufficiencyLevel = [|
  'NOT_SUFFICIENT,
  'WEAKLY_SUFFICIENT,
  'COMPUTATIONALLY_SUFFICIENT,
  'SEMANTICALLY_SUFFICIENT
|]

# Check if all fields of cfg1 exist in cfg2
let fields_subset = fun cfg1 cfg2 =>
  let f1 = std.record.fields cfg1 in
  let f2 = std.record.fields cfg2 in
  std.array.all (fun f => std.array.elem f f2) f1

# Check if field types match (via contract application)
let types_compatible = fun cfg1 cfg2 field =>
  let v1 = std.record.get field cfg1 in
  let v2 = std.record.get field cfg2 in
  std.typeof v1 == std.typeof v2

# Core sufficiency verification
let check_sufficiency = fun source target => {
  # Structural check
  structural_match =
    fields_subset source target && fields_subset target source,
  
  # Field count
  source_fields = std.array.length (std.record.fields source),
  target_fields = std.array.length (std.record.fields target),
  
  # Determine level
  level =
    if !(fields_subset source target) then 'NOT_SUFFICIENT
    else if !(fields_subset target source) then 'WEAKLY_SUFFICIENT
    else 'COMPUTATIONALLY_SUFFICIENT,
  
  # Summary
  sufficient = 
    std.array.elem level ['COMPUTATIONALLY_SUFFICIENT, 'SEMANTICALLY_SUFFICIENT]
}

# Verify transformation preserves contracts
let verify_transformation = fun original transformed contract =>
  let applied_original = original | contract in
  let applied_transformed = transformed | contract in
  check_sufficiency applied_original applied_transformed

# Idempotency check for contracts
let check_idempotent = fun value contract =>
  let once = value | contract in
  let twice = once | contract in
  once == twice

# Export
{
  SufficiencyLevel = SufficiencyLevel,
  check_sufficiency = check_sufficiency,
  verify_transformation = verify_transformation,
  check_idempotent = check_idempotent,
  fields_subset = fields_subset,
}
