###
### Deprecations
###

Base.@deprecate compile_rules(rules) RuleSet(rules)
Base.@deprecate compile_rules(rules, index) RuleSet(rules, index)

"""
    compile_rules(rules, index = BucketIndex)

Deprecated — use the [`RuleSet`](@ref) constructor instead.
"""
compile_rules
