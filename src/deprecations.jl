###
### Deprecations
###

Base.@deprecate compile_rules(rules) ruleset(rules)
Base.@deprecate compile_rules(rules, index) ruleset(rules, index)

"""
    compile_rules(rules, index = BucketIndex)

Deprecated — use [`ruleset`](@ref) instead.
"""
compile_rules
