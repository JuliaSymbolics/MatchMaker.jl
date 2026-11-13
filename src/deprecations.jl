###
### Deprecations
###

Base.@deprecate compile_rules(rules) ruleset(rules)
Base.@deprecate compile_rules(rules, index) ruleset(rules, index)
