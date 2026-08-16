package staticAnalysisResult.Verification

# Final verdict as a string
default compliant := "noncompliant"

##################################################
# Locate runs
##################################################

# indices of runs in the SARIF doc
runs_indices contains i if {
  doc := input.PrefastConfigContent.resolvedData.content
  doc.runs[i]
}

has_runs if { runs_indices[_] }

##################################################
# Invocation checks (per run index i)
##################################################

# at least one success
inv_any_true contains i if {
  doc := input.PrefastConfigContent.resolvedData.content
  doc.runs[i]                                  # bind i
  some j
  doc.runs[i].invocations[j].executionSuccessful == true
}

# any explicit failure
inv_has_false contains i if {
  doc := input.PrefastConfigContent.resolvedData.content
  doc.runs[i]                                  # bind i
  some j
  doc.runs[i].invocations[j].executionSuccessful == false
}

# invocation OK iff there is at least one true AND no false
inv_ok contains i if {
  runs_indices[i]                              # bind i
  inv_any_true[i]
  not inv_has_false[i]
}

##################################################
# Results empty (per run index i)
##################################################

# missing results counts as empty
results_empty contains i if {
  doc := input.PrefastConfigContent.resolvedData.content
  doc.runs[i]                                  # bind i
  not doc.runs[i].results
}

# results exists and is an empty array
results_empty contains i if {
  doc := input.PrefastConfigContent.resolvedData.content
  doc.runs[i]                                  # bind i
  is_array(doc.runs[i].results)
  count(doc.runs[i].results) == 0
}

##################################################
# Per-run and overall
##################################################

run_ok contains i if {
  runs_indices[i]                              # bind i
  inv_ok[i]
  results_empty[i]
}

# any run index that exists but is not ok
any_non_ok if {
  i := runs_indices[_]
  not run_ok[i]
}

# overall verdict string
compliant := "compliant" if {
  has_runs
  not any_non_ok
} else := "noncompliant"
