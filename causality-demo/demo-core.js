import init, { Rvm } from "./pkg/regorusjs.js";

let runtimePromise;

export function initRuntime() {
  if (!runtimePromise) {
    runtimePromise = init();
  }
  return runtimePromise;
}

export function formatJson(value) {
  return JSON.stringify(value, null, 2);
}

function parseJsonText(label, text) {
  try {
    return JSON.stringify(JSON.parse(text || "{}"));
  } catch (error) {
    throw new Error(`${label} is not valid JSON: ${error.message}`);
  }
}

function explanationMode(options) {
  return {
    enabled: true,
    valueMode: options.whyFullValues ? "full" : "redacted",
    conditionMode: options.whyAllConditions ? "all_contributing" : "primary_only",
    assumeUnknownInput: !!options.assumeUnknownInput,
    detail: options.detail || "standard"
  };
}

function summarizeEvaluation(evaluation) {
  if (!evaluation) {
    return { meta: [], checks: [] };
  }

  const meta = [];
  const checks = [];
  if (evaluation.operator) {
    meta.push({ text: `operator: ${evaluation.operator}` });
  }
  if (Object.prototype.hasOwnProperty.call(evaluation, "actual_value")) {
    meta.push({
      text: `actual: ${JSON.stringify(evaluation.actual_value)}`,
      provenance: evaluation.actual_path ? `← ${evaluation.actual_path}` : null
    });
  }
  if (Object.prototype.hasOwnProperty.call(evaluation, "expected_value")) {
    meta.push({
      text: `expected: ${JSON.stringify(evaluation.expected_value)}`,
      provenance: evaluation.expected_path ? `← ${evaluation.expected_path}` : null
    });
  }
  if (evaluation.witness?.collection_path) {
    meta.push({
      text: "collection:",
      provenance: evaluation.witness.collection_path
    });
  }
  if (evaluation.witness?.iteration_count != null) {
    meta.push({ text: `${evaluation.witness.iteration_count} iterations` });
  }
  if (evaluation.witness?.success_count != null) {
    meta.push({ text: `${evaluation.witness.success_count} successes` });
  }
  if (evaluation.witness?.yield_count != null) {
    meta.push({ text: `${evaluation.witness.yield_count} yielded values` });
  }
  if (evaluation.witness?.condition_texts?.length) {
    checks.push(...evaluation.witness.condition_texts);
  }
  return { meta, checks };
}

function summarizeWitness(witness) {
  if (!witness) {
    return [];
  }

  const details = [];
  if (witness.sample_value !== undefined
      && !witness.passing_iteration?.sample_value
      && !witness.failing_iteration?.sample_value) {
    details.push({ text: `sample: ${JSON.stringify(witness.sample_value)}` });
  }
  return details;
}

function buildIterationSamples(witness) {
  if (!witness) return null;
  const passing = witness.passing_iteration;
  const failing = witness.failing_iteration;
  if (!passing && !failing) return null;

  const wrapper = document.createElement("div");
  wrapper.className = "iteration-samples";

  [{ data: passing, label: "Passing iteration", cls: "sample-passing" },
   { data: failing, label: "Failing iteration", cls: "sample-failing" }]
    .forEach(({ data, label, cls }) => {
      if (!data) return;
      const details = document.createElement("details");
      details.className = `iteration-sample ${cls}`;
      const summary = document.createElement("summary");
      summary.className = "sample-summary";
      const tag = document.createElement("span");
      tag.className = "sample-tag";
      tag.textContent = label;
      summary.appendChild(tag);
      if (data.sample_key != null) {
        const key = document.createElement("span");
        key.className = "sample-key";
        key.textContent = `key = ${JSON.stringify(data.sample_key)}`;
        summary.appendChild(key);
      }
      details.appendChild(summary);
      const pre = document.createElement("pre");
      pre.className = "sample-json";
      pre.textContent = JSON.stringify(data.sample_value, null, 2);
      details.appendChild(pre);
      wrapper.appendChild(details);
    });

  return wrapper.children.length ? wrapper : null;
}

export function renderConditionCards(container, reasons) {
  container.innerHTML = "";

  if (!reasons.length) {
    container.innerHTML = '<div class="loading-card">No conditions were returned for this evaluation.</div>';
    return;
  }

  reasons.forEach((reason) => {
    const group = document.createElement("article");
    group.className = "reason-group";

    const header = document.createElement("div");
    header.className = "reason-header";
    header.innerHTML = `
      <div>
        <p class="reason-label">Observed result</p>
        <h4 class="reason-result">${JSON.stringify(reason.result)}</h4>
      </div>
      <span class="result-count">${reason.conditions.length} condition${reason.conditions.length === 1 ? "" : "s"}</span>
    `;

    const list = document.createElement("div");
    list.className = "reason-condition-list";

    reason.conditions.forEach((condition, index) => {
      const item = document.createElement("section");
      item.className = "condition-card nested-condition-card";

      const top = document.createElement("div");
      top.className = "condition-topline";
      top.innerHTML = `
        <div class="condition-heading">
          <span class="condition-index">${index + 1}</span>
          <span class="badge ${condition.outcome}">${condition.outcome}</span>
          <span class="condition-kind">${condition.evaluation?.kind || "condition"}</span>
        </div>
        <span class="condition-location">${condition.location?.row ? `L${condition.location.row}` : ""}</span>
      `;

      const text = document.createElement("p");
      text.className = "condition-text";
      text.textContent = condition.text;

      const evaluationSummary = summarizeEvaluation(condition.evaluation);
      const meta = document.createElement("div");
      meta.className = "condition-meta";
      [...evaluationSummary.meta, ...summarizeWitness(condition.evaluation?.witness)].forEach((entry) => {
        const chip = document.createElement("span");
        chip.className = "meta-chip";
        const label = document.createElement("span");
        label.textContent = entry.text;
        chip.appendChild(label);
        if (entry.provenance) {
          const prov = document.createElement("span");
          prov.className = "meta-provenance";
          prov.textContent = ` ${entry.provenance}`;
          chip.appendChild(prov);
        }
        meta.appendChild(chip);
      });

      let checks = null;
      if (evaluationSummary.checks.length) {
        checks = document.createElement("div");
        checks.className = "condition-detail-group";

        const label = document.createElement("p");
        label.className = "condition-detail-label";
        label.textContent = "Checks";

        const list = document.createElement("ul");
        list.className = "condition-detail-list";
        evaluationSummary.checks.forEach((entry) => {
          const item = document.createElement("li");
          item.className = "condition-detail-item";
          item.textContent = entry;
          list.appendChild(item);
        });

        checks.appendChild(label);
        checks.appendChild(list);
      }

      let bindings = null;
      if (condition.bindings?.length) {
        bindings = document.createElement("div");
        bindings.className = "condition-detail-group condition-bindings";
        const label = document.createElement("p");
        label.className = "condition-detail-label";
        label.textContent = "Bindings";

        const list = document.createElement("ul");
        list.className = "condition-detail-list";
        condition.bindings.forEach((binding) => {
          const item = document.createElement("li");
          item.className = "condition-detail-item binding-item";
          const assign = document.createElement("span");
          assign.className = "binding-assign";
          assign.textContent = `${binding.name} = ${JSON.stringify(binding.value)}`;
          item.appendChild(assign);
          if (binding.source_path) {
            const prov = document.createElement("span");
            prov.className = "binding-provenance";
            prov.textContent = `← ${binding.source_path}`;
            item.appendChild(prov);
          }
          list.appendChild(item);
        });
        bindings.appendChild(label);
        bindings.appendChild(list);
      }

      item.appendChild(top);
      item.appendChild(text);
      if (meta.childElementCount) {
        item.appendChild(meta);
      }
      if (checks) {
        item.appendChild(checks);
      }
      if (bindings) {
        item.appendChild(bindings);
      }

      const samples = buildIterationSamples(condition.evaluation?.witness);
      if (samples) {
        item.appendChild(samples);
      }

      list.appendChild(item);
    });

    group.appendChild(header);
    group.appendChild(list);
    container.appendChild(group);
  });
}

export function renderAssumptionCards(container, assumptions) {
  container.innerHTML = "";

  if (!assumptions.length) {
    container.innerHTML = '<div class="loading-card">No assumptions were made — all input fields were known.</div>';
    return;
  }

  const group = document.createElement("article");
  group.className = "reason-group";

  const header = document.createElement("div");
  header.className = "reason-header";
  header.innerHTML = `
    <div>
      <p class="reason-label">Assumed inputs</p>
      <h4 class="reason-result">${assumptions.length} assumption${assumptions.length === 1 ? "" : "s"}</h4>
    </div>
    <span class="result-count">The engine assumed unknown input fields hold specific values to make the policy succeed.</span>
  `;

  const list = document.createElement("div");
  list.className = "reason-condition-list";

  assumptions.forEach((assumption, index) => {
    const item = document.createElement("section");
    item.className = "condition-card nested-condition-card";

    const top = document.createElement("div");
    top.className = "condition-topline";
    top.innerHTML = `
      <div class="condition-heading">
        <span class="condition-index">${index + 1}</span>
        <span class="badge assumed">assumed</span>
        <span class="condition-kind">${assumption.kind}</span>
      </div>
      <span class="condition-location">${assumption.location?.row ? `L${assumption.location.row}` : ""}</span>
    `;

    const text = document.createElement("p");
    text.className = "condition-text";
    text.textContent = assumption.assumed_holds;

    const meta = document.createElement("div");
    meta.className = "condition-meta";

    const pathChip = document.createElement("span");
    pathChip.className = "meta-chip";
    pathChip.innerHTML = `<span>path: <strong>${assumption.input_path}</strong></span>`;
    meta.appendChild(pathChip);

    if (assumption.operator) {
      const opChip = document.createElement("span");
      opChip.className = "meta-chip";
      opChip.textContent = `operator: ${assumption.operator}`;
      meta.appendChild(opChip);
    }

    if (assumption.assumed_value !== undefined && assumption.assumed_value !== null) {
      const valChip = document.createElement("span");
      valChip.className = "meta-chip";
      valChip.textContent = `assumed value: ${JSON.stringify(assumption.assumed_value)}`;
      meta.appendChild(valChip);
    }

    item.appendChild(top);
    item.appendChild(text);
    if (meta.childElementCount) {
      item.appendChild(meta);
    }

    list.appendChild(item);
  });

  group.appendChild(header);
  group.appendChild(list);
  container.appendChild(group);
}

function summarizeQueryResults(result) {
  const expressions = result?.result?.[0]?.expressions ?? [];
  if (!expressions.length) {
    return "undefined";
  }
  return summarizeValue(expressions[0].value);
}

function summarizeValue(value) {
  if (typeof value === "boolean") {
    return String(value);
  }
  if (Array.isArray(value)) {
    return `${value.length} result(s)`;
  }
  if (value && typeof value === "object") {
    return `object with ${Object.keys(value).length} field(s)`;
  }
  return JSON.stringify(value);
}

async function evaluateRvm(options) {
  const vm = new Rvm();
  const mode = explanationMode(options);
  vm.setExplanationOptions(mode.enabled, mode.valueMode, mode.conditionMode, mode.assumeUnknownInput, mode.detail);
  vm.loadModules(
    parseJsonText("Data", options.data),
    JSON.stringify([{ id: "demo.rego", content: options.policy }]),
    JSON.stringify([options.query])
  );
  vm.setInputJson(parseJsonText("Input", options.input));

  const result = JSON.parse(vm.executeEntryPoint(options.query));
  const report = JSON.parse(vm.takeCausalityReport());

  // Helper: transform a list of raw conditions into the UI format.
  function mapConditions(conds) {
    return (conds || []).map((cond) => ({
      text: cond.text,
      outcome: cond.outcome,
      location: cond.location,
      evaluation: {
        kind: cond.kind,
        operator: cond.operator,
        ...(cond.left ? { actual_value: cond.left.value, actual_path: cond.left.provenance } : {}),
        ...(cond.right ? { expected_value: cond.right.value, expected_path: cond.right.provenance } : {}),
        witness: cond.witness
      },
      bindings: cond.binding_name && cond.left
        ? [{ name: cond.binding_name, value: cond.left.value, source_path: cond.left.provenance }]
        : []
    }));
  }

  // Transform causality report into the reasons format expected by the UI.
  // For partial rules (set/object), use emissions so each emitted value has
  // its own causal trace.  For complete/boolean rules, use definitions.
  // Filter to just the queried entry point rule to exclude helper rules.
  const queriedRules = (report.rules || []).filter(
    (rule) => rule.name === options.query
  );
  const reasons = (queriedRules.length > 0 ? queriedRules : report.rules || []).flatMap((rule) => {
    if (rule.emissions && rule.emissions.length > 0) {
      // Partial rule: one reason per emission (skip undefined results)
      return rule.emissions
        .filter((em) => em.result !== "<undefined>" && em.result !== undefined)
        .map((em) => ({
        result: em.result,
        definitionIndex: em.definition_index,
        conditions: mapConditions(em.conditions)
      }));
    }
    // Complete/boolean rule: one reason per rule, definitions flat-mapped
    return [{
      result: rule.result,
      conditions: (rule.definitions || []).flatMap((def) => mapConditions(def.conditions))
    }];
  });

  return {
    result,
    why: { reasons },
    assumptions: report.assumptions || [],
    resultSummary: summarizeValue(result)
  };
}

export async function evaluatePolicy(options) {
  await initRuntime();
  const started = performance.now();
  const payload = await evaluateRvm(options);

  return {
    ...payload,
    runtimeMs: Math.round(performance.now() - started)
  };
}

export async function evaluateScenario(scenario) {
  return evaluatePolicy(scenario);
}

export async function evaluateCustom(request) {
  if (!request.policy?.trim()) {
    throw new Error("Policy must not be empty.");
  }
  if (!request.query?.trim()) {
    throw new Error("Entry point must not be empty.");
  }
  return evaluatePolicy(request);
}