import { evaluateScenario, formatJson, renderConditionCards, renderAssumptionCards, renderResidualQueries, initRuntime } from "./demo-core.js";
import { createCodeEditor } from "./code-editor.js";
import { scenarios } from "./scenarios.js";

const state = {
  activeExampleId: scenarios[0]?.id ?? null,
  activeOutputTab: "result",
  activeRequestTab: "input",
  lastRun: null,
  scenarioDrafts: {}
};

const nav = document.querySelector("#example-nav");
const heroTitle = document.querySelector("#hero-title");
const heroSummary = document.querySelector("#hero-summary");
const heroResult = document.querySelector("#hero-result");
const heroFocus = document.querySelector("#hero-focus");
const featureStrip = document.querySelector("#feature-strip");
const conditionList = document.querySelector("#condition-list");
const assumptionList = document.querySelector("#assumption-list");
const assumptionPanel = document.querySelector("#assumption-panel");
const tabs = document.querySelector("#tabs");
const tabContent = document.querySelector("#tab-content");
const serverStatus = document.querySelector("#server-status");
const exampleRuntime = document.querySelector("#example-runtime");
const runAnalysis = document.querySelector("#run-analysis");
const analysisStatus = document.querySelector("#analysis-status");
const analysisPanel = document.querySelector("#analysis-panel");
const policyContent = document.querySelector("#policy-content");
const policyLabel = document.querySelector("#policy-label");
const requestTabs = document.querySelector("#request-tabs");
const requestContent = document.querySelector("#request-content");
const requestHeading = document.querySelector("#request-heading");
const entryPoint = document.querySelector("#entry-point");
const valueMode = document.querySelector("#value-mode");
const conditionMode = document.querySelector("#condition-mode");
const detailLevel = document.querySelector("#detail-level");
const assumeUnknown = document.querySelector("#assume-unknown");
const evalModeSelect = document.querySelector("#eval-mode");
const unknownsRow = document.querySelector("#unknowns-row");
const unknownsInput = document.querySelector("#unknowns-input");
const pePanel = document.querySelector("#pe-panel");
const peResults = document.querySelector("#pe-results");
const policyEditor = createCodeEditor(policyContent, { language: "rego" });
const requestEditor = createCodeEditor(requestContent, { language: "json" });

function focusAnalysis() {
  analysisPanel?.scrollIntoView({
    behavior: "smooth",
    block: "start"
  });
}

function currentScenario() {
  return scenarios.find((scenario) => scenario.id === state.activeExampleId) ?? scenarios[0];
}

function ensureScenarioDraft(scenario) {
  if (!state.scenarioDrafts[scenario.id]) {
    state.scenarioDrafts[scenario.id] = {
      policy: scenario.policy,
      input: scenario.input,
      data: scenario.data
    };
  }

  return state.scenarioDrafts[scenario.id];
}

function renderNav() {
  nav.innerHTML = "";
  scenarios.forEach((scenario) => {
    const button = document.createElement("button");
    button.type = "button";
    button.className = `nav-button${scenario.id === state.activeExampleId ? " active" : ""}`;
    button.innerHTML = `<strong>${scenario.navTitle}</strong><span>${scenario.navSubtitle}</span>`;
    button.addEventListener("click", () => {
      state.activeExampleId = scenario.id;
      state.activeOutputTab = "result";
      state.activeRequestTab = "input";
      state.lastRun = null;
      renderScenario();
    });
    nav.appendChild(button);
  });
}

function renderFeatures(features) {
  featureStrip.innerHTML = "";
  features.forEach((feature) => {
    const pill = document.createElement("span");
    pill.className = "pill";
    pill.textContent = feature;
    featureStrip.appendChild(pill);
  });
}

function requestTabMap(scenario) {
  const draft = ensureScenarioDraft(scenario);
  return {
    input: draft.input,
    data: draft.data
  };
}

function syncPolicyDraft() {
  const scenario = currentScenario();
  const draft = ensureScenarioDraft(scenario);
  draft.policy = policyContent.value;
}

function syncRequestDraft() {
  const scenario = currentScenario();
  const draft = ensureScenarioDraft(scenario);
  draft[state.activeRequestTab] = requestContent.value;
}

function renderRequestTabs(scenario) {
  const tabMap = requestTabMap(scenario);
  requestTabs.innerHTML = "";
  Object.entries(tabMap).forEach(([key, value]) => {
    const button = document.createElement("button");
    button.type = "button";
    button.className = `tab-button${key === state.activeRequestTab ? " active" : ""}`;
    button.textContent = key;
    button.addEventListener("click", () => {
      state.activeRequestTab = key;
      renderRequestTabs(scenario);
    });
    requestTabs.appendChild(button);
    if (!value?.trim()) {
      button.disabled = true;
    }
  });

  requestHeading.textContent = state.activeRequestTab === "data" ? "Data" : "Input";
  requestEditor.setValue(tabMap[state.activeRequestTab] || "{}");
}

function outputTabPayload() {
  if (!state.lastRun) {
    return {
      result: "Run the analysis to populate the result payload.",
      why: "Run the analysis to populate the explanation payload."
    };
  }

  const tabs = {
    result: formatJson(state.lastRun.result),
    why: state.lastRun.pe ? formatJson(state.lastRun.pe) : formatJson(state.lastRun.why)
  };
  if (state.lastRun.pe) {
    tabs.pe = formatJson(state.lastRun.pe);
  }
  return tabs;
}

function renderOutputTabs() {
  const payload = outputTabPayload();
  tabs.innerHTML = "";
  Object.keys(payload).forEach((key) => {
    const button = document.createElement("button");
    button.type = "button";
    button.className = `tab-button${key === state.activeOutputTab ? " active" : ""}`;
    button.textContent = key;
    button.addEventListener("click", () => {
      state.activeOutputTab = key;
      renderOutputTabs();
    });
    tabs.appendChild(button);
  });
  tabContent.textContent = payload[state.activeOutputTab] || "";
}

function renderScenario() {
  const scenario = currentScenario();
  const draft = ensureScenarioDraft(scenario);
  renderNav();
  renderFeatures(scenario.features);
  heroTitle.textContent = scenario.title;
  heroSummary.textContent = scenario.summary;
  heroResult.textContent = state.lastRun?.resultSummary || "pending";
  heroFocus.textContent = scenario.focus;
  policyEditor.setValue(draft.policy);
  policyLabel.textContent = "rvm";
  entryPoint.textContent = scenario.query;
  valueMode.textContent = scenario.whyFullValues ? "full" : "redacted";
  conditionMode.textContent = scenario.whyAllConditions ? "all contributing" : "primary only";
  detailLevel.value = scenario.detail || "standard";
  assumeUnknown.checked = !!scenario.assumeUnknownInput;
  const isPartial = scenario.evalMode === "partial";
  evalModeSelect.value = isPartial ? "partial" : "causality";
  unknownsRow.style.display = isPartial ? "" : "none";
  unknownsInput.value = scenario.unknowns || "input";
  if (isPartial) {
    assumeUnknown.checked = true;
    assumeUnknown.disabled = true;
  } else {
    assumeUnknown.disabled = false;
  }
  analysisStatus.textContent = state.lastRun ? "completed" : "ready";
  exampleRuntime.textContent = state.lastRun?.runtimeMs ? `${state.lastRun.runtimeMs} ms` : "";
  renderRequestTabs(scenario);
  renderOutputTabs();

  const isPartialRun = state.lastRun?.pe;

  if (state.lastRun) {
    if (isPartialRun) {
      // PE mode: show residual queries, hide causality panels
      analysisPanel.style.display = "none";
      if (assumptionPanel) assumptionPanel.style.display = "none";
      if (pePanel) {
        pePanel.style.display = "";
        renderResidualQueries(peResults, state.lastRun.pe);
      }
    } else {
      // Causality mode: show conditions and assumptions, hide PE panel
      analysisPanel.style.display = "";
      if (pePanel) pePanel.style.display = "none";
      renderConditionCards(conditionList, state.lastRun.why.reasons || []);
      const assumptions = state.lastRun.assumptions || [];
      if (assumptionPanel) {
        assumptionPanel.style.display = assumptions.length ? "" : "none";
      }
      if (assumptionList) {
        renderAssumptionCards(assumptionList, assumptions);
      }
    }
  } else {
    conditionList.innerHTML = '<div class="loading-card">Policy and request are shown first. Run the analysis to inspect the decision and explanation chain.</div>';
    analysisPanel.style.display = "";
    if (assumptionPanel) {
      assumptionPanel.style.display = "none";
    }
    if (pePanel) {
      pePanel.style.display = "none";
    }
  }
}

async function runCurrentScenario() {
  const scenario = currentScenario();
  const draft = ensureScenarioDraft(scenario);
  runAnalysis.disabled = true;
  analysisStatus.textContent = "running";
  exampleRuntime.textContent = "";
  conditionList.innerHTML = '<div class="loading-card">Evaluating scenario in wasm…</div>';
  requestAnimationFrame(focusAnalysis);

  try {
    state.lastRun = await evaluateScenario({
      ...scenario,
      engine: "rvm",
      policy: draft.policy,
      input: draft.input,
      data: draft.data,
      detail: detailLevel.value,
      assumeUnknownInput: assumeUnknown.checked,
      evalMode: evalModeSelect.value,
      unknowns: unknownsInput.value
    });
    analysisStatus.textContent = "completed";
    renderScenario();
    requestAnimationFrame(focusAnalysis);
  } catch (error) {
    state.lastRun = null;
    heroResult.textContent = "error";
    analysisStatus.textContent = "error";
    tabContent.textContent = error.message;
    conditionList.innerHTML = `<div class="error-banner">${error.message}</div>`;
    requestAnimationFrame(focusAnalysis);
  } finally {
    runAnalysis.disabled = false;
  }
}

policyContent.addEventListener("input", syncPolicyDraft);
requestContent.addEventListener("input", syncRequestDraft);
runAnalysis.addEventListener("click", runCurrentScenario);
evalModeSelect.addEventListener("change", () => {
  const isPartial = evalModeSelect.value === "partial";
  unknownsRow.style.display = isPartial ? "" : "none";
  if (isPartial) {
    assumeUnknown.checked = true;
    assumeUnknown.disabled = true;
  } else {
    assumeUnknown.disabled = false;
  }
});

async function bootstrap() {
  renderScenario();
  try {
    await initRuntime();
    serverStatus.textContent = "Wasm runtime ready. Scenarios execute entirely in the browser.";
  } catch (error) {
    serverStatus.textContent = "Failed to initialize the wasm runtime.";
    conditionList.innerHTML = `<div class="error-banner">${error.message}</div>`;
    runAnalysis.disabled = true;
  }
}

bootstrap();