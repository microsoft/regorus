import { evaluateCustom, formatJson, initRuntime, renderConditionCards, renderAssumptionCards } from "./demo-core.js";
import { createCodeEditor } from "./code-editor.js";

const samplePolicy = `package demo
import rego.v1

default allow := false

allow if {
  input.user.role == "admin"
  count(violations) == 0
}

violations contains msg if {
  svc := input.services[_]
  svc.public
  svc.protocol == "http"
  msg := sprintf("service %v is public over http", [svc.name])
}`;

const sampleInput = `{
  "user": {"role": "admin"},
  "services": [
    {"name": "frontend", "public": true, "protocol": "http"},
    {"name": "api", "public": false, "protocol": "https"}
  ]
}`;

const policyText = document.querySelector("#policy-text");
const requestText = document.querySelector("#request-text");
const requestTabs = document.querySelector("#playground-request-tabs");
const requestHeading = document.querySelector("#playground-request-heading");
const queryText = document.querySelector("#query-text");
const whyBindings = document.querySelector("#flag-why-bindings");
const whyFullValues = document.querySelector("#flag-why-full-values");
const whyAllConditions = document.querySelector("#flag-why-all-conditions");
const whyAssumeUnknown = document.querySelector("#flag-assume-unknown");
const detailSelect = document.querySelector("#detail-select");
const resultView = document.querySelector("#playground-result");
const whyView = document.querySelector("#playground-why");
const conditionsView = document.querySelector("#playground-conditions");
const assumptionsView = document.querySelector("#playground-assumptions");
const assumptionPanel = document.querySelector("#playground-assumption-panel");
const runtimeChip = document.querySelector("#playground-runtime");
const runButton = document.querySelector("#run-playground");
const loadSampleButton = document.querySelector("#load-sample");
const analysisPanel = document.querySelector("#playground-analysis-panel");
const policyEditor = createCodeEditor(policyText, { language: "rego" });
const requestEditor = createCodeEditor(requestText, { language: "json" });
const requestState = {
  activeTab: "input",
  input: sampleInput,
  data: "{}"
};

function renderRequestTabs() {
  requestTabs.innerHTML = "";

  ["input", "data"].forEach((key) => {
    const button = document.createElement("button");
    button.type = "button";
    button.className = `tab-button${requestState.activeTab === key ? " active" : ""}`;
    button.textContent = key;
    button.addEventListener("click", () => {
      requestState.activeTab = key;
      renderRequestTabs();
    });
    requestTabs.appendChild(button);
  });

  requestHeading.textContent = requestState.activeTab === "data" ? "Data" : "Input";
  requestEditor.setValue(requestState[requestState.activeTab] || "{}");
}

function syncRequestDraft() {
  requestState[requestState.activeTab] = requestEditor.getValue();
}

function focusAnalysis() {
  analysisPanel?.scrollIntoView({
    behavior: "smooth",
    block: "start"
  });
}

async function runPlayground() {
  runButton.disabled = true;
  resultView.textContent = "Running…";
  whyView.textContent = "Running…";
  conditionsView.innerHTML = '<div class="loading-card">Running in wasm…</div>';
  requestAnimationFrame(focusAnalysis);

  try {
    const payload = await evaluateCustom({
      policy: policyEditor.getValue(),
      data: requestState.data,
      input: requestState.input,
      query: queryText.value,
      engine: "rvm",
      whyBindings: whyBindings.checked,
      whyFullValues: whyFullValues.checked,
      whyAllConditions: whyAllConditions.checked,
      assumeUnknownInput: whyAssumeUnknown?.checked ?? false,
      detail: detailSelect?.value ?? "standard"
    });

    runtimeChip.textContent = payload.runtimeMs ? `${payload.runtimeMs} ms` : "";
    resultView.textContent = formatJson(payload.result);
    whyView.textContent = formatJson(payload.why);
    renderConditionCards(conditionsView, payload.why.reasons || []);
    const assumptions = payload.assumptions || [];
    if (assumptionPanel) {
      assumptionPanel.style.display = assumptions.length ? "" : "none";
    }
    if (assumptionsView) {
      renderAssumptionCards(assumptionsView, assumptions);
    }
    requestAnimationFrame(focusAnalysis);
  } catch (error) {
    runtimeChip.textContent = "error";
    resultView.textContent = error.message;
    whyView.textContent = error.message;
    conditionsView.innerHTML = `<div class="error-banner">${error.message}</div>`;
    requestAnimationFrame(focusAnalysis);
  } finally {
    runButton.disabled = false;
  }
}

loadSampleButton.addEventListener("click", () => {
  policyEditor.setValue(samplePolicy);
  requestState.input = sampleInput;
  requestState.data = "{}";
  requestState.activeTab = "input";
  renderRequestTabs();
  queryText.value = "data.demo.allow";
  whyBindings.checked = false;
  whyFullValues.checked = false;
  whyAllConditions.checked = true;
});

requestText.addEventListener("input", syncRequestDraft);
runButton.addEventListener("click", runPlayground);

async function bootstrap() {
  loadSampleButton.click();
  try {
    await initRuntime();
    runtimeChip.textContent = "ready";
  } catch (error) {
    runtimeChip.textContent = "error";
    resultView.textContent = error.message;
    whyView.textContent = error.message;
    conditionsView.innerHTML = `<div class="error-banner">${error.message}</div>`;
    runButton.disabled = true;
  }
}

bootstrap();