import { evaluateCustom, formatJson, initRuntime, renderConditionCards, renderAssumptionCards, renderResidualQueries } from "./demo-core.js";
import { createCodeEditor } from "./code-editor.js";
import {
  buildShareUrl,
  loadStateFromLocation,
  writeShareTokenToLocation,
  encodeShareToken,
} from "./share.js";

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
const shareButton = document.querySelector("#share-playground");
const analysisPanel = document.querySelector("#playground-analysis-panel");
const evalModeSelect = document.querySelector("#eval-mode-select");
const unknownsRow = document.querySelector("#pg-unknowns-row");
const unknownsText = document.querySelector("#unknowns-text");
const pePanel = document.querySelector("#playground-pe-panel");
const peResults = document.querySelector("#playground-pe-results");
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
      detail: detailSelect?.value ?? "standard",
      evalMode: evalModeSelect?.value ?? "causality",
      unknowns: unknownsText?.value ?? "input"
    });

    runtimeChip.textContent = payload.runtimeMs ? `${payload.runtimeMs} ms` : "";
    resultView.textContent = formatJson(payload.result);
    whyView.textContent = payload.pe ? formatJson(payload.pe) : formatJson(payload.why);

    if (payload.pe) {
      // PE mode: show residual queries panel, hide causality condition cards
      conditionsView.innerHTML = '<div class="loading-card">Partial evaluation mode — see residual queries below.</div>';
      if (assumptionPanel) assumptionPanel.style.display = "none";
      if (pePanel) {
        pePanel.style.display = "";
        renderResidualQueries(peResults, payload.pe);
      }
    } else {
      // Causality mode
      if (pePanel) pePanel.style.display = "none";
      renderConditionCards(conditionsView, payload.why.reasons || []);
      const assumptions = payload.assumptions || [];
      if (assumptionPanel) {
        assumptionPanel.style.display = assumptions.length ? "" : "none";
      }
      if (assumptionsView) {
        renderAssumptionCards(assumptionsView, assumptions);
      }
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
evalModeSelect?.addEventListener("change", () => {
  const isPartial = evalModeSelect.value === "partial";
  unknownsRow.style.display = isPartial ? "" : "none";
  if (isPartial) {
    whyAssumeUnknown.checked = true;
    whyAssumeUnknown.disabled = true;
  } else {
    whyAssumeUnknown.disabled = false;
  }
});

function captureShareState() {
  // Make sure the in-memory request draft reflects whatever is in the editor
  // for the currently-active tab before snapshotting.
  syncRequestDraft();
  return {
    policy: policyEditor.getValue(),
    input: requestState.input,
    data: requestState.data,
    query: queryText?.value ?? "",
    evalMode: evalModeSelect?.value ?? "causality",
    unknowns: unknownsText?.value ?? "input",
    whyBindings: !!whyBindings?.checked,
    whyFullValues: !!whyFullValues?.checked,
    whyAllConditions: !!whyAllConditions?.checked,
    whyAssumeUnknown: !!whyAssumeUnknown?.checked,
    detail: detailSelect?.value ?? "standard",
  };
}

function applyShareState(state) {
  if (!state || typeof state !== "object") return;
  if (typeof state.policy === "string") policyEditor.setValue(state.policy);
  if (typeof state.input === "string") requestState.input = state.input;
  if (typeof state.data === "string") requestState.data = state.data;
  requestState.activeTab = "input";
  renderRequestTabs();
  if (queryText && typeof state.query === "string") queryText.value = state.query;
  if (evalModeSelect && typeof state.evalMode === "string") {
    evalModeSelect.value = state.evalMode;
    evalModeSelect.dispatchEvent(new Event("change"));
  }
  if (unknownsText && typeof state.unknowns === "string") {
    unknownsText.value = state.unknowns;
  }
  if (whyBindings && typeof state.whyBindings === "boolean") whyBindings.checked = state.whyBindings;
  if (whyFullValues && typeof state.whyFullValues === "boolean") whyFullValues.checked = state.whyFullValues;
  if (whyAllConditions && typeof state.whyAllConditions === "boolean") whyAllConditions.checked = state.whyAllConditions;
  if (whyAssumeUnknown && typeof state.whyAssumeUnknown === "boolean" && !whyAssumeUnknown.disabled) {
    whyAssumeUnknown.checked = state.whyAssumeUnknown;
  }
  if (detailSelect && typeof state.detail === "string") detailSelect.value = state.detail;
}

function showShareFeedback(message, kind = "ok") {
  // Lightweight transient feedback that doesn't require new CSS.  Reuses
  // the runtime chip slot so the message is visible without layout shift.
  if (!runtimeChip) return;
  const prev = runtimeChip.textContent;
  runtimeChip.textContent = message;
  runtimeChip.dataset.shareFeedback = kind;
  setTimeout(() => {
    if (runtimeChip.dataset.shareFeedback === kind) {
      runtimeChip.textContent = prev;
      delete runtimeChip.dataset.shareFeedback;
    }
  }, 2000);
}

async function copyShareLink() {
  try {
    const state = captureShareState();
    const url = await buildShareUrl(state);
    // Also reflect the token in the address bar so a manual copy works too.
    const token = await encodeShareToken(state);
    writeShareTokenToLocation(token);

    if (navigator.clipboard?.writeText) {
      await navigator.clipboard.writeText(url);
      showShareFeedback("link copied");
    } else {
      // Final fallback: select the URL in a temp textarea so the user can
      // copy manually.  Required on insecure contexts where clipboard is
      // not available.
      const ta = document.createElement("textarea");
      ta.value = url;
      ta.setAttribute("readonly", "");
      ta.style.position = "absolute";
      ta.style.left = "-9999px";
      document.body.appendChild(ta);
      ta.select();
      try {
        document.execCommand("copy");
        showShareFeedback("link copied");
      } finally {
        document.body.removeChild(ta);
      }
    }
  } catch (err) {
    showShareFeedback("share failed", "err");
    console.error("share failed", err);
  }
}

shareButton?.addEventListener("click", copyShareLink);

async function bootstrap() {
  // Start from sample so all DOM has a value (in case the share decode
  // doesn't populate every field — e.g. older link versions or partial
  // state).
  loadSampleButton.click();

  // If the URL fragment carries shared state, apply it over the sample.
  try {
    const shared = await loadStateFromLocation();
    if (shared) {
      applyShareState(shared);
    }
  } catch (err) {
    console.warn("failed to load shared state from URL:", err);
    showShareFeedback("bad link", "err");
  }

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