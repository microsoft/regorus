function escapeHtml(value) {
  return value
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;");
}

function highlightWithPattern(source, pattern, classify) {
  let cursor = 0;
  let output = "";

  source.replace(pattern, (match, ...groups) => {
    const offset = groups.at(-2);
    output += escapeHtml(source.slice(cursor, offset));
    output += `<span class="${classify(match)}">${escapeHtml(match)}</span>`;
    cursor = offset + match.length;
    return match;
  });

  output += escapeHtml(source.slice(cursor));
  return output;
}

function highlightJson(source) {
  const jsonPattern = /"(?:\\.|[^"\\])*"(?=\s*:)|"(?:\\.|[^"\\])*"|\btrue\b|\bfalse\b|\bnull\b|-?\b\d+(?:\.\d+)?(?:[eE][+-]?\d+)?\b|[{}\[\],:]/g;
  return highlightWithPattern(source, jsonPattern, (match) => {
    if (match.startsWith('"')) {
      return /"(?:\\.|[^"\\])*"(?=\s*:)$/.test(match)
        ? "token token-key"
        : "token token-string";
    }
    if (/^(true|false)$/.test(match)) {
      return "token token-boolean";
    }
    if (match === "null") {
      return "token token-null";
    }
    if (/^-?\b\d/.test(match)) {
      return "token token-number";
    }
    return "token token-punctuation";
  });
}

function highlightRego(source) {
  const regoPattern = /#.*$|"(?:\\.|[^"\\])*"|`[^`]*`|\b(?:package|import|default|if|contains|some|every|not|in|with|else|true|false|null)\b|-?\b\d+(?:\.\d+)?\b|\bdata\b|\binput\b|\bcount\b|\bstartswith\b|\bendswith\b|\blower\b|\bsprintf\b|:=|==|!=|>=|<=|>|<|[{}\[\](),.:]/gm;
  return highlightWithPattern(source, regoPattern, (match) => {
    if (match.startsWith("#")) {
      return "token token-comment";
    }
    if (match.startsWith('"') || match.startsWith("`")) {
      return "token token-string";
    }
    if (/^(package|import|default|if|contains|some|every|not|in|with|else)$/.test(match)) {
      return "token token-keyword";
    }
    if (/^(true|false|null)$/.test(match)) {
      return "token token-boolean";
    }
    if (/^(data|input|count|startswith|endswith|lower|sprintf)$/.test(match)) {
      return "token token-builtin";
    }
    if (/^-?\b\d/.test(match)) {
      return "token token-number";
    }
    if (/^(:=|==|!=|>=|<=|>|<)$/.test(match)) {
      return "token token-operator";
    }
    return "token token-punctuation";
  });
}

function highlightText(source, language) {
  if (!source) {
    return "<br />";
  }

  const normalized = source.endsWith("\n") ? `${source} ` : source;
  const highlighted = language === "json"
    ? highlightJson(normalized)
    : highlightRego(normalized);

  return highlighted.replaceAll("\n", "<br />");
}

function handleTabInsertion(textarea) {
  textarea.addEventListener("keydown", (event) => {
    if (event.key !== "Tab") {
      return;
    }

    event.preventDefault();
    const { selectionStart, selectionEnd, value } = textarea;
    const updatedValue = `${value.slice(0, selectionStart)}  ${value.slice(selectionEnd)}`;
    textarea.value = updatedValue;
    textarea.setSelectionRange(selectionStart + 2, selectionStart + 2);
    textarea.dispatchEvent(new Event("input", { bubbles: true }));
  });
}

export function createCodeEditor(textarea, options = {}) {
  const language = options.language ?? "rego";
  const wrapper = document.createElement("div");
  wrapper.className = "code-editor-shell";

  const pre = document.createElement("pre");
  pre.className = "code-editor-highlight";
  pre.setAttribute("aria-hidden", "true");

  const code = document.createElement("code");
  code.className = `code-editor-language-${language}`;
  pre.appendChild(code);

  textarea.parentNode.insertBefore(wrapper, textarea);
  wrapper.appendChild(pre);
  wrapper.appendChild(textarea);
  textarea.classList.add("code-editor-input");

  const render = () => {
    code.innerHTML = highlightText(textarea.value, editor.language);
  };

  const syncScroll = () => {
    pre.scrollTop = textarea.scrollTop;
    pre.scrollLeft = textarea.scrollLeft;
  };

  handleTabInsertion(textarea);
  textarea.addEventListener("input", render);
  textarea.addEventListener("scroll", syncScroll);

  const editor = {
    language,
    element: textarea,
    setValue(value) {
      textarea.value = value;
      render();
      syncScroll();
    },
    getValue() {
      return textarea.value;
    },
    refresh() {
      render();
      syncScroll();
    }
  };

  render();
  return editor;
}