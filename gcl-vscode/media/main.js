const vscode = acquireVsCodeApi();

/**
 * @type {EventListener}
 */
function handleReduce(event) {
  event.stopPropagation();

  const el = event.target;

  const redex = el.dataset.redex.split(",").map(Number);
  const po = Number(el.closest(".gcl-expr").dataset.po);

  vscode.postMessage({
    po,
    redex,
  });
}

const redexes = document.querySelectorAll(".gcl-redex");

for (const redex of redexes) {
  redex.addEventListener("click", handleReduce);
}
