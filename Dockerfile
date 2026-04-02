FROM rocq/rocq-prover:9.1.0

WORKDIR /workspace
COPY . /workspace

# Prefer the modern rocq CLI; fall back to coqc if needed.
CMD ["sh", "-lc", "if command -v rocq >/dev/null 2>&1; then rocq compile integer.v; else coqc integer.v; fi"]
