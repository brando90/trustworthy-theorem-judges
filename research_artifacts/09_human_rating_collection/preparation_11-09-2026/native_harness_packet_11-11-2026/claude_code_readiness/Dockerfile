FROM exp07-agentic-clean:latest AS lean_cache
FROM node:22.19.0-bookworm-slim AS node_runtime
FROM ubuntu:24.04
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates curl git python3 build-essential libatomic1 && rm -rf /var/lib/apt/lists/*
RUN useradd -m -u 1001 -s /bin/bash user
COPY --from=node_runtime /usr/local/bin/node /usr/bin/node
COPY --from=node_runtime /usr/local/lib/node_modules/npm /usr/lib/node_modules/npm
RUN ln -s /usr/lib/node_modules/npm/bin/npm-cli.js /usr/bin/npm && ln -s /usr/lib/node_modules/npm/bin/npx-cli.js /usr/bin/npx
RUN npm install -g @anthropic-ai/claude-code@2.1.322 @earendil-works/pi-coding-agent@1.5.2
COPY --from=lean_cache --chown=user:user /home/agent/.elan /home/user/.elan
COPY --from=lean_cache --chown=user:user /home/agent/lean_project/.lake/packages /home/user/lean_project/.lake/packages
COPY --from=lean_cache --chown=user:user /home/agent/lean_project/lean-toolchain /home/user/lean_project/lean-toolchain
COPY --from=lean_cache --chown=user:user /home/agent/lean_project/lakefile.toml /home/user/lean_project/lakefile.toml
COPY --from=lean_cache --chown=user:user /home/agent/lean_project/lake-manifest.json /home/user/lean_project/lake-manifest.json
RUN rm -f /home/user/.elan/known-projects && mkdir -p /workspace /home/user/lean_project/Veribench && chown -R user:user /workspace /home/user/lean_project/Veribench
ENV PATH="/home/user/.elan/bin:/usr/local/bin:/usr/bin:/bin"
USER user
WORKDIR /home/user/lean_project
RUN lean --version && claude --version && pi --version && printf 'import Mathlib\n#check Nat\n' > /tmp/check.lean && lake env lean /tmp/check.lean && rm /tmp/check.lean
