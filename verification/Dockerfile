# syntax=docker/dockerfile:1.7@sha256:a57df69d0ea827fb7266491f2813635de6f17269be881f696fbfdf2d83dda33e

FROM --platform=linux/amd64 docker.io/library/rust:1.95.0-bookworm@sha256:4c2fd73ef19c5ef9d54bee03b06b2839a392604fbfcd578ed948b71b37c1d7fb AS rust_toolchain

FROM --platform=linux/amd64 docker.io/library/python:3.13.7-bookworm@sha256:dff7bf7639ce459600e6e042228480eb9b6c627ce590e282c9b1d7c03fcad30b AS tool_builder

ARG VERUS_VERSION=0.2026.05.24.ecee80a

ADD --checksum=sha256:f9bfc2c35622b41bf64a99c2885e2de0b9a134219479fdb0d6bc2c3849b82719 \
    https://static.crates.io/crates/automation-structures/automation-structures-0.4.0.crate \
    /tmp/automation-structures.crate
RUN mkdir -p /opt/automation-structures \
    && tar -xzf /tmp/automation-structures.crate -C /opt/automation-structures --strip-components=1 \
    && test -f /opt/automation-structures/src/lib.rs \
    && test -f /opt/automation-structures/verification/run_verus_gate.sh \
    && test -f /opt/automation-structures/.cargo_vcs_info.json \
    && rm /tmp/automation-structures.crate

ADD --checksum=sha256:4b2220e232a97997b436ca6ab15cbf70171ecff52958a46159dfa5a8c44ca4de \
    https://github.com/adoptium/temurin21-binaries/releases/download/jdk-21.0.11%2B10/OpenJDK21U-jdk_x64_linux_hotspot_21.0.11_10.tar.gz \
    /tmp/jdk.tar.gz
RUN mkdir -p /opt/java \
    && tar -xzf /tmp/jdk.tar.gz -C /opt/java --strip-components=1 \
    && rm /tmp/jdk.tar.gz

ADD --checksum=sha256:323a44c0d787ce9a788665e1c6922360c44a72d1b9696359ec4f7bf5fbbc63e6 \
    https://github.com/verus-lang/verus/releases/download/release%2F0.2026.05.24.ecee80a/verus-0.2026.05.24.ecee80a-x86-linux.zip \
    /tmp/verus.zip
RUN mkdir -p /opt/verus \
    && cd /opt/verus \
    && /opt/java/bin/jar -xf /tmp/verus.zip \
    && chmod 0555 /opt/verus/verus-x86-linux/verus \
                  /opt/verus/verus-x86-linux/cargo-verus \
                  /opt/verus/verus-x86-linux/rust_verify \
                  /opt/verus/verus-x86-linux/z3 \
                  /opt/verus/verus-x86-linux/verus-root \
    && test -x /opt/verus/verus-x86-linux/verus \
    && rm /tmp/verus.zip

ADD --checksum=sha256:ebb7a3f271bdb564f74cb0a2767ef7b9ff7045621a9be7c50d363a03c2e6f08a \
    https://github.com/tlaplus/tlapm/releases/download/202210041448/tlaps-1.5.0-x86_64-linux-gnu-inst.bin \
    /tmp/tlaps.bin
RUN chmod 0555 /tmp/tlaps.bin \
    && /tmp/tlaps.bin -d /opt/tlaps \
    && rm /tmp/tlaps.bin \
    && sed -i \
       's|^ISABELLE_TMP_PREFIX="/tmp/isabelle-$USER"$|ISABELLE_TMP_PREFIX="${ISABELLE_TMP_PREFIX:-/tmp/isabelle-$USER}"|' \
       /opt/tlaps/lib/tlaps/Isabelle2011-1/etc/settings \
    && grep -Fqx \
       'ISABELLE_TMP_PREFIX="${ISABELLE_TMP_PREFIX:-/tmp/isabelle-$USER}"' \
       /opt/tlaps/lib/tlaps/Isabelle2011-1/etc/settings \
    && test "$(ISABELLE_TMP_PREFIX=/tmp/isabelle-contract-probe \
       /opt/tlaps/lib/tlaps/Isabelle2011-1/bin/isabelle \
       getenv -b ISABELLE_TMP_PREFIX)" = /tmp/isabelle-contract-probe

COPY --chmod=0444 toolchain/tla2tools.jar /opt/tlaplus/tla2tools.jar
RUN echo "ab323b79802aedc3203b3f9af37c6aca3ed43f4e0225b36f2aa77b26de46c05f  /opt/tlaplus/tla2tools.jar" \
    | sha256sum --check --strict

FROM --platform=linux/amd64 docker.io/library/python:3.13.7-bookworm@sha256:dff7bf7639ce459600e6e042228480eb9b6c627ce590e282c9b1d7c03fcad30b

ARG VERUS_VERSION=0.2026.05.24.ecee80a

COPY --from=rust_toolchain /usr/local/cargo /usr/local/cargo
COPY --from=rust_toolchain /usr/local/rustup /usr/local/rustup
COPY --from=tool_builder /opt/java /opt/java
COPY --from=tool_builder /opt/verus /opt/verus
COPY --from=tool_builder /opt/tlaps /opt/tlaps
COPY --from=tool_builder /opt/tlaplus /opt/tlaplus
COPY --from=tool_builder /opt/automation-structures /opt/automation-structures

ENV JAVA_HOME=/opt/java \
    RUSTUP_HOME=/usr/local/rustup \
    CARGO_HOME=/usr/local/cargo \
    VERUS_BIN=/opt/verus/verus-x86-linux/verus \
    RUSTUP_BIN=/usr/local/cargo/bin/rustup \
    PY=/usr/local/bin/python3 \
    AUTOMATION_STRUCTURE_ROOT=/source/automation-structure-research \
    AUTOMATION_STRUCTURES_CRATE_ROOT=/opt/automation-structures \
    AUTOMATION_STRUCTURE_PROOF_CONTAINER=1 \
    AUTOMATION_STRUCTURE_VERIFIER_VERSION=0.5.2 \
    PATH=/opt/java/bin:/opt/tlaps/bin:/opt/verus/verus-x86-linux:/usr/local/cargo/bin:/usr/local/bin:/usr/bin:/bin

RUN rustup component add rustfmt clippy --toolchain 1.95.0-x86_64-unknown-linux-gnu \
    && cargo fetch --locked --manifest-path /opt/automation-structures/Cargo.toml \
    && cargo metadata --locked --offline --all-features --manifest-path /opt/automation-structures/Cargo.toml --format-version 1 > /dev/null \
    && chmod -R a+rX /usr/local/cargo/registry \
    && install -d -m 0755 -o 65532 -g 65532 /target \
    && rustc --version \
    && rustfmt --version \
    && clippy-driver --version \
    && python3 --version \
    && java -version \
    && tlapm --version \
    && verus --version

COPY --chmod=0555 run_proofs.py /usr/local/bin/run_proofs.py

LABEL org.opencontainers.image.title="Automation Structure formal verifier" \
      org.opencontainers.image.description="Pinned, offline runtime for TLC, TLAPS, Verus, and executable cross-checks" \
      org.opencontainers.image.version="0.5.2" \
      org.opencontainers.image.source="automation-structure-research/verification/Dockerfile" \
      io.automation-structures.verus.version="${VERUS_VERSION}" \
      io.automation-structures.crate.version="0.4.0" \
      io.automation-structures.crate.sha256="f9bfc2c35622b41bf64a99c2885e2de0b9a134219479fdb0d6bc2c3849b82719" \
      io.automation-structures.crate.vcs-sha1="cd414aaeb4b2b17bcd32d1444f8bb486a6ca4bb2" \
      io.automation-structures.tla-tools.version="2026.08.11.125311" \
      io.automation-structures.tla-tools.sha256="ab323b79802aedc3203b3f9af37c6aca3ed43f4e0225b36f2aa77b26de46c05f" \
      io.automation-structures.tlaps.version="1.5.0" \
      io.automation-structures.rust.version="1.95.0" \
      io.automation-structures.python.version="3.13.7" \
      io.automation-structures.java.version="21.0.11+10"

USER 65532:65532
WORKDIR /work
ENTRYPOINT ["/usr/local/bin/python3", "/usr/local/bin/run_proofs.py"]
CMD ["list"]
