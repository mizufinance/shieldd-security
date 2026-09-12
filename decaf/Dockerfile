FROM binsec/binsec@sha256:19a0ff4b0278906bd6f00a5752cab19e8cad7153715cecf32d4f885826f62967
USER root
COPY decaf/install-tools.sh /tmp/decaf-install-tools.sh
RUN bash /tmp/decaf-install-tools.sh
RUN git config --system --add safe.directory /workspace
ENV CARGO_HOME=/opt/decaf/cargo RUSTUP_HOME=/opt/decaf/rustup
ENV PATH=/opt/decaf/cargo/bin:/opt/decaf/go/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin
WORKDIR /workspace
