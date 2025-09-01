FROM mcr.microsoft.com/devcontainers/base:jammy

USER vscode
WORKDIR /home/vscode

RUN curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain none

# Install Python and Graphviz prerequisites for LeanBlueprint
RUN sudo apt-get update -y && \
    sudo apt-get install -y python3 python3-pip graphviz libgraphviz-dev && \
    pip install --no-cache-dir leanblueprint

ENV PATH="/home/vscode/.elan/bin:${PATH}"