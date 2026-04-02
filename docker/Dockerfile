FROM ubuntu:26.04

ARG USERNAME=user
ARG UID=1000
ARG GID=1000

RUN apt-get -y update && \
    apt-get -y upgrade && \
    apt-get -y install build-essential zsh git curl libncurses5-dev opam libgmp-dev pkg-config

RUN if getent group ${GID} >/dev/null; then \
        GROUPNAME=$(getent group ${GID} | cut -d: -f1); \
    else \
        groupadd -g ${GID} ${USERNAME}; \
        GROUPNAME=${USERNAME}; \
    fi && \
    if getent passwd ${UID} >/dev/null; then \
        EXISTING_USER=$(getent passwd ${UID} | cut -d: -f1); \
        usermod -s /bin/zsh ${EXISTING_USER}; \
        mkdir -p /home/${EXISTING_USER}; \
    else \
        useradd -m -s /bin/zsh -u ${UID} -g ${GID} ${USERNAME}; \
        EXISTING_USER=${USERNAME}; \
    fi && \
    echo "Container user: ${EXISTING_USER}"

COPY zshrc /tmp/.zshrc

RUN TARGET_USER=$(getent passwd ${UID} | cut -d: -f1) && \
    TARGET_HOME=$(getent passwd ${UID} | cut -d: -f6) && \
    cp /tmp/.zshrc ${TARGET_HOME}/.zshrc && \
    chown ${UID}:${GID} ${TARGET_HOME}/.zshrc

# RUN bash -c "sh <(curl -fsSL https://opam.ocaml.org/install.sh)"

USER ${TARGET_USER}
WORKDIR ${TARGET_HOME}
ENV HOME=${TARGET_HOME}

RUN whoami && id && echo "HOME=$HOME"

RUN opam init --disable-sandboxing --yes --auto-setup && \
    eval $(opam env)

RUN opam repo add rocq-released https://rocq-prover.org/opam/released && \
    opam update && \
    opam install -y rocq-prover rocq-stdlib vsrocq-language-server

RUN curl -fsSL https://claude.ai/install.sh | bash

CMD ["/bin/zsh"]
