# Run the following commands from root directory to build and run locally
# docker build -f automation/Dockerfile -t <NAME> .
# docker run -it <NAME>
FROM rust:latest
RUN apt-get update
RUN apt-get --yes upgrade
# tzdata is a dependency, won't install otherwise
ARG DEBIAN_FRONTEND=noninteractive

RUN rustup target add thumbv6m-none-eabi armv7-unknown-linux-gnueabihf \
	thumbv7em-none-eabihf x86_64-unknown-linux-gnu && \
	rustup component add rustfmt clippy
