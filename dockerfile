FROM rust:1.83.0
RUN mkdir rarust-oopsla25
COPY . /rarust-oopsla25/
RUN cd rarust-oopsla25 && \
    sh coincbc.sh && \
    sh reproduce.sh