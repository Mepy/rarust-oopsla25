LLBC_PATH="../evaluation/benchmark/benchmark.llbc"
RESULT_PATH="../benchmark.result"
cd charon && make && cd ..
cd evaluation/benchmark && ../../charon/bin/charon && cd ../..
cd rarust && cargo run >/dev/null -- $LLBC_PATH $RESULT_PATH  && cd ..