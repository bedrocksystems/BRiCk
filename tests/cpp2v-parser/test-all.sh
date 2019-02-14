CPP2V=./../cpp2v
COQC=coqc
TESTS=`seq 1 15`

for x in $TESTS
do
    echo "Running test$x..."
    ${CPP2V} test$x.cpp -- > test${x}_cpp.v
    ${COQC} -Q ../../theories Cpp test${x}_cpp.v
done
