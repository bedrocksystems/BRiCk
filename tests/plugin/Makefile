CPP2V=$(shell which cpp2v)
CPP2V_PATH=$(shell dirname ${CPP2V})
CPP2V_PLUGIN=${CPP2V_PATH}/libcpp2v_plugin.so

LOAD_PLUGIN=-Xclang -load -Xclang ${CPP2V_PLUGIN} -Xclang -add-plugin -Xclang cpp2v
OUT_OPTION=-Xclang -plugin-arg-cpp2v -Xclang -o -Xclang -plugin-arg-cpp2v -Xclang
SPEC_OPTION=-Xclang -plugin-arg-cpp2v -Xclang -spec -Xclang -plugin-arg-cpp2v -Xclang

COQPATH=-Q ../../theories Cpp

all: demo_cpp.v demo_cpp.vo demo_cpp_spec.vo

config:
	@ echo ${CPP2V_PATH}

demo_cpp.v demo.o demo_cpp_spec.v: demo.cpp $(CPP2V)
	clang++ ${LOAD_PLUGIN} ${OUT_OPTION} demo_cpp.v ${SPEC_OPTION} demo_cpp_spec.v $< -c

demo_cpp.vo: demo_cpp.v
	coqc ${COQPATH} demo_cpp.v

demo_cpp_spec.vo: demo_cpp_spec.v
	coqc ${COQPATH} demo_cpp_spec.v
