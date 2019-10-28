add_executable (bv Bv.cpp)
target_link_libraries (bv ${Z3_LIBRARY} ${Boost_SYSTEM_LIBRARY} ${GMPXX_LIB} ${GMP_LIB})
llvm_config (bv bitwriter)
install(TARGETS bv RUNTIME DESTINATION bin)
