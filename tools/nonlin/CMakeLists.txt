add_executable (theoref TheorefSolver.cpp)
target_link_libraries (theoref ${Z3_LIBRARY} ${Boost_SYSTEM_LIBRARY} ${GMPXX_LIB} ${GMP_LIB})
llvm_config (theoref bitwriter)
install(TARGETS theoref RUNTIME DESTINATION bin)
