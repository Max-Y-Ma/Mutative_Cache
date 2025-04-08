#/bin/bash

cd sim

if [ ! -f simulation.log ] || grep -v 'UVM_WARNING :\|UVM_ERROR :\|UVM_FATAL :' simulation.log | grep -iq 'error\|warning\|fatal'; 
then
    echo -e "\033[0;31mSim failed:\033[0m"
    grep -v 'UVM_WARNING :\|UVM_ERROR :\|UVM_FATAL :' simulation.log |\
    grep -i 'error\|warning\|fatal'
    exit 1
else
    echo -e "\033[0;32mSim Successful \033[0m"
fi

exit 0
