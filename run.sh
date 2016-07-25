#!/bin/bash
T="$(date +%s)"
dir=$(pwd)
echo "Computing potential Conflicts"
./main $1 $2

cd $2;

conflicts=() #array with BCs
for check_file in `ls *.ltl`; do
	> $check_file.OUT
	c=$(head -n 1 $check_file)
	echo
	echo "Filtering: $c" 
	inconsistency=true
	ok=true
	while read -r line; do
		#call SAT
		echo "$line"
		res=`echo "$line"| $dir/pltl tree | awk 'NF'`
		echo "$res" 
    	echo "$res"  >> $check_file.OUT
		if $inconsistency ;  
		then
			if [[ $res == *unsatisfiable ]] 
			then
				inconsistency=false
			else
				ok=false
				break
			fi
		else #checking minimality
    		#echo "$line"	
    		if [[ $res == *unsatisfiable ]]
    		then
				ok=false
				break
			fi
    	fi
  	done <<< "$(tail -n +2 $check_file)"
  	if $ok ; then
  		conflicts+=("$c")
  	fi
done
echo
echo "#BCs: ${#conflicts[@]}"
echo "Computed BCs:"
for i in "${conflicts[@]}"
do
	echo $i
done

T="$(($(date +%s)-T))"
echo
echo "TOTAL execution time (secs) ${T}"