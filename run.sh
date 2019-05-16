i="gm17_sw6_3072"
echo "Start run with $i bytes input"
cargo test --release -- --nocapture prove_and_verify_blake2s_cicruit_sw6 2>&1 cargo_log_$i.txt &
sleep 5
pid=$(ps auxh | awk -v max=0 '{if($3>max){CPU=$3; PID=$2; NAME=$11; max=$3}} END{printf "%6d",PID}')
python ps_mem.py -p $pid -w 10 > mem_log_$i.txt
