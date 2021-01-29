onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -expand -group offload_xbar /acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/valid_o
add wave -noupdate -expand -group offload_xbar /acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/ready_i
add wave -noupdate -expand -group offload_xbar /acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/sel_i
add wave -noupdate -expand -group offload_xbar /acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/valid_i
add wave -noupdate -expand -group offload_xbar /acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/ready_o
add wave -noupdate -expand -group offload_xbar /acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/SelWidth
add wave -noupdate -expand -group offload_xbar /acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/rst_ni
add wave -noupdate -expand -group offload_xbar /acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/rr_i
add wave -noupdate -expand -group offload_xbar /acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/OutSpillReg
add wave -noupdate -expand -group offload_xbar /acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/out_valid
add wave -noupdate -expand -group offload_xbar /acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/out_ready
add wave -noupdate -expand -group offload_xbar /acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/out_data
add wave -noupdate -expand -group offload_xbar /acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/NumOut
add wave -noupdate -expand -group offload_xbar /acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/NumInp
add wave -noupdate -expand -group offload_xbar /acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/LockIn
add wave -noupdate -expand -group offload_xbar /acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/inp_valid
add wave -noupdate -expand -group offload_xbar /acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/inp_ready
add wave -noupdate -expand -group offload_xbar /acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/IdxWidth
add wave -noupdate -expand -group offload_xbar /acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/idx_o
add wave -noupdate -expand -group offload_xbar /acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/flush_i
add wave -noupdate -expand -group offload_xbar /acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/ExtPrio
add wave -noupdate -expand -group offload_xbar /acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/DataWidth
add wave -noupdate -expand -group offload_xbar /acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/data_o
add wave -noupdate -expand -group offload_xbar /acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/data_i
add wave -noupdate -expand -group offload_xbar /acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/clk_i
add wave -noupdate -expand -group offload_xbar /acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/AxiVldRdy
add wave -noupdate -expand -group offload_xbar {/acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/gen_outs[0]/spill}
add wave -noupdate -expand -group offload_xbar {/acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/gen_outs[0]/j}
add wave -noupdate -expand -group offload_xbar {/acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/gen_outs[0]/arb_valid}
add wave -noupdate -expand -group offload_xbar {/acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/gen_outs[0]/arb_ready}
add wave -noupdate -expand -group offload_xbar {/acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/gen_outs[0]/arb}

add wave -noupdate -expand -group response_xbar /acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/valid_o
add wave -noupdate -expand -group response_xbar /acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/ready_i
add wave -noupdate -expand -group response_xbar /acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/sel_i
add wave -noupdate -expand -group response_xbar /acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/valid_i
add wave -noupdate -expand -group response_xbar /acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/ready_o
add wave -noupdate -expand -group response_xbar /acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/SelWidth
add wave -noupdate -expand -group response_xbar /acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/rst_ni
add wave -noupdate -expand -group response_xbar /acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/rr_i
add wave -noupdate -expand -group response_xbar /acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/OutSpillReg
add wave -noupdate -expand -group response_xbar /acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/out_valid
add wave -noupdate -expand -group response_xbar /acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/out_ready
add wave -noupdate -expand -group response_xbar /acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/out_data
add wave -noupdate -expand -group response_xbar /acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/NumOut
add wave -noupdate -expand -group response_xbar /acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/NumInp
add wave -noupdate -expand -group response_xbar /acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/LockIn
add wave -noupdate -expand -group response_xbar /acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/inp_valid
add wave -noupdate -expand -group response_xbar /acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/inp_ready
add wave -noupdate -expand -group response_xbar /acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/IdxWidth
add wave -noupdate -expand -group response_xbar /acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/idx_o
add wave -noupdate -expand -group response_xbar /acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/flush_i
add wave -noupdate -expand -group response_xbar /acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/ExtPrio
add wave -noupdate -expand -group response_xbar /acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/DataWidth
add wave -noupdate -expand -group response_xbar /acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/data_o
add wave -noupdate -expand -group response_xbar /acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/data_i
add wave -noupdate -expand -group response_xbar /acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/clk_i
add wave -noupdate -expand -group response_xbar /acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/AxiVldRdy
add wave -noupdate -expand -group response_xbar {/acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/gen_outs[0]/spill}
add wave -noupdate -expand -group response_xbar {/acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/gen_outs[0]/j}
add wave -noupdate -expand -group response_xbar {/acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/gen_outs[0]/arb_valid}
add wave -noupdate -expand -group response_xbar {/acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/gen_outs[0]/arb_ready}
add wave -noupdate -expand -group response_xbar {/acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/gen_outs[0]/arb}
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {122000 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 578
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 0
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ps
update
WaveRestoreZoom {34459 ps} {135029 ps}
