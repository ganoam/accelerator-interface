onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /acc_interconnect_tb/dut/clk_i
add wave -noupdate /acc_interconnect_tb/dut/acc_interconnect_i/sender_id
add wave -noupdate /acc_interconnect_tb/dut/acc_interconnect_i/receiver_id
add wave -noupdate -expand -group {master[0]} {/acc_interconnect_tb/master[0]/q_valid}
add wave -noupdate -expand -group {master[0]} {/acc_interconnect_tb/master[0]/q_ready}
add wave -noupdate -expand -group {master[0]} {/acc_interconnect_tb/master[0]/q_id}
add wave -noupdate -expand -group {master[0]} {/acc_interconnect_tb/master[0]/q_data_op}
add wave -noupdate -expand -group {master[0]} {/acc_interconnect_tb/master[0]/q_data_argc}
add wave -noupdate -expand -group {master[0]} {/acc_interconnect_tb/master[0]/q_data_argb}
add wave -noupdate -expand -group {master[0]} {/acc_interconnect_tb/master[0]/q_data_arga}
add wave -noupdate -expand -group {master[0]} {/acc_interconnect_tb/master[0]/q_addr}
add wave -noupdate -expand -group {master[0]} {/acc_interconnect_tb/master[0]/p_valid}
add wave -noupdate -expand -group {master[0]} {/acc_interconnect_tb/master[0]/p_ready}
add wave -noupdate -expand -group {master[0]} {/acc_interconnect_tb/master[0]/p_id}
add wave -noupdate -expand -group {master[0]} {/acc_interconnect_tb/master[0]/p_error}
add wave -noupdate -expand -group {master[0]} {/acc_interconnect_tb/master[0]/p_data}
add wave -noupdate -expand -group {master[1]} {/acc_interconnect_tb/master[1]/q_valid}
add wave -noupdate -expand -group {master[1]} {/acc_interconnect_tb/master[1]/q_ready}
add wave -noupdate -expand -group {master[1]} {/acc_interconnect_tb/master[1]/q_id}
add wave -noupdate -expand -group {master[1]} {/acc_interconnect_tb/master[1]/q_data_op}
add wave -noupdate -expand -group {master[1]} {/acc_interconnect_tb/master[1]/q_data_argc}
add wave -noupdate -expand -group {master[1]} {/acc_interconnect_tb/master[1]/q_data_argb}
add wave -noupdate -expand -group {master[1]} {/acc_interconnect_tb/master[1]/q_data_arga}
add wave -noupdate -expand -group {master[1]} {/acc_interconnect_tb/master[1]/q_addr}
add wave -noupdate -expand -group {master[1]} {/acc_interconnect_tb/master[1]/p_valid}
add wave -noupdate -expand -group {master[1]} {/acc_interconnect_tb/master[1]/p_ready}
add wave -noupdate -expand -group {master[1]} {/acc_interconnect_tb/master[1]/p_id}
add wave -noupdate -expand -group {master[1]} {/acc_interconnect_tb/master[1]/p_error}
add wave -noupdate -expand -group {master[1]} {/acc_interconnect_tb/master[1]/p_data}
add wave -noupdate -group {master[2]} {/acc_interconnect_tb/master[2]/q_valid}
add wave -noupdate -group {master[2]} {/acc_interconnect_tb/master[2]/q_ready}
add wave -noupdate -group {master[2]} {/acc_interconnect_tb/master[2]/q_id}
add wave -noupdate -group {master[2]} {/acc_interconnect_tb/master[2]/q_data_op}
add wave -noupdate -group {master[2]} {/acc_interconnect_tb/master[2]/q_data_argc}
add wave -noupdate -group {master[2]} {/acc_interconnect_tb/master[2]/q_data_argb}
add wave -noupdate -group {master[2]} {/acc_interconnect_tb/master[2]/q_data_arga}
add wave -noupdate -group {master[2]} {/acc_interconnect_tb/master[2]/q_addr}
add wave -noupdate -group {master[2]} {/acc_interconnect_tb/master[2]/p_valid}
add wave -noupdate -group {master[2]} {/acc_interconnect_tb/master[2]/p_ready}
add wave -noupdate -group {master[2]} {/acc_interconnect_tb/master[2]/p_id}
add wave -noupdate -group {master[2]} {/acc_interconnect_tb/master[2]/p_error}
add wave -noupdate -group {master[2]} {/acc_interconnect_tb/master[2]/p_data}
add wave -noupdate -group {master[3]} {/acc_interconnect_tb/master[3]/q_valid}
add wave -noupdate -group {master[3]} {/acc_interconnect_tb/master[3]/q_ready}
add wave -noupdate -group {master[3]} {/acc_interconnect_tb/master[3]/q_id}
add wave -noupdate -group {master[3]} {/acc_interconnect_tb/master[3]/q_data_op}
add wave -noupdate -group {master[3]} {/acc_interconnect_tb/master[3]/q_data_argc}
add wave -noupdate -group {master[3]} {/acc_interconnect_tb/master[3]/q_data_argb}
add wave -noupdate -group {master[3]} {/acc_interconnect_tb/master[3]/q_data_arga}
add wave -noupdate -group {master[3]} {/acc_interconnect_tb/master[3]/q_addr}
add wave -noupdate -group {master[3]} {/acc_interconnect_tb/master[3]/p_valid}
add wave -noupdate -group {master[3]} {/acc_interconnect_tb/master[3]/p_ready}
add wave -noupdate -group {master[3]} {/acc_interconnect_tb/master[3]/p_id}
add wave -noupdate -group {master[3]} {/acc_interconnect_tb/master[3]/p_error}
add wave -noupdate -group {master[3]} {/acc_interconnect_tb/master[3]/p_data}
add wave -noupdate -group {master[4]} {/acc_interconnect_tb/master[4]/q_valid}
add wave -noupdate -group {master[4]} {/acc_interconnect_tb/master[4]/q_ready}
add wave -noupdate -group {master[4]} {/acc_interconnect_tb/master[4]/q_id}
add wave -noupdate -group {master[4]} {/acc_interconnect_tb/master[4]/q_data_op}
add wave -noupdate -group {master[4]} {/acc_interconnect_tb/master[4]/q_data_argc}
add wave -noupdate -group {master[4]} {/acc_interconnect_tb/master[4]/q_data_argb}
add wave -noupdate -group {master[4]} {/acc_interconnect_tb/master[4]/q_data_arga}
add wave -noupdate -group {master[4]} {/acc_interconnect_tb/master[4]/q_addr}
add wave -noupdate -group {master[4]} {/acc_interconnect_tb/master[4]/p_valid}
add wave -noupdate -group {master[4]} {/acc_interconnect_tb/master[4]/p_ready}
add wave -noupdate -group {master[4]} {/acc_interconnect_tb/master[4]/p_id}
add wave -noupdate -group {master[4]} {/acc_interconnect_tb/master[4]/p_error}
add wave -noupdate -group {master[4]} {/acc_interconnect_tb/master[4]/p_data}
add wave -noupdate -group {master[5]} {/acc_interconnect_tb/master[5]/q_valid}
add wave -noupdate -group {master[5]} {/acc_interconnect_tb/master[5]/q_ready}
add wave -noupdate -group {master[5]} {/acc_interconnect_tb/master[5]/q_id}
add wave -noupdate -group {master[5]} {/acc_interconnect_tb/master[5]/q_data_op}
add wave -noupdate -group {master[5]} {/acc_interconnect_tb/master[5]/q_data_argc}
add wave -noupdate -group {master[5]} {/acc_interconnect_tb/master[5]/q_data_argb}
add wave -noupdate -group {master[5]} {/acc_interconnect_tb/master[5]/q_data_arga}
add wave -noupdate -group {master[5]} {/acc_interconnect_tb/master[5]/q_addr}
add wave -noupdate -group {master[5]} {/acc_interconnect_tb/master[5]/p_valid}
add wave -noupdate -group {master[5]} {/acc_interconnect_tb/master[5]/p_ready}
add wave -noupdate -group {master[5]} {/acc_interconnect_tb/master[5]/p_id}
add wave -noupdate -group {master[5]} {/acc_interconnect_tb/master[5]/p_error}
add wave -noupdate -group {master[5]} {/acc_interconnect_tb/master[5]/p_data}
add wave -noupdate -group {master[6]} {/acc_interconnect_tb/master[6]/q_valid}
add wave -noupdate -group {master[6]} {/acc_interconnect_tb/master[6]/q_ready}
add wave -noupdate -group {master[6]} {/acc_interconnect_tb/master[6]/q_id}
add wave -noupdate -group {master[6]} {/acc_interconnect_tb/master[6]/q_data_op}
add wave -noupdate -group {master[6]} {/acc_interconnect_tb/master[6]/q_data_argc}
add wave -noupdate -group {master[6]} {/acc_interconnect_tb/master[6]/q_data_argb}
add wave -noupdate -group {master[6]} {/acc_interconnect_tb/master[6]/q_data_arga}
add wave -noupdate -group {master[6]} {/acc_interconnect_tb/master[6]/q_addr}
add wave -noupdate -group {master[6]} {/acc_interconnect_tb/master[6]/p_valid}
add wave -noupdate -group {master[6]} {/acc_interconnect_tb/master[6]/p_ready}
add wave -noupdate -group {master[6]} {/acc_interconnect_tb/master[6]/p_id}
add wave -noupdate -group {master[6]} {/acc_interconnect_tb/master[6]/p_error}
add wave -noupdate -group {master[6]} {/acc_interconnect_tb/master[6]/p_data}
add wave -noupdate -group {master[7]} {/acc_interconnect_tb/master[7]/q_valid}
add wave -noupdate -group {master[7]} {/acc_interconnect_tb/master[7]/q_ready}
add wave -noupdate -group {master[7]} {/acc_interconnect_tb/master[7]/q_id}
add wave -noupdate -group {master[7]} {/acc_interconnect_tb/master[7]/q_data_op}
add wave -noupdate -group {master[7]} {/acc_interconnect_tb/master[7]/q_data_argc}
add wave -noupdate -group {master[7]} {/acc_interconnect_tb/master[7]/q_data_argb}
add wave -noupdate -group {master[7]} {/acc_interconnect_tb/master[7]/q_data_arga}
add wave -noupdate -group {master[7]} {/acc_interconnect_tb/master[7]/q_addr}
add wave -noupdate -group {master[7]} {/acc_interconnect_tb/master[7]/p_valid}
add wave -noupdate -group {master[7]} {/acc_interconnect_tb/master[7]/p_ready}
add wave -noupdate -group {master[7]} {/acc_interconnect_tb/master[7]/p_id}
add wave -noupdate -group {master[7]} {/acc_interconnect_tb/master[7]/p_error}
add wave -noupdate -group {master[7]} {/acc_interconnect_tb/master[7]/p_data}
add wave -noupdate -group {slave[0]} {/acc_interconnect_tb/slave[0]/q_valid}
add wave -noupdate -group {slave[0]} {/acc_interconnect_tb/slave[0]/q_ready}
add wave -noupdate -group {slave[0]} {/acc_interconnect_tb/slave[0]/q_id}
add wave -noupdate -group {slave[0]} {/acc_interconnect_tb/slave[0]/q_data_op}
add wave -noupdate -group {slave[0]} {/acc_interconnect_tb/slave[0]/q_data_argc}
add wave -noupdate -group {slave[0]} {/acc_interconnect_tb/slave[0]/q_data_argb}
add wave -noupdate -group {slave[0]} {/acc_interconnect_tb/slave[0]/q_data_arga}
add wave -noupdate -group {slave[0]} {/acc_interconnect_tb/slave[0]/q_addr}
add wave -noupdate -group {slave[0]} {/acc_interconnect_tb/slave[0]/p_valid}
add wave -noupdate -group {slave[0]} {/acc_interconnect_tb/slave[0]/p_ready}
add wave -noupdate -group {slave[0]} {/acc_interconnect_tb/slave[0]/p_id}
add wave -noupdate -group {slave[0]} {/acc_interconnect_tb/slave[0]/p_error}
add wave -noupdate -group {slave[0]} {/acc_interconnect_tb/slave[0]/p_data}
add wave -noupdate -group {slave[1]} {/acc_interconnect_tb/slave[1]/q_valid}
add wave -noupdate -group {slave[1]} {/acc_interconnect_tb/slave[1]/q_ready}
add wave -noupdate -group {slave[1]} {/acc_interconnect_tb/slave[1]/q_id}
add wave -noupdate -group {slave[1]} {/acc_interconnect_tb/slave[1]/q_data_op}
add wave -noupdate -group {slave[1]} {/acc_interconnect_tb/slave[1]/q_data_argc}
add wave -noupdate -group {slave[1]} {/acc_interconnect_tb/slave[1]/q_data_argb}
add wave -noupdate -group {slave[1]} {/acc_interconnect_tb/slave[1]/q_data_arga}
add wave -noupdate -group {slave[1]} {/acc_interconnect_tb/slave[1]/q_addr}
add wave -noupdate -group {slave[1]} {/acc_interconnect_tb/slave[1]/p_valid}
add wave -noupdate -group {slave[1]} {/acc_interconnect_tb/slave[1]/p_ready}
add wave -noupdate -group {slave[1]} {/acc_interconnect_tb/slave[1]/p_id}
add wave -noupdate -group {slave[1]} {/acc_interconnect_tb/slave[1]/p_error}
add wave -noupdate -group {slave[1]} {/acc_interconnect_tb/slave[1]/p_data}
add wave -noupdate -group {slave[2]} {/acc_interconnect_tb/slave[2]/q_valid}
add wave -noupdate -group {slave[2]} {/acc_interconnect_tb/slave[2]/q_ready}
add wave -noupdate -group {slave[2]} {/acc_interconnect_tb/slave[2]/q_id}
add wave -noupdate -group {slave[2]} {/acc_interconnect_tb/slave[2]/q_data_op}
add wave -noupdate -group {slave[2]} {/acc_interconnect_tb/slave[2]/q_data_argc}
add wave -noupdate -group {slave[2]} {/acc_interconnect_tb/slave[2]/q_data_argb}
add wave -noupdate -group {slave[2]} {/acc_interconnect_tb/slave[2]/q_data_arga}
add wave -noupdate -group {slave[2]} {/acc_interconnect_tb/slave[2]/q_addr}
add wave -noupdate -group {slave[2]} {/acc_interconnect_tb/slave[2]/p_valid}
add wave -noupdate -group {slave[2]} {/acc_interconnect_tb/slave[2]/p_ready}
add wave -noupdate -group {slave[2]} {/acc_interconnect_tb/slave[2]/p_id}
add wave -noupdate -group {slave[2]} {/acc_interconnect_tb/slave[2]/p_error}
add wave -noupdate -group {slave[2]} {/acc_interconnect_tb/slave[2]/p_data}
add wave -noupdate -group {slave[3]} {/acc_interconnect_tb/slave[3]/q_valid}
add wave -noupdate -group {slave[3]} {/acc_interconnect_tb/slave[3]/q_ready}
add wave -noupdate -group {slave[3]} {/acc_interconnect_tb/slave[3]/q_id}
add wave -noupdate -group {slave[3]} {/acc_interconnect_tb/slave[3]/q_data_op}
add wave -noupdate -group {slave[3]} {/acc_interconnect_tb/slave[3]/q_data_argc}
add wave -noupdate -group {slave[3]} {/acc_interconnect_tb/slave[3]/q_data_argb}
add wave -noupdate -group {slave[3]} {/acc_interconnect_tb/slave[3]/q_data_arga}
add wave -noupdate -group {slave[3]} {/acc_interconnect_tb/slave[3]/q_addr}
add wave -noupdate -group {slave[3]} {/acc_interconnect_tb/slave[3]/p_valid}
add wave -noupdate -group {slave[3]} {/acc_interconnect_tb/slave[3]/p_ready}
add wave -noupdate -group {slave[3]} {/acc_interconnect_tb/slave[3]/p_id}
add wave -noupdate -group {slave[3]} {/acc_interconnect_tb/slave[3]/p_error}
add wave -noupdate -group {slave[3]} {/acc_interconnect_tb/slave[3]/p_data}
add wave -noupdate -group {slave[4]} {/acc_interconnect_tb/slave[4]/q_valid}
add wave -noupdate -group {slave[4]} {/acc_interconnect_tb/slave[4]/q_ready}
add wave -noupdate -group {slave[4]} {/acc_interconnect_tb/slave[4]/q_id}
add wave -noupdate -group {slave[4]} {/acc_interconnect_tb/slave[4]/q_data_op}
add wave -noupdate -group {slave[4]} {/acc_interconnect_tb/slave[4]/q_data_argc}
add wave -noupdate -group {slave[4]} {/acc_interconnect_tb/slave[4]/q_data_argb}
add wave -noupdate -group {slave[4]} {/acc_interconnect_tb/slave[4]/q_data_arga}
add wave -noupdate -group {slave[4]} {/acc_interconnect_tb/slave[4]/q_addr}
add wave -noupdate -group {slave[4]} {/acc_interconnect_tb/slave[4]/p_valid}
add wave -noupdate -group {slave[4]} {/acc_interconnect_tb/slave[4]/p_ready}
add wave -noupdate -group {slave[4]} {/acc_interconnect_tb/slave[4]/p_id}
add wave -noupdate -group {slave[4]} {/acc_interconnect_tb/slave[4]/p_error}
add wave -noupdate -group {slave[4]} {/acc_interconnect_tb/slave[4]/p_data}
add wave -noupdate -group offload_xbar /acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/valid_i
add wave -noupdate -group offload_xbar /acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/valid_o
add wave -noupdate -group offload_xbar /acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/ready_i
add wave -noupdate -group offload_xbar /acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/ready_o
add wave -noupdate -group offload_xbar /acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/idx_o
add wave -noupdate -group offload_xbar /acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/sel_i
add wave -noupdate -group offload_xbar /acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/data_i
add wave -noupdate -group offload_xbar /acc_interconnect_tb/dut/acc_interconnect_i/offload_xbar_i/data_o
add wave -noupdate -group response_xbar /acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/valid_i
add wave -noupdate -group response_xbar /acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/valid_o
add wave -noupdate -group response_xbar /acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/ready_i
add wave -noupdate -group response_xbar /acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/ready_o
add wave -noupdate -group response_xbar /acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/idx_o
add wave -noupdate -group response_xbar /acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/sel_i
add wave -noupdate -group response_xbar /acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/data_i
add wave -noupdate -group response_xbar /acc_interconnect_tb/dut/acc_interconnect_i/response_xbar_i/data_o
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {0 ps} 0}
quietly wave cursor active 0
configure wave -namecolwidth 150
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 1
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
WaveRestoreZoom {0 ps} {149461 ps}
