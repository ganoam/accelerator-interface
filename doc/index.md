# Accelerator Interface

The `accelerator_interface` is a portable interface for RISC-V CPU cores to communicate with external functional units.
The interface provides a unified way to implement custom ISA extensions in external accelerator structures and to share accelerator units among multiple cores.
The design concurrently supports core-private and shared functional units.
It implements two independent decoupled channels (request and response) which are handshaked according to the following scheme:

  - The initiator asserts `valid`. The assertion of `valid` must not depend on `ready`. The assertion of `ready` may depend on `valid`.
  - Once `valid` has been asserted all data must remain stable.
  - The receiver asserts `ready` whenever it is ready to receive the transaction. Asserting `ready` by default is allowed. While `valid` is low, `ready` may be retracted at any time.
  - When both `valid` and `ready` are high the transaction is successful.

## Overview

### Hierarchical Interconnect
The accelerator interface is designed to enable a number of flexible topologies.
The simplest topology is the direct attachment of one or multiple accelerator to a single CPU core.
The interconnect also supports sharinig of accelerators accross multiple accelerators accross multiple cores in a cluster-like topology.
The sharing granularity of accelerators is flexible.
Any number of cores in a cluster can be connected to share a selection of accelerators resulting in a hierarchical interconnect.

An example cluster topology is shown below.
The cluster features a total of four cores.
Each core is connected to four core-private accelerators.
Two cores each share a set of another two accelerators.
Finally, two accelerators are shared among all cluster cores.

![Accelerator Interconnect](img/acc-interconnect.svg)

### Multiple Accelerators of the Same Type
The depicted interconnect schematic relies upon the [stream\_xbar](https://github.com/pulp-platform/common_cells/blob/master/src/stream_xbar.sv) IP to facilitate routing of requests and responses from and to the accelerator structures.
One limitation of using this IP is that it is not possible to utilize multiple accelerators of the same type at the same accelerator address.
This issue will be relieved by implementing a variant of the IP which uses a N:K streaming arbiter in the output path of the stream\_xbar.
An according IP exists in the [APU Cluster](https://github.com/pulp-platform/apu_cluster/tree/master/sourcecode/marx).

### Accelerator-agnostic Instruction offloading
To decouple the development of accelerators and cores, it may be beneficial separate the handling of offloaded instructions from the rest of the core's operation.
To minimize the hardware changes to the core architecture to support ISA extensions through external accelerators, a specialized [Accelerator Adapter](accelerator_agnostic_interface.md) module has been defined.

## Interface Definition
The accelerator interconnect features two independent decoupled channels for offloading requests and accelerator write-back.

### Request Channel (`q`)
An offload request comprises the entire 32-bit RISC-V instruction three operands and a request ID tag specifying requesting entity.
The nature of the offloaded instructions is not of importance to the accelerator interconnect.
The request channel interface signals are:

| Signal Name   | Width / Range              | Description                                     |
| ------------- | -------------------------- | ----------------------------------------------- |
| `q_addr`      | `clog2(NumHier)` / MSB     | Accelerator hierarchy level.                    |
|               | `clog2(max(NumReq))` / LSB | Accelerator Address. Unique per hierarchy level |
| `q_id`        | `clog2(NumReq)` / MSB      | Requester ID.                                   |
|               | `5` / `4:0`                | Destination Register Address                    |
| `q_data_op`   | `31`                       | RISC-V Instruction Data                         |
| `q_data_arga` | `DataWidth`                | Operand A                                       |
| `q_data_argb` | `DataWidth`                | Operand B                                       |
| `q_data_argc` | `DataWidth`                | Operand C                                       |

Notes:
  - The accelerator address `q_addr` is partitioned into the MSB Range identifying the interconnect hierarchy level of the target accelerator and the LSB Range denoting the accelerator address within a given hierarchy level.
    The total width of the accelerator address signal is given by `clog2(Number of hierarchy levels) + clog2(max(Number of accelerators per level))`
    The full accelerator address must be known to the offloading entity (core or [accelerator adapter](accelerator_agnostic_interface.md)).
  - The `q_id` signal uniquely identifies the response target of any request.
    On the core level, the signal is assigned five bits `4:0` identifying the eventual destination register.
    During traversal of the accelerator interconnect, the signal is extended with an additional `clog2(NumReq)` bits at the MSB end, to identify the originating port.
    The width of the signal at the core request input port of the interconnect is 5 bits.
    The width at the accelerator request output port of the interconnect is `5+clog2(NumReq)` bits.
    `NumReq` denotes the number of requesting entities in the target interconnect hierarchy level.
    The signal is latched by the accelerator subsystem and used for eventual route-back of the instruction write-back data.


### Response Channel (`p`)
*Not* every operation which was offloaded must ultimately return a response.
If a response is returned, the response channel carries the following signals:

| Signal Name   | Range                   | Description                          |
| ------------- | ----------------------- | ------------------------------------ |
| `p_id`        | MSB                     | Requester ID                         |
|               | `4:0`                   | Destination Register Address         |
| `p_data0`     | `DataWidth-1:0`         | Primary Writeback Data               |
| `p_data1`     | `DataWidth-1:0`         | Secondary Writeback Data             |
| `p_dualwb`    | `0:0`                   | Dual-Writeback Response              |
| `p_error`     | `0:0`                   | Error Flag                           |

Notes:
  - `p_data0` and `p_data1` carry the response data resulting from offloaded instructions.
    `p_data0` carries the default write-back data and is written to the destination register identified by `p_rd_id`.
    `p_data1` is used only for dual-writeback instructions.
  - Dual write-back instructions are marked by the accelerator sub-system by setting `p_dualwb`.
  - The error flag included in the response channel indicates processing errors encountered by the accelerator.
    The actions to be taken by a core to recover from accelerator errors are not yet fully defined.

## Interconnect Module
The interconnect module is instantiated at each hierarchy level.

### Parameters

#### Level Specific Parameters
On each interconnect level, the following parameters are set:
| Name               | Type / Range  | Description                                      |
| ------------------ | ------------- | ------------------------------------------------ |
| `NumReq`           | `int` (>=1)   | Number of requesting entities                    |
| `NumRsp`           | `int` (>=1)   | Number of responding entities                    |
| `HierLevel`        | `int` (>=0)   | Hierarchical position of the interconnect module |
| `RegisterReq`      | `bit` (0,1)   | Register Request Path                            |
| `RegisterRsp`      | `bit` (0,1)   | Register Response Path                           |

##### Global Parameters

| Name               | Type / Value                   | Description                                    |
| ------------------ | ------------------------------ | ---------------------------------------------- |
| `NumHier`          | `int` (>=1)   | Number of hierarchical levels                    |
| `

#### Global Interconnect Parameters
The following parameters are set on the cluster level and are the same for each interconnect level

| Name               | Type / Range  | Description                                |
| ------------------ | ------------- | ------------------------------------------ |
| `NumReq`           | `int` (>=1)   | Number of requesting entities              |
| `NumRsp`           | `int` (>=1)   | Number of responding entities              |
| `HierLevel`        | `int` (>=0)   | Position of the interconnect module


On each hierarchy level, the following dependent paramters are
| Name               | Value              | Description                           |
| ------------------ | ------------------ | ------------------------------------- |
| `ExtIdWidth`       | `5 + clog2(NumReq) | Extended Width of Request ID Signal   |






| `AccAddrWidth`     | `int` clog2(max(NumRespPriv, NumRespShared)) + 1 | Accelerator Address                        |
| `DataWidth`        | `int` (32, 64, 128)                              | ISA Bit Width                              |
## Channels


### Response Channel (`p`)
*Not* every operation which was offloaded must ultimately return a response.
If a response is returned, the response channel carries the following signals:

| Signal Name   | Range                   | Description                          |
| ------------- | ----------------------- | ------------------------------------ |
| `p_req_id`    | `clog2(NumReq)-1:0`     | Requester ID                         |
| `p_rd_id`     | `4:0`                   | Destination Register Address         |
| `p_data0`     | `DataWidth-1:0`         | Primary Writeback Data               |
| `p_data1`     | `DataWidth-1:0`         | Secondary Writeback Data             |
| `p_dualwb`    | `0:0`                   | Dual-Writeback Response.             |
| `p_error`     | `0:0`                   | Error Flag                           |

Notes:
  - The *Requester ID* signal is used to route responses generated in external accelerators back to the offloading core.
  - `p_data0` and `p_data1` carry the response data resulting from offloaded instructions.
    `p_data0` carries the default write-back data and is written to the destination register identified by `p_rd_id`.
    `p_data1` is used only for dual-writeback instructions.
  - Dual write-back instructions are marked by the accelerator sub-system by setting `p_dualwb`.
  - The error flag included in the response channel indicates processing errors encountered by the accelerator.
    The actions to be taken by a core to recover from accelerator errors are not yet fully defined.

## Core Support
In order to make use of the accelerator interface, a compliant core must
  - Generate accelerator interface signals.
    - On the core level the *q_id* signal comprises only the destination register address.
      The *Requester ID* is appended to the MSB range of the signal depending on the location of the core within the cluster.
  - Handle handshaking with the accelerator interconnect.
  - Maintain a scoreboard to keep track of outstanding accelerator write-backs.
    The core can continue normal operation during accelerator operation unless a source register reserved by an offloaded instruction is used.
  - The core must wait for any outstanding write-backs before entering sleep mode in case of a wait for interrupt (`wfi`) instruction.

### Operand Origin
The operands forwarded to the accelerator interconnect are determined in the same way as any regular RISC-V instructions.
Any source registers from the integer register file of the offloading core and encoded immediate values as defined in the [RISC-V User-Level ISA specification](https://riscv.org/wp-content/uploads/2017/05/riscv-spec-v2.2.pdf#page=24) are allowed.
If source registers are used, operand A, B and C contain `rs1`, `rs2` and `rs3` respectively.
For ternary instructions, the instruction format R4-type instruction format is to be used, defining the `rs3` register address by bits `instr_data[31:27]`.

### Write-back Destination
The default writeback destination for offloaded instruction is the RISC-V destination register specified by `instr_data[11:7]`.

### Dual-Writeback Instructions
This section of the specification provides *preliminary* information.
The contents are subject to discussion and may change anytime.

Custom ISA extensions may mandate dual register writebacks.
In order to accomodate that need we provision the possibility to reserve multiple destination registers for a single offloaded instruction.
For even destination registers other than `X0`,  `Xn` and `Xn+1` are reserved for write-back upon offloading a dual write-back instruction, where `Xn` denotes the destination register addresss extracted from `instr_data[11:7]`.

For responses resulting from dual-writeback instructions, the accelerator asserts `p_dualwb`.
Upon accepting the accelerator response, the offloading core writes back data contained in `p_data0` to register `p_id[4:0]`.
`p_data1` is written back to `p_id[4:0]` + 1.


In order to maximize benefits from dual-writeback instructions, the interconnect response path must accomodate simultaneous transfer of two operation results (`p_data0` and `p_data1`).
If none of the connected accelerators implement dual write-back instructions, the according signal paths will be removed by synthesis tools.

In order to support accelerators implementing dual write-back instructions, the offloading core must include provisions to reserve two destination registers upon offloading an instruction.
Also, the core should include provisions for simultaneous writeback, implying dual write-ports to the internal register file.

### Accelerator-Agnostic Cores
To decouple the development of accelerators and cores, it may be beneficial separate the handling of offloaded instructions from the rest of the core's operation.
An external pre-decoder structure may be implemented to facilitate this use case.

A tentative specification thereof is given [here](accelerator_agnostic_interface.md)

## Accelerator Support
In order to accept instructions off the accelerator interface, an accelerator subsystem must decode the RISC-V instruction data and generate the specific control signals for communication with the accelerator.
For instructions mandating writeback to the core, the request ID must be returned together with the according response packet.

![Accelerator Subsystem](img/acc-ss.svg)


## Open Questions

### Memory Consistency
In the event of offloaded memory access instructions, there is currently no way to guarantee the order in which the operations are executed.
At the moment, no ultimate solution exists in our design.
The fact that outstanding register file writebacks can be detected in the scoreboard of the offloading core provides some measure of control.
However, it is not guaranteed that the accelerator will not make memory requests that do not impact the integer register file.
To handle this case, we could implement a memory fence instruction, which would need to be sent to each accelerator that is capable of accessing memory.

For more information, ideas and contributions to the subject, please refer to the corresponding [issue](https://github.com/ganoam/accelerator-interface/issues/2).

### External Register Files
*Tentative specification*
In case of shared accelerators relying on dedicated register files, a shared accelerator needs to maintain one private register file per sharing core.
Similarly, for status-based extensions the accelerator subsystem must separately maintain the the status of each core.

