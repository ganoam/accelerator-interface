# Accelerator Interface

The accelerator interface is used to offload entire RISC-V instructions and relevant operands to compatible accelerators.
The interface features two independent decoupled channels.
One for offloading the operation and a back-channel for write-back of the result.
A more thourough documentation can be found in the [docs](doc/index.md) folder.

## List of Modules

| Name               | Description                                                        | Status         |
| ------------------ | --------------------------------------------------------------- | ----------------- |
| `acc_intf`         | Systemverilog interface definition of the `accelerator interface`. | in development |
| `acc_interconnect` | Accelerator offload and response path.                             | in development |
| `acc_adapter`      | Accelerator-agnostic instruction offloading adapter.               | in development |
| `acc_predecoder`   | Accelerator-specific instruction predecoder.                       | in development |
