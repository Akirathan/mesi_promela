
## Communication between CPUs

## Operation cancelation

## Constraints
- Allowed states for two cache lines with same index and same `tag` on two different CPUs:
    - `I I`
    - `M I`
    - `E I`
    - `S I`
    - `S S`
    - ie. either one is Invalid or both are Shared.
- If there is a Modified cache line with `addr` tag on CPU `cpu_idx`, and this CPU gets
  `BusRd`, or `BusRdX` signals, this cache line will be flushed into `memory[addr]`.
