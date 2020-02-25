
# MESI protocol modeling
MESI protocol modeling with Promela.
Implementation is based on this [Wikipedia arcticle](https://en.wikipedia.org/wiki/MESI_protocol),
however many concepts are omitted for simplicity - for example cache-to-cache transfers
are not implemented, and only `BusRd` and `BusRdX` signals are implemented.

Every CPU does a certain amount of steps (configurable via `STEP_NUM` macro) in which it either
reads or writes to a random memory.
Note that `STEP_NUM` is very important for the verification - if it is too high, the
verification takes too much time.
`STEP_NUM = 3` seems to be reasonable choice.

## Data structures
The caches and the memory are represented with global variables - both arrays.


## Communication between CPUs
### Signals
There are only two signals implemented from the Wiki article - `BusRd` and `BusRdX`.
Originally, there were more signals but the code base was so complex that it became virtually
impossible to verify anything.

### Channels
The communication between CPUs is modeled with two types of channels - `req_channel`, and `resp_channel`.
When a CPU decides to do an operation, for example read, it sends `BusRd` signal to `req_channel` of
every other CPU in a for cycle.
When a CPU wants to respond to a request, it checks its `req_channel`, and sends a reponds to
the corresponding sender.

Communication via channels is **blocking** ie. there are no `timeout` statements, neither there are
polling of channels.

Every CPU runs in a cycle in which it does these steps:
1. Signal all other CPUs about intended operation via `signal_all` inline function.
2. Respond to the requests made by other CPUs via `respond` inline function.
3. Block the CPU's `resp_channel` untill it receives all the responses it needs in order
  to continue with the operation, eg. in write operation it waits untill it receives
  an acknowledgement from other CPUs (denoted as `Invalid` message - see code for more info).
  In read operation it may receive `Invalid`, or `Shared` messages.
4. If the operation was not canceled, do the actual operation, eg. write into cache
  and mark it as Modified. If it was canceled, do nothing.

## Operation cancelation
Under certain circumstances, an operation by a CPU may be canceled.
For example when two CPUs decide to write to the same memory, both of them will cancel the
operation, or when one CPU wants to read and other CPU wants to write the same memory, the
former CPU cancels the operation.

## Constraints
- Allowed states for two cache lines with same index and same `tag` on two different CPUs:
    - `I I`
    - `M I`
    - `E I`
    - `S I`
    - `S S`
    - ie. either one is Invalid or both are Shared.
    - This is verified in two LTL formulas.
- If there is a Modified cache line with `addr` tag on CPU `cpu_idx`, and this CPU gets
  `BusRd`, or `BusRdX` signals, this cache line will be flushed into `memory[addr]`.
- *Consistency of caches*, eg. if a cache line is Modified, its `tag` must be correctly set.
  This consistency is checked periodically in `assert_correct_cache_state`, from within
  the cpu process itself.
