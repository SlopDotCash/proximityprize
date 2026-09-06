# W13 paper recurrence correction

The [primary paper](https://arxiv.org/html/2606.27075v1), equations 1.1 and 1.3 and the forward-difference definition in section 1.1, gives

`W_(t+2) = 2 W_(t+1) - (I + Delta^(a,b)) W_t`, with `W_0=W_1=I`.

Here `Delta^(a,b)=b*((q+1)I-A)-aI`. This follows by expanding the forward second difference in the stated wave equation. The probe instead implements `K_(t+1)=A K_t-q K_(t-1)`, with `K_0=I, K_1=A`. The different first step already disproves the asserted direct identification on its nontrivial loopless graphs.

The implementation is retained as a polynomial recurrence diagnostic, with its false paper attribution removed from the module and function descriptions. Computational statements are unchanged; an AST comparison excluding docstrings and output strings verifies this. Python compilation and documentation checks pass. This does not implement the actual wave kernels or validate the paper's trace formula. Full F1/F2 replay and archive review remain pending; completed retention coverage remains 56/92.
