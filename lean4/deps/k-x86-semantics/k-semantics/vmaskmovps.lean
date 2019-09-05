def vmaskmovps1 : instruction :=
  definst "vmaskmovps" $ do
    pattern fun (v_2587 : Mem) (v_2588 : reg (bv 128)) (v_2589 : reg (bv 128)) => do
      v_9790 <- getRegister v_2588;
      v_9792 <- evaluateAddress v_2587;
      v_9793 <- load v_9792 16;
      setRegister (lhs.of_reg v_2589) (concat (mux (isBitSet v_9790 0) (extract v_9793 0 32) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_9790 32) (extract v_9793 32 64) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_9790 64) (extract v_9793 64 96) (expression.bv_nat 32 0)) (mux (isBitSet v_9790 96) (extract v_9793 96 128) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_2592 : Mem) (v_2593 : reg (bv 256)) (v_2594 : reg (bv 256)) => do
      v_9809 <- getRegister v_2593;
      v_9811 <- evaluateAddress v_2592;
      v_9812 <- load v_9811 32;
      setRegister (lhs.of_reg v_2594) (concat (mux (isBitSet v_9809 0) (extract v_9812 0 32) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_9809 32) (extract v_9812 32 64) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_9809 64) (extract v_9812 64 96) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_9809 96) (extract v_9812 96 128) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_9809 128) (extract v_9812 128 160) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_9809 160) (extract v_9812 160 192) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_9809 192) (extract v_9812 192 224) (expression.bv_nat 32 0)) (mux (isBitSet v_9809 224) (extract v_9812 224 256) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end;
    pattern fun (v_2578 : reg (bv 128)) (v_2579 : reg (bv 128)) (v_2577 : Mem) => do
      v_12334 <- evaluateAddress v_2577;
      v_12335 <- getRegister v_2579;
      v_12337 <- getRegister v_2578;
      v_12339 <- load v_12334 16;
      store v_12334 (concat (mux (isBitSet v_12335 0) (extract v_12337 0 32) (extract v_12339 0 32)) (concat (mux (isBitSet v_12335 32) (extract v_12337 32 64) (extract v_12339 32 64)) (concat (mux (isBitSet v_12335 64) (extract v_12337 64 96) (extract v_12339 64 96)) (mux (isBitSet v_12335 96) (extract v_12337 96 128) (extract v_12339 96 128))))) 16;
      pure ()
    pat_end;
    pattern fun (v_2583 : reg (bv 256)) (v_2584 : reg (bv 256)) (v_2582 : Mem) => do
      v_12358 <- evaluateAddress v_2582;
      v_12359 <- getRegister v_2584;
      v_12361 <- getRegister v_2583;
      v_12363 <- load v_12358 32;
      store v_12358 (concat (mux (isBitSet v_12359 0) (extract v_12361 0 32) (extract v_12363 0 32)) (concat (mux (isBitSet v_12359 32) (extract v_12361 32 64) (extract v_12363 32 64)) (concat (mux (isBitSet v_12359 64) (extract v_12361 64 96) (extract v_12363 64 96)) (concat (mux (isBitSet v_12359 96) (extract v_12361 96 128) (extract v_12363 96 128)) (concat (mux (isBitSet v_12359 128) (extract v_12361 128 160) (extract v_12363 128 160)) (concat (mux (isBitSet v_12359 160) (extract v_12361 160 192) (extract v_12363 160 192)) (concat (mux (isBitSet v_12359 192) (extract v_12361 192 224) (extract v_12363 192 224)) (mux (isBitSet v_12359 224) (extract v_12361 224 256) (extract v_12363 224 256))))))))) 32;
      pure ()
    pat_end
