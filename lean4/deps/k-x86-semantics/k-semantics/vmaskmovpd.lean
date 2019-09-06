def vmaskmovpd1 : instruction :=
  definst "vmaskmovpd" $ do
    pattern fun (v_2592 : Mem) (v_2593 : reg (bv 128)) (v_2594 : reg (bv 128)) => do
      v_9785 <- getRegister v_2593;
      v_9787 <- evaluateAddress v_2592;
      v_9788 <- load v_9787 16;
      setRegister (lhs.of_reg v_2594) (concat (mux (isBitSet v_9785 0) (extract v_9788 0 64) (expression.bv_nat 64 0)) (mux (isBitSet v_9785 64) (extract v_9788 64 128) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2597 : Mem) (v_2598 : reg (bv 256)) (v_2599 : reg (bv 256)) => do
      v_9796 <- getRegister v_2598;
      v_9798 <- evaluateAddress v_2597;
      v_9799 <- load v_9798 32;
      setRegister (lhs.of_reg v_2599) (concat (mux (isBitSet v_9796 0) (extract v_9799 0 64) (expression.bv_nat 64 0)) (concat (mux (isBitSet v_9796 64) (extract v_9799 64 128) (expression.bv_nat 64 0)) (concat (mux (isBitSet v_9796 128) (extract v_9799 128 192) (expression.bv_nat 64 0)) (mux (isBitSet v_9796 192) (extract v_9799 192 256) (expression.bv_nat 64 0)))));
      pure ()
    pat_end;
    pattern fun (v_2583 : reg (bv 128)) (v_2584 : reg (bv 128)) (v_2582 : Mem) => do
      v_12323 <- evaluateAddress v_2582;
      v_12324 <- getRegister v_2584;
      v_12326 <- getRegister v_2583;
      v_12328 <- load v_12323 16;
      store v_12323 (concat (mux (isBitSet v_12324 0) (extract v_12326 0 64) (extract v_12328 0 64)) (mux (isBitSet v_12324 64) (extract v_12326 64 128) (extract v_12328 64 128))) 16;
      pure ()
    pat_end;
    pattern fun (v_2588 : reg (bv 256)) (v_2589 : reg (bv 256)) (v_2587 : Mem) => do
      v_12337 <- evaluateAddress v_2587;
      v_12338 <- getRegister v_2589;
      v_12340 <- getRegister v_2588;
      v_12342 <- load v_12337 32;
      store v_12337 (concat (mux (isBitSet v_12338 0) (extract v_12340 0 64) (extract v_12342 0 64)) (concat (mux (isBitSet v_12338 64) (extract v_12340 64 128) (extract v_12342 64 128)) (concat (mux (isBitSet v_12338 128) (extract v_12340 128 192) (extract v_12342 128 192)) (mux (isBitSet v_12338 192) (extract v_12340 192 256) (extract v_12342 192 256))))) 32;
      pure ()
    pat_end
