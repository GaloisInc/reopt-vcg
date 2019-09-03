def decl1 : instruction :=
  definst "decl" $ do
    pattern fun (v_2685 : reg (bv 32)) => do
      v_4404 <- getRegister v_2685;
      v_4405 <- eval (sub v_4404 (expression.bv_nat 32 1));
      setRegister (lhs.of_reg v_2685) v_4405;
      setRegister of (mux (bit_and (eq (extract v_4404 0 1) (expression.bv_nat 1 1)) (eq (extract v_4404 1 32) (expression.bv_nat 31 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4405 24 32));
      setRegister zf (zeroFlag v_4405);
      setRegister af (mux (eq (extract v_4404 28 32) (expression.bv_nat 4 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (extract v_4405 0 1);
      pure ()
    pat_end;
    pattern fun (v_2682 : Mem) => do
      v_9441 <- evaluateAddress v_2682;
      v_9442 <- load v_9441 4;
      v_9443 <- eval (sub v_9442 (expression.bv_nat 32 1));
      store v_9441 v_9443 4;
      setRegister of (mux (bit_and (eq (extract v_9442 0 1) (expression.bv_nat 1 1)) (eq (extract v_9442 1 32) (expression.bv_nat 31 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_9443 24 32));
      setRegister af (mux (eq (extract v_9442 28 32) (expression.bv_nat 4 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_9443);
      setRegister sf (extract v_9443 0 1);
      pure ()
    pat_end
