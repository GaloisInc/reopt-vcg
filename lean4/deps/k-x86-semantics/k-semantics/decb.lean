def decb1 : instruction :=
  definst "decb" $ do
    pattern fun (v_2685 : reg (bv 8)) => do
      v_4379 <- getRegister v_2685;
      v_4380 <- eval (sub v_4379 (expression.bv_nat 8 1));
      setRegister (lhs.of_reg v_2685) v_4380;
      setRegister of (mux (bit_and (eq (extract v_4379 0 1) (expression.bv_nat 1 1)) (eq (extract v_4379 1 8) (expression.bv_nat 7 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4380 0 8));
      setRegister zf (zeroFlag v_4380);
      setRegister af (mux (eq (extract v_4379 4 8) (expression.bv_nat 4 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (extract v_4380 0 1);
      pure ()
    pat_end;
    pattern fun (v_2689 : reg (bv 8)) => do
      v_4400 <- getRegister v_2689;
      v_4401 <- eval (sub v_4400 (expression.bv_nat 8 1));
      setRegister (lhs.of_reg v_2689) v_4401;
      setRegister of (mux (bit_and (eq (extract v_4400 0 1) (expression.bv_nat 1 1)) (eq (extract v_4400 1 8) (expression.bv_nat 7 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4401 0 8));
      setRegister af (mux (eq (extract v_4400 4 8) (expression.bv_nat 4 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_4401);
      setRegister sf (extract v_4401 0 1);
      pure ()
    pat_end;
    pattern fun (v_2682 : Mem) => do
      v_10009 <- evaluateAddress v_2682;
      v_10010 <- load v_10009 1;
      v_10011 <- eval (sub v_10010 (expression.bv_nat 8 1));
      store v_10009 v_10011 1;
      setRegister of (mux (bit_and (eq (extract v_10010 0 1) (expression.bv_nat 1 1)) (eq (extract v_10010 1 8) (expression.bv_nat 7 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_10011 0 8));
      setRegister af (mux (eq (extract v_10010 4 8) (expression.bv_nat 4 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_10011);
      setRegister sf (extract v_10011 0 1);
      pure ()
    pat_end
